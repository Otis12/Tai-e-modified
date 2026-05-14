/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.core.solver.profile;

import com.fasterxml.jackson.databind.ObjectMapper;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.summary.JdkBoundaryClassifier;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Set;
import java.util.function.ToIntFunction;

/**
 * Exports method-level CG/PTA evidence for single-run heavy pollution review.
 *
 * <p>This profiler observes solver events after they happen. It does not
 * influence propagation, call graph construction, or summary decisions.</p>
 */
public class PtaHeavyMethodProfiler {

    public static final String DEFAULT_CI_METHOD_PROFILE_FILE =
            "pta-ci-method-profile.json";

    public static final String DEFAULT_METHOD_METRICS_FILE =
            "pta-method-cg-pta-metrics.json";

    public static final String DEFAULT_HEAVY_METHODS_FILE =
            "pta-heavy-polluting-methods.json";

    public static final String DEFAULT_HEAVY_METHODS_MARKDOWN_FILE =
            "pta-heavy-polluting-methods.md";

    public static final String DEFAULT_HEAVY_METHOD_CALLGRAPH_FILE =
            "pta-heavy-method-callgraph.json";

    private static final ObjectMapper JSON = new ObjectMapper();

    private static final int MAX_TOP_NEIGHBORS = 8;

    private final AnalysisOptions options;

    private final JdkBoundaryClassifier classifier;

    private final Map<String, MethodStats> methods = Maps.newLinkedHashMap();

    private final List<CallEdgeInfo> callEdges = new ArrayList<>();

    private final Map<Obj, String> allocationOwners = new IdentityHashMap<>();

    private final Set<String> seenPfgEdges = Sets.newLinkedSet();

    private final long startNanos = System.nanoTime();

    private List<HeavyMethod> heavyMethods = List.of();

    public PtaHeavyMethodProfiler(AnalysisOptions options,
                                  JdkBoundaryClassifier classifier) {
        this.options = options;
        this.classifier = Objects.requireNonNull(classifier, "classifier");
    }

    public boolean isEnabled() {
        String configured = optionString("pta-heavy-method-profile");
        return configured != null && !configured.isBlank();
    }

    public void recordReachableMethod(JMethod method, boolean bodyProcessed,
                                      String ignoredReason) {
        if (method == null) {
            return;
        }
        MethodStats stats = method(method);
        stats.reachable = true;
        stats.bodyProcessed = stats.bodyProcessed || bodyProcessed;
        if (ignoredReason != null) {
            stats.ignoredReason = ignoredReason;
        }
        if (bodyProcessed) {
            scanIrState(stats, method);
        }
    }

    public void recordAllocation(JMethod method, Obj obj) {
        if (method == null || obj == null) {
            return;
        }
        MethodStats stats = method(method);
        stats.allocationCount++;
        allocationOwners.put(obj, method.getSignature());
    }

    public void recordCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (edge == null || edge.getCallee() == null
                || edge.getCallSite() == null) {
            return;
        }
        CSCallSite csCallSite = edge.getCallSite();
        JMethod caller = csCallSite.getContainer() == null
                ? null : csCallSite.getContainer().getMethod();
        JMethod callee = edge.getCallee().getMethod();
        if (caller == null || callee == null) {
            return;
        }
        MethodStats callerStats = method(caller);
        MethodStats calleeStats = method(callee);
        String callerSig = caller.getSignature();
        String calleeSig = callee.getSignature();
        String callsiteId = callsiteId(caller, csCallSite);

        callerStats.outgoingCallEdgeCount++;
        callerStats.calleeCounts.merge(calleeSig, 1, Integer::sum);
        calleeStats.incomingCallEdgeCount++;
        calleeStats.callerCounts.merge(callerSig, 1, Integer::sum);
        calleeStats.callsiteIds.add(callsiteId);
        if (caller.isApplication()) {
            calleeStats.directAppCallsiteIds.add(callsiteId);
            calleeStats.directAppCallers.add(callerSig);
        }
        callEdges.add(new CallEdgeInfo(callerSig, calleeSig, callsiteId));
    }

    public void recordPFGEdge(PointerFlowEdge edge) {
        if (edge == null) {
            return;
        }
        String edgeKey = edge.kind() + "|" + edge.source() + "|"
                + edge.target();
        if (!seenPfgEdges.add(edgeKey)) {
            return;
        }
        String sourceOwner = ownerMethodOfPointer(edge.source());
        String targetOwner = ownerMethodOfPointer(edge.target());
        if (sourceOwner != null) {
            MethodStats stats = methods.get(sourceOwner);
            if (stats != null) {
                stats.pfgOutDegreeSum++;
            }
        }
        if (targetOwner != null) {
            MethodStats stats = methods.get(targetOwner);
            if (stats != null) {
                stats.pfgInDegreeSum++;
            }
        }
        recordPfgKind(edge.kind(), sourceOwner, targetOwner, edgeKey,
                edge.source(), edge.target());
    }

    public void recordPropagate(Pointer pointer, PointsToSet diff) {
        if (pointer == null || diff == null || diff.isEmpty()) {
            return;
        }
        String owner = ownerMethodOfPointer(pointer);
        if (owner == null) {
            recordAllocationConsumers(pointer, diff);
            return;
        }
        MethodStats stats = methods.get(owner);
        if (stats == null) {
            recordAllocationConsumers(pointer, diff);
            return;
        }
        stats.methodPtsTotal += diff.size();
        int currentPtsSize = currentPtsSize(pointer, diff);
        if (pointer instanceof CSVar csVar) {
            recordVarPointsTo(stats, csVar.getVar(), currentPtsSize, diff);
        }
        recordAllocationConsumers(pointer, diff);
    }

    public Map<String, String> writeArtifacts() {
        if (!isEnabled()) {
            return Map.of();
        }
        computeAppReachability();
        computeHeavyMethods();
        Path heavyPath = heavyMethodsPath();
        Path artifactDir = artifactDir(heavyPath);
        Path profilePath = artifactDir.resolve(DEFAULT_CI_METHOD_PROFILE_FILE);
        Path metricsPath = artifactDir.resolve(DEFAULT_METHOD_METRICS_FILE);
        Path markdownPath = artifactDir.resolve(
                DEFAULT_HEAVY_METHODS_MARKDOWN_FILE);
        Path callGraphPath = artifactDir.resolve(
                DEFAULT_HEAVY_METHOD_CALLGRAPH_FILE);

        writeJson(profilePath, methodProfilePayload());
        writeJson(metricsPath, metricsPayload());
        writeJson(heavyPath, heavyMethodsPayload());
        writeJson(callGraphPath, heavyMethodCallGraphPayload());
        writeMarkdown(markdownPath, heavyMethodsMarkdown());

        Map<String, String> paths = Maps.newLinkedHashMap();
        paths.put("pta_ci_method_profile", profilePath.toString());
        paths.put("pta_method_cg_pta_metrics", metricsPath.toString());
        paths.put("pta_heavy_polluting_methods", heavyPath.toString());
        paths.put("pta_heavy_polluting_methods_markdown",
                markdownPath.toString());
        paths.put("pta_heavy_method_callgraph", callGraphPath.toString());
        return paths;
    }

    private void scanIrState(MethodStats stats, JMethod method) {
        IR ir = method.getIR();
        Var thisVar = ir.getThis();
        for (Stmt stmt : ir.getStmts()) {
            if (stmt instanceof LoadField loadField) {
                stats.fieldIrAccessCount++;
                if (thisVar != null && loadField.getFieldAccess()
                        instanceof pascal.taie.ir.exp.InstanceFieldAccess access
                        && access.getBase() == thisVar) {
                    stats.receiverStateEffect = true;
                }
            } else if (stmt instanceof StoreField storeField) {
                stats.fieldIrAccessCount++;
                if (thisVar != null && storeField.getFieldAccess()
                        instanceof pascal.taie.ir.exp.InstanceFieldAccess access
                        && access.getBase() == thisVar) {
                    stats.receiverStateEffect = true;
                }
            } else if (stmt instanceof LoadArray) {
                stats.arrayIrAccessCount++;
            } else if (stmt instanceof StoreArray) {
                stats.arrayIrAccessCount++;
            }
        }
    }

    private void recordPfgKind(FlowKind kind, String sourceOwner,
                               String targetOwner, String edgeKey,
                               Pointer source, Pointer target) {
        if (kind == FlowKind.RETURN) {
            addReturnEdge(sourceOwner, edgeKey);
        }
        if (kind == FlowKind.INSTANCE_LOAD
                || kind == FlowKind.INSTANCE_STORE
                || kind == FlowKind.STATIC_LOAD
                || kind == FlowKind.STATIC_STORE) {
            addFieldEdge(sourceOwner, edgeKey);
            addFieldEdge(targetOwner, edgeKey);
            markReceiverState(sourceOwner, source, target);
            markReceiverState(targetOwner, source, target);
        }
        if (kind == FlowKind.ARRAY_LOAD || kind == FlowKind.ARRAY_STORE) {
            addArrayEdge(sourceOwner, edgeKey);
            addArrayEdge(targetOwner, edgeKey);
            markReceiverState(sourceOwner, source, target);
            markReceiverState(targetOwner, source, target);
        }
    }

    private void addReturnEdge(String owner, String edgeKey) {
        MethodStats stats = owner == null ? null : methods.get(owner);
        if (stats != null && stats.returnEdgeIds.add(edgeKey)) {
            stats.returnEdgeCount++;
        }
    }

    private void addFieldEdge(String owner, String edgeKey) {
        MethodStats stats = owner == null ? null : methods.get(owner);
        if (stats != null && stats.fieldEdgeIds.add(edgeKey)) {
            stats.fieldStoreLoadEdgeCount++;
        }
    }

    private void addArrayEdge(String owner, String edgeKey) {
        MethodStats stats = owner == null ? null : methods.get(owner);
        if (stats != null && stats.arrayEdgeIds.add(edgeKey)) {
            stats.arrayStoreLoadEdgeCount++;
        }
    }

    private void markReceiverState(String owner, Pointer source,
                                   Pointer target) {
        MethodStats stats = owner == null ? null : methods.get(owner);
        if (stats != null
                && (isStatePointer(source) || isStatePointer(target))) {
            stats.receiverStateEffect = true;
        }
    }

    private void recordVarPointsTo(MethodStats stats, Var var,
                                   int currentPtsSize, PointsToSet diff) {
        JMethod method = var.getMethod();
        IR ir = method.getIR();
        if (ir.isParam(var)) {
            stats.paramPtsMax = Math.max(stats.paramPtsMax, currentPtsSize);
        } else if (!ir.isThisOrParam(var)) {
            stats.localPtsMax = Math.max(stats.localPtsMax, currentPtsSize);
        }
        if (ir.getReturnVars().contains(var)) {
            diff.forEach(obj -> stats.returnObjects.add(obj.getObject()));
        }
    }

    private void recordAllocationConsumers(Pointer pointer, PointsToSet diff) {
        String pointerId = pointer.toString();
        diff.forEach(csObj -> {
            Obj obj = csObj.getObject();
            String owner = allocationOwners.get(obj);
            if (owner == null) {
                owner = obj.getContainerMethod()
                        .map(JMethod::getSignature)
                        .orElse(null);
            }
            MethodStats stats = owner == null ? null : methods.get(owner);
            if (stats != null) {
                stats.allocatedObjectConsumerPointers.add(pointerId);
            }
        });
    }

    private void computeAppReachability() {
        Map<String, Set<String>> outgoing = Maps.newLinkedHashMap();
        for (CallEdgeInfo edge : callEdges) {
            outgoing.computeIfAbsent(edge.caller, ignored -> Sets.newLinkedSet())
                    .add(edge.callee);
        }
        Set<String> appReachable = Sets.newLinkedSet();
        Queue<String> queue = new ArrayDeque<>();
        methods.values().stream()
                .filter(m -> m.reachable && m.isApp)
                .map(m -> m.signature)
                .forEach(signature -> {
                    if (appReachable.add(signature)) {
                        queue.add(signature);
                    }
                });
        while (!queue.isEmpty()) {
            String method = queue.remove();
            for (String callee : outgoing.getOrDefault(method, Set.of())) {
                if (appReachable.add(callee)) {
                    queue.add(callee);
                }
            }
        }
        for (CallEdgeInfo edge : callEdges) {
            if (!appReachable.contains(edge.caller)) {
                continue;
            }
            MethodStats callee = methods.get(edge.callee);
            if (callee != null) {
                callee.appReachableCallsiteIds.add(edge.callsiteId);
                callee.appReachableCallers.add(edge.caller);
            }
        }
    }

    private void computeHeavyMethods() {
        List<MethodStats> candidates = methods.values().stream()
                .filter(m -> m.reachable && m.bodyProcessed)
                .toList();
        Thresholds thresholds = Thresholds.from(candidates);
        double maxIncoming = max(candidates, m -> m.incomingCallEdgeCount);
        double maxAppCallsites = max(candidates,
                MethodStats::appReachableCallsiteCount);
        double maxAppCallers = max(candidates,
                m -> m.appReachableCallers.size());
        double maxReturnPts = max(candidates, MethodStats::returnPtsSize);
        double maxLocalPts = max(candidates, m -> m.localPtsMax);
        double maxMethodPts = max(candidates, m -> m.methodPtsTotal);
        double maxPfgDegree = max(candidates, MethodStats::pfgDegreeTotal);
        double maxReturnEdges = max(candidates, m -> m.returnEdgeCount);
        double maxFieldArray = max(candidates, MethodStats::fieldArrayEdgeCount);

        List<HeavyMethod> selected = new ArrayList<>();
        for (MethodStats method : candidates) {
            List<String> reasons = new ArrayList<>();
            Map<String, Object> triggered = Maps.newLinkedHashMap();
            addThresholdReason(reasons, triggered,
                    "incoming_call_edge_count", method.incomingCallEdgeCount,
                    thresholds.incomingCallEdgeCount);
            addThresholdReason(reasons, triggered,
                    "app_reachable_callsite_count",
                    method.appReachableCallsiteCount(),
                    thresholds.appReachableCallsiteCount);
            addThresholdReason(reasons, triggered,
                    "return_pts_size", method.returnPtsSize(),
                    thresholds.returnPtsSize);
            addThresholdReason(reasons, triggered,
                    "local_pts_max", method.localPtsMax,
                    thresholds.localPtsMax);
            addThresholdReason(reasons, triggered,
                    "method_pts_total", method.methodPtsTotal,
                    thresholds.methodPtsTotal);
            addThresholdReason(reasons, triggered,
                    "pfg_degree_total", method.pfgDegreeTotal(),
                    thresholds.pfgDegreeTotal);
            addThresholdReason(reasons, triggered,
                    "return_edge_count", method.returnEdgeCount,
                    thresholds.returnEdgeCount);
            addThresholdReason(reasons, triggered,
                    "field_array_edge_count", method.fieldArrayEdgeCount(),
                    thresholds.fieldArrayEdgeCount);
            if (method.receiverStateEffect && method.hasNonTrivialEvidence()) {
                reasons.add("receiver_state_effect with nontrivial CG/PTA");
                triggered.put("receiver_state_effect", true);
            }
            if (reasons.isEmpty()) {
                continue;
            }
            double score = 1.5 * normalize(method.incomingCallEdgeCount,
                    maxIncoming)
                    + 2.0 * normalize(method.appReachableCallsiteCount(),
                    maxAppCallsites)
                    + 1.5 * normalize(method.appReachableCallers.size(),
                    maxAppCallers)
                    + 2.0 * normalize(method.returnPtsSize(), maxReturnPts)
                    + 1.5 * normalize(method.localPtsMax, maxLocalPts)
                    + 1.5 * normalize(method.methodPtsTotal, maxMethodPts)
                    + 1.5 * normalize(method.pfgDegreeTotal(), maxPfgDegree)
                    + 2.0 * normalize(method.returnEdgeCount, maxReturnEdges)
                    + 1.5 * normalize(method.fieldArrayEdgeCount(),
                    maxFieldArray)
                    + (method.receiverStateEffect ? 1.0 : 0.0);
            TfProxyEvidence tfProxy = tfProxyEvidence(method, score,
                    thresholds);
            selected.add(new HeavyMethod(method, score, tfProxy, reasons,
                    triggered));
        }
        List<HeavyMethod> ptaScoreOrder = new ArrayList<>(selected);
        ptaScoreOrder.sort(Comparator
                .comparingDouble((HeavyMethod m) -> m.score)
                .reversed()
                .thenComparing(m -> m.stats.signature));
        for (int i = 0; i < ptaScoreOrder.size(); i++) {
            ptaScoreOrder.get(i).ptaScoreRank = i + 1;
        }
        selected.sort(Comparator
                .comparingDouble((HeavyMethod m) -> m.tfProxy.score())
                .reversed()
                .thenComparing(Comparator
                        .comparingDouble((HeavyMethod m) -> m.score)
                        .reversed())
                .thenComparing(m -> m.stats.signature));
        for (int i = 0; i < selected.size(); i++) {
            selected.get(i).rank = i + 1;
            selected.get(i).tfProxyRank = i + 1;
        }
        heavyMethods = selected;
    }

    private TfProxyEvidence tfProxyEvidence(MethodStats method,
                                            double ptaScore,
                                            Thresholds thresholds) {
        int localThreshold = Math.max(1, thresholds.localPtsMax);
        boolean arrayLocalShape = method.arrayStoreLoadEdgeCount > 0
                && method.localPtsMax >= localThreshold;
        boolean paramLocalShape = method.paramPtsMax > 0
                && method.localPtsMax >= localThreshold;
        boolean receiverShape = method.receiverStateEffect
                && method.localPtsMax >= localThreshold
                && (method.arrayStoreLoadEdgeCount > 0
                || method.fieldStoreLoadEdgeCount > 0);

        double score = ptaScore;
        List<String> reasons = new ArrayList<>();
        Map<String, Object> bonuses = Maps.newLinkedHashMap();
        if (method.returnsArray) {
            score += addBonus(bonuses, "returns_array", 3.0);
            reasons.add("returns_array");
        } else if (method.returnsContainerLike) {
            score += addBonus(bonuses, "returns_container_like", 1.0);
            reasons.add("returns_container_like");
        }
        if (arrayLocalShape) {
            score += addBonus(bonuses, "array_local_flow_shape", 2.5);
            reasons.add("array_local_flow_shape");
        }
        if (paramLocalShape) {
            score += addBonus(bonuses, "param_local_flow_shape", 1.5);
            reasons.add("param_local_flow_shape");
        }
        if (receiverShape) {
            score += addBonus(bonuses, "receiver_state_flow_shape", 1.5);
            reasons.add("receiver_state_flow_shape");
        }
        score += addBonus(bonuses, "array_store_load_edge_count",
                cappedBonus(method.arrayStoreLoadEdgeCount, 100.0, 2.0));
        score += addBonus(bonuses, "param_pts_max",
                cappedBonus(method.paramPtsMax, 100.0, 2.0));
        score += addBonus(bonuses, "local_pts_max",
                cappedBonus(method.localPtsMax, 1000.0, 2.0));

        return new TfProxyEvidence(score, method.returnsArray,
                method.returnsContainerLike, arrayLocalShape,
                paramLocalShape, receiverShape, List.copyOf(reasons),
                new java.util.LinkedHashMap<>(bonuses));
    }

    private static double addBonus(Map<String, Object> bonuses, String name,
                                   double bonus) {
        if (bonus > 0.0) {
            bonuses.put(name, bonus);
        }
        return bonus;
    }

    private static double cappedBonus(int value, double scale, double cap) {
        return Math.min(value / scale, cap);
    }

    private static boolean isContainerLikeReturnType(String typeName) {
        return typeName.equals("java.lang.Object")
                || typeName.equals("java.lang.String")
                || typeName.equals("java.lang.CharSequence")
                || typeName.equals("java.util.List")
                || typeName.equals("java.util.Collection")
                || typeName.equals("java.util.Set")
                || typeName.equals("java.util.Map")
                || typeName.equals("java.lang.Iterable")
                || typeName.equals("java.util.Iterator")
                || typeName.equals("java.util.Enumeration");
    }

    private void addThresholdReason(List<String> reasons,
                                    Map<String, Object> triggered,
                                    String metric, int value, int threshold) {
        if (value <= 0 || value < threshold) {
            return;
        }
        reasons.add(metric + " >= p95");
        triggered.put(metric, Map.of("value", value, "threshold", threshold));
    }

    private Object methodProfilePayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "A");
        payload.put("methods", orderedMethods().stream()
                .map(this::profileMap)
                .toList());
        return payload;
    }

    private Object metricsPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "B");
        payload.put("metric_availability", metricAvailability());
        payload.put("methods", orderedMethods().stream()
                .filter(m -> m.reachable)
                .map(this::metricsMap)
                .toList());
        return payload;
    }

    private Object heavyMethodsPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "C");
        payload.put("selection_strategy",
                "reachable && body_processed && p95 CG/PTA footprint reasons");
        payload.put("ranking_strategy",
                "tf_proxy_score desc, then PTA score desc");
        payload.put("tf_proxy_score",
                "PTA score plus bonuses for array/container returns, "
                        + "array-local flow, param-local flow, "
                        + "receiver-state flow, and capped "
                        + "array/param/local footprint");
        payload.put("included_categories",
                "app, third-party, jdk, jdk-internal, other-jdk, unknown");
        payload.put("heavy_method_count", heavyMethods.size());
        payload.put("thresholds", Thresholds.from(methods.values().stream()
                .filter(m -> m.reachable && m.bodyProcessed)
                .toList()).toMap());
        payload.put("metric_availability", metricAvailability());
        payload.put("heavy_polluting_methods", heavyMethods.stream()
                .map(HeavyMethod::toMap)
                .toList());
        return payload;
    }

    private Object heavyMethodCallGraphPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "CG");
        payload.put("analysis", "pta-heavy-method-callgraph");
        payload.put("source", "normal ci PTA call graph edges");
        payload.put("heavy_method_count", heavyMethods.size());

        Set<String> heavySignatures = heavyMethodSignatures();
        List<CallEdgeInfo> heavyEdges = heavyEdges(heavySignatures, false);
        List<CallEdgeInfo> nonAppHeavyEdges = heavyEdges(heavySignatures, true);
        List<CallComponent> withAppComponents =
                sourceComponents(heavySignatures, heavyEdges, false);
        List<CallComponent> withoutAppComponents =
                sourceComponents(heavySignatures, nonAppHeavyEdges, true);

        payload.put("heavy_method_edge_count", heavyEdges.size());
        payload.put("heavy_method_distinct_edge_count",
                distinctEdgeCount(heavyEdges));
        payload.put("heavy_method_edges", edgeMaps(heavyEdges));
        payload.put("heavy_methods_with_heavy_callers",
                methodsWithCallers(heavyEdges).stream()
                        .map(this::methodRef)
                        .toList());
        payload.put("heavy_methods_without_heavy_callers",
                sourceMethodSignatures(withAppComponents).stream()
                        .map(this::methodRef)
                        .toList());
        payload.put("top_level_components_with_app",
                withAppComponents.stream()
                        .map(component -> component.toMap(this))
                        .toList());
        payload.put("top_level_callers_with_app",
                sourceMethodSignatures(withAppComponents).stream()
                        .map(this::methodRef)
                        .toList());
        payload.put("top_level_components_without_app",
                withoutAppComponents.stream()
                        .map(component -> component.toMap(this))
                        .toList());
        payload.put("top_level_callers_without_app",
                sourceMethodSignatures(withoutAppComponents).stream()
                        .map(this::methodRef)
                        .toList());
        return payload;
    }

    private Set<String> heavyMethodSignatures() {
        return heavyMethods.stream()
                .map(method -> method.stats.signature)
                .collect(java.util.stream.Collectors.toCollection(
                        Sets::newLinkedSet));
    }

    private List<CallEdgeInfo> heavyEdges(Set<String> heavySignatures,
                                          boolean excludeApp) {
        return callEdges.stream()
                .filter(edge -> heavySignatures.contains(edge.caller)
                        && heavySignatures.contains(edge.callee))
                .filter(edge -> !excludeApp
                        || (!isApp(edge.caller) && !isApp(edge.callee)))
                .toList();
    }

    private List<Map<String, Object>> edgeMaps(List<CallEdgeInfo> edges) {
        return edges.stream()
                .sorted(Comparator.comparing(CallEdgeInfo::caller)
                        .thenComparing(CallEdgeInfo::callee)
                        .thenComparing(CallEdgeInfo::callsiteId))
                .map(edge -> {
                    Map<String, Object> item = Maps.newLinkedHashMap();
                    item.put("caller", methodRef(edge.caller));
                    item.put("callee", methodRef(edge.callee));
                    item.put("callsite_id", edge.callsiteId);
                    return item;
                })
                .toList();
    }

    private int distinctEdgeCount(List<CallEdgeInfo> edges) {
        return edges.stream()
                .map(edge -> edge.caller + "\u0000" + edge.callee)
                .collect(java.util.stream.Collectors.toSet())
                .size();
    }

    private Set<String> methodsWithCallers(List<CallEdgeInfo> edges) {
        return edges.stream()
                .map(CallEdgeInfo::callee)
                .collect(java.util.stream.Collectors.toCollection(
                        Sets::newLinkedSet));
    }

    private List<String> sourceMethodSignatures(List<CallComponent> components) {
        return components.stream()
                .flatMap(component -> component.members.stream())
                .sorted(Comparator
                        .comparingInt((String signature) -> rankOf(signature))
                        .thenComparing(signature -> signature))
                .toList();
    }

    private List<CallComponent> sourceComponents(Set<String> heavySignatures,
                                                 List<CallEdgeInfo> edges,
                                                 boolean excludeApp) {
        Set<String> nodes = heavySignatures.stream()
                .filter(signature -> !excludeApp || !isApp(signature))
                .collect(java.util.stream.Collectors.toCollection(
                        Sets::newLinkedSet));
        Map<String, Set<String>> outgoing = Maps.newLinkedHashMap();
        Map<String, Set<String>> incoming = Maps.newLinkedHashMap();
        for (String node : nodes) {
            outgoing.put(node, Sets.newLinkedSet());
            incoming.put(node, Sets.newLinkedSet());
        }
        for (CallEdgeInfo edge : edges) {
            if (nodes.contains(edge.caller) && nodes.contains(edge.callee)) {
                outgoing.computeIfAbsent(edge.caller,
                        ignored -> Sets.newLinkedSet()).add(edge.callee);
                incoming.computeIfAbsent(edge.callee,
                        ignored -> Sets.newLinkedSet()).add(edge.caller);
            }
        }
        List<Set<String>> components = stronglyConnectedComponents(nodes,
                outgoing);
        Map<String, Integer> componentIds = Maps.newLinkedHashMap();
        for (int i = 0; i < components.size(); i++) {
            for (String method : components.get(i)) {
                componentIds.put(method, i);
            }
        }
        List<CallComponent> sources = new ArrayList<>();
        for (int i = 0; i < components.size(); i++) {
            Set<String> component = components.get(i);
            boolean hasExternalIncoming = false;
            for (String method : component) {
                for (String caller : incoming.getOrDefault(method, Set.of())) {
                    Integer callerComponent = componentIds.get(caller);
                    if (callerComponent != null && callerComponent != i) {
                        hasExternalIncoming = true;
                        break;
                    }
                }
                if (hasExternalIncoming) {
                    break;
                }
            }
            if (!hasExternalIncoming) {
                sources.add(new CallComponent(component, outgoing));
            }
        }
        sources.sort(Comparator
                .comparingInt((CallComponent c) -> c.bestRank())
                .thenComparing(c -> c.members.get(0)));
        for (int i = 0; i < sources.size(); i++) {
            sources.get(i).componentRank = i + 1;
        }
        return sources;
    }

    private List<Set<String>> stronglyConnectedComponents(
            Set<String> nodes, Map<String, Set<String>> outgoing) {
        Tarjan tarjan = new Tarjan(nodes, outgoing);
        return tarjan.components();
    }

    private boolean isApp(String signature) {
        MethodStats stats = methods.get(signature);
        return stats != null && stats.isApp;
    }

    private int rankOf(String signature) {
        for (HeavyMethod method : heavyMethods) {
            if (method.stats.signature.equals(signature)) {
                return method.rank;
            }
        }
        return Integer.MAX_VALUE;
    }

    private Map<String, Object> methodRef(String signature) {
        MethodStats stats = methods.get(signature);
        Map<String, Object> item = Maps.newLinkedHashMap();
        item.put("method_signature", signature);
        item.put("declaring_class", stats == null ? null : stats.declaringClass);
        item.put("category", stats == null ? "unknown" : stats.category);
        item.put("rank", rankOf(signature) == Integer.MAX_VALUE
                ? null : rankOf(signature));
        return item;
    }

    private Map<String, Object> basePayload() {
        Map<String, Object> payload = Maps.newLinkedHashMap();
        payload.put("schema_version", 1);
        payload.put("analysis", "pta-heavy-polluting-method-profile");
        payload.put("ranking_unit", "method");
        payload.put("elapsed_ms",
                (System.nanoTime() - startNanos) / 1_000_000L);
        payload.put("options", Map.of(
                "cs", optionValue("cs"),
                "only_app", optionValue("only-app"),
                "codesummary", optionValue("codesummary"),
                "jdk_analysis_mode", optionValue("jdk-analysis-mode"),
                "merge_string_objects", optionValue("merge-string-objects"),
                "merge_string_builders", optionValue(
                        "merge-string-builders")));
        return payload;
    }

    private Map<String, Object> profileMap(MethodStats m) {
        Map<String, Object> item = Maps.newLinkedHashMap();
        item.put("method_signature", m.signature);
        item.put("declaring_class", m.declaringClass);
        item.put("category", m.category);
        item.put("reachable", m.reachable);
        item.put("body_processed", m.bodyProcessed);
        item.put("ignored_reason", m.ignoredReason);
        item.put("is_app", m.isApp);
        item.put("is_non_app", !m.isApp);
        return item;
    }

    private Map<String, Object> metricsMap(MethodStats m) {
        Map<String, Object> item = profileMap(m);
        item.put("return_type", m.returnTypeName);
        item.put("returns_array", m.returnsArray);
        item.put("returns_container_like", m.returnsContainerLike);
        item.put("incoming_call_edge_count", m.incomingCallEdgeCount);
        item.put("distinct_direct_caller_count", m.callerCounts.size());
        item.put("outgoing_call_edge_count", m.outgoingCallEdgeCount);
        item.put("distinct_direct_callee_count", m.calleeCounts.size());
        item.put("app_reachable_callsite_count",
                m.appReachableCallsiteCount());
        item.put("distinct_app_reachable_caller_count",
                m.appReachableCallers.size());
        item.put("direct_app_callsite_count", m.directAppCallsiteCount());
        item.put("direct_app_caller_count", m.directAppCallers.size());
        item.put("top_callers", topNeighbors(m.callerCounts));
        item.put("top_callees", topNeighbors(m.calleeCounts));
        putAvailableMetric(item, "param_pts_max", m.paramPtsMax);
        putAvailableMetric(item, "return_pts_size", m.returnPtsSize());
        putAvailableMetric(item, "local_pts_max", m.localPtsMax);
        putAvailableMetric(item, "method_pts_total", m.methodPtsTotal);
        putAvailableMetric(item, "allocation_count", m.allocationCount);
        putUnavailableMetric(item, "allocated_object_pts_fanout");
        putAvailableMetric(item, "pfg_in_degree_sum", m.pfgInDegreeSum);
        putAvailableMetric(item, "pfg_out_degree_sum", m.pfgOutDegreeSum);
        putAvailableMetric(item, "return_edge_count", m.returnEdgeCount);
        putAvailableMetric(item, "field_store_load_edge_count",
                m.fieldStoreLoadEdgeCount);
        putAvailableMetric(item, "array_store_load_edge_count",
                m.arrayStoreLoadEdgeCount);
        item.put("receiver_state_effect", m.receiverStateEffect);
        item.put("receiver_state_effect_metric_available", true);
        return item;
    }

    private static void putAvailableMetric(Map<String, Object> item,
                                           String metric, int value) {
        item.put(metric, value);
        item.put(metric + "_metric_available", true);
    }

    private static void putUnavailableMetric(Map<String, Object> item,
                                             String metric) {
        item.put(metric, null);
        item.put(metric + "_metric_available", false);
    }

    private Map<String, Object> metricAvailability() {
        Map<String, Object> availability = Maps.newLinkedHashMap();
        for (String metric : List.of(
                "param_pts_max",
                "return_pts_size",
                "local_pts_max",
                "method_pts_total",
                "allocation_count",
                "pfg_in_degree_sum",
                "pfg_out_degree_sum",
                "return_edge_count",
                "field_store_load_edge_count",
                "array_store_load_edge_count",
                "return_type",
                "returns_array",
                "returns_container_like",
                "receiver_state_effect")) {
            availability.put(metric, true);
        }
        availability.put("allocated_object_pts_fanout", false);
        return availability;
    }

    private List<MethodStats> orderedMethods() {
        return methods.values().stream()
                .sorted(Comparator.comparing((MethodStats m) -> !m.reachable)
                        .thenComparing(m -> m.signature))
                .toList();
    }

    private List<Map<String, Object>> topNeighbors(Map<String, Integer> counts) {
        return counts.entrySet().stream()
                .sorted(Map.Entry.<String, Integer>comparingByValue()
                        .reversed()
                        .thenComparing(Map.Entry.comparingByKey()))
                .limit(MAX_TOP_NEIGHBORS)
                .map(entry -> {
                    Map<String, Object> item = Maps.newLinkedHashMap();
                    item.put("method_signature", entry.getKey());
                    MethodStats method = methods.get(entry.getKey());
                    item.put("category", method == null
                            ? "unknown" : method.category);
                    item.put("call_edge_count", entry.getValue());
                    return item;
                })
                .toList();
    }

    private String heavyMethodsMarkdown() {
        StringBuilder md = new StringBuilder();
        md.append("# PTA Heavy Polluting Methods\n\n");
        md.append("Total: ").append(heavyMethods.size()).append("\n\n");
        md.append("| Rank | Score | Category | Method | Reasons |\n");
        md.append("|---:|---:|---|---|---|\n");
        for (HeavyMethod method : heavyMethods) {
            md.append("| ")
                    .append(method.rank)
                    .append(" | ")
                    .append(String.format(java.util.Locale.ROOT, "%.4f",
                            method.score))
                    .append(" | ")
                    .append(escapeMd(method.stats.category))
                    .append(" | `")
                    .append(escapeMd(method.stats.signature))
                    .append("` | ")
                    .append(escapeMd(String.join("; ",
                            method.selectionReasons)))
                    .append(" |\n");
        }
        return md.toString();
    }

    private static String escapeMd(String value) {
        return value == null ? "" : value.replace("|", "\\|");
    }

    private MethodStats method(JMethod method) {
        return methods.computeIfAbsent(method.getSignature(),
                ignored -> new MethodStats(method, categoryOf(method)));
    }

    private String ownerMethodOfPointer(Pointer pointer) {
        if (pointer instanceof CSVar csVar) {
            return csVar.getVar().getMethod().getSignature();
        }
        if (pointer instanceof ArrayIndex arrayIndex) {
            return ownerMethodOfObject(arrayIndex.getArray().getObject());
        }
        if (pointer instanceof InstanceField instanceField) {
            return ownerMethodOfObject(instanceField.getBase().getObject());
        }
        if (pointer instanceof StaticField) {
            return null;
        }
        return null;
    }

    private String ownerMethodOfObject(Obj obj) {
        if (obj == null) {
            return null;
        }
        String owner = allocationOwners.get(obj);
        if (owner != null) {
            return owner;
        }
        return obj.getContainerMethod()
                .map(JMethod::getSignature)
                .orElse(null);
    }

    private String categoryOf(JMethod method) {
        if (method.isApplication()) {
            return "app";
        }
        return categoryOf(method.getDeclaringClass());
    }

    private String categoryOf(JClass cls) {
        if (cls == null) {
            return "unknown";
        }
        return categoryOfClassName(cls.getName(), cls.isApplication());
    }

    private String categoryOfClassName(String className, boolean application) {
        if (application) {
            return "app";
        }
        if (className == null || className.isBlank()) {
            return "unknown";
        }
        if (classifier.isJdkInternalClass(className)) {
            return "jdk-internal";
        }
        if (classifier.isJdkPlatformClass(className)) {
            return "jdk";
        }
        if (className.startsWith("javax.")
                || className.startsWith("org.w3c.")
                || className.startsWith("org.xml.")
                || className.startsWith("org.ietf.jgss.")) {
            return "other-jdk";
        }
        return "third-party";
    }

    private static boolean isStatePointer(Pointer pointer) {
        if (pointer instanceof InstanceField instanceField) {
            String owner = String.valueOf(
                    instanceField.getBase().getObject().getType());
            return owner.contains("StringBuilder")
                    || owner.contains("StringBuffer")
                    || owner.contains("Map")
                    || owner.contains("List")
                    || owner.contains("Collection")
                    || owner.contains("Iterator")
                    || owner.contains("String");
        }
        return false;
    }

    private static int currentPtsSize(Pointer pointer, PointsToSet diff) {
        PointsToSet pts = pointer.getPointsToSet();
        return pts == null ? diff.size() : pts.size();
    }

    private static String callsiteId(JMethod caller, CSCallSite csCallSite) {
        if (csCallSite.getCallSite() == null) {
            return caller.getSignature() + "#<unknown>";
        }
        return caller.getSignature()
                + "#" + csCallSite.getCallSite().getIndex()
                + "@L" + csCallSite.getCallSite().getLineNumber();
    }

    private Path heavyMethodsPath() {
        String configured = optionString("pta-heavy-method-profile");
        if (configured != null && !configured.isBlank()) {
            return Path.of(configured);
        }
        if (World.get() != null) {
            return World.get().getOptions().getOutputDir().toPath()
                    .resolve(DEFAULT_HEAVY_METHODS_FILE);
        }
        return Path.of(DEFAULT_HEAVY_METHODS_FILE);
    }

    private static Path artifactDir(Path heavyPath) {
        Path parent = heavyPath.getParent();
        return parent == null ? Path.of(".") : parent;
    }

    private void writeJson(Path path, Object value) {
        try {
            Path parent = path.getParent();
            if (parent != null) {
                Files.createDirectories(parent);
            }
            JSON.writerWithDefaultPrettyPrinter().writeValue(path.toFile(),
                    value);
        } catch (IOException e) {
            throw new UncheckedIOException("Failed to write " + path, e);
        }
    }

    private void writeMarkdown(Path path, String value) {
        try {
            Path parent = path.getParent();
            if (parent != null) {
                Files.createDirectories(parent);
            }
            Files.writeString(path, value, StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException("Failed to write " + path, e);
        }
    }

    private String optionString(String key) {
        if (!options.has(key)) {
            return null;
        }
        Object value = options.get(key);
        return value == null ? null : String.valueOf(value);
    }

    private Object optionValue(String key) {
        return options.has(key) ? options.get(key) : null;
    }

    private static double normalize(double value, double max) {
        return max <= 0.0 ? 0.0 : value / max;
    }

    private static double max(Collection<MethodStats> methods,
                              ToIntFunction<MethodStats> getter) {
        return methods.stream()
                .mapToInt(getter)
                .max()
                .orElse(0);
    }

    private static int percentile(Collection<MethodStats> methods,
                                  ToIntFunction<MethodStats> getter,
                                  double percentile) {
        List<Integer> values = methods.stream()
                .mapToInt(getter)
                .sorted()
                .boxed()
                .toList();
        if (values.isEmpty()) {
            return 0;
        }
        int index = (int) Math.ceil(percentile * values.size()) - 1;
        index = Math.max(0, Math.min(values.size() - 1, index));
        return values.get(index);
    }

    private record CallEdgeInfo(String caller, String callee,
                                String callsiteId) {
    }

    private static class MethodStats {

        private final String signature;
        private final String declaringClass;
        private final String category;
        private final boolean isApp;
        private final String returnTypeName;
        private final boolean returnsArray;
        private final boolean returnsContainerLike;
        private final Map<String, Integer> callerCounts = Maps.newLinkedHashMap();
        private final Map<String, Integer> calleeCounts = Maps.newLinkedHashMap();
        private final Set<String> callsiteIds = Sets.newLinkedSet();
        private final Set<String> appReachableCallsiteIds =
                Sets.newLinkedSet();
        private final Set<String> directAppCallsiteIds = Sets.newLinkedSet();
        private final Set<String> directAppCallers = Sets.newLinkedSet();
        private final Set<String> appReachableCallers = Sets.newLinkedSet();
        private final Set<String> returnEdgeIds = Sets.newLinkedSet();
        private final Set<String> fieldEdgeIds = Sets.newLinkedSet();
        private final Set<String> arrayEdgeIds = Sets.newLinkedSet();
        private final Set<Obj> returnObjects =
                Collections.newSetFromMap(new IdentityHashMap<>());
        private final Set<String> allocatedObjectConsumerPointers =
                Sets.newLinkedSet();
        private boolean reachable;
        private boolean bodyProcessed;
        private String ignoredReason;
        private int incomingCallEdgeCount;
        private int outgoingCallEdgeCount;
        private int paramPtsMax;
        private int localPtsMax;
        private int methodPtsTotal;
        private int allocationCount;
        private int pfgInDegreeSum;
        private int pfgOutDegreeSum;
        private int returnEdgeCount;
        private int fieldStoreLoadEdgeCount;
        private int arrayStoreLoadEdgeCount;
        private int fieldIrAccessCount;
        private int arrayIrAccessCount;
        private boolean receiverStateEffect;

        private MethodStats(JMethod method, String category) {
            this.signature = method.getSignature();
            this.declaringClass = method.getDeclaringClass().getName();
            this.category = category;
            this.isApp = method.isApplication();
            Type returnType = method.getReturnType();
            this.returnTypeName = returnType.getName();
            this.returnsArray = returnType instanceof ArrayType;
            this.returnsContainerLike = returnsArray
                    || isContainerLikeReturnType(returnTypeName);
        }

        private int returnPtsSize() {
            return returnObjects.size();
        }

        private int appReachableCallsiteCount() {
            return appReachableCallsiteIds.size();
        }

        private int directAppCallsiteCount() {
            return directAppCallsiteIds.size();
        }

        private int pfgDegreeTotal() {
            return pfgInDegreeSum + pfgOutDegreeSum;
        }

        private int fieldArrayEdgeCount() {
            return fieldStoreLoadEdgeCount + arrayStoreLoadEdgeCount;
        }

        private boolean hasNonTrivialEvidence() {
            return incomingCallEdgeCount > 1
                    || appReachableCallsiteCount() > 1
                    || returnPtsSize() > 1
                    || localPtsMax > 1
                    || methodPtsTotal > 1
                    || pfgDegreeTotal() > 1
                    || fieldArrayEdgeCount() > 1;
        }
    }

    private class HeavyMethod {

        private final MethodStats stats;
        private final double score;
        private final TfProxyEvidence tfProxy;
        private final List<String> selectionReasons;
        private final Map<String, Object> triggeredThresholds;
        private int rank;
        private int ptaScoreRank;
        private int tfProxyRank;

        private HeavyMethod(MethodStats stats, double score,
                            TfProxyEvidence tfProxy,
                            List<String> selectionReasons,
                            Map<String, Object> triggeredThresholds) {
            this.stats = stats;
            this.score = score;
            this.tfProxy = tfProxy;
            this.selectionReasons = List.copyOf(selectionReasons);
            this.triggeredThresholds = Map.copyOf(
                    new java.util.LinkedHashMap<>(triggeredThresholds));
        }

        private Map<String, Object> toMap() {
            Map<String, Object> item = metricsMap(stats);
            item.put("rank", rank);
            item.put("score", score);
            item.put("pta_score_rank", ptaScoreRank);
            item.put("tf_proxy_rank", tfProxyRank);
            item.put("tf_proxy_score", tfProxy.score());
            item.put("tf_proxy_reasons", tfProxy.reasons());
            item.put("tf_proxy_bonuses", tfProxy.bonuses());
            item.put("array_local_flow_shape", tfProxy.arrayLocalShape());
            item.put("param_local_flow_shape", tfProxy.paramLocalShape());
            item.put("receiver_state_flow_shape", tfProxy.receiverShape());
            item.put("selection_reasons", selectionReasons);
            item.put("triggered_thresholds", triggeredThresholds);
            item.put("pfg_degree_total", stats.pfgDegreeTotal());
            item.put("field_array_edge_count", stats.fieldArrayEdgeCount());
            return item;
        }
    }

    private record TfProxyEvidence(
            double score,
            boolean returnsArray,
            boolean returnsContainerLike,
            boolean arrayLocalShape,
            boolean paramLocalShape,
            boolean receiverShape,
            List<String> reasons,
            Map<String, Object> bonuses) {
    }

    private class CallComponent {

        private final List<String> members;
        private final List<String> outgoingComponents;
        private int componentRank;

        private CallComponent(Set<String> members,
                              Map<String, Set<String>> outgoing) {
            this.members = members.stream()
                    .sorted(Comparator
                            .comparingInt((String signature) ->
                                    rankOf(signature))
                            .thenComparing(signature -> signature))
                    .toList();
            this.outgoingComponents = members.stream()
                    .flatMap(method -> outgoing.getOrDefault(method, Set.of())
                            .stream())
                    .filter(callee -> !members.contains(callee))
                    .sorted(Comparator
                            .comparingInt((String signature) ->
                                    rankOf(signature))
                            .thenComparing(signature -> signature))
                    .toList();
        }

        private int bestRank() {
            return members.stream()
                    .mapToInt(PtaHeavyMethodProfiler.this::rankOf)
                    .min()
                    .orElse(Integer.MAX_VALUE);
        }

        private Map<String, Object> toMap(PtaHeavyMethodProfiler profiler) {
            Map<String, Object> item = Maps.newLinkedHashMap();
            item.put("component_rank", componentRank);
            item.put("is_recursive_component", members.size() > 1);
            item.put("methods", members.stream()
                    .map(profiler::methodRef)
                    .toList());
            item.put("outgoing_heavy_callees", outgoingComponents.stream()
                    .map(profiler::methodRef)
                    .toList());
            return item;
        }
    }

    private class Tarjan {

        private final Set<String> nodes;
        private final Map<String, Set<String>> outgoing;
        private final Map<String, Integer> indexes = Maps.newLinkedHashMap();
        private final Map<String, Integer> lowLinks = Maps.newLinkedHashMap();
        private final ArrayDeque<String> stack = new ArrayDeque<>();
        private final Set<String> onStack = Sets.newLinkedSet();
        private final List<Set<String>> components = new ArrayList<>();
        private int index;

        private Tarjan(Set<String> nodes, Map<String, Set<String>> outgoing) {
            this.nodes = nodes;
            this.outgoing = outgoing;
        }

        private List<Set<String>> components() {
            nodes.stream()
                    .sorted(Comparator
                            .comparingInt((String signature) ->
                                    rankOf(signature))
                            .thenComparing(signature -> signature))
                    .forEach(node -> {
                        if (!indexes.containsKey(node)) {
                            strongConnect(node);
                        }
                    });
            return components;
        }

        private void strongConnect(String node) {
            indexes.put(node, index);
            lowLinks.put(node, index);
            index++;
            stack.push(node);
            onStack.add(node);

            for (String callee : outgoing.getOrDefault(node, Set.of())) {
                if (!nodes.contains(callee)) {
                    continue;
                }
                if (!indexes.containsKey(callee)) {
                    strongConnect(callee);
                    lowLinks.put(node, Math.min(lowLinks.get(node),
                            lowLinks.get(callee)));
                } else if (onStack.contains(callee)) {
                    lowLinks.put(node, Math.min(lowLinks.get(node),
                            indexes.get(callee)));
                }
            }

            if (!Objects.equals(lowLinks.get(node), indexes.get(node))) {
                return;
            }
            Set<String> component = Sets.newLinkedSet();
            String member;
            do {
                member = stack.pop();
                onStack.remove(member);
                component.add(member);
            } while (!node.equals(member));
            components.add(component);
        }
    }

    private record Thresholds(
            int incomingCallEdgeCount,
            int appReachableCallsiteCount,
            int returnPtsSize,
            int localPtsMax,
            int methodPtsTotal,
            int pfgDegreeTotal,
            int returnEdgeCount,
            int fieldArrayEdgeCount) {

        private static Thresholds from(Collection<MethodStats> methods) {
            return new Thresholds(
                    percentile(methods, m -> m.incomingCallEdgeCount, 0.95),
                    percentile(methods,
                            MethodStats::appReachableCallsiteCount, 0.95),
                    percentile(methods, MethodStats::returnPtsSize, 0.95),
                    percentile(methods, m -> m.localPtsMax, 0.95),
                    percentile(methods, m -> m.methodPtsTotal, 0.95),
                    percentile(methods, MethodStats::pfgDegreeTotal, 0.95),
                    percentile(methods, m -> m.returnEdgeCount, 0.95),
                    percentile(methods, MethodStats::fieldArrayEdgeCount,
                            0.95));
        }

        private Map<String, Object> toMap() {
            return Map.of(
                    "percentile", "p95",
                    "incoming_call_edge_count", incomingCallEdgeCount,
                    "app_reachable_callsite_count",
                    appReachableCallsiteCount,
                    "return_pts_size", returnPtsSize,
                    "local_pts_max", localPtsMax,
                    "method_pts_total", methodPtsTotal,
                    "pfg_degree_total", pfgDegreeTotal,
                    "return_edge_count", returnEdgeCount,
                    "field_array_edge_count", fieldArrayEdgeCount);
        }
    }
}
