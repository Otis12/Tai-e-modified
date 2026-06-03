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
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.summary.JdkBoundaryClassifier;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Set;
import java.util.function.ToIntFunction;

/**
 * Profiles app-used non-app summary frontiers and attributes app-origin mixed
 * PTA hubs back to those frontier methods.
 */
public class PtaSummaryFrontierProfiler {

    public static final String DEFAULT_APP_FRONTIER_METHODS_FILE =
            "pta-app-frontier-methods.json";

    public static final String DEFAULT_APP_ORIGIN_HUBS_FILE =
            "pta-app-origin-hubs.json";

    public static final String DEFAULT_FRONTIER_SLICES_FILE =
            "pta-frontier-slices.json";

    public static final String DEFAULT_METHOD_HUB_ATTRIBUTION_FILE =
            "pta-method-hub-attribution.json";

    public static final String DEFAULT_SUMMARY_FRONTIER_RANKING_FILE =
            "pta-summary-frontier-ranking.json";

    public static final String DEFAULT_FRONTIER_HUB_COVERAGE_FILE =
            "pta-frontier-hub-coverage.json";

    private static final ObjectMapper JSON = new ObjectMapper();

    private static final int MAX_DIRECT_CALLSITES = 64;

    private static final int MAX_HELPER_METHODS = 128;

    private static final int MAX_EVIDENCE_HUBS = 10;

    private final AnalysisOptions options;

    private final JdkBoundaryClassifier classifier;

    private final boolean enabled;

    private final Map<String, FrontierMethodStats> frontiers =
            Maps.newLinkedHashMap();

    private final Map<String, MethodInfo> methods = Maps.newLinkedHashMap();

    private final Map<String, Set<String>> nonAppCalls = Maps.newLinkedHashMap();

    private final Map<String, Map<String, String>> helperParents =
            Maps.newLinkedHashMap();

    private final Map<String, HubStats> hubs = Maps.newLinkedHashMap();

    private final Map<Pointer, OriginSet> pointerOrigins = new IdentityHashMap<>();

    private final Map<Obj, OriginSet> objectOrigins = new IdentityHashMap<>();

    private final Map<String, Set<String>> edgeKindsByPointer =
            Maps.newLinkedHashMap();

    private final Map<String, Integer> inDegreeByPointer =
            Maps.newLinkedHashMap();

    private final Map<String, Integer> outDegreeByPointer =
            Maps.newLinkedHashMap();

    private final int originCap;

    private final int maxSliceDepth;

    private final double targetRecall;

    private final long startNanos = System.nanoTime();

    private List<Attribution> attributions = List.of();

    private List<RankingEntry> rankingEntries = List.of();

    private CoverageResult coverageResult;

    private List<HubStats> highWeightHubs = List.of();

    public PtaSummaryFrontierProfiler(AnalysisOptions options,
                                      JdkBoundaryClassifier classifier) {
        this.options = options;
        this.classifier = Objects.requireNonNull(classifier, "classifier");
        this.enabled = booleanOption("pta-summary-frontier-profile-enabled", false)
                || booleanOption("pta-summary-frontier-enabled", false);
        this.originCap = intOption("pta-summary-frontier-origin-cap", 256);
        this.maxSliceDepth = intOption(
                "pta-summary-frontier-max-slice-depth", 32);
        this.targetRecall = doubleOption(
                "pta-summary-frontier-target-recall", 1.0);
    }

    public void recordReachableMethod(JMethod method, boolean bodyProcessed,
                                      String ignoredReason) {
        if (!enabled) {
            return;
        }
        MethodInfo info = methodInfo(method);
        info.bodyProcessed = info.bodyProcessed || bodyProcessed;
        if (ignoredReason != null) {
            info.ignoredReason = ignoredReason;
        }
        FrontierMethodStats frontier = frontiers.get(method.getSignature());
        if (frontier != null) {
            frontier.bodyProcessed = frontier.bodyProcessed || bodyProcessed;
            if (ignoredReason != null) {
                frontier.ignoredReason = ignoredReason;
            }
        }
    }

    public void recordAllocation(JMethod method, Obj obj) {
        if (!enabled) {
            return;
        }
        if (method == null || obj == null) {
            return;
        }
        OriginSet origins = objectOrigins.computeIfAbsent(obj,
                ignored -> new OriginSet(originCap));
        if (method.isApplication()) {
            origins.add(new AppOrigin(method.getSignature(),
                    "alloc:" + method.getSignature() + "#"
                            + System.identityHashCode(obj),
                    allocationId(obj),
                    null));
        }
    }

    public void recordCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (!enabled) {
            return;
        }
        if (edge == null || edge.getCallee() == null) {
            return;
        }
        CSCallSite csCallSite = edge.getCallSite();
        Invoke callSite = csCallSite == null ? null : csCallSite.getCallSite();
        JMethod caller = callSite == null ? null : callSite.getContainer();
        JMethod callee = edge.getCallee().getMethod();
        if (caller != null && callee != null
                && !caller.isApplication()
                && !callee.isApplication()) {
            recordNonAppCall(caller, callee, edge.getKind().name(),
                    isAmbiguous(edge, callee));
        }
        if (caller != null && callee != null
                && caller.isApplication()
                && !callee.isApplication()) {
            recordDirectFrontier(caller, callee,
                    callsiteId(caller, callSite), lineNumber(callSite));
        }
    }

    public void recordDirectFrontier(JMethod caller, JMethod callee,
                                     String callsiteId, int lineNumber) {
        if (!enabled) {
            return;
        }
        if (caller == null || callee == null || caller.isApplication()
                == callee.isApplication()) {
            return;
        }
        if (!caller.isApplication() || callee.isApplication()) {
            return;
        }
        methodInfo(callee);
        FrontierMethodStats stats = frontier(callee);
        stats.appCallsiteCount++;
        stats.distinctAppCallers.add(caller.getSignature());
        if (stats.directAppCallsiteIds.size() < MAX_DIRECT_CALLSITES) {
            stats.directAppCallsiteIds.add(callsiteId);
        }
        stats.lineNumbers.add(lineNumber);
    }

    public void recordNonAppCall(JMethod caller, JMethod callee,
                                 String kind, boolean ambiguous) {
        if (!enabled) {
            return;
        }
        if (caller == null || callee == null
                || caller.isApplication() || callee.isApplication()) {
            return;
        }
        String callerSig = caller.getSignature();
        String calleeSig = callee.getSignature();
        methodInfo(caller);
        methodInfo(callee);
        nonAppCalls.computeIfAbsent(callerSig, ignored -> Sets.newLinkedSet())
                .add(calleeSig);
        if (ambiguous) {
            MethodInfo info = methods.get(callerSig);
            if (info != null) {
                info.ambiguousCallees.add(calleeSig + "|" + kind);
            }
        }
    }

    public void recordCallArgumentOrigin(Edge<CSCallSite, CSMethod> edge,
                                         Pointer arg,
                                         Pointer param) {
        if (!enabled) {
            return;
        }
        if (edge == null || arg == null || param == null) {
            return;
        }
        JMethod callee = edge.getCallee().getMethod();
        Invoke callSite = edge.getCallSite().getCallSite();
        JMethod caller = callSite == null ? null : callSite.getContainer();
        if (caller == null || callee == null) {
            return;
        }
        OriginSet argOrigins = originsOfPointer(arg);
        if (caller.isApplication() && !callee.isApplication()) {
            AppOrigin boundaryOrigin = new AppOrigin(
                    caller.getSignature(),
                    callsiteId(caller, callSite),
                    null,
                    callee.getSignature());
            argOrigins.add(boundaryOrigin);
            originsOfPointer(param).add(boundaryOrigin);
            frontiers.computeIfAbsent(callee.getSignature(),
                    ignored -> frontier(callee));
        }
        originsOfPointer(param).addAll(argOrigins);
    }

    public void recordReceiverOrigin(Invoke callSite, JMethod callee,
                                     Pointer receiver, Pointer calleeThis) {
        if (!enabled) {
            return;
        }
        if (callSite == null || callee == null
                || receiver == null || calleeThis == null) {
            return;
        }
        JMethod caller = callSite.getContainer();
        if (caller == null) {
            return;
        }
        OriginSet receiverOrigins = originsOfPointer(receiver);
        if (caller.isApplication() && !callee.isApplication()) {
            AppOrigin boundaryOrigin = new AppOrigin(
                    caller.getSignature(),
                    callsiteId(caller, callSite),
                    null,
                    callee.getSignature());
            receiverOrigins.add(boundaryOrigin);
            originsOfPointer(calleeThis).add(boundaryOrigin);
        }
        originsOfPointer(calleeThis).addAll(receiverOrigins);
    }

    public void recordReturnOrigin(Edge<CSCallSite, CSMethod> edge,
                                   Pointer ret,
                                   Pointer lhs) {
        if (!enabled) {
            return;
        }
        if (edge == null || ret == null || lhs == null) {
            return;
        }
        OriginSet retOrigins = originsOfPointer(ret);
        Invoke callSite = edge.getCallSite().getCallSite();
        JMethod caller = callSite == null ? null : callSite.getContainer();
        JMethod callee = edge.getCallee().getMethod();
        if (caller != null && callee != null
                && caller.isApplication()
                && !callee.isApplication()) {
            retOrigins.add(new AppOrigin(
                    caller.getSignature(),
                    callsiteId(caller, callSite),
                    null,
                    callee.getSignature()));
        }
        originsOfPointer(lhs).addAll(retOrigins);
    }

    public void recordPFGEdge(PointerFlowEdge edge) {
        if (!enabled) {
            return;
        }
        if (edge == null) {
            return;
        }
        String source = pointerId(edge.source());
        String target = pointerId(edge.target());
        outDegreeByPointer.merge(source, 1, Integer::sum);
        inDegreeByPointer.merge(target, 1, Integer::sum);
        edgeKindsByPointer.computeIfAbsent(source, ignored -> Sets.newLinkedSet())
                .add(edge.kind().name());
        edgeKindsByPointer.computeIfAbsent(target, ignored -> Sets.newLinkedSet())
                .add(edge.kind().name());
        mergeEdgeOrigins(edge.source(), edge.target(), edge.kind());
    }

    public void recordPropagate(Pointer pointer, PointsToSet diff) {
        if (!enabled) {
            return;
        }
        if (pointer == null || diff == null || diff.isEmpty()) {
            return;
        }
        OriginSet pointerOrigin = originsOfPointer(pointer);
        diff.forEach(csObj -> {
            Obj obj = csObj.getObject();
            OriginSet objOrigin = objectOrigins.get(obj);
            if (objOrigin != null) {
                pointerOrigin.addAll(objOrigin);
            } else if (ownerOfObject(obj) != null
                    && "app".equals(ownerOfObject(obj).category)) {
                AppOrigin appAllocation = new AppOrigin(
                        ownerOfObject(obj).methodSignature,
                        "alloc:" + ownerOfObject(obj).methodSignature,
                        allocationId(obj),
                        null);
                objectOrigins.computeIfAbsent(obj,
                        ignored -> new OriginSet(originCap)).add(appAllocation);
                pointerOrigin.add(appAllocation);
            }
        });
        HubStats hub = hub(pointer);
        hub.ptsSize += diff.size();
        hub.origins.addAll(pointerOrigin);
    }

    public void recordSyntheticHub(
            String hubId,
            JMethod ownerMethod,
            String pointerKind,
            int ptsSize,
            int originAppCallsiteCount,
            int originAppMethodCount,
            int pfgInDegree,
            int pfgOutDegree,
            Set<String> edgeKinds,
            List<AppOrigin> origins) {
        if (!enabled) {
            return;
        }
        MethodInfo methodInfo = methodInfo(ownerMethod);
        HubStats hub = new HubStats(hubId, pointerKind,
                new Owner(methodInfo.className, methodInfo.signature,
                        methodInfo.category),
                originCap);
        hub.ptsSize = ptsSize;
        hub.inDegree = pfgInDegree;
        hub.outDegree = pfgOutDegree;
        hub.edgeKinds.addAll(edgeKinds);
        origins.forEach(hub.origins::add);
        hub.syntheticOriginAppCallsiteCount = originAppCallsiteCount;
        hub.syntheticOriginAppMethodCount = originAppMethodCount;
        hubs.put(hubId, hub);
    }

    public Map<String, String> writeArtifacts() {
        if (!enabled) {
            return Map.of();
        }
        buildSlices();
        classifyHubs();
        attributeHubs();
        rankAndCover();

        Path rankingPath = rankingPath();
        Path artifactDir = artifactDir(rankingPath);
        Path frontiersPath = artifactDir.resolve(DEFAULT_APP_FRONTIER_METHODS_FILE);
        Path hubsPath = artifactDir.resolve(DEFAULT_APP_ORIGIN_HUBS_FILE);
        Path slicesPath = artifactDir.resolve(DEFAULT_FRONTIER_SLICES_FILE);
        Path attributionPath = artifactDir.resolve(
                DEFAULT_METHOD_HUB_ATTRIBUTION_FILE);
        Path coveragePath = artifactDir.resolve(
                DEFAULT_FRONTIER_HUB_COVERAGE_FILE);

        writeJson(frontiersPath, appFrontierPayload());
        writeJson(hubsPath, hubsPayload());
        writeJson(slicesPath, slicesPayload());
        writeJson(attributionPath, attributionPayload());
        writeJson(rankingPath, rankingPayload());
        writeJson(coveragePath, coveragePayload());

        Map<String, String> paths = Maps.newLinkedHashMap();
        paths.put("pta_app_frontier_methods", frontiersPath.toString());
        paths.put("pta_app_origin_hubs", hubsPath.toString());
        paths.put("pta_frontier_slices", slicesPath.toString());
        paths.put("pta_method_hub_attribution", attributionPath.toString());
        paths.put("pta_summary_frontier_ranking", rankingPath.toString());
        paths.put("pta_frontier_hub_coverage", coveragePath.toString());
        return paths;
    }

    private void mergeEdgeOrigins(Pointer source, Pointer target,
                                  FlowKind kind) {
        OriginSet sourceOrigins = originsOfPointer(source);
        OriginSet targetOrigins = originsOfPointer(target);
        if (source instanceof CSVar sourceVar
                && sourceVar.getVar().getMethod().isApplication()) {
            addAppPointerAllocationOrigins(sourceVar, sourceOrigins);
        }
        targetOrigins.addAll(sourceOrigins);
        if (target instanceof ArrayIndex arrayIndex) {
            objectOrigins.computeIfAbsent(arrayIndex.getArray().getObject(),
                    ignored -> new OriginSet(originCap)).addAll(targetOrigins);
        }
        if (target instanceof InstanceField instanceField) {
            objectOrigins.computeIfAbsent(instanceField.getBase().getObject(),
                    ignored -> new OriginSet(originCap)).addAll(targetOrigins);
        }
        if (kind == FlowKind.RETURN && sourceOrigins.isEmpty()) {
            targetOrigins.addAll(sourceOrigins);
        }
    }

    private void addAppPointerAllocationOrigins(CSVar sourceVar,
                                                OriginSet origins) {
        Var var = sourceVar.getVar();
        JMethod method = var.getMethod();
        if (method != null && method.isApplication()) {
            origins.add(new AppOrigin(
                    method.getSignature(),
                    "local:" + method.getSignature() + "#" + var.getIndex(),
                    null,
                    null));
        }
    }

    private void buildSlices() {
        for (FrontierMethodStats frontier : frontiers.values()) {
            frontier.helperMethods.clear();
            frontier.sliceCallEdges.clear();
            frontier.ambiguousEdges.clear();
            Map<String, String> parent = Maps.newLinkedHashMap();
            Queue<SliceNode> queue = new ArrayDeque<>();
            queue.add(new SliceNode(frontier.signature, 0));
            Set<String> visited = Sets.newLinkedSet();
            visited.add(frontier.signature);
            while (!queue.isEmpty()) {
                SliceNode node = queue.remove();
                if (node.depth >= maxSliceDepth) {
                    continue;
                }
                for (String callee : nonAppCalls.getOrDefault(
                        node.method, Set.of())) {
                    frontier.sliceCallEdges.add(node.method + " -> " + callee);
                    if (!visited.add(callee)) {
                        continue;
                    }
                    parent.put(callee, node.method);
                    frontier.helperMethods.add(callee);
                    if (frontier.helperMethods.size() >= MAX_HELPER_METHODS) {
                        frontier.ambiguousEdges.add(
                                node.method + " -> " + callee
                                        + " | max-helper-methods");
                        continue;
                    }
                    MethodInfo calleeInfo = methods.get(callee);
                    if (calleeInfo != null) {
                        frontier.ambiguousEdges.addAll(
                                calleeInfo.ambiguousCallees);
                    }
                    queue.add(new SliceNode(callee, node.depth + 1));
                }
            }
            helperParents.put(frontier.signature, parent);
        }
    }

    private void classifyHubs() {
        for (Map.Entry<String, Set<String>> entry : edgeKindsByPointer.entrySet()) {
            HubStats hub = hubs.get(entry.getKey());
            if (hub != null) {
                hub.edgeKinds.addAll(entry.getValue());
            }
        }
        for (Map.Entry<String, Integer> entry : inDegreeByPointer.entrySet()) {
            HubStats hub = hubs.get(entry.getKey());
            if (hub != null) {
                hub.inDegree = Math.max(hub.inDegree, entry.getValue());
            }
        }
        for (Map.Entry<String, Integer> entry : outDegreeByPointer.entrySet()) {
            HubStats hub = hubs.get(entry.getKey());
            if (hub != null) {
                hub.outDegree = Math.max(hub.outDegree, entry.getValue());
            }
        }
        int ptsThreshold = percentile(hubs.values(), h -> h.ptsSize, 0.95);
        int degreeThreshold = percentile(hubs.values(),
                h -> h.inDegree + h.outDegree, 0.95);
        for (HubStats hub : hubs.values()) {
            hub.highWeight = false;
        }
        highWeightHubs = hubs.values().stream()
                .filter(h -> !"app".equals(h.owner.category))
                .filter(h -> h.originAppCallsiteCount() >= 2)
                .filter(h -> h.ptsSize >= ptsThreshold
                        || h.inDegree + h.outDegree >= degreeThreshold
                        || containsStructuralEdge(h.edgeKinds))
                .peek(h -> h.highWeight = true)
                .sorted(Comparator.comparingDouble(HubStats::hubWeight)
                        .reversed()
                        .thenComparing(h -> h.hubId))
                .toList();
    }

    private void attributeHubs() {
        List<Attribution> result = new ArrayList<>();
        Set<String> highWeightIds = highWeightHubs.stream()
                .map(h -> h.hubId)
                .collect(java.util.stream.Collectors.toSet());
        for (HubStats hub : highWeightHubs) {
            Map<String, Integer> originWeights = hub.origins.boundaryMethodCounts();
            Set<String> matched = Sets.newLinkedSet();
            if (frontiers.containsKey(hub.owner.methodSignature)) {
                String frontier = hub.owner.methodSignature;
                result.add(new Attribution(hub.hubId, frontier,
                        "DIRECT_OWNER", hub.hubWeight(),
                        List.of(frontier), false));
                matched.add(frontier);
            }
            for (FrontierMethodStats frontier : frontiers.values()) {
                if (Objects.equals(frontier.signature,
                        hub.owner.methodSignature)) {
                    continue;
                }
                if (frontier.helperMethods.contains(hub.owner.methodSignature)) {
                    double weight = hub.hubWeight();
                    if (!originWeights.isEmpty()) {
                        int frontierOrigins = originWeights.getOrDefault(
                                frontier.signature, 0);
                        int total = originWeights.values().stream()
                                .mapToInt(Integer::intValue)
                                .sum();
                        if (frontierOrigins > 0 && total > 0) {
                            weight = hub.hubWeight() * frontierOrigins / total;
                        }
                    }
                    boolean ambiguous = helperSharedByMultipleFrontiers(
                            hub.owner.methodSignature)
                            && !originWeights.containsKey(frontier.signature);
                    result.add(new Attribution(hub.hubId, frontier.signature,
                            ambiguous ? "AMBIGUOUS_SHARED_HELPER"
                                    : "DOMINATED_HELPER",
                            weight,
                            helperPath(frontier.signature,
                                    hub.owner.methodSignature),
                            ambiguous));
                    matched.add(frontier.signature);
                }
            }
            for (String boundary : originWeights.keySet()) {
                if (frontiers.containsKey(boundary)
                        && !matched.contains(boundary)) {
                    result.add(new Attribution(hub.hubId, boundary,
                            "FRONTIER_STATE",
                            hub.hubWeight() * originWeights.get(boundary)
                                    / originWeights.values().stream()
                                    .mapToInt(Integer::intValue).sum(),
                            List.of(boundary), false));
                    matched.add(boundary);
                }
            }
            if (matched.isEmpty()) {
                result.add(new Attribution(hub.hubId, null,
                        "UNCOVERED", 0.0, List.of(), true));
            }
        }
        attributions = result.stream()
                .filter(a -> highWeightIds.contains(a.hubId))
                .toList();
    }

    private void rankAndCover() {
        Map<String, FrontierCoverage> coverages = Maps.newLinkedHashMap();
        Map<String, HubStats> highHubById = Maps.newLinkedHashMap();
        for (HubStats hub : highWeightHubs) {
            highHubById.put(hub.hubId, hub);
        }
        for (Attribution attribution : attributions) {
            if (attribution.frontierMethod == null
                    || attribution.ambiguous
                    || !highHubById.containsKey(attribution.hubId)) {
                continue;
            }
            coverages.computeIfAbsent(attribution.frontierMethod,
                    FrontierCoverage::new)
                    .add(attribution, highHubById.get(attribution.hubId));
        }
        Set<String> uncovered = Sets.newLinkedSet();
        highHubById.keySet().forEach(uncovered::add);
        List<String> selected = new ArrayList<>();
        List<SelectionStep> steps = new ArrayList<>();
        double totalWeight = highWeightHubs.stream()
                .mapToDouble(HubStats::hubWeight)
                .sum();
        double coveredWeight = 0.0;
        while (!uncovered.isEmpty()
                && totalWeight > 0.0
                && coveredWeight / totalWeight < targetRecall) {
            FrontierCoverage best = null;
            double bestGain = 0.0;
            for (FrontierCoverage coverage : coverages.values()) {
                if (selected.contains(coverage.frontierMethod)) {
                    continue;
                }
                double gain = coverage.uncoveredWeight(uncovered);
                if (gain > bestGain
                        || (gain == bestGain && best != null
                        && coverage.frontierMethod.compareTo(
                        best.frontierMethod) < 0)) {
                    best = coverage;
                    bestGain = gain;
                }
            }
            if (best == null || bestGain <= 0.0) {
                break;
            }
            selected.add(best.frontierMethod);
            for (String hubId : best.coveredHubIds()) {
                if (uncovered.remove(hubId)) {
                    coveredWeight += highHubById.get(hubId).hubWeight();
                }
            }
            steps.add(new SelectionStep(
                    best.frontierMethod,
                    bestGain,
                    coveredWeight,
                    totalWeight <= 0.0 ? 1.0 : coveredWeight / totalWeight,
                    new ArrayList<>(uncovered)));
        }
        coverageResult = new CoverageResult(
                selected,
                totalWeight,
                coveredWeight,
                totalWeight <= 0.0 ? 1.0 : coveredWeight / totalWeight,
                uncovered.stream().map(highHubById::get).toList(),
                steps);
        rankingEntries = coverages.values().stream()
                .map(c -> rankingEntry(c, selected.indexOf(c.frontierMethod)))
                .sorted((left, right) -> {
                    int leftIndex = left.selectionIndex < 0
                            ? Integer.MAX_VALUE : left.selectionIndex;
                    int rightIndex = right.selectionIndex < 0
                            ? Integer.MAX_VALUE : right.selectionIndex;
                    int byIndex = Integer.compare(leftIndex, rightIndex);
                    if (byIndex != 0) {
                        return byIndex;
                    }
                    int byWeight = Double.compare(
                            right.coveredHubWeight, left.coveredHubWeight);
                    if (byWeight != 0) {
                        return byWeight;
                    }
                    return left.methodSignature.compareTo(right.methodSignature);
                })
                .toList();
    }

    private RankingEntry rankingEntry(FrontierCoverage coverage,
                                      int selectionIndex) {
        FrontierMethodStats frontier = frontiers.get(coverage.frontierMethod);
        List<HubStats> hubs = coverage.coveredHubIds().stream()
                .map(id -> this.hubs.get(id))
                .filter(Objects::nonNull)
                .sorted(Comparator.comparingDouble(HubStats::hubWeight)
                        .reversed()
                        .thenComparing(h -> h.hubId))
                .toList();
        double selectedWeightBefore = 0.0;
        if (coverageResult != null && selectionIndex >= 0
                && selectionIndex < coverageResult.selectionSteps.size()) {
            SelectionStep step = coverageResult.selectionSteps.get(selectionIndex);
            selectedWeightBefore = step.coveredWeightAfterPick
                    - step.uncoveredWeightCovered;
        }
        double recallContribution = coverageResult == null
                || coverageResult.totalHubWeight <= 0.0
                ? 0.0
                : coverage.uncoveredWeight(allHubIds())
                / coverageResult.totalHubWeight;
        return new RankingEntry(
                coverage.frontierMethod,
                selectionIndex,
                coverage.score(),
                hubs.size(),
                coverage.totalCoveredWeight(),
                coverageResult == null ? 0.0
                        : Math.max(0.0, coverageResult.totalHubWeight
                        - selectedWeightBefore
                        - coverage.uncoveredWeight(allHubIds())),
                frontier == null ? 0 : frontier.appCallsiteCount,
                frontier == null ? 0 : frontier.distinctAppCallers.size(),
                frontier == null ? List.of()
                        : frontier.helperMethods.stream()
                        .sorted()
                        .limit(MAX_HELPER_METHODS)
                        .toList(),
                hubs.stream().limit(MAX_EVIDENCE_HUBS)
                        .map(HubStats::toEvidenceMap)
                        .toList(),
                recallContribution);
    }

    private Set<String> allHubIds() {
        Set<String> ids = Sets.newLinkedSet();
        highWeightHubs.stream()
                .map(h -> h.hubId)
                .forEach(ids::add);
        return ids;
    }

    private List<String> helperPath(String frontierMethod,
                                    String helperMethod) {
        if (Objects.equals(frontierMethod, helperMethod)) {
            return List.of(frontierMethod);
        }
        Map<String, String> parent = helperParents.getOrDefault(
                frontierMethod, Map.of());
        List<String> path = new ArrayList<>();
        String current = helperMethod;
        Set<String> seen = Sets.newHybridSet();
        while (current != null && seen.add(current)) {
            path.add(current);
            if (Objects.equals(current, frontierMethod)) {
                break;
            }
            current = parent.get(current);
        }
        java.util.Collections.reverse(path);
        if (path.isEmpty() || !Objects.equals(path.get(0), frontierMethod)) {
            return List.of(frontierMethod, helperMethod);
        }
        return path;
    }

    private boolean helperSharedByMultipleFrontiers(String helperMethod) {
        int count = 0;
        for (FrontierMethodStats frontier : frontiers.values()) {
            if (frontier.helperMethods.contains(helperMethod)) {
                count++;
            }
        }
        return count > 1;
    }

    private HubStats hub(Pointer pointer) {
        String id = pointerId(pointer);
        HubStats hub = hubs.get(id);
        if (hub != null) {
            return hub;
        }
        Owner owner = ownerOfPointer(pointer);
        if (owner == null) {
            owner = Owner.unknown();
        }
        hub = new HubStats(id, pointerKind(pointer), owner, originCap);
        hubs.put(id, hub);
        return hub;
    }

    private OriginSet originsOfPointer(Pointer pointer) {
        return pointerOrigins.computeIfAbsent(pointer,
                ignored -> new OriginSet(originCap));
    }

    private FrontierMethodStats frontier(JMethod method) {
        return frontiers.computeIfAbsent(method.getSignature(),
                ignored -> new FrontierMethodStats(method, categoryOf(method)));
    }

    private MethodInfo methodInfo(JMethod method) {
        return methods.computeIfAbsent(method.getSignature(),
                ignored -> new MethodInfo(method, categoryOf(method)));
    }

    private Owner ownerOfPointer(Pointer pointer) {
        if (pointer instanceof CSVar csVar) {
            return ownerOfMethod(csVar.getVar().getMethod());
        }
        if (pointer instanceof ArrayIndex arrayIndex) {
            return ownerOfObject(arrayIndex.getArray().getObject());
        }
        if (pointer instanceof InstanceField instanceField) {
            Owner objectOwner = ownerOfObject(instanceField.getBase().getObject());
            if (objectOwner != null) {
                return objectOwner;
            }
            return ownerOfClass(instanceField.getField().getDeclaringClass());
        }
        if (pointer instanceof StaticField staticField) {
            return ownerOfClass(staticField.getField().getDeclaringClass());
        }
        return null;
    }

    private Owner ownerOfObject(Obj obj) {
        if (obj == null) {
            return null;
        }
        return obj.getContainerMethod()
                .map(this::ownerOfMethod)
                .orElseGet(() -> {
                    String type = String.valueOf(obj.getType());
                    return type == null || type.isBlank()
                            ? null
                            : new Owner(type, null,
                            categoryOfClassName(type, false));
                });
    }

    private Owner ownerOfMethod(JMethod method) {
        if (method == null) {
            return null;
        }
        return new Owner(
                method.getDeclaringClass().getName(),
                method.getSignature(),
                categoryOf(method));
    }

    private Owner ownerOfClass(JClass cls) {
        if (cls == null) {
            return null;
        }
        return new Owner(cls.getName(), null, categoryOf(cls));
    }

    private String categoryOf(JMethod method) {
        if (method.isApplication()) {
            return "app";
        }
        return categoryOfClassName(method.getDeclaringClass().getName(),
                false);
    }

    private String categoryOf(JClass cls) {
        return categoryOfClassName(cls.getName(), cls.isApplication());
    }

    private String categoryOfClassName(String className, boolean application) {
        if (application) {
            return "app";
        }
        if (classifier.isJdkInternalClass(className)) {
            return "jdk-internal";
        }
        if (classifier.isJdkPlatformClass(className)) {
            return "jdk";
        }
        if (className != null && (className.startsWith("javax.")
                || className.startsWith("org.w3c.")
                || className.startsWith("org.xml."))) {
            return "other-jdk";
        }
        if (className == null || className.isBlank()) {
            return "unknown";
        }
        return "third-party";
    }

    private static String pointerKind(Pointer pointer) {
        if (pointer instanceof CSVar csVar) {
            Var var = csVar.getVar();
            return "local";
        }
        if (pointer instanceof ArrayIndex) {
            return "array-index";
        }
        if (pointer instanceof InstanceField instanceField) {
            String owner = instanceField.getBase().getObject().getType().toString();
            if (owner.contains("StringBuilder")
                    || owner.contains("StringBuffer")) {
                return "builder-state";
            }
            if (owner.contains("Map") || owner.contains("List")
                    || owner.contains("Collection")
                    || owner.contains("Iterator")) {
                return "container-state";
            }
            return "instance-field";
        }
        if (pointer instanceof StaticField) {
            return "static-field";
        }
        return pointer.getClass().getSimpleName();
    }

    private static String pointerId(Pointer pointer) {
        return pointer.toString();
    }

    private static String allocationId(Obj obj) {
        return obj == null ? null : String.valueOf(obj.getAllocation());
    }

    private static String callsiteId(JMethod caller, Invoke callSite) {
        if (caller == null) {
            return "<unknown>";
        }
        int index = callSite == null ? -1 : callSite.getIndex();
        int line = callSite == null ? -1 : callSite.getLineNumber();
        return caller.getSignature() + "#" + index + "@L" + line;
    }

    private static int lineNumber(Invoke callSite) {
        return callSite == null ? -1 : callSite.getLineNumber();
    }

    private static boolean isAmbiguous(Edge<CSCallSite, CSMethod> edge,
                                       JMethod callee) {
        return edge.getKind() == CallKind.OTHER
                || callee.isNative()
                || callee.getSignature().contains("java.lang.reflect.")
                || callee.getSignature().contains("java.lang.invoke.");
    }

    private static boolean containsStructuralEdge(Set<String> edgeKinds) {
        return edgeKinds.stream().anyMatch(kind ->
                kind.contains("RETURN")
                        || kind.contains("ARRAY")
                        || kind.contains("INSTANCE_STORE")
                        || kind.contains("INSTANCE_LOAD"));
    }

    private static int percentile(Collection<HubStats> hubs,
                                  ToIntFunction<HubStats> value,
                                  double percentile) {
        List<Integer> values = hubs.stream()
                .filter(h -> !"app".equals(h.owner.category))
                .mapToInt(value)
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

    private Map<String, Object> basePayload() {
        Map<String, Object> payload = Maps.newLinkedHashMap();
        payload.put("schema_version", 1);
        payload.put("analysis", "pta-summary-frontier-attribution");
        payload.put("ranking_unit", "method");
        payload.put("elapsed_ms",
                (System.nanoTime() - startNanos) / 1_000_000L);
        payload.put("options", Map.of(
                "cs", optionValue("cs"),
                "only_app", optionValue("only-app"),
                "codesummary", optionValue("codesummary"),
                "jdk_analysis_mode", optionValue("jdk-analysis-mode"),
                "merge_string_objects", optionValue("merge-string-objects"),
                "merge_string_builders", optionValue("merge-string-builders"),
                "target_recall", targetRecall,
                "max_slice_depth", maxSliceDepth,
                "origin_cap", originCap));
        return payload;
    }

    private Object appFrontierPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "SF1");
        payload.put("frontier_methods", frontiers.values().stream()
                .sorted(Comparator.comparingInt(
                                (FrontierMethodStats f) -> f.appCallsiteCount)
                        .reversed()
                        .thenComparing(f -> f.signature))
                .map(FrontierMethodStats::toMap)
                .toList());
        return payload;
    }

    private Object hubsPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "SF2-SF3");
        payload.put("high_weight_hub_count", highWeightHubs.size());
        payload.put("hubs", highWeightHubs.stream()
                .map(HubStats::toMap)
                .toList());
        return payload;
    }

    private Object slicesPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "SF4");
        payload.put("max_depth", maxSliceDepth);
        payload.put("frontier_slices", frontiers.values().stream()
                .sorted(Comparator.comparing(f -> f.signature))
                .map(FrontierMethodStats::sliceMap)
                .toList());
        return payload;
    }

    private Object attributionPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "SF5");
        payload.put("attributions", attributions.stream()
                .map(Attribution::toMap)
                .toList());
        return payload;
    }

    private Object rankingPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "SF6");
        payload.put("universe",
                "all high-weight app-origin mixed hubs");
        payload.put("candidate",
                "app-used non-app frontier methods covering at least one hub");
        payload.put("selection_strategy",
                "greedy weighted set cover, summary_cost=1");
        payload.put("selected_methods", rankingEntries.stream()
                .filter(e -> e.selectionIndex >= 0)
                .map(RankingEntry::toMap)
                .toList());
        payload.put("ranking", rankingEntries.stream()
                .map(RankingEntry::toMap)
                .toList());
        return payload;
    }

    private Object coveragePayload() {
        Map<String, Object> payload = basePayload();
        payload.put("stage", "SF6");
        if (coverageResult == null) {
            payload.put("selected_methods", List.of());
            payload.put("total_hub_weight", 0.0);
            payload.put("covered_hub_weight", 0.0);
            payload.put("recall", 1.0);
            payload.put("uncovered_hubs", List.of());
            payload.put("selection_steps", List.of());
            return payload;
        }
        payload.put("selected_methods", coverageResult.selectedMethods);
        payload.put("total_hub_weight", coverageResult.totalHubWeight);
        payload.put("covered_hub_weight", coverageResult.coveredHubWeight);
        payload.put("recall", coverageResult.recall);
        payload.put("uncovered_hubs", coverageResult.uncoveredHubs.stream()
                .map(HubStats::toEvidenceMap)
                .toList());
        payload.put("selection_steps", coverageResult.selectionSteps.stream()
                .map(SelectionStep::toMap)
                .toList());
        return payload;
    }

    private Path rankingPath() {
        String configured = optionString("pta-summary-frontier-profile");
        if (configured != null && !configured.isBlank()) {
            return Path.of(configured);
        }
        if (World.get() != null) {
            return World.get().getOptions().getOutputDir().toPath()
                    .resolve(DEFAULT_SUMMARY_FRONTIER_RANKING_FILE);
        }
        return Path.of(DEFAULT_SUMMARY_FRONTIER_RANKING_FILE);
    }

    private static Path artifactDir(Path rankingPath) {
        Path parent = rankingPath.getParent();
        return parent == null ? Path.of(".") : parent;
    }

    private void writeJson(Path path, Object value) {
        try {
            Path parent = path.getParent();
            if (parent != null) {
                Files.createDirectories(parent);
            }
            JSON.writerWithDefaultPrettyPrinter().writeValue(path.toFile(), value);
        } catch (IOException e) {
            throw new UncheckedIOException("Failed to write " + path, e);
        }
    }

    private int intOption(String key, int defaultValue) {
        if (!options.has(key)) {
            return defaultValue;
        }
        Object value = options.get(key);
        if (value instanceof Number n) {
            return n.intValue();
        }
        if (value == null || String.valueOf(value).isBlank()) {
            return defaultValue;
        }
        return Integer.parseInt(String.valueOf(value));
    }

    private double doubleOption(String key, double defaultValue) {
        if (!options.has(key)) {
            return defaultValue;
        }
        Object value = options.get(key);
        if (value instanceof Number n) {
            return n.doubleValue();
        }
        if (value == null || String.valueOf(value).isBlank()) {
            return defaultValue;
        }
        return Double.parseDouble(String.valueOf(value));
    }

    private boolean booleanOption(String key, boolean defaultValue) {
        if (!options.has(key)) {
            return defaultValue;
        }
        Object value = options.get(key);
        if (value instanceof Boolean b) {
            return b;
        }
        if (value == null || String.valueOf(value).isBlank()) {
            return defaultValue;
        }
        return Boolean.parseBoolean(String.valueOf(value));
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

    private record SliceNode(String method, int depth) {
    }

    private record Owner(String className, String methodSignature,
                         String category) {

        private static Owner unknown() {
            return new Owner("<unknown>", null, "unknown");
        }
    }

    private static class MethodInfo {

        private final String signature;
        private final String className;
        private final String category;
        private final Set<String> ambiguousCallees = Sets.newLinkedSet();
        private boolean bodyProcessed;
        private String ignoredReason;

        private MethodInfo(JMethod method, String category) {
            this.signature = method.getSignature();
            this.className = method.getDeclaringClass().getName();
            this.category = category;
        }
    }

    private static class FrontierMethodStats {

        private final String signature;
        private final String declaringClass;
        private final String category;
        private final Set<String> distinctAppCallers = Sets.newLinkedSet();
        private final Set<String> directAppCallsiteIds = Sets.newLinkedSet();
        private final Set<Integer> lineNumbers = Sets.newLinkedSet();
        private final Set<String> helperMethods = Sets.newLinkedSet();
        private final Set<String> sliceCallEdges = Sets.newLinkedSet();
        private final Set<String> ambiguousEdges = Sets.newLinkedSet();
        private boolean bodyProcessed;
        private String ignoredReason;
        private int appCallsiteCount;

        private FrontierMethodStats(JMethod method, String category) {
            this.signature = method.getSignature();
            this.declaringClass = method.getDeclaringClass().getName();
            this.category = category;
        }

        private Map<String, Object> toMap() {
            Map<String, Object> item = Maps.newLinkedHashMap();
            item.put("method_signature", signature);
            item.put("declaring_class", declaringClass);
            item.put("category", category);
            item.put("body_processed", bodyProcessed);
            item.put("ignored_reason", ignoredReason);
            item.put("app_callsite_count", appCallsiteCount);
            item.put("distinct_app_caller_count", distinctAppCallers.size());
            item.put("direct_app_callsite_ids",
                    directAppCallsiteIds.stream().sorted().toList());
            return item;
        }

        private Map<String, Object> sliceMap() {
            Map<String, Object> item = Maps.newLinkedHashMap();
            item.put("frontier_method", signature);
            item.put("helper_methods", helperMethods.stream().sorted().toList());
            item.put("ambiguous_edges",
                    ambiguousEdges.stream().sorted().toList());
            item.put("slice_call_edges",
                    sliceCallEdges.stream().sorted().toList());
            return item;
        }
    }

    private static class HubStats {

        private final String hubId;
        private final String pointerKind;
        private final Owner owner;
        private final OriginSet origins;
        private final Set<String> edgeKinds = Sets.newLinkedSet();
        private int ptsSize;
        private int inDegree;
        private int outDegree;
        private boolean highWeight;
        private int syntheticOriginAppCallsiteCount = -1;
        private int syntheticOriginAppMethodCount = -1;

        private HubStats(String hubId, String pointerKind, Owner owner,
                         int originCap) {
            this.hubId = hubId;
            this.pointerKind = pointerKind;
            this.owner = owner;
            this.origins = new OriginSet(originCap);
        }

        private int originAppCallsiteCount() {
            return syntheticOriginAppCallsiteCount >= 0
                    ? syntheticOriginAppCallsiteCount
                    : origins.appCallsiteCount();
        }

        private int originAppMethodCount() {
            return syntheticOriginAppMethodCount >= 0
                    ? syntheticOriginAppMethodCount
                    : origins.appMethodCount();
        }

        private double hubWeight() {
            double edgeWeight = containsStructuralEdge(edgeKinds) ? 2.0 : 1.0;
            return edgeWeight * Math.max(1, originAppCallsiteCount())
                    + Math.max(0, ptsSize)
                    + inDegree + outDegree;
        }

        private Map<String, Object> toMap() {
            Map<String, Object> item = toEvidenceMap();
            item.put("origin_app_method_count", originAppMethodCount());
            item.put("frontier_origin_count",
                    origins.boundaryMethodCounts().size());
            item.put("origin_capped", origins.isCapped());
            item.put("origin_boundary_methods",
                    origins.boundaryMethodCounts());
            item.put("high_weight", highWeight);
            return item;
        }

        private Map<String, Object> toEvidenceMap() {
            Map<String, Object> item = Maps.newLinkedHashMap();
            item.put("hub_id", hubId);
            item.put("owner_method", owner.methodSignature);
            item.put("owner_class", owner.className);
            item.put("pointer_kind", pointerKind);
            item.put("pts_size", ptsSize);
            item.put("origin_app_callsite_count",
                    originAppCallsiteCount());
            item.put("pfg_in_degree", inDegree);
            item.put("pfg_out_degree", outDegree);
            item.put("edge_kinds", edgeKinds.stream().sorted().toList());
            item.put("escape_to_app", containsStructuralEdge(edgeKinds));
            item.put("hub_weight", hubWeight());
            return item;
        }
    }

    private record Attribution(
            String hubId,
            String frontierMethod,
            String coverageReason,
            double coverageWeight,
            List<String> helperPath,
            boolean ambiguous) {

        private Map<String, Object> toMap() {
            Map<String, Object> item = Maps.newLinkedHashMap();
            item.put("hub_id", hubId);
            item.put("frontier_method", frontierMethod);
            item.put("coverage_reason", coverageReason);
            item.put("coverage_weight", coverageWeight);
            item.put("helper_path", helperPath);
            item.put("ambiguous", ambiguous);
            return item;
        }
    }

    private static class FrontierCoverage {

        private final String frontierMethod;
        private final Map<String, Double> hubWeights = Maps.newLinkedHashMap();
        private final Map<String, HubStats> hubs = Maps.newLinkedHashMap();

        private FrontierCoverage(String frontierMethod) {
            this.frontierMethod = frontierMethod;
        }

        private void add(Attribution attribution, HubStats hub) {
            hubWeights.merge(attribution.hubId,
                    attribution.coverageWeight, Double::sum);
            hubs.put(attribution.hubId, hub);
        }

        private Set<String> coveredHubIds() {
            return hubWeights.keySet();
        }

        private double uncoveredWeight(Set<String> uncovered) {
            return hubWeights.entrySet().stream()
                    .filter(e -> uncovered.contains(e.getKey()))
                    .mapToDouble(Map.Entry::getValue)
                    .sum();
        }

        private double totalCoveredWeight() {
            return hubWeights.values().stream()
                    .mapToDouble(Double::doubleValue)
                    .sum();
        }

        private double score() {
            return totalCoveredWeight();
        }
    }

    private record SelectionStep(
            String methodSignature,
            double uncoveredWeightCovered,
            double coveredWeightAfterPick,
            double recallAfterPick,
            List<String> remainingUncoveredHubs) {

        private Map<String, Object> toMap() {
            Map<String, Object> item = Maps.newLinkedHashMap();
            item.put("method_signature", methodSignature);
            item.put("uncovered_weight_covered", uncoveredWeightCovered);
            item.put("covered_weight_after_pick", coveredWeightAfterPick);
            item.put("recall_after_pick", recallAfterPick);
            item.put("remaining_uncovered_hubs", remainingUncoveredHubs);
            return item;
        }
    }

    private record CoverageResult(
            List<String> selectedMethods,
            double totalHubWeight,
            double coveredHubWeight,
            double recall,
            List<HubStats> uncoveredHubs,
            List<SelectionStep> selectionSteps) {
    }

    private record RankingEntry(
            String methodSignature,
            int selectionIndex,
            double summaryFrontierScore,
            int coveredHubCount,
            double coveredHubWeight,
            double uncoveredHubWeightAfterPick,
            int appCallsiteCount,
            int distinctAppCallerCount,
            List<String> dominatedHelperMethods,
            List<Map<String, Object>> topEvidenceHubs,
            double recallContribution) {

        private Map<String, Object> toMap() {
            Map<String, Object> item = Maps.newLinkedHashMap();
            item.put("method_signature", methodSignature);
            item.put("selected", selectionIndex >= 0);
            item.put("selection_index", selectionIndex);
            item.put("summary_frontier_score", summaryFrontierScore);
            item.put("covered_hub_count", coveredHubCount);
            item.put("covered_hub_weight", coveredHubWeight);
            item.put("uncovered_hub_weight_after_pick",
                    uncoveredHubWeightAfterPick);
            item.put("app_callsite_count", appCallsiteCount);
            item.put("distinct_app_caller_count", distinctAppCallerCount);
            item.put("dominated_helper_methods", dominatedHelperMethods);
            item.put("top_evidence_hubs", topEvidenceHubs);
            item.put("recall_contribution", recallContribution);
            return item;
        }
    }
}
