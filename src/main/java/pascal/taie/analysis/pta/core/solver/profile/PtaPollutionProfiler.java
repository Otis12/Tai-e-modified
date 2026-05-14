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

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
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
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Collects PTA-level evidence for class/family-level pollution attribution.
 *
 * <p>The primary output is a culprit class ranking. Method signatures are kept
 * only as evidence slices that explain why a class became a hub under CI.</p>
 */
public class PtaPollutionProfiler {

    public static final String DEFAULT_CLASS_PROFILE_FILE =
            "pta-class-pollution-profile.json";

    public static final String DEFAULT_BOUNDARY_DELTA_FILE =
            "pta-class-boundary-delta.json";

    public static final String DEFAULT_SHARED_HUBS_FILE =
            "pta-shared-hubs.json";

    public static final String DEFAULT_CULPRIT_RANKING_FILE =
            "pta-culprit-ranking.json";

    private static final ObjectMapper JSON = new ObjectMapper();

    private static final int MAX_EVIDENCE_METHODS = 8;

    private static final int MAX_SHARED_HUBS = 200;

    private final AnalysisOptions options;

    private final JdkBoundaryClassifier categoryClassifier =
            new JdkBoundaryClassifier();

    private final Map<String, ClassStats> classes = Maps.newOrderedMap();

    private final Map<String, MethodStats> methods = Maps.newOrderedMap();

    private final Map<String, HubStats> hubs = Maps.newMap();

    private final Map<Obj, SharedObjectStats> sharedObjects =
            new IdentityHashMap<>();

    private final Set<String> seenPfgEdges = Sets.newLinkedSet();

    private final long startNanos = System.nanoTime();

    public PtaPollutionProfiler(AnalysisOptions options,
                                JdkBoundaryClassifier classifier) {
        this.options = options;
        Objects.requireNonNull(classifier, "classifier");
    }

    public void recordReachableMethod(JMethod method, boolean bodyProcessed,
                                      String ignoredReason) {
        MethodStats methodStats = method(method);
        ClassStats classStats = clazz(method);
        methodStats.reachable = true;
        methodStats.bodyProcessed = methodStats.bodyProcessed || bodyProcessed;
        methodStats.ignoredReason = ignoredReason;
        classStats.reachableMethodSignatures.add(method.getSignature());
        if (bodyProcessed) {
            classStats.bodyProcessedMethodCount++;
        } else {
            classStats.ignoredMethodCount++;
            if (ignoredReason != null) {
                classStats.ignoredReasons.add(ignoredReason);
            }
        }
    }

    public void recordAllocation(JMethod method, Obj obj) {
        MethodStats methodStats = method(method);
        methodStats.allocatedObjectCount++;
        clazz(method).allocatedObjectCount++;
    }

    public void recordCallEdge(Edge<CSCallSite, CSMethod> edge,
                               int receiverPtsSize,
                               int argPtsTotal,
                               boolean hasResult) {
        JMethod callee = edge.getCallee().getMethod();
        MethodStats methodStats = method(callee);
        ClassStats classStats = clazz(callee);
        methodStats.callsiteCount++;
        classStats.callsiteCount++;
        methodStats.receiverPtsSize += receiverPtsSize;
        classStats.receiverPtsSize += receiverPtsSize;
        methodStats.argPtsTotal += argPtsTotal;
        classStats.argPtsTotal += argPtsTotal;
        if (hasResult) {
            methodStats.returnFanOut++;
            classStats.returnFanOut++;
        }

        Invoke callSite = edge.getCallSite().getCallSite();
        if (callSite != null && callSite.getContainer() != null) {
            String caller = callSite.getContainer().getSignature();
            methodStats.distinctCallers.add(caller);
            classStats.distinctCallers.add(caller);
        }
    }

    public void recordPFGEdge(PointerFlowEdge edge) {
        String edgeKey = edge.kind() + "|" + edge.source() + "|" + edge.target();
        if (!seenPfgEdges.add(edgeKey)) {
            return;
        }
        recordPFGEndpoint(edge.source(), true, edge);
        recordPFGEndpoint(edge.target(), false, edge);
        recordHubEdge(edge);
    }

    public void recordPropagate(Pointer pointer, PointsToSet diff) {
        if (diff.isEmpty()) {
            return;
        }
        Owner owner = ownerOfPointer(pointer);
        if (owner == null) {
            return;
        }
        ClassStats classStats = classes.computeIfAbsent(owner.className,
                className -> new ClassStats(className, owner.category));
        MethodStats methodStats = owner.methodSignature == null
                ? null : methods.get(owner.methodSignature);
        int size = diff.size();
        if (pointer instanceof CSVar) {
            classStats.localPtsTotal += size;
            if (methodStats != null) {
                methodStats.localPtsTotal += size;
            }
        } else if (pointer instanceof ArrayIndex) {
            classStats.arrayIndexPtsTotal += size;
            if (methodStats != null) {
                methodStats.arrayIndexPtsTotal += size;
            }
        } else if (pointer instanceof InstanceField) {
            classStats.instanceFieldPtsTotal += size;
            if (methodStats != null) {
                methodStats.instanceFieldPtsTotal += size;
            }
        }
        HubStats hub = hub(pointer);
        hub.ptsSize += size;
        diff.forEach(obj -> recordObjectConsumer(obj.getObject(), owner));
    }

    public Map<String, String> writeArtifacts() {
        finishSharedEvidence();
        computeBoundaryDeltaScores();
        computeScores();
        Path classProfile = classProfilePath();
        Path artifactDir = artifactDir(classProfile);
        Path hubsPath = artifactDir.resolve(DEFAULT_SHARED_HUBS_FILE);
        Path rankingPath = artifactDir.resolve(DEFAULT_CULPRIT_RANKING_FILE);
        Path deltaPath = artifactDir.resolve(DEFAULT_BOUNDARY_DELTA_FILE);

        writeJson(classProfile, classProfilePayload());
        writeJson(hubsPath, sharedHubsPayload());
        writeJson(rankingPath, rankingPayload());
        writeJson(deltaPath, boundaryDeltaPayload());

        Map<String, String> paths = Maps.newLinkedHashMap();
        paths.put("pta_class_pollution_profile", classProfile.toString());
        paths.put("pta_class_boundary_delta", deltaPath.toString());
        paths.put("pta_shared_hubs", hubsPath.toString());
        paths.put("pta_culprit_ranking", rankingPath.toString());
        return paths;
    }

    private void recordPFGEndpoint(Pointer pointer, boolean source,
                                   PointerFlowEdge edge) {
        Owner owner = ownerOfPointer(pointer);
        if (owner == null) {
            return;
        }
        ClassStats classStats = classes.computeIfAbsent(owner.className,
                className -> new ClassStats(className, owner.category));
        MethodStats methodStats = owner.methodSignature == null
                ? null : methods.get(owner.methodSignature);
        if (source) {
            classStats.pfgOutDegree++;
            if (methodStats != null) {
                methodStats.pfgOutDegree++;
            }
        } else {
            classStats.pfgInDegree++;
            if (methodStats != null) {
                methodStats.pfgInDegree++;
            }
        }
        if (edge.kind() == pascal.taie.analysis.graph.flowgraph.FlowKind.RETURN) {
            classStats.returnFanOut++;
            if (methodStats != null) {
                methodStats.returnFanOut++;
            }
        }
    }

    private void recordHubEdge(PointerFlowEdge edge) {
        HubStats sourceHub = hub(edge.source());
        HubStats targetHub = hub(edge.target());
        sourceHub.outDegree++;
        sourceHub.edgeKinds.add(edge.kind().name());
        targetHub.inDegree++;
        targetHub.edgeKinds.add(edge.kind().name());
        Owner sourceOwner = ownerOfPointer(edge.source());
        Owner targetOwner = ownerOfPointer(edge.target());
        if (sourceOwner != null) {
            targetHub.incomingOwners.add(sourceOwner.ownerKey());
        }
        if (targetOwner != null) {
            sourceHub.outgoingOwners.add(targetOwner.ownerKey());
        }
    }

    private void recordObjectConsumer(Obj obj, Owner consumer) {
        SharedObjectStats stats = sharedObjects.computeIfAbsent(obj,
                SharedObjectStats::new);
        stats.consumerOwners.add(consumer.ownerKey());
    }

    private void finishSharedEvidence() {
        for (HubStats hub : hubs.values()) {
            if (!hub.isShared()) {
                continue;
            }
            ClassStats classStats = classes.computeIfAbsent(hub.owner.className,
                    className -> new ClassStats(className, hub.owner.category));
            classStats.sharedHubCount++;
            if ("array-index".equals(hub.kind)) {
                classStats.sharedArrayIndexCount++;
            }
            MethodStats methodStats = hub.owner.methodSignature == null
                    ? null : methods.get(hub.owner.methodSignature);
            if (methodStats != null) {
                methodStats.sharedHubCount++;
                if ("array-index".equals(hub.kind)) {
                    methodStats.sharedArrayIndexCount++;
                }
            }
        }
        for (SharedObjectStats sharedObject : sharedObjects.values()) {
            if (sharedObject.consumerOwners.size() < 2) {
                continue;
            }
            ownerOfObject(sharedObject.obj).ifPresent(owner -> {
                ClassStats classStats = classes.computeIfAbsent(owner.className,
                        className -> new ClassStats(className, owner.category));
                classStats.sharedAllocationCount++;
                if (owner.methodSignature != null) {
                    MethodStats methodStats = methods.get(owner.methodSignature);
                    if (methodStats != null) {
                        methodStats.sharedAllocationCount++;
                    }
                }
            });
        }
    }

    private void computeScores() {
        double maxReturnFanOut = maxClassValue(c -> c.returnFanOut);
        double maxSharedArray = maxClassValue(c -> c.sharedArrayIndexCount);
        double maxLocalPts = maxClassValue(c -> c.localPtsTotal);
        double maxCallerCount = maxClassValue(c -> c.distinctCallers.size());
        double maxPfgOut = maxClassValue(c -> c.pfgOutDegree);
        double maxSharedAlloc = maxClassValue(c -> c.sharedAllocationCount);
        classes.values().forEach(c -> c.pollutionScore =
                2.0 * normalize(c.returnFanOut, maxReturnFanOut)
                        + 2.0 * normalize(c.sharedArrayIndexCount, maxSharedArray)
                        + 1.5 * normalize(c.localPtsTotal, maxLocalPts)
                        + 1.5 * normalize(c.distinctCallers.size(), maxCallerCount)
                        + 1.0 * normalize(c.pfgOutDegree, maxPfgOut)
                        + 1.0 * normalize(c.sharedAllocationCount, maxSharedAlloc)
                        + 2.0 * c.boundaryDeltaScore);
        methods.values().forEach(m -> m.evidenceScore =
                m.returnFanOut
                        + m.sharedArrayIndexCount
                        + m.localPtsTotal
                        + m.distinctCallers.size()
                        + m.pfgOutDegree
                        + m.sharedAllocationCount);
    }

    private void computeBoundaryDeltaScores() {
        String baselinePath = optionString("pta-boundary-baseline");
        if (!isReadableJson(baselinePath)) {
            return;
        }
        Map<String, ClassSnapshot> baseline = readClassSnapshots(baselinePath);
        Map<String, ClassSnapshot> selected =
                comparisonSnapshots(optionString("pta-boundary-selected"));
        Map<String, ClassSnapshot> fullSummary =
                comparisonSnapshots(optionString("pta-boundary-full-summary"));
        if (baseline.isEmpty()
                || (selected.isEmpty() && fullSummary.isEmpty())) {
            return;
        }
        double maxDelta = 0.0;
        for (ClassStats classStats : classes.values()) {
            ClassSnapshot base = baseline.get(classStats.className);
            double delta = Math.max(
                    bodyMetricDropScore(base, selected.get(classStats.className)),
                    bodyMetricDropScore(base, fullSummary.get(classStats.className)));
            classStats.boundaryDeltaScore = delta;
            maxDelta = Math.max(maxDelta, delta);
        }
        if (maxDelta > 0.0) {
            for (ClassStats classStats : classes.values()) {
                classStats.boundaryDeltaScore /= maxDelta;
            }
        }
    }

    private Map<String, ClassSnapshot> comparisonSnapshots(String path) {
        if (path == null || path.isBlank()) {
            return Map.of();
        }
        Path configuredPath = Path.of(path);
        if (samePath(configuredPath, classProfilePath())) {
            return currentSnapshots();
        }
        return isReadableJson(path) ? readClassSnapshots(path) : Map.of();
    }

    private boolean isComparisonProfileAvailable(String path) {
        return path != null
                && !path.isBlank()
                && (samePath(Path.of(path), classProfilePath())
                || isReadableJson(path));
    }

    private Map<String, ClassSnapshot> currentSnapshots() {
        Map<String, ClassSnapshot> snapshots = Maps.newLinkedHashMap();
        classes.values().forEach(classStats ->
                snapshots.put(classStats.className,
                        ClassSnapshot.from(classStats)));
        return snapshots;
    }

    private static boolean samePath(Path first, Path second) {
        return first.toAbsolutePath().normalize()
                .equals(second.toAbsolutePath().normalize());
    }

    private static double bodyMetricDropScore(ClassSnapshot baseline,
                                             ClassSnapshot comparison) {
        if (baseline == null) {
            return 0.0;
        }
        ClassSnapshot compared = comparison == null
                ? ClassSnapshot.zero()
                : comparison;
        WeightedAverage score = new WeightedAverage();
        score.add(0.5, baseline.bodyProcessedMethodCount,
                compared.bodyProcessedMethodCount);
        score.add(0.5, baseline.returnFanOut, compared.returnFanOut);
        score.add(2.0, baseline.sharedArrayIndexCount,
                compared.sharedArrayIndexCount);
        score.add(1.5, baseline.sharedHubCount, compared.sharedHubCount);
        score.add(1.5, baseline.localPtsTotal, compared.localPtsTotal);
        score.add(1.0, baseline.arrayIndexPtsTotal,
                compared.arrayIndexPtsTotal);
        score.add(1.0, baseline.instanceFieldPtsTotal,
                compared.instanceFieldPtsTotal);
        score.add(1.0, baseline.pfgOutDegree, compared.pfgOutDegree);
        score.add(1.0, baseline.pfgInDegree, compared.pfgInDegree);
        score.add(1.0, baseline.sharedAllocationCount,
                compared.sharedAllocationCount);
        score.add(0.5, baseline.allocatedObjectCount,
                compared.allocatedObjectCount);
        return score.value();
    }

    private double maxClassValue(java.util.function.ToDoubleFunction<ClassStats> get) {
        return classes.values().stream()
                .mapToDouble(get)
                .max()
                .orElse(0.0);
    }

    private static double normalize(double value, double max) {
        return max <= 0.0 ? 0.0 : value / max;
    }

    private MethodStats method(JMethod method) {
        return methods.computeIfAbsent(method.getSignature(),
                signature -> new MethodStats(method, categoryOf(method)));
    }

    private ClassStats clazz(JMethod method) {
        return classes.computeIfAbsent(
                method.getDeclaringClass().getName(),
                className -> new ClassStats(className, categoryOf(method)));
    }

    private HubStats hub(Pointer pointer) {
        String key = pointer.toString();
        return hubs.computeIfAbsent(key, ignored -> {
            Owner owner = ownerOfPointer(pointer);
            if (owner == null) {
                owner = Owner.unknown();
            }
            return new HubStats(key, pointerKind(pointer), owner);
        });
    }

    private Owner ownerOfPointer(Pointer pointer) {
        if (pointer instanceof CSVar csVar) {
            return ownerOfMethod(csVar.getVar().getMethod());
        }
        if (pointer instanceof ArrayIndex arrayIndex) {
            return ownerOfObject(arrayIndex.getArray().getObject())
                    .orElse(null);
        }
        if (pointer instanceof InstanceField instanceField) {
            return ownerOfObject(instanceField.getBase().getObject())
                    .orElseGet(() -> ownerOfClass(
                            instanceField.getField().getDeclaringClass()));
        }
        if (pointer instanceof StaticField staticField) {
            return ownerOfClass(staticField.getField().getDeclaringClass());
        }
        return null;
    }

    private java.util.Optional<Owner> ownerOfObject(Obj obj) {
        return obj.getContainerMethod()
                .map(this::ownerOfMethod)
                .or(() -> java.util.Optional.ofNullable(
                        ownerOfClassName(String.valueOf(obj.getType()))));
    }

    private Owner ownerOfMethod(JMethod method) {
        return new Owner(
                method.getDeclaringClass().getName(),
                method.getSignature(),
                categoryOf(method));
    }

    private Owner ownerOfClass(JClass cls) {
        return new Owner(cls.getName(), null, categoryOf(cls));
    }

    private Owner ownerOfClassName(String className) {
        if (className == null || className.isBlank()) {
            return null;
        }
        return new Owner(className, null, categoryOfClassName(className, false));
    }

    private String categoryOf(JMethod method) {
        if (method.isApplication()) {
            return "app";
        }
        return categoryOfClassName(method.getDeclaringClass().getName(), false);
    }

    private String categoryOf(JClass cls) {
        return categoryOfClassName(cls.getName(), cls.isApplication());
    }

    private String categoryOfClassName(String className, boolean application) {
        if (application) {
            return "app";
        }
        if (categoryClassifier.isStringFamilyClass(className)) {
            return "jdk-string";
        }
        if (categoryClassifier.isJdkContainerClass(className)) {
            return "jdk-container";
        }
        if (categoryClassifier.isJdkInternalClass(className)) {
            return "jdk-internal";
        }
        if (categoryClassifier.isJdkPlatformClass(className)) {
            return "other-jdk";
        }
        return "third-party";
    }

    private static String pointerKind(Pointer pointer) {
        if (pointer instanceof CSVar) {
            return "local";
        }
        if (pointer instanceof ArrayIndex) {
            return "array-index";
        }
        if (pointer instanceof InstanceField) {
            return "instance-field";
        }
        if (pointer instanceof StaticField) {
            return "static-field";
        }
        return pointer.getClass().getSimpleName();
    }

    private Object classProfilePayload() {
        Map<String, Object> payload = basePayload();
        payload.put("classes", orderedClasses().stream()
                .map(this::classMap)
                .toList());
        return payload;
    }

    private Object rankingPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("ranking_unit", "class");
        payload.put("score_formula",
                "2*return_fan_out + 2*shared_array_index_count + "
                        + "1.5*local_pts_total + 1.5*distinct_caller_count + "
                        + "1*pfg_out_degree + 1*shared_allocation_count + "
                        + "2*boundary_delta_score, all normalized per run");
        payload.put("culprit_ranking", orderedClasses().stream()
                .filter(c -> !"app".equals(c.category))
                .map(this::classMap)
                .toList());
        return payload;
    }

    private Object sharedHubsPayload() {
        Map<String, Object> payload = basePayload();
        payload.put("shared_hubs", hubs.values().stream()
                .filter(HubStats::isShared)
                .sorted(Comparator.comparingDouble(HubStats::hubScore).reversed()
                        .thenComparing(h -> h.pointer))
                .limit(MAX_SHARED_HUBS)
                .map(this::hubMap)
                .toList());
        return payload;
    }

    private Object boundaryDeltaPayload() {
        Map<String, Object> payload = basePayload();
        String baselinePath = optionString("pta-boundary-baseline");
        String selectedPath = optionString("pta-boundary-selected");
        String fullSummaryPath = optionString("pta-boundary-full-summary");
        boolean selectedAvailable = isComparisonProfileAvailable(selectedPath);
        boolean fullSummaryAvailable =
                isComparisonProfileAvailable(fullSummaryPath);
        payload.put("baseline", baselinePath);
        payload.put("selected", selectedPath);
        payload.put("full_summary_only", fullSummaryPath);
        payload.put("selected_available", selectedAvailable);
        payload.put("full_summary_only_available", fullSummaryAvailable);
        if (!isReadableJson(baselinePath)
                || (!selectedAvailable && !fullSummaryAvailable)) {
            payload.put("available", false);
            payload.put("reason",
                    "Boundary delta requires a baseline profile and at least "
                            + "one comparison profile.");
            payload.put("classes", List.of());
            return payload;
        }
        Map<String, ClassSnapshot> baseline = readClassSnapshots(baselinePath);
        Map<String, ClassSnapshot> selected = selectedAvailable
                ? comparisonSnapshots(selectedPath) : Map.of();
        Map<String, ClassSnapshot> full = fullSummaryAvailable
                ? comparisonSnapshots(fullSummaryPath) : Map.of();
        List<String> classNames = new ArrayList<>(baseline.keySet());
        if (selectedAvailable) {
            selected.keySet().stream()
                    .filter(name -> !classNames.contains(name))
                    .forEach(classNames::add);
        }
        if (fullSummaryAvailable) {
            full.keySet().stream()
                    .filter(name -> !classNames.contains(name))
                    .forEach(classNames::add);
        }
        List<Map<String, Object>> deltas = classNames.stream()
                .map(className -> deltaMap(className, baseline, selected, full,
                        selectedAvailable, fullSummaryAvailable))
                .sorted(Comparator.comparingDouble(
                        (Map<String, Object> m) -> ((Number) m.get("max_drop")).doubleValue())
                        .reversed())
                .toList();
        payload.put("available", true);
        payload.put("classes", deltas);
        return payload;
    }

    private Map<String, Object> basePayload() {
        Map<String, Object> payload = Maps.newLinkedHashMap();
        payload.put("schema_version", 1);
        payload.put("analysis", "pta-class-pollution-profile");
        payload.put("ranking_unit", "class");
        payload.put("elapsed_ms", (System.nanoTime() - startNanos) / 1_000_000L);
        payload.put("options", Map.of(
                "cs", optionString("cs"),
                "only_app", optionValue("only-app"),
                "codesummary", optionString("codesummary"),
                "jdk_analysis_mode", optionString("jdk-analysis-mode"),
                "merge_string_objects", optionValue("merge-string-objects"),
                "merge_string_builders", optionValue("merge-string-builders")));
        return payload;
    }

    private Map<String, Object> classMap(ClassStats c) {
        Map<String, Object> item = Maps.newLinkedHashMap();
        item.put("class_name", c.className);
        item.put("category", c.category);
        item.put("body_processed_methods", c.bodyProcessedMethodCount);
        item.put("ignored_methods", c.ignoredMethodCount);
        item.put("ignored_reasons", sortedList(c.ignoredReasons));
        item.put("reachable_method_count", c.reachableMethodSignatures.size());
        item.put("callsite_count", c.callsiteCount);
        item.put("distinct_caller_count", c.distinctCallers.size());
        item.put("receiver_pts_size", c.receiverPtsSize);
        item.put("arg_pts_total", c.argPtsTotal);
        item.put("return_fan_out", c.returnFanOut);
        item.put("local_pts_total", c.localPtsTotal);
        item.put("allocated_object_count", c.allocatedObjectCount);
        item.put("shared_allocation_count", c.sharedAllocationCount);
        item.put("array_index_pts_total", c.arrayIndexPtsTotal);
        item.put("instance_field_pts_total", c.instanceFieldPtsTotal);
        item.put("shared_array_index_count", c.sharedArrayIndexCount);
        item.put("shared_hub_count", c.sharedHubCount);
        item.put("pfg_in_degree", c.pfgInDegree);
        item.put("pfg_out_degree", c.pfgOutDegree);
        item.put("boundary_delta_score", c.boundaryDeltaScore);
        item.put("pollution_score", c.pollutionScore);
        item.put("evidence_methods", evidenceMethods(c));
        return item;
    }

    private Map<String, Object> hubMap(HubStats hub) {
        Map<String, Object> item = Maps.newLinkedHashMap();
        item.put("pointer", hub.pointer);
        item.put("kind", hub.kind);
        item.put("owner_class", hub.owner.className);
        item.put("owner_method", hub.owner.methodSignature);
        item.put("category", hub.owner.category);
        item.put("pts_size", hub.ptsSize);
        item.put("pfg_in_degree", hub.inDegree);
        item.put("pfg_out_degree", hub.outDegree);
        item.put("incoming_owner_count", hub.incomingOwners.size());
        item.put("outgoing_owner_count", hub.outgoingOwners.size());
        item.put("edge_kinds", sortedList(hub.edgeKinds));
        item.put("hub_score", hub.hubScore());
        return item;
    }

    private Map<String, Object> deltaMap(
            String className,
            Map<String, ClassSnapshot> baseline,
            Map<String, ClassSnapshot> selected,
            Map<String, ClassSnapshot> full,
            boolean selectedAvailable,
            boolean fullAvailable) {
        ClassSnapshot baseSnapshot = baseline.get(className);
        ClassSnapshot selectedSnapshot = selectedAvailable
                ? selected.get(className) : null;
        ClassSnapshot fullSnapshot = fullAvailable ? full.get(className) : null;
        double base = scoreOf(baseSnapshot);
        Double selectedScore = selectedAvailable ? scoreOf(selectedSnapshot) : null;
        Double fullScore = fullAvailable ? scoreOf(fullSnapshot) : null;
        Double selectedDrop = selectedAvailable
                ? Math.max(0.0, base - selectedScore) : null;
        Double fullDrop = fullAvailable
                ? Math.max(0.0, base - fullScore) : null;
        Double selectedBodyMetricDrop = selectedAvailable
                ? bodyMetricDropScore(baseSnapshot, selectedSnapshot) : null;
        Double fullBodyMetricDrop = fullAvailable
                ? bodyMetricDropScore(baseSnapshot, fullSnapshot) : null;
        Map<String, Object> item = Maps.newLinkedHashMap();
        item.put("class_name", className);
        item.put("baseline_score", base);
        item.put("selected_score", selectedScore);
        item.put("full_summary_score", fullScore);
        item.put("normal_vs_selected_string_delta", selectedDrop);
        item.put("normal_vs_full_summary_only_delta", fullDrop);
        item.put("selected_body_metric_drop", selectedBodyMetricDrop);
        item.put("full_summary_body_metric_drop", fullBodyMetricDrop);
        item.put("body_metric_max_drop", maxNullable(
                selectedBodyMetricDrop, fullBodyMetricDrop));
        item.put("max_drop", maxNullable(selectedDrop, fullDrop));
        return item;
    }

    private static double maxNullable(Double first, Double second) {
        return Math.max(first == null ? 0.0 : first, second == null ? 0.0 : second);
    }

    private List<Map<String, Object>> evidenceMethods(ClassStats classStats) {
        return methods.values().stream()
                .filter(m -> Objects.equals(m.className, classStats.className))
                .sorted(Comparator.comparingDouble((MethodStats m) -> m.evidenceScore).reversed()
                        .thenComparing(m -> m.signature))
                .limit(MAX_EVIDENCE_METHODS)
                .map(this::methodMap)
                .toList();
    }

    private Map<String, Object> methodMap(MethodStats m) {
        Map<String, Object> item = Maps.newLinkedHashMap();
        item.put("method_signature", m.signature);
        item.put("body_processed", m.bodyProcessed);
        item.put("ignored_reason", m.ignoredReason);
        item.put("callsite_count", m.callsiteCount);
        item.put("distinct_caller_count", m.distinctCallers.size());
        item.put("return_fan_out", m.returnFanOut);
        item.put("local_pts_total", m.localPtsTotal);
        item.put("allocated_object_count", m.allocatedObjectCount);
        item.put("shared_allocation_count", m.sharedAllocationCount);
        item.put("array_index_pts_total", m.arrayIndexPtsTotal);
        item.put("instance_field_pts_total", m.instanceFieldPtsTotal);
        item.put("shared_array_index_count", m.sharedArrayIndexCount);
        item.put("shared_hub_count", m.sharedHubCount);
        item.put("pfg_in_degree", m.pfgInDegree);
        item.put("pfg_out_degree", m.pfgOutDegree);
        item.put("evidence_score", m.evidenceScore);
        return item;
    }

    private List<ClassStats> orderedClasses() {
        return classes.values().stream()
                .sorted(Comparator.comparingDouble((ClassStats c) -> c.pollutionScore).reversed()
                        .thenComparing(c -> c.className))
                .toList();
    }

    private Path classProfilePath() {
        String configured = optionString("pta-profile-output");
        if (configured != null && !configured.isBlank()) {
            return Path.of(configured);
        }
        return World.get().getOptions().getOutputDir().toPath()
                .resolve(DEFAULT_CLASS_PROFILE_FILE);
    }

    private static Path artifactDir(Path classProfile) {
        Path parent = classProfile.getParent();
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

    private static double scoreOf(ClassSnapshot snapshot) {
        return snapshot == null ? 0.0 : snapshot.pollutionScore;
    }

    private Map<String, ClassSnapshot> readClassSnapshots(String path) {
        try {
            JsonNode root = JSON.readTree(Path.of(path).toFile());
            JsonNode classesNode = root.get("classes");
            if (classesNode == null || !classesNode.isArray()) {
                return Map.of();
            }
            Map<String, ClassSnapshot> scores = Maps.newLinkedHashMap();
            for (JsonNode item : classesNode) {
                JsonNode className = item.get("class_name");
                if (className != null) {
                    scores.put(className.asText(), ClassSnapshot.from(item));
                }
            }
            return scores;
        } catch (IOException e) {
            throw new UncheckedIOException("Failed to read " + path, e);
        }
    }

    private static int intValue(JsonNode item, String field) {
        JsonNode value = item.get(field);
        return value == null ? 0 : value.asInt();
    }

    private static double doubleValue(JsonNode item, String field) {
        JsonNode value = item.get(field);
        return value == null ? 0.0 : value.asDouble();
    }

    private static boolean isReadableJson(String path) {
        return path != null && !path.isBlank() && Files.isRegularFile(Path.of(path));
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

    private static List<String> sortedList(Set<String> values) {
        return values.stream().sorted().toList();
    }

    private record Owner(String className, String methodSignature,
                         String category) {

        private String ownerKey() {
            return methodSignature != null ? methodSignature : className;
        }

        private static Owner unknown() {
            return new Owner("<unknown>", null, "unknown");
        }
    }

    private static class ClassStats {

        private final String className;
        private final String category;
        private final Set<String> reachableMethodSignatures = Sets.newLinkedSet();
        private final Set<String> ignoredReasons = Sets.newLinkedSet();
        private final Set<String> distinctCallers = Sets.newLinkedSet();
        private int bodyProcessedMethodCount;
        private int ignoredMethodCount;
        private int callsiteCount;
        private int receiverPtsSize;
        private int argPtsTotal;
        private int returnFanOut;
        private int localPtsTotal;
        private int allocatedObjectCount;
        private int sharedAllocationCount;
        private int arrayIndexPtsTotal;
        private int instanceFieldPtsTotal;
        private int sharedArrayIndexCount;
        private int sharedHubCount;
        private int pfgInDegree;
        private int pfgOutDegree;
        private double boundaryDeltaScore;
        private double pollutionScore;

        private ClassStats(String className, String category) {
            this.className = className;
            this.category = category;
        }
    }

    private static class MethodStats {

        private final String signature;
        private final String className;
        private final String category;
        private final Set<String> distinctCallers = Sets.newLinkedSet();
        private boolean reachable;
        private boolean bodyProcessed;
        private String ignoredReason;
        private int callsiteCount;
        private int receiverPtsSize;
        private int argPtsTotal;
        private int returnFanOut;
        private int localPtsTotal;
        private int allocatedObjectCount;
        private int sharedAllocationCount;
        private int arrayIndexPtsTotal;
        private int instanceFieldPtsTotal;
        private int sharedArrayIndexCount;
        private int sharedHubCount;
        private int pfgInDegree;
        private int pfgOutDegree;
        private double evidenceScore;

        private MethodStats(JMethod method, String category) {
            this.signature = method.getSignature();
            this.className = method.getDeclaringClass().getName();
            this.category = category;
        }
    }

    private static class HubStats {

        private final String pointer;
        private final String kind;
        private final Owner owner;
        private final Set<String> incomingOwners = Sets.newLinkedSet();
        private final Set<String> outgoingOwners = Sets.newLinkedSet();
        private final Set<String> edgeKinds = Sets.newLinkedSet();
        private int ptsSize;
        private int inDegree;
        private int outDegree;

        private HubStats(String pointer, String kind, Owner owner) {
            this.pointer = pointer;
            this.kind = kind;
            this.owner = owner;
        }

        private boolean isShared() {
            return ptsSize > 1
                    || incomingOwners.size() > 1
                    || outgoingOwners.size() > 1
                    || inDegree > 1
                    || outDegree > 1;
        }

        private double hubScore() {
            return ptsSize + inDegree + outDegree
                    + incomingOwners.size() + outgoingOwners.size();
        }
    }

    private static class SharedObjectStats {

        private final Obj obj;
        private final Set<String> consumerOwners = Sets.newLinkedSet();

        private SharedObjectStats(Obj obj) {
            this.obj = obj;
        }
    }

    private record ClassSnapshot(
            double pollutionScore,
            int bodyProcessedMethodCount,
            int returnFanOut,
            int localPtsTotal,
            int allocatedObjectCount,
            int sharedAllocationCount,
            int arrayIndexPtsTotal,
            int instanceFieldPtsTotal,
            int sharedArrayIndexCount,
            int sharedHubCount,
            int pfgInDegree,
            int pfgOutDegree) {

        private static ClassSnapshot from(ClassStats classStats) {
            return new ClassSnapshot(
                    classStats.pollutionScore,
                    classStats.bodyProcessedMethodCount,
                    classStats.returnFanOut,
                    classStats.localPtsTotal,
                    classStats.allocatedObjectCount,
                    classStats.sharedAllocationCount,
                    classStats.arrayIndexPtsTotal,
                    classStats.instanceFieldPtsTotal,
                    classStats.sharedArrayIndexCount,
                    classStats.sharedHubCount,
                    classStats.pfgInDegree,
                    classStats.pfgOutDegree);
        }

        private static ClassSnapshot from(JsonNode item) {
            return new ClassSnapshot(
                    doubleValue(item, "pollution_score"),
                    intValue(item, "body_processed_methods"),
                    intValue(item, "return_fan_out"),
                    intValue(item, "local_pts_total"),
                    intValue(item, "allocated_object_count"),
                    intValue(item, "shared_allocation_count"),
                    intValue(item, "array_index_pts_total"),
                    intValue(item, "instance_field_pts_total"),
                    intValue(item, "shared_array_index_count"),
                    intValue(item, "shared_hub_count"),
                    intValue(item, "pfg_in_degree"),
                    intValue(item, "pfg_out_degree"));
        }

        private static ClassSnapshot zero() {
            return new ClassSnapshot(
                    0.0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0);
        }
    }

    private static class WeightedAverage {

        private double weightedSum;
        private double totalWeight;

        private void add(double weight, int baseline, int comparison) {
            if (weight <= 0.0 || baseline <= 0) {
                return;
            }
            weightedSum += weight
                    * Math.max(0.0, baseline - comparison) / baseline;
            totalWeight += weight;
        }

        private double value() {
            return totalWeight <= 0.0 ? 0.0 : weightedSum / totalWeight;
        }
    }
}
