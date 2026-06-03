/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.solver.SummaryDebugConfig;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.taint.TaintProvenanceDebug;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.StringLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Cast;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.VoidType;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Sets;
import javax.annotation.Nullable;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * SummaryManager - 管理方法摘要的核心组件
 *
 * <p>该类负责：
 * <ol>
 *   <li>存储和查询摘要配置（从 YAML 或插件加载）</li>
 *   <li>维护调用点到参数的映射（用于参数变化时重新计算）</li>
 *   <li>应用摘要逻辑：解析 source 的 pts，传播到 target 的 pts</li>
 * </ol>
 *
 * <p>核心思想：将方法调用从"图遍历问题"转化为"函数求值问题"
 *
 * <p>摘要规则格式：{@code source -> target}，其中 source 和 target 是 {@link AccessPath}
 */
public class SummaryManager {

    private static final Logger logger = LogManager.getLogger(SummaryManager.class);

    /**
     * 摘要配置
     */
    private SummaryConfig config = SummaryConfig.EMPTY;

    /**
     * 方法 -> 摘要规则 的索引，用于快速查询
     */
    private MultiMap<MethodRef, SummaryDetail> methodToSummaries = Maps.newMultiMap();

    /**
     * 方法 -> 容器摘要规则 的索引，用于 JDK 容器方法
     */
    private MultiMap<MethodRef, ContainerSummaryDetail> methodToContainerSummaries = Maps.newMultiMap();

    /**
     * 方法 -> Criteria builder 摘要规则 的索引。
     *
     * <p>这类摘要不会替换方法体分析，而是维护独立的 builder 状态。
     */
    private MultiMap<MethodRef, CriteriaSummaryDetail> methodToCriteriaSummaries = Maps.newMultiMap();

    /**
     * 方法 -> 轻量 query-family 摘要规则 的索引。
     */
    private MultiMap<MethodRef, QuerySummaryDetail> methodToQuerySummaries = Maps.newMultiMap();

    /**
     * 方法引用归一化缓存。
     * 仅缓存“这个方法最终应该查哪个 summary 方法”的 lookup 结果。
     */
    private final Map<MethodRef, MethodRef> resolvedSummaryMethodRefCache = Maps.newMap();

    /**
     * 摘要查询缓存。
     * 仅缓存 lookup 结果，不缓存传播/污点状态。
     */
    private final Map<MethodRef, ResolvedSummaries> summaryLookupCache = Maps.newMap();

    /**
     * 已注册 summary 调用点索引。
     * key 可以是调用点原始 method ref，也可以是归一化后的 summary method ref。
     */
    private final MultiMap<MethodRef, TrackedSummaryCallSite> summaryCallSites = Maps.newMultiMap();

    /**
     * 已注册 summary 调用点集合，用于 phase-end 增量重放。
     */
    private final Set<TrackedSummaryCallSite> trackedSummaryCallSites = Sets.newHybridSet();

    /**
     * 活跃调用点注册表
     * <p>用于追踪哪些调用点正在使用摘要，以便参数变化时重新计算
     * <p>Key: CSVar (参数变量)
     * <p>Value: 使用该参数的调用点集合
     */
    private final MultiMap<CSVar, ActiveCall> argToActiveCalls = Maps.newMultiMap();

    private final Solver solver;
    private final CSManager csManager;
    private final boolean enableMapContainerSummaries;
    private final boolean enableListContainerSummaries;
    private final boolean enableCollectionContainerSummaries;
    private final boolean enableIteratorContainerSummaries;
    private final boolean enableTransferPfgEdges;
    private final ContainerSummaryStore containerSummaryStore;
    private final CriteriaSummaryStore criteriaSummaryStore;
    private final QuerySummaryStore querySummaryStore;
    private final MultiMap<CSVar, IteratorLoadSite> iteratorVarToLoadSites = Maps.newMultiMap();
    private final MultiMap<CSVar, CSObj> iteratorVarToContainers = Maps.newMultiMap();
    private final MultiMap<CSObj, IteratorLoadSite> containerToIteratorLoadSites = Maps.newMultiMap();
    private final MultiMap<CSObj, ExampleLoadSite> exampleToLoadSites = Maps.newMultiMap();
    private final MultiMap<CSObj, QueryReadSite> carrierToQueryReadSites = Maps.newMultiMap();
    private final MultiMap<CSObj, QueryReadSite> executorToQueryReadSites = Maps.newMultiMap();
    private final Set<QueryReadSite> trackedQueryReadSites = Sets.newHybridSet();
    private final Set<CSObj> dirtyQueryCarriers = Sets.newHybridSet();
    private final Set<CSObj> dirtyQueryExecutors = Sets.newHybridSet();
    private final MultiMap<CSVar, CSObj> criteriaVarToExamples = Maps.newMultiMap();
    private final MultiMap<CSVar, CSVar> criteriaVarAliasSources = Maps.newMultiMap();
    private final MultiMap<CSVar, CSVar> criteriaVarAliasTargets = Maps.newMultiMap();
    private final Map<CSVar, PointsToSet> deferredCriteriaVarValues = Maps.newMap();
    private long queryWriteCount;
    private long queryReadCount;
    private long queryAttachCount;
    private long summaryAppliedCount;
    private long summaryPfgEdgeRequestCount;
    private long summaryNoopFastPathCount;
    private long summarySnapshotApplyCount;
    private long legacyCriteriaFallbackCount;
    private long globalReapplyFallbackCount;
    private JdkSummaryCatalogStats jdkSummaryCatalogStats =
            new JdkSummaryCatalogStats("none", List.of(), 0, 0, List.of());
    private Set<String> jdkSummaryCatalogMethodSignatures = Set.of();
    private List<JdkNoOpSummary> jdkNoOpSummaries = List.of();

    /**
     * 活跃调用点记录
     */
    public record ActiveCall(
            CSCallSite csCallSite,
            Context callerContext,
            JMethod callee,
            SummaryDetail summaryDetail
    ) {}

    private record IteratorLoadSite(Context context, Var resultVar) {}

    private record ExampleLoadSite(Context context, Var exampleVar) {}

    private record TrackedSummaryCallSite(CSCallSite csCallSite,
                                          MethodRef replayMethodRef,
                                          boolean hasQuerySummary,
                                          boolean hasNonQuerySummary) {}

    private record QueryReadSite(CSCallSite csCallSite,
                                 QuerySummaryDetail summary) {}

    private record ResolvedSummaries(Set<SummaryDetail> transferSummaries,
                                     Set<ContainerSummaryDetail> containerSummaries,
                                     Set<CriteriaSummaryDetail> criteriaSummaries,
                                     Set<QuerySummaryDetail> querySummaries) {

        private boolean isEmpty() {
            return transferSummaries.isEmpty()
                    && containerSummaries.isEmpty()
                    && criteriaSummaries.isEmpty()
                    && querySummaries.isEmpty();
        }

        private boolean hasQuerySummaries() {
            return !querySummaries.isEmpty();
        }

        private boolean hasNonQuerySummaries() {
            return !transferSummaries.isEmpty()
                    || !containerSummaries.isEmpty()
                    || !criteriaSummaries.isEmpty();
        }
    }

    private static final ResolvedSummaries EMPTY_SUMMARIES =
            new ResolvedSummaries(Set.of(), Set.of(), Set.of(), Set.of());

    private static final String PRECISE_CRITERIA_DEFERRED_META_KEY =
            "__criteria_var_deferred_values__";

    public SummaryManager(Solver solver) {
        this.solver = solver;
        this.csManager = solver.getCSManager();
        this.enableMapContainerSummaries =
                resolveBooleanOption("summary-container-map", true);
        this.enableListContainerSummaries =
                resolveBooleanOption("summary-container-list", true);
        this.enableCollectionContainerSummaries =
                resolveBooleanOption("summary-container-collection", true);
        this.enableIteratorContainerSummaries =
                resolveBooleanOption("summary-container-iterator", true);
        this.enableTransferPfgEdges =
                resolveBooleanOption("summary-transfer-pfg-edges", false);
        this.containerSummaryStore = new ContainerSummaryStore(solver::makePointsToSet);
        this.criteriaSummaryStore = new CriteriaSummaryStore(solver::makePointsToSet);
        this.querySummaryStore = new QuerySummaryStore(solver::makePointsToSet);
    }

    // ==================== 配置管理 ====================

    /**
     * 初始化硬编码的测试摘要规则
     * 需要在 ClassHierarchy 可用后调用
     */
    public void initHardcodedSummaries() {
        clearSummaryLookupCaches();
        var hierarchy = solver.getHierarchy();
        var parser = new AccessPathParser(hierarchy);
        logger.info("Container summary toggles: map={}, list={}, collection={}, iterator={}",
                enableMapContainerSummaries,
                enableListContainerSummaries,
                enableCollectionContainerSummaries,
                enableIteratorContainerSummaries);

        java.util.List<SummaryDetail> summaries = new java.util.ArrayList<>();

//         UserQuery.getKeyword(): base.keyword -> result
//        JMethod getKeyword = hierarchy.getMethod(
//                "<com.macro.mall.test.dto.UserQuery: java.lang.String getKeyword()>");
//        if (getKeyword != null) {
//            AccessPath source = parser.parse(getKeyword, "base.keyword");
//            AccessPath target = parser.parse(getKeyword, "result");
//            if (source != null && target != null) {
//                summaries.add(SummaryDetail.of(getKeyword, "base.keyword", "result", source, target));
//                logger.info("Registered hardcoded summary: {}", getKeyword.getSignature());
//            }
//        }
//
//        // UserQuery.setKeyword(String): 0 -> base.keyword
//        JMethod setKeyword = hierarchy.getMethod(
//                "<com.macro.mall.test.dto.UserQuery: void setKeyword(java.lang.String)>");
//        if (setKeyword != null) {
//            AccessPath source = parser.parse(setKeyword, "0");
//            AccessPath target = parser.parse(setKeyword, "base.keyword");
//            if (source != null && target != null) {
//                summaries.add(SummaryDetail.of(setKeyword, "0", "base.keyword", source, target));
//                logger.info("Registered hardcoded summary: {}", setKeyword.getSignature());
//            }
//        }

        int registeredGetterSummaries = 0;
        int registeredSetterSummaries = 0;

        boolean enableAppAccessorSummaries =
                resolveBooleanOption("summary-app-accessor", true);
        if (enableAppAccessorSummaries) {
            for (JClass clazz : hierarchy.allClasses().toList()) {
                if (clazz.isApplication()) {  // Only analyze application classes
                    for (JMethod method : clazz.getDeclaredMethods()) {
                        if (method.isAbstract() || method.isNative()) {
                            continue;
                        }

                        String methodType = checkGSetterMethod(method);
                        SummaryDetail accessorSummary = buildAccessorSummary(method, methodType);
                        if (accessorSummary != null) {
                            summaries.add(accessorSummary);
                            logger.info("Registered hardcoded summary: {}", method.getSignature());
                            if ("Getter".equals(methodType)) {
                                registeredGetterSummaries++;
                            } else if ("Setter".equals(methodType)) {
                                registeredSetterSummaries++;
                            }
                        }
                    }
                }
            }
        } else {
            logger.info("Application getter/setter summaries disabled by summary-app-accessor=false");
        }

        logger.info("Registered {} application getter summaries and {} application setter summaries",
                registeredGetterSummaries, registeredSetterSummaries);

        boolean enableJdkTransferSummaries =
                resolveBooleanOption("summary-jdk-transfer", true);
        if (enableJdkTransferSummaries) {
            if (resolveBooleanOption("summary-jdk-utility", true)) {
                addJdkUtilitySummaries(hierarchy, parser, summaries);
            } else {
                logger.info("JDK utility summaries disabled by summary-jdk-utility=false");
            }
            if (resolveBooleanOption("summary-jdk-catalog", true)) {
                JdkSummaryCatalog jdkCatalog = loadJdkSummaryCatalog();
                summaries.addAll(jdkCatalog.summaryConfig().summaryDetails());
                jdkSummaryCatalogStats = jdkCatalog.stats();
                jdkNoOpSummaries = jdkCatalog.noops();
                jdkSummaryCatalogMethodSignatures = jdkCatalog.summaryConfig()
                        .summaryDetails()
                        .stream()
                        .map(summary -> summary.method().getSignature())
                        .collect(Collectors.toUnmodifiableSet());
                logger.info("Initialized {} JDK catalog transfer summary rules and {} no-op selectors",
                        jdkSummaryCatalogStats.summaryCount(),
                        jdkSummaryCatalogStats.noopCount());
            } else {
                logger.info("JDK catalog summaries disabled by summary-jdk-catalog=false");
            }
        } else {
            logger.info("JDK transfer summaries disabled by summary-jdk-transfer=false");
        }

        if (!summaries.isEmpty()) {
            SummaryConfig hardcodedConfig = new SummaryConfig(summaries);
            mergeConfig(hardcodedConfig);
            logger.info("Initialized {} hardcoded transfer summary rules", summaries.size());
        }

        int registeredContainerSummaries = addJdkContainerSummaries(hierarchy);
        if (registeredContainerSummaries > 0) {
            logger.info("Initialized {} JDK container summaries", registeredContainerSummaries);
        }

        int registeredQuerySummaries = addCriteriaSummaries(hierarchy)
                + addMyBatisPlusQuerySummaries(hierarchy);
        if (registeredQuerySummaries > 0) {
            logger.info("Initialized {} query builder summaries", registeredQuerySummaries);
        }

    }

    private String checkGSetterMethod(JMethod method) {

        String methodName = method.getName();

        // Check getter pattern: T getName() with no parameters
        if (method.getParamCount() == 0
                && !method.getReturnType().equals(VoidType.VOID)) {
            if (methodName.startsWith("get") && methodName.length() > 3) {
                return "Getter";
            }
        }

        // Check setter pattern

        if (method.getParamCount() == 1
                && method.getReturnType().equals(VoidType.VOID)) {
            if (methodName.startsWith("set") && methodName.length() > 3) {
                return "Setter";
            }
        }

        return "null";
    }

    private String inferFieldNameFromGetter(JMethod method) {
        String methodName = method.getName();

        // Handle "get" prefix
        if (methodName.startsWith("get") && methodName.length() > 3) {
            String fieldName = methodName.substring(3);
            // Convert first char to lowercase: getName -> name
            return Character.toLowerCase(fieldName.charAt(0)) + fieldName.substring(1);
        }

        // Handle "is" prefix for boolean getters
        if (methodName.startsWith("is") && methodName.length() > 2) {
            String fieldName = methodName.substring(2);
            return Character.toLowerCase(fieldName.charAt(0)) + fieldName.substring(1);
        }

        return null;
    }

    private String inferFieldNameFromSetter(JMethod method) {
        String methodName = method.getName();

        if (methodName.startsWith("set") && methodName.length() > 3) {
            String fieldName = methodName.substring(3);
            return Character.toLowerCase(fieldName.charAt(0)) + fieldName.substring(1);
        }

        return null;
    }

    @Nullable
    private SummaryDetail buildAccessorSummary(JMethod method, String methodType) {
        return switch (methodType) {
            case "Getter" -> buildGetterSummary(method);
            case "Setter" -> buildSetterSummary(method);
            default -> null;
        };
    }

    @Nullable
    private SummaryDetail buildGetterSummary(JMethod method) {
        JField field = findFieldInClass(
                method.getDeclaringClass(),
                inferFieldNameFromGetter(method),
                method.getReturnType());
        if (field == null) {
            return null;
        }
        String sourceStr = "base." + field.getName().toString();
        String targetStr = "result";
        AccessPath source = AccessPath.ofField(InvokeUtils.BASE, field);
        AccessPath target = AccessPath.ofVar(InvokeUtils.RESULT);
        return SummaryDetail.of(method, sourceStr, targetStr, source, target);
    }

    @Nullable
    private SummaryDetail buildSetterSummary(JMethod method) {
        if (method.isStatic()) {
            return null;
        }
        JField field = findFieldInClass(
                method.getDeclaringClass(),
                inferFieldNameFromSetter(method),
                method.getParamType(0));
        if (field == null) {
            return null;
        }
        String sourceStr = "0";
        String targetStr = "base." + field.getName().toString();
        AccessPath source = AccessPath.ofVar(0);
        AccessPath target = AccessPath.ofField(InvokeUtils.BASE, field);
        return SummaryDetail.of(method, sourceStr, targetStr, source, target);
    }

    private JField findFieldInClass(JClass clazz, String fieldName, Type expectedType) {
        // First try declared fields
        JField field = clazz.getDeclaredField(fieldName);
        if (field != null && isTypeCompatible(field.getType(), expectedType)) {
            return field;
        }

        // Try superclass
        JClass superClass = clazz.getSuperClass();
        if (superClass != null) {
            return findFieldInClass(superClass, fieldName, expectedType);
        }

        return null;
    }

    /**
     * Check if field type is compatible with expected type
     */
    private boolean isTypeCompatible(Type fieldType, Type expectedType) {
        if (fieldType.equals(expectedType)) {
            return true;
        }

        var hierarchy = solver.getHierarchy();

        // Allow subtype relationships for reference types
        if (fieldType instanceof ClassType && expectedType instanceof ClassType) {
            JClass fieldClass = ((ClassType) fieldType).getJClass();
            JClass expectedClass = ((ClassType) expectedType).getJClass();
            return hierarchy.isSubclass(expectedClass, fieldClass)
                    || hierarchy.isSubclass(fieldClass, expectedClass);
        }

        return false;
    }

    /**
     * 设置摘要配置
     *
     * @param config 摘要配置
     */
    public void setConfig(SummaryConfig config) {
        this.config = config;
        this.methodToSummaries = config.buildMethodIndex();
        clearSummaryLookupCaches();
        logger.info("Loaded {} summary rules for {} methods",
                config.summaryDetails().size(), methodToSummaries.keySet().size());
    }

    /**
     * 合并新的摘要配置
     *
     * @param other 要合并的配置
     */
    public void mergeConfig(SummaryConfig other) {
        this.config = this.config.mergeWith(other);
        this.methodToSummaries = config.buildMethodIndex();
        clearSummaryLookupCaches();
    }

    // ==================== 查询接口 ====================

    /**
     * 判断方法是否有摘要规则
     */
    public boolean hasSummary(MethodRef methodref) {
        return !lookupSummaries(methodref).isEmpty();
    }

    public boolean hasQuerySummary(MethodRef methodRef) {
        return lookupSummaries(methodRef).hasQuerySummaries();
    }

    /**
     * 获取方法的所有摘要规则
     */
    public Set<SummaryDetail> getSummaries(MethodRef methodRef) {
        return methodToSummaries.get(methodRef);
    }

    // ==================== 核心逻辑：应用摘要 ====================

    /**
     * 应用摘要 - 核心入口
     *
     * <p>当 processCall 发现目标方法有摘要规则时调用此方法。
     * 该方法会：
     * <ol>
     *   <li>查找该方法的所有摘要规则</li>
     *   <li>对每条规则：解析 source 的 pts，传播到 target 的 pts</li>
     *   <li>注册活跃调用点（用于参数变化时增量重新计算）</li>
     * </ol>
     *
     * @param csCallSite      上下文敏感的调用点
     * @param calleeMethodRef 被调用的方法
     * @param callerContext   调用者的上下文
     * @return true 如果摘要被成功应用
     */
    public boolean applySummary(CSCallSite csCallSite, MethodRef calleeMethodRef, Context callerContext) {
        ResolvedSummaries summaries = lookupSummaries(calleeMethodRef);
        if (summaries.isEmpty()) {
            return false;
        }

        registerTrackedSummaryCallSite(csCallSite, calleeMethodRef, summaries);

        Invoke callSite = csCallSite.getCallSite();
        debugCriteriaEvent(callSite, () -> String.format(
                "applySummary callee=%s resolvedTransfer=%d resolvedContainer=%d resolvedCriteria=%d resolvedQuery=%d receiver=%s result=%s arg0=%s arg1=%s",
                calleeMethodRef,
                summaries.transferSummaries().size(),
                summaries.containerSummaries().size(),
                summaries.criteriaSummaries().size(),
                summaries.querySummaries().size(),
                describePointsToSet(resolveReceiverPts(callSite, callerContext)),
                describePointsToSet(resolveVarPts(callSite, callerContext, InvokeUtils.RESULT)),
                describePointsToSet(resolveVarPts(callSite, callerContext, 0)),
                describePointsToSet(resolveVarPts(callSite, callerContext, 1))));
//        logger.info("Applying {} summary rules for {} @ {}",
//                summaries.size(), calleeMethodRef.getName(), callSite);

        for (SummaryDetail summary : summaries.transferSummaries()) {
            summaryAppliedCount++;
            applySingleSummary(csCallSite, callerContext, callSite, summary);
        }

        for (ContainerSummaryDetail summary : summaries.containerSummaries()) {
            summaryAppliedCount++;
            applyContainerSummary(callerContext, callSite, summary);
        }

        for (QuerySummaryDetail summary : summaries.querySummaries()) {
            summaryAppliedCount++;
            applyQuerySummary(csCallSite, callerContext, callSite, summary);
        }

        for (CriteriaSummaryDetail summary : summaries.criteriaSummaries()) {
            summaryAppliedCount++;
            legacyCriteriaFallbackCount++;
            applyCriteriaSummary(callerContext, callSite, summary);
        }

        return true;
    }

    /**
     * 应用单条摘要规则
     */
    private void applySingleSummary(CSCallSite csCallSite, Context context,
                                    Invoke callSite, SummaryDetail summary) {
        AccessPath source = summary.source();
        AccessPath target = summary.target();

        if (enableTransferPfgEdges
                && source.isSimpleVar()
                && target.isSimpleVar()) {
            applySimpleTransferSummaryAsPfgEdge(context, callSite, source, target);
            return;
        }

        // 注册活跃调用点（用于增量更新）
//        registerActiveCall(csCallSite, context, summary, callSite);

        // 解析 source 的 pts
        PointsToSet sourcePts = resolveSourcePts(callSite, context, source);
//        logger.info("source pts: {}, context: {}, target: {}, callsite: {}",
//                sourcePts, context, target, callSite);

        if (sourcePts == null || sourcePts.isEmpty()) {
            return;
        }
        summarySnapshotApplyCount++;

        TaintProvenanceDebug.logSummary(callSite, summary.method(),
                "transfer", summary, sourcePts);

        // 将 source pts 传播到 target
        propagateToTarget(callSite, context, target, sourcePts);


    }

    private void applySimpleTransferSummaryAsPfgEdge(Context context, Invoke callSite,
                                                     AccessPath source, AccessPath target) {
        Var sourceVar = getVarByIndex(callSite, source.base());
        Var targetVar = getVarByIndex(callSite, target.base());
        if (sourceVar == null || targetVar == null) {
            return;
        }
        if (sourceVar.equals(targetVar)) {
            summaryNoopFastPathCount++;
            return;
        }
        CSVar sourcePointer = csManager.getCSVar(context, sourceVar);
        CSVar targetPointer = csManager.getCSVar(context, targetVar);
        solver.addPFGEdge(sourcePointer, targetPointer, FlowKind.ID);
        summaryPfgEdgeRequestCount++;
    }

    private void applyContainerSummary(Context context, Invoke callSite,
                                       ContainerSummaryDetail summary) {
        switch (summary.kind()) {
            case MAP_GET -> applyMapGet(context, callSite);
            case MAP_PUT -> applyMapPut(context, callSite);
            case MAP_GET_OR_DEFAULT -> applyMapGetOrDefault(context, callSite);
            case MAP_REMOVE -> applyMapRemove(context, callSite);
            case ATTRIBUTE_GET -> applyAttributeGet(context, callSite);
            case ATTRIBUTE_SET -> applyAttributeSet(context, callSite);
            case LIST_GET -> applyListGet(context, callSite);
            case LIST_SET -> applyListSet(context, callSite);
            case LIST_REMOVE -> applyListRemove(context, callSite);
            case COLLECTION_ADD -> applyCollectionAdd(context, callSite);
            case ITERATOR_BIND_RESULT -> applyIteratorBindResult(context, callSite);
            case ITERATOR_NEXT -> applyIteratorNext(context, callSite);
        }
    }

    private void applyMapGet(Context context, Invoke callSite) {
        KeySelector key = resolveKeySelector(callSite, context, 0);
        propagateLoadedValues(context, callSite.getResult(),
                resolveReceiverPts(callSite, context),
                container -> containerSummaryStore.loadMapValues(container, key));
    }

    private void applyMapPut(Context context, Invoke callSite) {
        PointsToSet receiverPts = resolveReceiverPts(callSite, context);
        KeySelector key = resolveKeySelector(callSite, context, 0);
        PointsToSet resultPts = solver.makePointsToSet();
        receiverPts.forEach(container ->
                resultPts.addAll(containerSummaryStore.loadMapValues(container, key)));
        propagateToVar(context, callSite.getResult(), resultPts);

        PointsToSet valuePts = resolveVarPts(callSite, context, 1);
        if (valuePts.isEmpty()) {
            return;
        }
        receiverPts.forEach(container ->
                containerSummaryStore.putMapValues(container, key, valuePts));
    }

    private void applyMapGetOrDefault(Context context, Invoke callSite) {
        PointsToSet resultPts = solver.makePointsToSet();
        PointsToSet receiverPts = resolveReceiverPts(callSite, context);
        KeySelector key = resolveKeySelector(callSite, context, 0);
        receiverPts.forEach(container ->
                resultPts.addAll(containerSummaryStore.loadMapValues(container, key)));
        resultPts.addAll(resolveVarPts(callSite, context, 1));
        propagateToVar(context, callSite.getResult(), resultPts);
    }

    private void applyMapRemove(Context context, Invoke callSite) {
        KeySelector key = resolveKeySelector(callSite, context, 0);
        propagateLoadedValues(context, callSite.getResult(),
                resolveReceiverPts(callSite, context),
                container -> containerSummaryStore.removeMapValues(container, key));
    }

    private void applyAttributeGet(Context context, Invoke callSite) {
        applyMapGet(context, callSite);
    }

    private void applyAttributeSet(Context context, Invoke callSite) {
        applyMapPut(context, callSite);
    }

    private void applyListGet(Context context, Invoke callSite) {
        propagateLoadedValues(context, callSite.getResult(),
                resolveReceiverPts(callSite, context),
                containerSummaryStore::loadListValues);
    }

    private void applyListSet(Context context, Invoke callSite) {
        PointsToSet receiverPts = resolveReceiverPts(callSite, context);
        PointsToSet resultPts = solver.makePointsToSet();
        receiverPts.forEach(container ->
                resultPts.addAll(containerSummaryStore.loadListValues(container)));
        propagateToVar(context, callSite.getResult(), resultPts);

        PointsToSet valuePts = resolveVarPts(callSite, context, 1);
        if (valuePts.isEmpty()) {
            return;
        }
        receiverPts.forEach(container ->
                containerSummaryStore.setListValues(container, valuePts));
        backfillIteratorLoads(receiverPts);
    }

    private void applyListRemove(Context context, Invoke callSite) {
        propagateLoadedValues(context, callSite.getResult(),
                resolveReceiverPts(callSite, context),
                containerSummaryStore::loadListValues);
    }

    private void applyCollectionAdd(Context context, Invoke callSite) {
        PointsToSet valuePts = resolveVarPts(callSite, context, 0);
        if (valuePts.isEmpty()) {
            return;
        }
        PointsToSet receiverPts = resolveReceiverPts(callSite, context);
        receiverPts.forEach(container ->
                containerSummaryStore.addCollectionValues(container, valuePts));
        backfillIteratorLoads(receiverPts);
    }

    private void applyIteratorBindResult(Context context, Invoke callSite) {
        Var iteratorVar = callSite.getResult();
        if (iteratorVar == null) {
            return;
        }
        PointsToSet containerPts = resolveReceiverPts(callSite, context);
        if (containerPts.isEmpty()) {
            return;
        }
        CSVar iteratorCsVar = csManager.getCSVar(context, iteratorVar);
        containerSummaryStore.bindIteratorVarToContainers(iteratorCsVar, containerPts);
        bindIteratorLoadSites(iteratorCsVar, containerPts);
        backfillIteratorLoads(iteratorCsVar);
        PointsToSet iteratorPts = resolveVarPts(callSite, context, InvokeUtils.RESULT);
        if (iteratorPts.isEmpty()) {
            return;
        }
        iteratorPts.forEach(iterator ->
                containerSummaryStore.bindIteratorToContainers(iterator, containerPts));
    }

    private void applyIteratorNext(Context context, Invoke callSite) {
        Var iteratorVar = getVarByIndex(callSite, InvokeUtils.BASE);
        if (iteratorVar == null) {
            return;
        }
        CSVar iteratorCsVar = csManager.getCSVar(context, iteratorVar);
        registerIteratorLoadSite(iteratorCsVar, context, callSite.getResult());
        PointsToSet receiverPts = resolveReceiverPts(callSite, context);
        PointsToSet loadedPts = containerSummaryStore.loadIteratorValues(
                iteratorCsVar,
                receiverPts);
        propagateToVar(context, callSite.getResult(), loadedPts);
    }

    private void registerIteratorLoadSite(CSVar iteratorVar, Context context,
                                          @Nullable Var resultVar) {
        if (resultVar == null) {
            return;
        }
        IteratorLoadSite loadSite = new IteratorLoadSite(context, resultVar);
        iteratorVarToLoadSites.put(iteratorVar, loadSite);
        iteratorVarToContainers.get(iteratorVar)
                .forEach(container -> containerToIteratorLoadSites.put(container, loadSite));
    }

    private void bindIteratorLoadSites(CSVar iteratorVar, PointsToSet containerPts) {
        containerPts.forEach(container -> {
            iteratorVarToContainers.put(iteratorVar, container);
            iteratorVarToLoadSites.get(iteratorVar)
                    .forEach(loadSite -> containerToIteratorLoadSites.put(container, loadSite));
        });
    }

    private void backfillIteratorLoads(CSVar iteratorVar) {
        PointsToSet loadedPts = solver.makePointsToSet();
        iteratorVarToContainers.get(iteratorVar)
                .forEach(container -> loadedPts.addAll(loadIteratorContainerValues(container)));
        if (loadedPts.isEmpty()) {
            return;
        }
        iteratorVarToLoadSites.get(iteratorVar).forEach(loadSite ->
                propagateToVar(loadSite.context(), loadSite.resultVar(), loadedPts));
    }

    private void backfillIteratorLoads(PointsToSet containerPts) {
        containerPts.forEach(this::backfillIteratorLoads);
    }

    private void backfillIteratorLoads(CSObj container) {
        PointsToSet loadedPts = loadIteratorContainerValues(container);
        if (loadedPts.isEmpty()) {
            return;
        }
        containerToIteratorLoadSites.get(container).forEach(loadSite ->
                propagateToVar(loadSite.context(), loadSite.resultVar(), loadedPts));
    }

    private PointsToSet loadIteratorContainerValues(CSObj container) {
        PointsToSet loadedPts = solver.makePointsToSet();
        loadedPts.addAll(containerSummaryStore.loadCollectionValues(container));
        loadedPts.addAll(containerSummaryStore.loadListValues(container));
        return loadedPts;
    }

    private void applyQuerySummary(CSCallSite csCallSite, Context context, Invoke callSite,
                                   QuerySummaryDetail summary) {
        switch (summary.kind()) {
            case QB_LINK -> applyQueryLink(context, callSite, summary);
            case QB_ATTACH -> applyQueryAttach(context, callSite, summary);
            case QB_WRITE_SLOT -> applyQueryWriteSlot(context, callSite, summary);
            case QB_WRITE_META -> applyQueryWriteMeta(context, callSite, summary);
            case QB_RESET -> applyQueryReset(context, callSite, summary);
            case QB_READ -> applyQueryRead(csCallSite, context, callSite, summary);
        }
    }

    private void applyQueryLink(Context context, Invoke callSite, QuerySummaryDetail summary) {
        if (applyPreciseCriteriaQueryLink(context, callSite, summary)) {
            return;
        }
        PointsToSet ownerPts = resolveVarPts(callSite, context, summary.receiverIndex());
        PointsToSet linkedPts = collectVarPts(callSite, context, summary.subjectIndexes());
        if (ownerPts.isEmpty() || linkedPts.isEmpty()) {
            return;
        }
        ownerPts.forEach(owner -> {
            querySummaryStore.linkCarriers(owner, linkedPts);
            markQueryCarrierDirty(owner);
        });
    }

    private void applyQueryAttach(Context context, Invoke callSite, QuerySummaryDetail summary) {
        PointsToSet executorPts = resolveVarPts(callSite, context, summary.receiverIndex());
        PointsToSet carrierPts = collectVarPts(callSite, context, summary.subjectIndexes());
        if (executorPts.isEmpty() || carrierPts.isEmpty()) {
            return;
        }
        queryAttachCount++;
        executorPts.forEach(executor -> {
            querySummaryStore.attachCarriers(executor, carrierPts);
            markQueryExecutorDirty(executor);
        });
    }

    private void applyQueryWriteSlot(Context context, Invoke callSite, QuerySummaryDetail summary) {
        if (applyPreciseCriteriaQueryMutation(context, callSite, summary)) {
            return;
        }
        PointsToSet carrierPts = resolveVarPts(callSite, context, summary.receiverIndex());
        PointsToSet valuePts = collectVarPts(callSite, context, summary.subjectIndexes());
        if (carrierPts.isEmpty() || valuePts.isEmpty() || summary.slotKey() == null) {
            return;
        }
        queryWriteCount++;
        String slotId = summary.slotKey().resolve(callSite).slotId();
        carrierPts.forEach(carrier -> {
            querySummaryStore.addSlotValues(carrier, slotId, valuePts);
            markQueryCarrierDirty(carrier);
        });
    }

    private void applyQueryWriteMeta(Context context, Invoke callSite, QuerySummaryDetail summary) {
        if (applyPreciseCriteriaQueryMutation(context, callSite, summary)) {
            return;
        }
        PointsToSet carrierPts = resolveVarPts(callSite, context, summary.receiverIndex());
        PointsToSet valuePts = collectVarPts(callSite, context, summary.subjectIndexes());
        if (carrierPts.isEmpty() || valuePts.isEmpty() || summary.metaKey() == null) {
            return;
        }
        queryWriteCount++;
        carrierPts.forEach(carrier -> {
            querySummaryStore.addMetaValues(carrier, summary.metaKey(), valuePts);
            markQueryCarrierDirty(carrier);
        });
    }

    private void applyQueryReset(Context context, Invoke callSite, QuerySummaryDetail summary) {
        if (applyPreciseCriteriaQueryMutation(context, callSite, summary)) {
            return;
        }
        PointsToSet carrierPts = resolveVarPts(callSite, context, summary.receiverIndex());
        if (carrierPts.isEmpty()) {
            return;
        }
        carrierPts.forEach(carrier -> {
            querySummaryStore.resetCarrier(carrier);
            markQueryCarrierDirty(carrier);
        });
    }

    private boolean applyPreciseCriteriaQueryLink(
            Context context, Invoke callSite, QuerySummaryDetail summary) {
        if (!isPreciseCriteriaQueryLink(summary)) {
            return false;
        }
        PointsToSet examplePts = filterExamplePts(resolveVarPts(
                callSite, context, summary.receiverIndex()));
        if (examplePts.isEmpty()) {
            return true;
        }
        boolean registeredPreciseBinding = false;
        for (int subjectIndex : summary.subjectIndexes()) {
            Var subjectVar = getVarByIndex(callSite, subjectIndex);
            if (subjectVar == null) {
                continue;
            }
            registerCriteriaVarExamples(context, subjectVar, examplePts);
            promoteDeferredCriteriaQueryValues(
                    callSite, context, subjectVar, examplePts, "QUERY_LINK_PRECISE");
            registeredPreciseBinding = true;
        }
        return registeredPreciseBinding;
    }

    private boolean applyPreciseCriteriaQueryMutation(
            Context context, Invoke callSite, QuerySummaryDetail summary) {
        if (!isPreciseCriteriaQueryMutation(summary)) {
            return false;
        }
        Var receiverVar = getVarByIndex(callSite, summary.receiverIndex());
        if (receiverVar == null) {
            return false;
        }
        Var resultVar = getVarByIndex(callSite, InvokeUtils.RESULT);
        registerCriteriaVarAlias(context, receiverVar, resultVar);
        PointsToSet examplePts = resolveCriteriaVarExamples(context, receiverVar);
        return switch (summary.kind()) {
            case QB_WRITE_SLOT -> {
                PointsToSet valuePts = collectVarPts(callSite, context, summary.subjectIndexes());
                if (valuePts.isEmpty() || summary.slotKey() == null) {
                    yield true;
                }
                if (!examplePts.isEmpty()) {
                    addQuerySlotValuesToExampleHosts(
                            callSite,
                            examplePts,
                            summary.slotKey().resolve(callSite).slotId(),
                            valuePts,
                            "QUERY_CRITERIA_WRITE_SLOT");
                    propagateCriteriaVarExamples(context, receiverVar, resultVar);
                    yield true;
                }
                deferCriteriaVarValues(context, receiverVar, valuePts);
                yield true;
            }
            case QB_WRITE_META -> {
                PointsToSet valuePts = collectVarPts(callSite, context, summary.subjectIndexes());
                if (valuePts.isEmpty() || summary.metaKey() == null) {
                    yield true;
                }
                if (!examplePts.isEmpty()) {
                    addQueryMetaValuesToExampleHosts(
                            callSite,
                            examplePts,
                            summary.metaKey(),
                            valuePts,
                            "QUERY_CRITERIA_WRITE_META");
                    propagateCriteriaVarExamples(context, receiverVar, resultVar);
                    yield true;
                }
                deferCriteriaVarValues(context, receiverVar, valuePts);
                yield true;
            }
            case QB_RESET -> {
                if (!examplePts.isEmpty()) {
                    resetQueryExampleHosts(callSite, examplePts, "QUERY_CRITERIA_RESET");
                    propagateCriteriaVarExamples(context, receiverVar, resultVar);
                    yield true;
                }
                clearDeferredCriteriaVarValues(context, receiverVar);
                yield true;
            }
            default -> false;
        };
    }

    private boolean isPreciseCriteriaQueryLink(QuerySummaryDetail summary) {
        return summary.kind() == QuerySummaryDetail.Kind.QB_LINK
                && looksLikeExampleClass(summary.method().getDeclaringClass());
    }

    private boolean isPreciseCriteriaQueryMutation(QuerySummaryDetail summary) {
        return switch (summary.kind()) {
            case QB_WRITE_SLOT, QB_WRITE_META, QB_RESET ->
                    looksLikeCriteriaClass(summary.method().getDeclaringClass());
            default -> false;
        };
    }

    private void addQuerySlotValuesToExampleHosts(
            @Nullable Invoke callSite, PointsToSet examplePts, String slotId,
            PointsToSet valuePts, String phase) {
        examplePts.forEach(example -> {
            querySummaryStore.addSlotValues(example, slotId, valuePts);
            markQueryCarrierDirty(example);
            debugCriteriaEvent(callSite, () -> String.format(
                    "%s example=%s slot=%s values=%s",
                    phase,
                    describeObj(example),
                    slotId,
                    describePointsToSet(valuePts)));
        });
    }

    private void addQueryMetaValuesToExampleHosts(
            @Nullable Invoke callSite, PointsToSet examplePts, String metaKey,
            PointsToSet valuePts, String phase) {
        examplePts.forEach(example -> {
            querySummaryStore.addMetaValues(example, metaKey, valuePts);
            markQueryCarrierDirty(example);
            debugCriteriaEvent(callSite, () -> String.format(
                    "%s example=%s meta=%s values=%s",
                    phase,
                    describeObj(example),
                    metaKey,
                    describePointsToSet(valuePts)));
        });
    }

    private void resetQueryExampleHosts(
            @Nullable Invoke callSite, PointsToSet examplePts, String phase) {
        examplePts.forEach(example -> {
            querySummaryStore.resetCarrier(example);
            markQueryCarrierDirty(example);
            debugCriteriaEvent(callSite, () -> String.format(
                    "%s example=%s reset",
                    phase,
                    describeObj(example)));
        });
    }

    private void applyQueryRead(CSCallSite csCallSite, Context context, Invoke callSite,
                                QuerySummaryDetail summary) {
        PointsToSet sourcePts = resolveVarPts(callSite, context, summary.receiverIndex());
        if (sourcePts.isEmpty()) {
            return;
        }
        registerQueryReadSite(sourcePts, csCallSite, summary);
        pullQueryReadValues(context, callSite, summary, sourcePts);
    }

    private void registerQueryReadSite(PointsToSet sourcePts, CSCallSite csCallSite,
                                       QuerySummaryDetail summary) {
        QueryReadSite readSite = new QueryReadSite(csCallSite, summary);
        trackedQueryReadSites.add(readSite);
        sourcePts.forEach(source -> {
            if (summary.role() == QuerySummaryDetail.Role.EXECUTOR) {
                executorToQueryReadSites.put(source, readSite);
            } else {
                carrierToQueryReadSites.put(source, readSite);
            }
        });
    }

    private void pullQueryReadValues(Context context, Invoke callSite,
                                     QuerySummaryDetail summary, PointsToSet sourcePts) {
        PointsToSet loadedPts = solver.makePointsToSet();
        sourcePts.forEach(source -> loadedPts.addAll(loadQueryValues(summary, source)));
        if (loadedPts.isEmpty()) {
            return;
        }
        queryReadCount++;
        for (int targetIndex : summary.targetIndexes()) {
            propagateToVar(context, getVarByIndex(callSite, targetIndex), loadedPts);
        }
    }

    private PointsToSet loadQueryValues(QuerySummaryDetail summary, CSObj source) {
        return summary.role() == QuerySummaryDetail.Role.EXECUTOR
                ? querySummaryStore.loadExecutorValues(source)
                : querySummaryStore.loadCarrierValues(source);
    }

    public boolean reapplyDirtyQueryReadSites() {
        Set<QueryReadSite> dirtyReadSites = Sets.newHybridSet();
        dirtyQueryCarriers.forEach(carrier -> dirtyReadSites.addAll(carrierToQueryReadSites.get(carrier)));
        dirtyQueryExecutors.forEach(executor -> dirtyReadSites.addAll(executorToQueryReadSites.get(executor)));
        dirtyQueryCarriers.clear();
        dirtyQueryExecutors.clear();
        boolean applied = false;
        for (QueryReadSite readSite : dirtyReadSites) {
            if (reapplyQueryReadSite(readSite)) {
                applied = true;
            }
        }
        return applied;
    }

    public boolean reapplyRegisteredQuerySummaries() {
        boolean applied = false;
        for (TrackedSummaryCallSite trackedCallSite : Set.copyOf(trackedSummaryCallSites)) {
            if (trackedCallSite.hasQuerySummary()
                    && reapplyTrackedSummaryCallSite(trackedCallSite)) {
                applied = true;
            }
        }
        if (reapplyDirtyQueryReadSites()) {
            applied = true;
        }
        return applied;
    }

    public boolean reapplyRegisteredNonQuerySummaries() {
        boolean applied = false;
        for (TrackedSummaryCallSite trackedCallSite : Set.copyOf(trackedSummaryCallSites)) {
            if (trackedCallSite.hasNonQuerySummary()
                    && reapplyTrackedSummaryCallSite(trackedCallSite)) {
                applied = true;
            }
        }
        return applied;
    }

    private boolean reapplyQueryReadSite(QueryReadSite readSite) {
        CSCallSite csCallSite = readSite.csCallSite();
        if (csCallSite == null || csCallSite.getCallSite() == null || csCallSite.getContext() == null) {
            return false;
        }
        applyQueryRead(csCallSite, csCallSite.getContext(), csCallSite.getCallSite(), readSite.summary());
        return true;
    }

    private void markQueryCarrierDirty(CSObj carrier) {
        if (carrier == null || !dirtyQueryCarriers.add(carrier)) {
            return;
        }
        querySummaryStore.linkedOwners(carrier).forEach(this::markQueryCarrierDirty);
        querySummaryStore.attachedExecutors(carrier).forEach(this::markQueryExecutorDirty);
    }

    private void markQueryExecutorDirty(CSObj executor) {
        if (executor != null) {
            dirtyQueryExecutors.add(executor);
        }
    }

    private void applyCriteriaSummary(Context context, Invoke callSite,
                                      CriteriaSummaryDetail summary) {
        switch (summary.kind()) {
            case EXAMPLE_LINK_RESULT -> applyExampleLinkResult(context, callSite);
            case EXAMPLE_LINK_ARGUMENT ->
                    applyExampleLinkArgument(context, callSite, summary.argIndexes());
            case CRITERIA_ADD_VALUES ->
                    applyCriteriaAddValues(context, callSite, summary.argIndexes());
            case BY_EXAMPLE_LOAD ->
                    applyByExampleLoad(context, callSite, summary.argIndexes());
        }
    }

    private void applyExampleLinkResult(Context context, Invoke callSite) {
        PointsToSet criteriaPts = filterCriteriaPts(
                resolveVarPts(callSite, context, InvokeUtils.RESULT));
        PointsToSet examplePts = filterExamplePts(resolveReceiverPts(callSite, context));
        Var resultVar = getVarByIndex(callSite, InvokeUtils.RESULT);
        debugCriteriaEvent(callSite, () -> String.format(
                "EXAMPLE_LINK_RESULT before receivers=%s filteredReceivers=%s resultPts=%s filteredResultPts=%s",
                describePointsToSet(resolveReceiverPts(callSite, context)),
                describePointsToSet(examplePts),
                describePointsToSet(resolveVarPts(callSite, context, InvokeUtils.RESULT)),
                describePointsToSet(criteriaPts)));
        if (criteriaPts.isEmpty() || examplePts.isEmpty()) {
            debugCriteriaEvent(callSite,
                    () -> "EXAMPLE_LINK_RESULT skipped because filtered receivers/resultPts are empty");
            return;
        }
        if (resultVar != null) {
            registerCriteriaVarExamples(context, resultVar, examplePts);
            promoteDeferredCriteriaVarValues(callSite, context, resultVar, examplePts,
                    "EXAMPLE_LINK_RESULT");
            return;
        }
        examplePts.forEach(example -> {
            criteriaSummaryStore.linkExampleToCriteria(example, criteriaPts);
            criteriaPts.forEach(criteria ->
                    debugCriteriaEvent(callSite, () -> String.format(
                            "EXAMPLE_LINK_RESULT linked example=%s to criteria=%s linkedExamples(criteria)=%s",
                            describeObj(example),
                            describeObj(criteria),
                            describeObjCollection(criteriaSummaryStore.linkedExamples(criteria)))));
            backfillExampleLoads(example);
        });
    }

    private void applyExampleLinkArgument(Context context, Invoke callSite,
                                          java.util.List<Integer> argIndexes) {
        PointsToSet criteriaPts = filterCriteriaPts(collectVarPts(callSite, context, argIndexes));
        PointsToSet examplePts = filterExamplePts(resolveReceiverPts(callSite, context));
        debugCriteriaEvent(callSite, () -> String.format(
                "EXAMPLE_LINK_ARGUMENT before receivers=%s filteredReceivers=%s argIndexes=%s argPts=%s filteredArgPts=%s",
                describePointsToSet(resolveReceiverPts(callSite, context)),
                describePointsToSet(examplePts),
                argIndexes,
                describePointsToSet(collectVarPts(callSite, context, argIndexes)),
                describePointsToSet(criteriaPts)));
        if (criteriaPts.isEmpty() || examplePts.isEmpty()) {
            debugCriteriaEvent(callSite,
                    () -> "EXAMPLE_LINK_ARGUMENT skipped because filtered receivers/argPts are empty");
            return;
        }
        boolean registeredPreciseBinding = false;
        for (int argIndex : argIndexes) {
            Var argVar = getVarByIndex(callSite, argIndex);
            if (argVar == null) {
                continue;
            }
            registerCriteriaVarExamples(context, argVar, examplePts);
            promoteDeferredCriteriaVarValues(callSite, context, argVar, examplePts,
                    "EXAMPLE_LINK_ARGUMENT");
            registeredPreciseBinding = true;
        }
        if (registeredPreciseBinding) {
            return;
        }
        examplePts.forEach(example -> {
            criteriaSummaryStore.linkExampleToCriteria(example, criteriaPts);
            criteriaPts.forEach(criteria ->
                    debugCriteriaEvent(callSite, () -> String.format(
                            "EXAMPLE_LINK_ARGUMENT linked example=%s to criteria=%s linkedExamples(criteria)=%s",
                            describeObj(example),
                            describeObj(criteria),
                            describeObjCollection(criteriaSummaryStore.linkedExamples(criteria)))));
            backfillExampleLoads(example);
        });
    }

    private void applyCriteriaAddValues(Context context, Invoke callSite,
                                        java.util.List<Integer> argIndexes) {
        PointsToSet valuePts = collectVarPts(callSite, context, argIndexes);
        PointsToSet criteriaPts = filterCriteriaPts(resolveReceiverPts(callSite, context));
        Var receiverVar = getVarByIndex(callSite, InvokeUtils.BASE);
        Var resultVar = getVarByIndex(callSite, InvokeUtils.RESULT);
        registerCriteriaVarAlias(context, receiverVar, resultVar);
        PointsToSet attachedExamplePts = resolveCriteriaVarExamples(context, receiverVar);
        debugCriteriaEvent(callSite, () -> String.format(
                "CRITERIA_ADD_VALUES before receivers=%s filteredReceivers=%s attachedExamples=%s argIndexes=%s valuePts=%s",
                describePointsToSet(resolveReceiverPts(callSite, context)),
                describePointsToSet(criteriaPts),
                describePointsToSet(attachedExamplePts),
                argIndexes,
                describePointsToSet(valuePts)));
        if (valuePts.isEmpty() || criteriaPts.isEmpty()) {
            debugCriteriaEvent(callSite,
                    () -> "CRITERIA_ADD_VALUES skipped because filtered receivers/valuePts are empty");
            return;
        }
        if (!attachedExamplePts.isEmpty()) {
            mirrorCriteriaValues(criteriaPts, valuePts);
            addValuesToExampleHosts(callSite, attachedExamplePts, valuePts, "CRITERIA_ADD_VALUES");
            propagateCriteriaVarExamples(context, receiverVar, resultVar);
            return;
        }
        if (receiverVar != null) {
            mirrorCriteriaValues(criteriaPts, valuePts);
            deferCriteriaVarValues(context, receiverVar, valuePts);
            debugCriteriaEvent(callSite, () -> String.format(
                    "CRITERIA_ADD_VALUES deferred receiverVar=%s deferredValues=%s criteria=%s",
                    receiverVar,
                    describePointsToSet(loadDeferredCriteriaVarValues(context, receiverVar)),
                    describePointsToSet(criteriaPts)));
            return;
        }
        criteriaPts.forEach(criteria -> {
            criteriaSummaryStore.addCriteriaValues(criteria, valuePts);
            debugCriteriaEvent(callSite, () -> String.format(
                    "CRITERIA_ADD_VALUES criteria=%s storedValues=%s linkedExamples=%s",
                    describeObj(criteria),
                    describePointsToSet(criteriaSummaryStore.loadCriteriaValues(criteria)),
                    describeObjCollection(criteriaSummaryStore.linkedExamples(criteria))));
            criteriaSummaryStore.linkedExamples(criteria)
                    .forEach(this::backfillExampleLoads);
        });
    }

    private void applyByExampleLoad(Context context, Invoke callSite,
                                    java.util.List<Integer> argIndexes) {
        if (argIndexes.isEmpty()) {
            return;
        }
        int exampleArgIndex = argIndexes.get(0);
        Var exampleVar = getVarByIndex(callSite, exampleArgIndex);
        if (exampleVar == null) {
            return;
        }
        PointsToSet loadedPts = solver.makePointsToSet();
        PointsToSet examplePts = filterExamplePts(resolveVarPts(callSite, context, exampleArgIndex));
        examplePts.forEach(example -> {
            exampleToLoadSites.put(example, new ExampleLoadSite(context, exampleVar));
            debugCriteriaEvent(callSite, () -> String.format(
                    "BY_EXAMPLE_LOAD register example=%s exampleVar=%s currentLoadSites=%d",
                    describeObj(example),
                    exampleVar,
                    exampleToLoadSites.get(example).size()));
            loadedPts.addAll(criteriaSummaryStore.loadExampleValues(example));
        });
        debugCriteriaEvent(callSite, () -> String.format(
                "BY_EXAMPLE_LOAD exampleArgIndex=%d examplePts=%s filteredExamplePts=%s loadedPts=%s",
                exampleArgIndex,
                describePointsToSet(resolveVarPts(callSite, context, exampleArgIndex)),
                describePointsToSet(examplePts),
                describePointsToSet(loadedPts)));
        propagateToVar(context, exampleVar, loadedPts);
    }

    private void backfillExampleLoads(CSObj example) {
        if (!isExampleObj(example)) {
            return;
        }
        PointsToSet loadedPts = criteriaSummaryStore.loadExampleValues(example);
        if (shouldDebugExample(example)) {
            logger.info("[criteria-debug] {}",
                    String.format("BACKFILL example=%s loadSites=%d loadedPts=%s",
                            describeObj(example),
                            exampleToLoadSites.get(example).size(),
                            describePointsToSet(loadedPts)));
        }
        if (loadedPts.isEmpty()) {
            return;
        }
        exampleToLoadSites.get(example).forEach(loadSite ->
                propagateToVar(loadSite.context(), loadSite.exampleVar(), loadedPts));
    }

    private PointsToSet collectVarPts(Invoke callSite, Context context,
                                      Collection<Integer> argIndexes) {
        PointsToSet result = solver.makePointsToSet();
        for (int argIndex : argIndexes) {
            result.addAll(resolveVarPts(callSite, context, argIndex));
        }
        return result;
    }

    private void propagateLoadedValues(Context context, @Nullable Var resultVar,
                                       PointsToSet receiverPts,
                                       java.util.function.Function<CSObj, PointsToSet> loader) {
        PointsToSet resultPts = solver.makePointsToSet();
        receiverPts.forEach(container -> resultPts.addAll(loader.apply(container)));
        propagateToVar(context, resultVar, resultPts);
    }

    private PointsToSet resolveReceiverPts(Invoke callSite, Context context) {
        return resolveVarPts(callSite, context, InvokeUtils.BASE);
    }

    private KeySelector resolveKeySelector(Invoke callSite, Context context, int argIndex) {
        Var var = getVarByIndex(callSite, argIndex);
        if (var != null && var.isConst() && var.getConstValue() instanceof StringLiteral literal) {
            return KeySelector.constant(literal.getString());
        }
        return KeySelector.wildcard();
    }

    private PointsToSet filterExamplePts(PointsToSet pts) {
        return filterPointsToSet(pts, this::isExampleObj);
    }

    private PointsToSet filterCriteriaPts(PointsToSet pts) {
        return filterPointsToSet(pts, this::isCriteriaObj);
    }

    private PointsToSet filterPointsToSet(PointsToSet pts,
                                          java.util.function.Predicate<CSObj> predicate) {
        PointsToSet result = solver.makePointsToSet();
        pts.forEach(obj -> {
            if (predicate.test(obj)) {
                result.addObject(obj);
            }
        });
        return result;
    }

    private PointsToSet resolveVarPts(Invoke callSite, Context context, int index) {
        Var var = getVarByIndex(callSite, index);
        return var == null ? solver.makePointsToSet()
                : solver.getPointsToSetOf(csManager.getCSVar(context, var));
    }

    private void propagateToVar(Context context, @Nullable Var var, PointsToSet sourcePts) {
        if (var == null || sourcePts.isEmpty()) {
            return;
        }
        CSVar csVar = csManager.getCSVar(context, var);
        PointsToSet diff = diffAgainstCurrent(csVar, sourcePts);
        if (!diff.isEmpty()) {
            solver.addPointsTo(csVar, diff);
        }
    }

    private void registerCriteriaVarExamples(Context context, @Nullable Var criteriaVar,
                                             PointsToSet examplePts) {
        if (criteriaVar == null || examplePts.isEmpty()) {
            return;
        }
        CSVar csVar = csManager.getCSVar(context, criteriaVar);
        examplePts.forEach(example -> criteriaVarToExamples.put(csVar, example));
    }

    private PointsToSet resolveCriteriaVarExamples(Context context, @Nullable Var criteriaVar) {
        if (criteriaVar == null) {
            return solver.makePointsToSet();
        }
        return resolveCriteriaVarExamples(csManager.getCSVar(context, criteriaVar), Sets.newSet());
    }

    private PointsToSet resolveCriteriaVarExamples(CSVar csVar,
                                                   Set<CSVar> visiting) {
        PointsToSet result = solver.makePointsToSet();
        criteriaVarToExamples.get(csVar).forEach(result::addObject);
        if (!result.isEmpty()) {
            return result;
        }
        if (!visiting.add(csVar)) {
            return result;
        }
        Context context = csVar.getContext();
        Var criteriaVar = csVar.getVar();
        for (Var sourceVar : resolveLocalAliasSources(criteriaVar)) {
            result.addAll(resolveCriteriaVarExamples(
                    csManager.getCSVar(context, sourceVar), visiting));
        }
        for (CSVar sourceVar : criteriaVarAliasSources.get(csVar)) {
            result.addAll(resolveCriteriaVarExamples(sourceVar, visiting));
        }
        if (!result.isEmpty()) {
            registerCriteriaVarExamples(context, criteriaVar, result);
        }
        return result;
    }

    private Collection<Var> resolveLocalAliasSources(Var targetVar) {
        JMethod method = targetVar.getMethod();
        if (method == null || method.ir == null) {
            return java.util.List.of();
        }
        Set<Var> sources = Sets.newLinkedSet();
        boolean hasDefinition = false;
        for (Stmt stmt : method.ir.getStmts()) {
            if (!(stmt instanceof DefinitionStmt<?, ?> definition)) {
                continue;
            }
            if (definition.getLValue() != targetVar) {
                continue;
            }
            hasDefinition = true;
            if (stmt instanceof Copy copy) {
                sources.add(copy.getRValue());
                continue;
            }
            if (stmt instanceof Cast cast) {
                sources.add(cast.getRValue().getValue());
                continue;
            }
            return java.util.List.of();
        }
        return hasDefinition ? sources : java.util.List.of();
    }

    private Collection<Var> resolveLocalAliasTargets(Var sourceVar) {
        JMethod method = sourceVar.getMethod();
        if (method == null || method.ir == null) {
            return java.util.List.of();
        }
        Set<Var> targets = Sets.newLinkedSet();
        for (Stmt stmt : method.ir.getStmts()) {
            if (stmt instanceof Copy copy && copy.getRValue() == sourceVar) {
                targets.add(copy.getLValue());
                continue;
            }
            if (stmt instanceof Cast cast && cast.getRValue().getValue() == sourceVar) {
                targets.add(cast.getLValue());
            }
        }
        return targets;
    }

    private void propagateCriteriaVarExamples(Context context, @Nullable Var fromVar,
                                              @Nullable Var toVar) {
        if (fromVar == null || toVar == null) {
            return;
        }
        registerCriteriaVarExamples(context, toVar, resolveCriteriaVarExamples(context, fromVar));
    }

    private void registerCriteriaVarAlias(Context context, @Nullable Var sourceVar,
                                          @Nullable Var targetVar) {
        if (sourceVar == null || targetVar == null || sourceVar == targetVar) {
            return;
        }
        CSVar source = csManager.getCSVar(context, sourceVar);
        CSVar target = csManager.getCSVar(context, targetVar);
        criteriaVarAliasSources.put(target, source);
        criteriaVarAliasTargets.put(source, target);
    }

    private void deferCriteriaVarValues(Context context, @Nullable Var criteriaVar,
                                        PointsToSet valuePts) {
        if (criteriaVar == null || valuePts.isEmpty()) {
            return;
        }
        deferredCriteriaVarValues
                .computeIfAbsent(csManager.getCSVar(context, criteriaVar),
                        __ -> solver.makePointsToSet())
                .addAll(valuePts);
    }

    private PointsToSet loadDeferredCriteriaVarValues(Context context, @Nullable Var criteriaVar) {
        if (criteriaVar == null) {
            return solver.makePointsToSet();
        }
        PointsToSet deferred = deferredCriteriaVarValues.get(csManager.getCSVar(context, criteriaVar));
        return deferred == null ? solver.makePointsToSet() : deferred.copy();
    }

    private void clearDeferredCriteriaVarValues(Context context, @Nullable Var criteriaVar) {
        if (criteriaVar == null) {
            return;
        }
        clearDeferredCriteriaVarValues(
                csManager.getCSVar(context, criteriaVar), Sets.newSet());
    }

    private void clearDeferredCriteriaVarValues(CSVar criteriaVar, Set<CSVar> visiting) {
        if (!visiting.add(criteriaVar)) {
            return;
        }
        deferredCriteriaVarValues.remove(criteriaVar);
        for (CSVar aliasTarget : criteriaVarAliasTargets.get(criteriaVar)) {
            clearDeferredCriteriaVarValues(aliasTarget, visiting);
        }
        for (Var localAliasTarget : resolveLocalAliasTargets(criteriaVar.getVar())) {
            clearDeferredCriteriaVarValues(
                    csManager.getCSVar(criteriaVar.getContext(), localAliasTarget),
                    visiting);
        }
    }

    private void promoteDeferredCriteriaQueryValues(@Nullable Invoke callSite, Context context,
                                                    @Nullable Var criteriaVar,
                                                    PointsToSet examplePts, String phase) {
        if (criteriaVar == null || examplePts.isEmpty()) {
            return;
        }
        promoteDeferredCriteriaQueryValues(callSite,
                csManager.getCSVar(context, criteriaVar), examplePts, phase, Sets.newSet());
    }

    private void promoteDeferredCriteriaQueryValues(@Nullable Invoke callSite, CSVar criteriaVar,
                                                    PointsToSet examplePts, String phase,
                                                    Set<CSVar> visiting) {
        if (!visiting.add(criteriaVar)) {
            return;
        }
        PointsToSet deferred = deferredCriteriaVarValues.get(criteriaVar);
        if (deferred != null && !deferred.isEmpty()) {
            addQueryMetaValuesToExampleHosts(
                    callSite,
                    examplePts,
                    PRECISE_CRITERIA_DEFERRED_META_KEY,
                    deferred,
                    phase + "_DEFERRED");
        }
        for (CSVar aliasTarget : criteriaVarAliasTargets.get(criteriaVar)) {
            promoteDeferredCriteriaQueryValues(callSite, aliasTarget, examplePts, phase, visiting);
        }
        for (Var localAliasTarget : resolveLocalAliasTargets(criteriaVar.getVar())) {
            promoteDeferredCriteriaQueryValues(callSite,
                    csManager.getCSVar(criteriaVar.getContext(), localAliasTarget),
                    examplePts, phase, visiting);
        }
    }

    private void promoteDeferredCriteriaVarValues(@Nullable Invoke callSite, Context context,
                                                  @Nullable Var criteriaVar, PointsToSet examplePts,
                                                  String phase) {
        if (criteriaVar == null || examplePts.isEmpty()) {
            return;
        }
        promoteDeferredCriteriaVarValues(callSite,
                csManager.getCSVar(context, criteriaVar), examplePts, phase, Sets.newSet());
    }

    private void promoteDeferredCriteriaVarValues(@Nullable Invoke callSite, CSVar criteriaVar,
                                                  PointsToSet examplePts, String phase,
                                                  Set<CSVar> visiting) {
        if (!visiting.add(criteriaVar)) {
            return;
        }
        PointsToSet deferred = deferredCriteriaVarValues.get(criteriaVar);
        if (deferred != null && !deferred.isEmpty()) {
            debugCriteriaEvent(callSite, () -> String.format(
                    "%s promoteDeferred criteriaVar=%s examples=%s deferredValues=%s",
                    phase,
                    criteriaVar,
                    describePointsToSet(examplePts),
                    describePointsToSet(deferred)));
            addValuesToExampleHosts(callSite, examplePts, deferred, phase + "_DEFERRED");
        }
        for (CSVar aliasTarget : criteriaVarAliasTargets.get(criteriaVar)) {
            promoteDeferredCriteriaVarValues(callSite, aliasTarget, examplePts, phase, visiting);
        }
        for (Var localAliasTarget : resolveLocalAliasTargets(criteriaVar.getVar())) {
            promoteDeferredCriteriaVarValues(callSite,
                    csManager.getCSVar(criteriaVar.getContext(), localAliasTarget),
                    examplePts, phase, visiting);
        }
    }

    private void addValuesToExampleHosts(@Nullable Invoke callSite, PointsToSet examplePts,
                                         PointsToSet valuePts, String phase) {
        examplePts.forEach(example -> {
            PointsToSet exampleHostPts = solver.makePointsToSet();
            exampleHostPts.addObject(example);
            criteriaSummaryStore.linkExampleToCriteria(example, exampleHostPts);
            criteriaSummaryStore.addCriteriaValues(example, valuePts);
            debugCriteriaEvent(callSite, () -> String.format(
                    "%s exampleHost=%s storedValues=%s",
                    phase,
                    describeObj(example),
                    describePointsToSet(criteriaSummaryStore.loadCriteriaValues(example))));
            backfillExampleLoads(example);
        });
    }

    private void promoteCriteriaValuesToExamples(@Nullable Invoke callSite, PointsToSet examplePts,
                                                 PointsToSet criteriaPts, String phase) {
        examplePts.forEach(example -> {
            criteriaPts.forEach(criteria -> {
                PointsToSet existingValues = criteriaSummaryStore.loadCriteriaValues(criteria);
                if (existingValues.isEmpty()) {
                    return;
                }
                debugCriteriaEvent(callSite, () -> String.format(
                        "%s promote criteria=%s -> example=%s values=%s",
                        phase,
                        describeObj(criteria),
                        describeObj(example),
                        describePointsToSet(existingValues)));
                PointsToSet exampleHostPts = solver.makePointsToSet();
                exampleHostPts.addObject(example);
                criteriaSummaryStore.linkExampleToCriteria(example, exampleHostPts);
                criteriaSummaryStore.addCriteriaValues(example, existingValues);
            });
            backfillExampleLoads(example);
        });
    }

    private void mirrorCriteriaValues(PointsToSet criteriaPts, PointsToSet valuePts) {
        criteriaPts.forEach(criteria -> criteriaSummaryStore.addCriteriaValues(criteria, valuePts));
    }

    /**
     * 重新应用摘要 - 用于分析后期的全局重新计算
     *
     * <p>与 applySummary 的区别：
     * <ul>
     *   <li>applySummary: 在 processCall 时调用，有 CSCallSite 和 Context</li>
     *   <li>reapplySummary: 在分析后期调用，需要从 CSManager 中获取所有调用点</li>
     * </ul>
     *
     * @param methodRef 方法引用
     * @return true 如果找到并重新应用了摘要
     */
    public boolean reapplySummary(MethodRef methodRef) {
        boolean applied = false;
        for (TrackedSummaryCallSite trackedCallSite : collectTrackedSummaryCallSites(methodRef)) {
            if (reapplyTrackedSummaryCallSite(trackedCallSite)) {
                applied = true;
            }
        }
        return applied;
    }

    public boolean reapplyRegisteredSummaries() {
        globalReapplyFallbackCount++;
        boolean applied = false;
        for (TrackedSummaryCallSite trackedCallSite : Set.copyOf(trackedSummaryCallSites)) {
            if (reapplyTrackedSummaryCallSite(trackedCallSite)) {
                applied = true;
            }
        }
        return applied;
    }

    private ResolvedSummaries lookupSummaries(MethodRef methodRef) {
        return summaryLookupCache.computeIfAbsent(methodRef, this::lookupSummariesUncached);
    }

    private MethodRef resolveSummaryMethodRef(MethodRef methodRef) {
        return resolvedSummaryMethodRefCache.computeIfAbsent(
                methodRef, this::resolveSummaryMethodRefUncached);
    }

    private ResolvedSummaries lookupSummariesUncached(MethodRef methodRef) {
        MethodRef resolvedMethodRef = resolveSummaryMethodRef(methodRef);
        Set<SummaryDetail> transferSummaries = methodToSummaries.get(resolvedMethodRef);
        Set<ContainerSummaryDetail> containerSummaries = methodToContainerSummaries.get(resolvedMethodRef);
        Set<CriteriaSummaryDetail> criteriaSummaries = methodToCriteriaSummaries.get(resolvedMethodRef);
        Set<QuerySummaryDetail> querySummaries = methodToQuerySummaries.get(resolvedMethodRef);
        if (transferSummaries.isEmpty()
                && containerSummaries.isEmpty()
                && criteriaSummaries.isEmpty()
                && querySummaries.isEmpty()) {
            QuerySummaryDetail synthesizedQuerySummary =
                    synthesizeQuerySummary(methodRef, resolvedMethodRef);
            if (synthesizedQuerySummary != null) {
                return new ResolvedSummaries(
                        Set.of(),
                        Set.of(),
                        Set.of(),
                        Set.of(synthesizedQuerySummary));
            }
            return EMPTY_SUMMARIES;
        }
        return new ResolvedSummaries(
                transferSummaries,
                containerSummaries,
                criteriaSummaries,
                querySummaries);
    }

    private MethodRef resolveSummaryMethodRefUncached(MethodRef methodRef) {
        if (hasDirectSummary(methodRef)) {
            return methodRef;
        }
        JMethod resolved = methodRef.resolveNullable();
        if (resolved == null) {
            return methodRef;
        }
        MethodRef resolvedRef = resolved.getRef();
        if (hasDirectSummary(resolvedRef)) {
            return resolvedRef;
        }
        MethodRef inheritedSummaryRef = findInheritedSummaryMethodRef(resolved);
        return inheritedSummaryRef != null ? inheritedSummaryRef : methodRef;
    }

    @Nullable
    private QuerySummaryDetail synthesizeQuerySummary(
            MethodRef requestedMethodRef, MethodRef resolvedMethodRef) {
        QuerySummaryDetail synthesized = synthesizeQuerySummary(resolvedMethodRef.resolveNullable());
        if (synthesized != null) {
            return synthesized;
        }
        if (!resolvedMethodRef.equals(requestedMethodRef)) {
            return synthesizeQuerySummary(requestedMethodRef.resolveNullable());
        }
        return null;
    }

    @Nullable
    private QuerySummaryDetail synthesizeQuerySummary(@Nullable JMethod method) {
        if (method == null) {
            return null;
        }
        QuerySummaryDetail criteriaSummary = buildCriteriaValueSummary(method);
        if (criteriaSummary != null) {
            return criteriaSummary;
        }
        return null;
    }

    private void clearSummaryLookupCaches() {
        resolvedSummaryMethodRefCache.clear();
        summaryLookupCache.clear();
    }

    private void registerTrackedSummaryCallSite(CSCallSite csCallSite, MethodRef calleeMethodRef,
                                                ResolvedSummaries summaries) {
        Invoke callSite = csCallSite.getCallSite();
        if (callSite == null || callSite.getInvokeExp() == null) {
            return;
        }
        TrackedSummaryCallSite trackedCallSite =
                new TrackedSummaryCallSite(
                        csCallSite,
                        calleeMethodRef,
                        summaries.hasQuerySummaries(),
                        summaries.hasNonQuerySummaries());
        trackedSummaryCallSites.add(trackedCallSite);
        MethodRef rawCallSiteMethodRef = callSite.getInvokeExp().getMethodRef();
        if (rawCallSiteMethodRef != null) {
            summaryCallSites.put(rawCallSiteMethodRef, trackedCallSite);
        }
        summaryCallSites.put(calleeMethodRef, trackedCallSite);
        summaryCallSites.put(resolveSummaryMethodRef(calleeMethodRef), trackedCallSite);
    }

    private Set<TrackedSummaryCallSite> collectTrackedSummaryCallSites(MethodRef methodRef) {
        Set<TrackedSummaryCallSite> tracked = Sets.newHybridSet();
        tracked.addAll(summaryCallSites.get(methodRef));
        MethodRef resolvedMethodRef = resolveSummaryMethodRef(methodRef);
        if (!resolvedMethodRef.equals(methodRef)) {
            tracked.addAll(summaryCallSites.get(resolvedMethodRef));
        }
        return tracked;
    }

    private boolean reapplyTrackedSummaryCallSite(TrackedSummaryCallSite trackedCallSite) {
        CSCallSite csCallSite = trackedCallSite.csCallSite();
        if (csCallSite == null) {
            return false;
        }
        Invoke callSite = csCallSite.getCallSite();
        Context callerContext = csCallSite.getContext();
        if (callSite == null || callerContext == null) {
            return false;
        }
        InvokeExp invokeExp = callSite.getInvokeExp();
        if (invokeExp == null) {
            return false;
        }

        boolean reappliedAtCallSite = false;
        if (invokeExp instanceof InvokeInstanceExp) {
            PointsToSet receiverPts = resolveReceiverPts(callSite, callerContext);
            for (CSObj receiver : receiverPts) {
                JMethod callee = CallGraphs.resolveCallee(
                        receiver.getObject().getType(), callSite);
                if (callee != null
                        && applySummary(csCallSite, callee.getRef(), callerContext)) {
                    reappliedAtCallSite = true;
                }
            }
        }

        if (!reappliedAtCallSite
                && applySummary(csCallSite, trackedCallSite.replayMethodRef(), callerContext)) {
            reappliedAtCallSite = true;
        }
        return reappliedAtCallSite;
    }

    @Nullable
    private MethodRef findInheritedSummaryMethodRef(JMethod method) {
        Set<JClass> visited = Sets.newHybridSet();
        java.util.Deque<JClass> worklist = new java.util.ArrayDeque<>();
        JClass declaringClass = method.getDeclaringClass();
        if (declaringClass.getSuperClass() != null) {
            worklist.addLast(declaringClass.getSuperClass());
        }
        declaringClass.getInterfaces().forEach(worklist::addLast);
        while (!worklist.isEmpty()) {
            JClass current = worklist.removeFirst();
            if (!visited.add(current)) {
                continue;
            }
            JMethod candidate = current.getDeclaredMethod(method.getSubsignature());
            if (candidate != null && hasDirectSummary(candidate.getRef())) {
                return candidate.getRef();
            }
            if (current.getSuperClass() != null) {
                worklist.addLast(current.getSuperClass());
            }
            current.getInterfaces().forEach(worklist::addLast);
        }
        return null;
    }

    private boolean hasDirectSummary(MethodRef methodRef) {
        return methodToSummaries.containsKey(methodRef)
                || methodToContainerSummaries.containsKey(methodRef)
                || methodToCriteriaSummaries.containsKey(methodRef)
                || methodToQuerySummaries.containsKey(methodRef);
    }

    /**
     * 解析 source AccessPath 的 PointsToSet
     */
    @Nullable
    private PointsToSet resolveSourcePts(Invoke callSite, Context context, AccessPath source) {
        // 获取 base 变量
        Var baseVar = getVarByIndex(callSite, source.base());
        if (baseVar == null) {
            logger.info("baseVar 解析失败");
            return null;
        }
        CSVar csBaseVar = csManager.getCSVar(context, baseVar);
        PointsToSet basePts = solver.getPointsToSetOf(csBaseVar);

        if (source.isSimpleVar()) {
            // 简单变量：直接返回 pts
            return basePts;
        } else if (source.hasFieldAccess()) {
            // 字段访问：base.field -> 收集所有 base 对象的 field pts
            JField field = source.getFirstField();
            if (field == null) {
                return null;
            }
            return collectFieldPts(basePts, field);
        } else if (source.hasArrayAccess()) {
            // 数组访问：base[*] -> 收集所有 base 数组的元素 pts
            return collectArrayPts(basePts);
        }

        return null;
    }

    /**
     * 收集字段的 pts（遍历所有 base 对象）
     */
    private PointsToSet collectFieldPts(PointsToSet basePts, JField field) {
        PointsToSet result = solver.makePointsToSet();
        basePts.forEach(baseObj -> {
            var instField = csManager.getInstanceField(baseObj, field);
            PointsToSet fieldPts = solver.getPointsToSetOf(instField);
            fieldPts.forEach(result::addObject);
        });
        return result;
    }

    /**
     * 收集数组元素的 pts（遍历所有 base 数组对象）
     */
    private PointsToSet collectArrayPts(PointsToSet basePts) {
        PointsToSet result = solver.makePointsToSet();
        basePts.forEach(baseObj -> {
            var arrayIndex = csManager.getArrayIndex(baseObj);
            PointsToSet elemPts = solver.getPointsToSetOf(arrayIndex);
            elemPts.forEach(result::addObject);
        });
        return result;
    }

    /**
     * 将 sourcePts 传播到 target AccessPath
     */
    private void propagateToTarget(Invoke callSite, Context context,
                                   AccessPath target, PointsToSet sourcePts) {
        // 获取 target base 变量
        Var targetBaseVar = getVarByIndex(callSite, target.base());
        if (targetBaseVar == null) {
            return;
        }

        if (target.isSimpleVar()) {
            // 简单变量：直接添加到变量的 pts
            CSVar targetVar = csManager.getCSVar(context, targetBaseVar);
            PointsToSet diff = diffAgainstCurrent(targetVar, sourcePts);
            if (!diff.isEmpty()) {
                solver.addPointsTo(targetVar, diff);
            }
        } else if (target.hasFieldAccess()) {
            // 字段访问：添加到 base.field 的 pts
            JField field = target.getFirstField();
            if (field == null) {
                return;
            }


            CSVar csTargetBase = csManager.getCSVar(context, targetBaseVar);
            PointsToSet targetBasePts = solver.getPointsToSetOf(csTargetBase);
            targetBasePts.forEach(baseObj -> {

                var instField = csManager.getInstanceField(baseObj, field);
                PointsToSet diff = diffAgainstCurrent(instField, sourcePts);
                if (!diff.isEmpty()) {
                    solver.addPointsTo(instField, diff);
                }
            });

        } else if (target.hasArrayAccess()) {
            // 数组访问：添加到 base[*] 的 pts
            // 用于支持容器 add/put 类摘要规则（如 from: 0, to: base[*]）
            CSVar csTargetBase = csManager.getCSVar(context, targetBaseVar);
            PointsToSet targetBasePts = solver.getPointsToSetOf(csTargetBase);
            targetBasePts.forEach(baseObj -> {
                var arrayIndex = csManager.getArrayIndex(baseObj);
                PointsToSet diff = diffAgainstCurrent(arrayIndex, sourcePts);
                if (!diff.isEmpty()) {
                    solver.addPointsTo(arrayIndex, diff);
                }
            });
        }
    }

    private PointsToSet diffAgainstCurrent(Pointer pointer, PointsToSet incoming) {
        PointsToSet current = solver.getPointsToSetOf(pointer);
        PointsToSet diff = solver.makePointsToSet();
        incoming.forEach(obj -> {
            if (!current.contains(obj)) {
                diff.addObject(obj);
            }
        });
        return diff;
    }


    // ==================== 工具方法 ====================

    /**
     * 根据索引获取变量
     *
     * @param callSite 调用点
     * @param index    变量索引（-1=base, -2=result, 0..n=参数）
     * @return 对应的变量，如果不存在则返回 null
     */
    @Nullable
    private Var getVarByIndex(Invoke callSite, int index) {
        InvokeExp invokeExp = callSite.getInvokeExp();
        return switch (index) {
            case InvokeUtils.BASE -> {
                if (invokeExp instanceof InvokeInstanceExp instanceExp) {
                    yield instanceExp.getBase();
                }
                yield null;
            }
            case InvokeUtils.RESULT -> callSite.getResult();
            default -> {
                if (index >= 0 && index < invokeExp.getArgCount()) {
                    yield invokeExp.getArg(index);
                }
                yield null;
            }
        };
    }

    // ==================== 辅助方法：JDK 容器摘要注册 ====================

    private int addJdkContainerSummaries(pascal.taie.language.classes.ClassHierarchy hierarchy) {
        int registered = 0;
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.HashMap: java.lang.Object get(java.lang.Object)>",
                ContainerSummaryDetail.Kind.MAP_GET);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                ContainerSummaryDetail.Kind.MAP_PUT);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.HashMap: java.lang.Object getOrDefault(java.lang.Object,java.lang.Object)>",
                ContainerSummaryDetail.Kind.MAP_GET_OR_DEFAULT);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.HashMap: java.lang.Object remove(java.lang.Object)>",
                ContainerSummaryDetail.Kind.MAP_REMOVE);

        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.ArrayList: java.lang.Object get(int)>",
                ContainerSummaryDetail.Kind.LIST_GET);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.ArrayList: java.lang.Object set(int,java.lang.Object)>",
                ContainerSummaryDetail.Kind.LIST_SET);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.ArrayList: java.lang.Object remove(int)>",
                ContainerSummaryDetail.Kind.LIST_REMOVE);

        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.LinkedList: java.lang.Object get(int)>",
                ContainerSummaryDetail.Kind.LIST_GET);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.LinkedList: java.lang.Object getFirst()>",
                ContainerSummaryDetail.Kind.LIST_GET);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.LinkedList: java.lang.Object getLast()>",
                ContainerSummaryDetail.Kind.LIST_GET);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.ArrayList: boolean add(java.lang.Object)>",
                ContainerSummaryDetail.Kind.COLLECTION_ADD);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.LinkedList: boolean add(java.lang.Object)>",
                ContainerSummaryDetail.Kind.COLLECTION_ADD);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.lang.Iterable: java.util.Iterator iterator()>",
                ContainerSummaryDetail.Kind.ITERATOR_BIND_RESULT);
        registered += addJdkContainerSummaryIfEnabled(hierarchy,
                "<java.util.Iterator: java.lang.Object next()>",
                ContainerSummaryDetail.Kind.ITERATOR_NEXT);
        registered += addAttributeCarrierSummaries(hierarchy);
        return registered;
    }

    private int addJdkContainerSummaryIfEnabled(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            String methodSignature,
            ContainerSummaryDetail.Kind kind) {
        return isContainerSummaryEnabled(kind)
                ? addJdkContainerSummary(hierarchy, methodSignature, kind)
                : 0;
    }

    private boolean isContainerSummaryEnabled(ContainerSummaryDetail.Kind kind) {
        return switch (kind) {
            case MAP_GET, MAP_PUT, MAP_GET_OR_DEFAULT, MAP_REMOVE ->
                    enableMapContainerSummaries;
            case LIST_GET, LIST_SET, LIST_REMOVE ->
                    enableListContainerSummaries;
            case COLLECTION_ADD -> enableCollectionContainerSummaries;
            case ITERATOR_BIND_RESULT, ITERATOR_NEXT ->
                    enableIteratorContainerSummaries;
            case ATTRIBUTE_GET, ATTRIBUTE_SET -> true;
        };
    }

    private boolean resolveBooleanOption(String key, boolean defaultValue) {
        try {
            var options = solver.getOptions();
            if (options != null && options.has(key)) {
                return options.getBoolean(key);
            }
        } catch (RuntimeException e) {
            logger.debug("SummaryManager: option '{}' unavailable, using default {}",
                    key, defaultValue, e);
        }
        return defaultValue;
    }

    private String resolveStringOption(String key, String defaultValue) {
        try {
            var options = solver.getOptions();
            if (options != null && options.has(key)) {
                Object value = options.get(key);
                return value == null ? defaultValue : value.toString();
            }
        } catch (RuntimeException e) {
            logger.debug("SummaryManager: option '{}' unavailable, using default {}",
                    key, defaultValue, e);
        }
        return defaultValue;
    }

    @SuppressWarnings("unchecked")
    private List<String> resolveStringListOption(String key) {
        try {
            var options = solver.getOptions();
            if (options != null && options.has(key)) {
                Object value = options.get(key);
                if (value instanceof List<?> list) {
                    return list.stream()
                            .filter(Objects::nonNull)
                            .map(Object::toString)
                            .toList();
                }
                if (value instanceof String str && !str.isBlank()) {
                    return List.of(str);
                }
            }
        } catch (RuntimeException e) {
            logger.debug("SummaryManager: option '{}' unavailable, using default []",
                    key, e);
        }
        return List.of();
    }

    private JdkSummaryCatalog loadJdkSummaryCatalog() {
        JdkSummaryCatalog catalog = new JdkSummaryCatalogLoader(
                solver.getHierarchy(),
                resolveStringOption("jdk-summary-profile", "auto"),
                resolveStringOption("jdk-summary-missing-signature", "warn"),
                resolveStringListOption("jdk-summary-configs")).load();
        List<String> includes = resolveStringListOption(
                "summary-jdk-catalog-include-substrings");
        List<String> excludes = resolveStringListOption(
                "summary-jdk-catalog-exclude-substrings");
        if (includes.isEmpty() && excludes.isEmpty()) {
            return catalog;
        }
        List<SummaryDetail> filtered = catalog.summaryConfig()
                .summaryDetails()
                .stream()
                .filter(summary -> matchesCatalogFilter(
                        summary.method().getSignature(), includes, excludes))
                .toList();
        logger.info("Filtered JDK catalog summaries from {} to {} "
                        + "(include-substrings={}, exclude-substrings={})",
                catalog.summaryConfig().summaryDetails().size(),
                filtered.size(),
                includes,
                excludes);
        return new JdkSummaryCatalog(
                new SummaryConfig(filtered),
                catalog.noops(),
                catalog.stats());
    }

    private boolean matchesCatalogFilter(
            String signature, List<String> includes, List<String> excludes) {
        boolean included = includes.isEmpty()
                || includes.stream().anyMatch(signature::contains);
        boolean excluded = excludes.stream().anyMatch(signature::contains);
        return included && !excluded;
    }

    private int addAttributeCarrierSummaries(pascal.taie.language.classes.ClassHierarchy hierarchy) {
        int registered = 0;
        registered += addJdkContainerSummary(hierarchy,
                "<javax.servlet.ServletRequest: void setAttribute(java.lang.String,java.lang.Object)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_SET);
        registered += addJdkContainerSummary(hierarchy,
                "<javax.servlet.ServletRequest: java.lang.Object getAttribute(java.lang.String)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_GET);
        registered += addJdkContainerSummary(hierarchy,
                "<javax.servlet.http.HttpSession: void setAttribute(java.lang.String,java.lang.Object)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_SET);
        registered += addJdkContainerSummary(hierarchy,
                "<javax.servlet.http.HttpSession: java.lang.Object getAttribute(java.lang.String)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_GET);
        registered += addJdkContainerSummary(hierarchy,
                "<jakarta.servlet.ServletRequest: void setAttribute(java.lang.String,java.lang.Object)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_SET);
        registered += addJdkContainerSummary(hierarchy,
                "<jakarta.servlet.ServletRequest: java.lang.Object getAttribute(java.lang.String)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_GET);
        registered += addJdkContainerSummary(hierarchy,
                "<jakarta.servlet.http.HttpSession: void setAttribute(java.lang.String,java.lang.Object)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_SET);
        registered += addJdkContainerSummary(hierarchy,
                "<jakarta.servlet.http.HttpSession: java.lang.Object getAttribute(java.lang.String)>",
                ContainerSummaryDetail.Kind.ATTRIBUTE_GET);
        return registered;
    }

    private int addCriteriaSummaries(pascal.taie.language.classes.ClassHierarchy hierarchy) {
        int registered = 0;
        for (JClass clazz : hierarchy.applicationClasses().toList()) {
            registered += addExampleBuilderSummaries(clazz);
            registered += addCriteriaValueSummaries(clazz);
            registered += addByExampleConsumerSummaries(clazz);
        }
        return registered;
    }

    private int addMyBatisPlusQuerySummaries(
            pascal.taie.language.classes.ClassHierarchy hierarchy) {
        JClass queryWrapperClass = hierarchy.getClass(
                "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper");
        JClass lambdaQueryWrapperClass = hierarchy.getClass(
                "com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper");
        int registered = 0;
        registered += addMyBatisPlusWrapperSummaries(
                hierarchy, queryWrapperClass, MyBatisPlusWrapperKind.STRING);
        registered += addMyBatisPlusWrapperSummaries(
                hierarchy, lambdaQueryWrapperClass, MyBatisPlusWrapperKind.LAMBDA);
        registered += addMyBatisPlusReadSummaries(
                hierarchy, queryWrapperClass, lambdaQueryWrapperClass);
        registered += addGridBinderQuerySummaries(
                hierarchy, queryWrapperClass, lambdaQueryWrapperClass);
        return registered;
    }

    private int addExampleBuilderSummaries(JClass clazz) {
        if (!looksLikeExampleClass(clazz)) {
            return 0;
        }
        int registered = 0;
        for (JMethod method : clazz.getDeclaredMethods()) {
            if (method.isStatic() || method.isNative()) {
                continue;
            }
            String methodName = method.getName();
            if ("createCriteria".equals(methodName)
                    && isCriteriaType(method.getReturnType())) {
                registerQuerySummary(method, QuerySummaryDetail.linkResult(method));
                registered++;
            } else if ("or".equals(methodName)
                    && method.getParamCount() == 0
                    && isCriteriaType(method.getReturnType())) {
                registerQuerySummary(method, QuerySummaryDetail.linkResult(method));
                registered++;
            } else if ("or".equals(methodName)
                    && method.getParamCount() == 1
                    && isCriteriaType(method.getParamType(0))) {
                registerQuerySummary(method, QuerySummaryDetail.linkArgument(method, 0));
                registered++;
            } else if ("clear".equals(methodName) && method.getParamCount() == 0) {
                registerQuerySummary(method,
                        QuerySummaryDetail.resetCarrier(method, InvokeUtils.BASE));
                registered++;
            }
        }
        return registered;
    }

    private int addCriteriaValueSummaries(JClass clazz) {
        if (!looksLikeCriteriaClass(clazz)) {
            return 0;
        }
        int registered = 0;
        for (JMethod method : clazz.getDeclaredMethods()) {
            if (method.isStatic() || method.isNative()) {
                continue;
            }
            QuerySummaryDetail querySummary = buildCriteriaValueSummary(method);
            if (querySummary != null) {
                registerQuerySummary(method, querySummary);
                registered++;
            }
        }
        return registered;
    }

    private int addByExampleConsumerSummaries(JClass clazz) {
        int registered = 0;
        for (JMethod method : clazz.getDeclaredMethods()) {
            if (!method.getName().contains("ByExample")) {
                continue;
            }
            int exampleArgIndex = findExampleArgIndex(method);
            if (exampleArgIndex < 0) {
                continue;
            }
            if (method.getReturnType().equals(VoidType.VOID)) {
                registerQuerySummary(method,
                        QuerySummaryDetail.readCarrier(method, exampleArgIndex, exampleArgIndex));
            } else {
                registerQuerySummary(method, QuerySummaryDetail.readCarrier(
                        method, exampleArgIndex, exampleArgIndex, InvokeUtils.RESULT));
            }
            registered++;
        }
        return registered;
    }

    private int addMyBatisPlusWrapperSummaries(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            @Nullable JClass wrapperClass,
            MyBatisPlusWrapperKind wrapperKind) {
        if (wrapperClass == null) {
            return 0;
        }
        int registered = 0;
        for (JClass clazz : hierarchy.getAllSubclassesOf(wrapperClass)) {
            for (JMethod method : clazz.getDeclaredMethods()) {
                if (method.isStatic() || method.isNative()) {
                    continue;
                }
                QuerySummaryDetail summary = buildMyBatisPlusWrapperSummary(method, wrapperKind);
                if (summary != null) {
                    registerQuerySummary(method, summary);
                    registered++;
                }
            }
        }
        return registered;
    }

    private int addMyBatisPlusReadSummaries(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            @Nullable JClass queryWrapperClass,
            @Nullable JClass lambdaQueryWrapperClass) {
        if (queryWrapperClass == null && lambdaQueryWrapperClass == null) {
            return 0;
        }
        int registered = 0;
        for (JClass clazz : hierarchy.allClasses().toList()) {
            for (JMethod method : clazz.getDeclaredMethods()) {
                if (!looksLikeMyBatisPlusReadMethod(method.getName())) {
                    continue;
                }
                int wrapperArgIndex = findMyBatisPlusWrapperArgIndex(
                        hierarchy, method, queryWrapperClass, lambdaQueryWrapperClass);
                if (wrapperArgIndex < 0) {
                    continue;
                }
                if (method.getReturnType().equals(VoidType.VOID)) {
                    registerQuerySummary(method,
                            QuerySummaryDetail.readCarrier(method, wrapperArgIndex, wrapperArgIndex));
                } else {
                    registerQuerySummary(method, QuerySummaryDetail.readCarrier(
                            method, wrapperArgIndex, wrapperArgIndex, InvokeUtils.RESULT));
                }
                registered++;
            }
        }
        return registered;
    }

    private int addGridBinderQuerySummaries(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            @Nullable JClass queryWrapperClass,
            @Nullable JClass lambdaQueryWrapperClass) {
        if (queryWrapperClass == null && lambdaQueryWrapperClass == null) {
            return 0;
        }
        int registered = 0;
        for (JClass clazz : hierarchy.allClasses().toList()) {
            if (!looksLikeGridBinderClass(clazz)) {
                continue;
            }
            for (JMethod method : clazz.getDeclaredMethods()) {
                if (method.isStatic() || method.isNative()) {
                    continue;
                }
                QuerySummaryDetail summary = buildGridBinderQuerySummary(
                        hierarchy, method, queryWrapperClass, lambdaQueryWrapperClass);
                if (summary != null) {
                    registerQuerySummary(method, summary);
                    registered++;
                }
            }
        }
        return registered;
    }

    private boolean looksLikeExampleClass(JClass clazz) {
        return clazz.getName().endsWith("Example");
    }

    private boolean looksLikeCriteriaClass(JClass clazz) {
        return clazz.getName().endsWith("Criteria");
    }

    private boolean isCriteriaType(Type type) {
        return type instanceof ClassType classType
                && classType.getJClass().getName().endsWith("Criteria");
    }

    private boolean isExampleType(Type type) {
        return type instanceof ClassType classType
                && classType.getJClass().getName().endsWith("Example");
    }

    private boolean looksLikeMyBatisPlusReadMethod(String methodName) {
        return "selectOne".equals(methodName)
                || "selectCount".equals(methodName)
                || "selectList".equals(methodName)
                || "selectPage".equals(methodName)
                || "count".equals(methodName)
                || "any".equals(methodName)
                || "filter".equals(methodName)
                || "all".equals(methodName)
                || "query".equals(methodName)
                || "queryObjs".equals(methodName)
                || "queryPage".equals(methodName)
                || "getOne".equals(methodName)
                || "list".equals(methodName);
    }

    private boolean looksLikeGridBinderClass(JClass clazz) {
        String className = clazz.getName();
        return className.equals("GridBinder")
                || className.endsWith(".GridBinder")
                || className.endsWith("GridBinder");
    }

    private boolean looksLikeGridBinderReadMethod(String methodName) {
        return "query".equals(methodName)
                || "queryObjs".equals(methodName)
                || "queryPage".equals(methodName);
    }

    private int findMyBatisPlusWrapperArgIndex(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            JMethod method,
            @Nullable JClass queryWrapperClass,
            @Nullable JClass lambdaQueryWrapperClass) {
        for (int i = 0; i < method.getParamCount(); i++) {
            if (isMyBatisPlusWrapperType(
                    hierarchy, method.getParamType(i), queryWrapperClass, lambdaQueryWrapperClass)) {
                return i;
            }
        }
        return -1;
    }

    private boolean isMyBatisPlusWrapperType(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            Type type,
            @Nullable JClass queryWrapperClass,
            @Nullable JClass lambdaQueryWrapperClass) {
        if (!(type instanceof ClassType classType)) {
            return false;
        }
        JClass candidate = classType.getJClass();
        return isSameOrSubclass(hierarchy, queryWrapperClass, candidate)
                || isSameOrSubclass(hierarchy, lambdaQueryWrapperClass, candidate);
    }

    private boolean isSameOrSubclass(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            @Nullable JClass base,
            @Nullable JClass candidate) {
        return base != null
                && candidate != null
                && (base.equals(candidate) || hierarchy.isSubclass(base, candidate));
    }

    @Nullable
    private QuerySummaryDetail buildGridBinderQuerySummary(
            pascal.taie.language.classes.ClassHierarchy hierarchy,
            JMethod method,
            @Nullable JClass queryWrapperClass,
            @Nullable JClass lambdaQueryWrapperClass) {
        String methodName = method.getName();
        if ("setWrapper".equals(methodName)) {
            int wrapperArgIndex = findMyBatisPlusWrapperArgIndex(
                    hierarchy, method, queryWrapperClass, lambdaQueryWrapperClass);
            if (wrapperArgIndex >= 0) {
                return QuerySummaryDetail.attachArgument(method, wrapperArgIndex);
            }
        }
        if (looksLikeGridBinderReadMethod(methodName)
                && !method.getReturnType().equals(VoidType.VOID)) {
            return QuerySummaryDetail.readExecutor(
                    method, InvokeUtils.BASE, InvokeUtils.RESULT);
        }
        return null;
    }

    private java.util.List<Integer> extractCriteriaValueArgs(JMethod method) {
        if (method.getName().startsWith("and")
                && method.getParamCount() > 0
                && isCriteriaType(method.getReturnType())) {
            java.util.List<Integer> valueArgs = new java.util.ArrayList<>(method.getParamCount());
            for (int i = 0; i < method.getParamCount(); i++) {
                valueArgs.add(i);
            }
            return valueArgs;
        }
        if ("addCriterion".equals(method.getName())) {
            return switch (method.getParamCount()) {
                case 3 -> java.util.List.of(1);
                case 4 -> java.util.List.of(1, 2);
                default -> java.util.List.of();
            };
        }
        return java.util.List.of();
    }

    @Nullable
    private QuerySummaryDetail buildCriteriaValueSummary(JMethod method) {
        if (method.getName().startsWith("and")
                && method.getParamCount() > 0
                && looksLikeCriteriaClass(method.getDeclaringClass())
                && !method.getReturnType().equals(VoidType.VOID)) {
            QuerySlotKey slotKey = QuerySlotKey.derived(deriveCriteriaPropertyName(method.getName()));
            return QuerySummaryDetail.writeSlot(
                    method,
                    slotKey,
                    InvokeUtils.BASE,
                    extractCriteriaValueArgs(method).stream().mapToInt(Integer::intValue).toArray());
        }
        if ("addCriterion".equals(method.getName())) {
            return switch (method.getParamCount()) {
                case 3 -> QuerySummaryDetail.writeSlot(
                        method, QuerySlotKey.stringArg(2), InvokeUtils.BASE, 1);
                case 4 -> QuerySummaryDetail.writeSlot(
                        method, QuerySlotKey.stringArg(3), InvokeUtils.BASE, 1, 2);
                default -> null;
            };
        }
        if ("clear".equals(method.getName()) && method.getParamCount() == 0) {
            return QuerySummaryDetail.resetCarrier(method, InvokeUtils.BASE);
        }
        return null;
    }

    @Nullable
    private QuerySummaryDetail buildMyBatisPlusWrapperSummary(
            JMethod method, MyBatisPlusWrapperKind wrapperKind) {
        String methodName = method.getName();
        if ("clear".equals(methodName) && method.getParamCount() == 0) {
            return QuerySummaryDetail.resetCarrier(method, InvokeUtils.BASE);
        }
        int startArg = hasLeadingConditionFlag(method) ? 1 : 0;
        if ("last".equals(methodName) && method.getParamCount() > startArg) {
            return QuerySummaryDetail.writeMeta(
                    method, "last", InvokeUtils.BASE, method.getParamCount() - 1);
        }
        if (("orderByAsc".equals(methodName) || "orderByDesc".equals(methodName))
                && method.getParamCount() > startArg) {
            int[] metaArgs = collectMethodArgIndexes(startArg, method.getParamCount());
            return QuerySummaryDetail.writeMeta(
                    method, methodName, InvokeUtils.BASE, metaArgs);
        }
        if (!isMyBatisPlusWriteMethod(methodName) || method.getParamCount() < startArg + 2) {
            return null;
        }
        QuerySlotKey slotKey = wrapperKind == MyBatisPlusWrapperKind.LAMBDA
                ? QuerySlotKey.lambdaArg(startArg)
                : QuerySlotKey.stringArg(startArg);
        return QuerySummaryDetail.writeSlot(
                method, slotKey, InvokeUtils.BASE, startArg + 1);
    }

    private boolean isMyBatisPlusWriteMethod(String methodName) {
        return "eq".equals(methodName)
                || "ne".equals(methodName)
                || "gt".equals(methodName)
                || "ge".equals(methodName)
                || "lt".equals(methodName)
                || "le".equals(methodName)
                || "like".equals(methodName)
                || "notLike".equals(methodName)
                || "likeLeft".equals(methodName)
                || "likeRight".equals(methodName)
                || "in".equals(methodName)
                || "notIn".equals(methodName);
    }

    private boolean hasLeadingConditionFlag(JMethod method) {
        return method.getParamCount() > 0 && isBooleanType(method.getParamType(0));
    }

    private boolean isBooleanType(Type type) {
        String typeName = type.getName();
        return "boolean".equals(typeName) || "java.lang.Boolean".equals(typeName);
    }

    private int[] collectMethodArgIndexes(int startInclusive, int endExclusive) {
        int[] indexes = new int[Math.max(0, endExclusive - startInclusive)];
        for (int i = startInclusive; i < endExclusive; i++) {
            indexes[i - startInclusive] = i;
        }
        return indexes;
    }

    private enum MyBatisPlusWrapperKind {
        STRING,
        LAMBDA
    }

    private String deriveCriteriaPropertyName(String methodName) {
        String property = methodName.substring(3);
        String[] suffixes = {
                "EqualTo", "NotEqualTo", "GreaterThan", "GreaterThanOrEqualTo",
                "LessThan", "LessThanOrEqualTo", "Like", "NotLike",
                "In", "NotIn", "Between", "NotBetween", "IsNull", "IsNotNull"
        };
        for (String suffix : suffixes) {
            if (property.endsWith(suffix) && property.length() > suffix.length()) {
                property = property.substring(0, property.length() - suffix.length());
                break;
            }
        }
        return property.isEmpty()
                ? methodName
                : Character.toLowerCase(property.charAt(0)) + property.substring(1);
    }

    private int findExampleArgIndex(JMethod method) {
        for (int i = 0; i < method.getParamCount(); i++) {
            if (isExampleType(method.getParamType(i))) {
                return i;
            }
        }
        return -1;
    }

    private void registerCriteriaSummary(JMethod method,
                                         CriteriaSummaryDetail.Kind kind,
                                         int... argIndexes) {
        methodToCriteriaSummaries.put(method.getRef(),
                CriteriaSummaryDetail.of(method, kind, argIndexes));
        logger.info("Registered criteria summary: {} ({})",
                method.getSignature(), kind);
    }

    private void registerQuerySummary(JMethod method, QuerySummaryDetail detail) {
        methodToQuerySummaries.put(method.getRef(), detail);
        logger.info("Registered query summary: {} ({})",
                method.getSignature(), detail.kind());
    }

    private void addJdkUtilitySummaries(pascal.taie.language.classes.ClassHierarchy hierarchy,
                            AccessPathParser parser,
                            java.util.List<SummaryDetail> summaries) {
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.Collections: java.util.List unmodifiableList(java.util.List)>",
                "0", "result");
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.Collections: java.util.Map unmodifiableMap(java.util.Map)>",
                "0", "result");
    }

    private int addJdkContainerSummary(pascal.taie.language.classes.ClassHierarchy hierarchy,
                                       String methodSignature,
                                       ContainerSummaryDetail.Kind kind) {
        JMethod method = hierarchy.getMethod(methodSignature);
        if (method == null) {
            logger.debug("JDK container summary: method not found, skipping: {}", methodSignature);
            return 0;
        }
        methodToContainerSummaries.put(method.getRef(), new ContainerSummaryDetail(method, kind));
        logger.info("Registered JDK container summary: {} ({})", methodSignature, kind);
        return 1;
    }

    /**
     * 添加单条 JDK 方法的 summary 规则。
     * 如果方法在当前类层次结构中不存在（如 JDK 版本不同），则跳过。
     */
    private void addJdkSummary(pascal.taie.language.classes.ClassHierarchy hierarchy,
                               AccessPathParser parser,
                               java.util.List<SummaryDetail> summaries,
                               String methodSignature,
                               String fromStr, String toStr) {
        JMethod method = hierarchy.getMethod(methodSignature);
        if (method == null) {
            logger.debug("JDK summary: method not found, skipping: {}", methodSignature);
            return;
        }
        addJdkSummary(parser, summaries, method, fromStr, toStr);
    }

    private void addJdkSummary(AccessPathParser parser,
                               java.util.List<SummaryDetail> summaries,
                               JMethod method,
                               String fromStr, String toStr) {
        String methodSignature = method.getSignature();
        AccessPath source = parser.parse(method, fromStr);
        AccessPath target = parser.parse(method, toStr);
        if (source != null && target != null) {
            summaries.add(SummaryDetail.of(method, fromStr, toStr, source, target));
            logger.info("Registered JDK summary: {} ({} → {})", methodSignature, fromStr, toStr);
        } else {
            logger.warn("JDK summary: failed to parse AccessPath for {}: {} → {}",
                    methodSignature, fromStr, toStr);
        }
    }

    // ==================== 查询接口：获取被摘要的方法 ====================

    /**
     * 获取所有有摘要规则的方法集合。
     * 用于在 SummarySolver.initialize() 中将这些方法注册为 ignored，
     * 阻止 PTA 进入其方法体分析（但保留 call edge 用于触发 TransferHandler）。
     */
    public Set<JMethod> getSummarizedMethods() {
        Set<JMethod> summarizedMethods = config.summaryDetails().stream()
                .map(SummaryDetail::method)
                .filter(Objects::nonNull)
                .collect(Collectors.toSet());
        methodToContainerSummaries.values().stream()
                .map(ContainerSummaryDetail::method)
                .filter(Objects::nonNull)
                .forEach(summarizedMethods::add);
        // Query / criteria builder summaries are observer-style helpers. Their
        // bodies must still be analyzed so that allocations and returns remain visible.
        return summarizedMethods;
    }

    private void debugCriteriaEvent(@Nullable Invoke callSite, Supplier<String> messageSupplier) {
        if (!shouldDebugCriteria(callSite)) {
            return;
        }
        logger.info("[criteria-debug] {}", messageSupplier.get());
    }

    private boolean shouldDebugCriteria(@Nullable Invoke callSite) {
        if (callSite == null) {
            return false;
        }
        JMethod container = callSite.getContainer();
        if (!SummaryDebugConfig.matchesMethod(container)) {
            return false;
        }
        String calleeName = callSite.getMethodRef().getName();
        return "createCriteria".equals(calleeName)
                || "or".equals(calleeName)
                || calleeName.startsWith("and")
                || calleeName.contains("ByExample");
    }

    private boolean shouldDebugExample(CSObj example) {
        return exampleToLoadSites.get(example).stream()
                .map(ExampleLoadSite::exampleVar)
                .map(Var::getMethod)
                .map(JMethod::getSignature)
                .anyMatch(SummaryDebugConfig::matchesSignature);
    }

    private String describePointsToSet(PointsToSet pts) {
        if (pts == null) {
            return "null";
        }
        java.util.List<String> samples = new java.util.ArrayList<>();
        int count = 0;
        for (CSObj obj : pts) {
            count++;
            if (samples.size() < 4) {
                samples.add(describeObj(obj));
            }
        }
        return "size=" + count + " samples=" + samples;
    }

    private String describeObjCollection(Collection<CSObj> objs) {
        java.util.List<String> samples = new java.util.ArrayList<>();
        int count = 0;
        for (CSObj obj : objs) {
            count++;
            if (samples.size() < 4) {
                samples.add(describeObj(obj));
            }
        }
        return "size=" + count + " samples=" + samples;
    }

    private String describeObj(CSObj obj) {
        return obj == null ? "null" : obj.getObject().toString();
    }

    private boolean isExampleObj(CSObj obj) {
        return obj != null && isExampleType(obj.getObject().getType());
    }

    private boolean isCriteriaObj(CSObj obj) {
        return obj != null && isCriteriaType(obj.getObject().getType());
    }

    // ==================== 统计与调试 ====================

    /**
     * 获取统计信息
     */
    public String getStatistics() {
        return String.format(
                "[SummaryManager] Statistics:\n" +
                        "  - Summary rules: %d\n" +
                        "  - Summarized methods: %d\n" +
                        "  - Active call mappings: %d\n" +
                        "  - Tracked summary callsites: %d\n" +
                        "  - Query read sites: %d\n" +
                        "  - Summary applications: %d\n" +
                        "  - Summary PFG edge requests: %d\n" +
                        "  - Summary no-op fast paths: %d\n" +
                        "  - Summary snapshot applies: %d\n" +
                        "  - Query writes / reads / attaches: %d / %d / %d\n" +
                        "  - Legacy criteria fallback count: %d\n" +
                        "  - Global reapply fallback count: %d",
                config.summaryDetails().size()
                        + methodToContainerSummaries.size()
                        + methodToCriteriaSummaries.size()
                        + methodToQuerySummaries.size(),
                methodToSummaries.keySet().size()
                        + methodToContainerSummaries.keySet().size()
                        + methodToCriteriaSummaries.keySet().size()
                        + methodToQuerySummaries.keySet().size(),
                argToActiveCalls.size(),
                trackedSummaryCallSites.size(),
                trackedQueryReadSites.size(),
                summaryAppliedCount,
                summaryPfgEdgeRequestCount,
                summaryNoopFastPathCount,
                summarySnapshotApplyCount,
                queryWriteCount,
                queryReadCount,
                queryAttachCount,
                legacyCriteriaFallbackCount,
                globalReapplyFallbackCount
        );
    }

    public long getSummaryAppliedCount() {
        return summaryAppliedCount;
    }

    public JdkSummaryCatalogStats getJdkSummaryCatalogStats() {
        return jdkSummaryCatalogStats;
    }

    public Set<String> getJdkSummaryCatalogMethodSignatures() {
        return jdkSummaryCatalogMethodSignatures;
    }

    public List<JdkNoOpSummary> getJdkNoOpSummaries() {
        return jdkNoOpSummaries;
    }

    /**
     * 清理（用于分析结束后）
     */
    public void clear() {
        argToActiveCalls.clear();
        iteratorVarToLoadSites.clear();
        iteratorVarToContainers.clear();
        containerToIteratorLoadSites.clear();
        exampleToLoadSites.clear();
        carrierToQueryReadSites.clear();
        executorToQueryReadSites.clear();
        trackedQueryReadSites.clear();
        dirtyQueryCarriers.clear();
        dirtyQueryExecutors.clear();
        criteriaVarToExamples.clear();
        criteriaVarAliasSources.clear();
        criteriaVarAliasTargets.clear();
        deferredCriteriaVarValues.clear();
        querySummaryStore.clear();
        queryWriteCount = 0;
        queryReadCount = 0;
        queryAttachCount = 0;
        summaryAppliedCount = 0;
        legacyCriteriaFallbackCount = 0;
        globalReapplyFallbackCount = 0;
        clearSummaryLookupCaches();
        summaryCallSites.clear();
        trackedSummaryCallSites.clear();
    }
}
