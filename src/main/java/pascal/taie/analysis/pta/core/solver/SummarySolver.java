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

package pascal.taie.analysis.pta.core.solver;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.profile.PtaHeavyMethodProfiler;
import pascal.taie.analysis.pta.core.solver.profile.PtaPollutionProfiler;
import pascal.taie.analysis.pta.core.solver.profile.PtaSummaryFrontierProfiler;
import pascal.taie.analysis.pta.core.solver.summary.JdkBoundaryClassifier;
import pascal.taie.analysis.pta.core.solver.summary.SummaryManager;
import pascal.taie.analysis.pta.core.solver.summary.YamlSummaryConfigProvider;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.taint.TaintProvenanceDebug;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.AssignLiteral;
import pascal.taie.ir.stmt.Cast;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;



import java.util.*;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.function.Predicate;
import java.util.regex.Matcher;

import static pascal.taie.language.classes.Signatures.FINALIZE;
import static pascal.taie.language.classes.Signatures.FINALIZER_REGISTER;

public class SummarySolver implements Solver {

    private static final Logger logger = LogManager.getLogger(SummarySolver.class);

    private static final ObjectMapper JSON = new ObjectMapper();

    public static final String IGNORED_METHOD_SIGNATURES_KEY =
            SummarySolver.class.getName() + ".ignoredMethodSignatures";

    public static final String IGNORED_METHOD_REASONS_KEY =
            SummarySolver.class.getName() + ".ignoredMethodReasons";

    public static final String SUMMARY_APPLIED_COUNT_KEY =
            SummarySolver.class.getName() + ".summaryAppliedCount";

    public static final String JDK_SUMMARY_CATALOG_STATS_KEY =
            SummarySolver.class.getName() + ".jdkSummaryCatalogStats";

    public static final String JDK_SUMMARY_CATALOG_METHOD_SIGNATURES_KEY =
            SummarySolver.class.getName() + ".jdkSummaryCatalogMethodSignatures";

    public static final String PTA_PROFILING_ARTIFACTS_KEY =
            SummarySolver.class.getName() + ".ptaProfilingArtifacts";

    public static final String PTA_CLASS_PROFILE_PATH_KEY =
            SummarySolver.class.getName() + ".ptaClassProfilePath";

    public static final String PTA_BOUNDARY_DELTA_PATH_KEY =
            SummarySolver.class.getName() + ".ptaBoundaryDeltaPath";

    public static final String PTA_SHARED_HUBS_PATH_KEY =
            SummarySolver.class.getName() + ".ptaSharedHubsPath";

    public static final String PTA_CULPRIT_RANKING_PATH_KEY =
            SummarySolver.class.getName() + ".ptaCulpritRankingPath";

    public static final String PTA_APP_FRONTIER_METHODS_PATH_KEY =
            SummarySolver.class.getName() + ".ptaAppFrontierMethodsPath";

    public static final String PTA_APP_ORIGIN_HUBS_PATH_KEY =
            SummarySolver.class.getName() + ".ptaAppOriginHubsPath";

    public static final String PTA_FRONTIER_SLICES_PATH_KEY =
            SummarySolver.class.getName() + ".ptaFrontierSlicesPath";

    public static final String PTA_METHOD_HUB_ATTRIBUTION_PATH_KEY =
            SummarySolver.class.getName() + ".ptaMethodHubAttributionPath";

    public static final String PTA_SUMMARY_FRONTIER_RANKING_PATH_KEY =
            SummarySolver.class.getName() + ".ptaSummaryFrontierRankingPath";

    public static final String PTA_FRONTIER_HUB_COVERAGE_PATH_KEY =
            SummarySolver.class.getName() + ".ptaFrontierHubCoveragePath";

    public static final String PTA_CI_METHOD_PROFILE_PATH_KEY =
            SummarySolver.class.getName() + ".ptaCiMethodProfilePath";

    public static final String PTA_METHOD_CG_PTA_METRICS_PATH_KEY =
            SummarySolver.class.getName() + ".ptaMethodCgPtaMetricsPath";

    public static final String PTA_HEAVY_POLLUTING_METHODS_PATH_KEY =
            SummarySolver.class.getName() + ".ptaHeavyPollutingMethodsPath";

    public static final String PTA_HEAVY_POLLUTING_METHODS_MARKDOWN_PATH_KEY =
            SummarySolver.class.getName()
                    + ".ptaHeavyPollutingMethodsMarkdownPath";

    public static final String PTA_HEAVY_METHOD_CALLGRAPH_PATH_KEY =
            SummarySolver.class.getName() + ".ptaHeavyMethodCallgraphPath";

    public static final String PTA_TOP_POLLUTING_METHODS_PATH_KEY =
            SummarySolver.class.getName() + ".ptaTopPollutingMethodsPath";

    /**
     * Descriptor for array objects created implicitly by multiarray instruction.
     */
    private static final Descriptor MULTI_ARRAY_DESC = () -> "MultiArrayObj";

    /**
     * Number that represents unlimited elapsed time.
     */
    private static final long UNLIMITED = -1;

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private final CSManager csManager;

    private final ClassHierarchy hierarchy;

    private final TypeSystem typeSystem;

    private final PointsToSetFactory ptsFactory;

    private final PropagateTypes propTypes;

    /**
     * Whether only analyzes application code.
     */
    private final boolean onlyApp;

    private final boolean jdkSummaryOnly;

    private final JdkBoundaryClassifier jdkBoundaryClassifier;

    private final Set<String> summaryFrontierOnlyMethods;

    /**
     * Time limit for pointer analysis (in seconds).
     */
    private final long timeLimit;

    private TimeLimiter timeLimiter;

    /**
     * Whether the analysis has reached time limit.
     */
    private volatile boolean isTimeout;

    private Plugin plugin;

    private WorkList workList;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private Set<JMethod> reachableMethods;

    /**
     * Set of classes that have been initialized.
     */
    private Set<JClass> initializedClasses;

    /**
     * Set of methods to be intercepted and ignored.
     */
    private Set<JMethod> ignoredMethods;

    private Map<JMethod, IgnoredReason> ignoredMethodReasons;

    private StmtProcessor stmtProcessor;

    private PointerAnalysisResult result;

    // //code summary: 摘要管理器 - 用于注入式方法摘要
    private SummaryManager summaryManager;

    private final boolean summaryGlobalReapplyFallback;

    private final boolean summaryNonQueryReapply;

    private long queryApplySummaryNanos;

    private long queryReapplyNanos;

    private long queryFallbackScanNanos;

    private PtaPollutionProfiler pollutionProfiler;

    private PtaSummaryFrontierProfiler summaryFrontierProfiler;

    private PtaHeavyMethodProfiler heavyMethodProfiler;

    @SuppressWarnings("unchecked")
    public SummarySolver(AnalysisOptions options, HeapModel heapModel,
                         ContextSelector contextSelector, CSManager csManager) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.csManager = csManager;
        hierarchy = World.get().getClassHierarchy();
        typeSystem = World.get().getTypeSystem();
        ptsFactory = new PointsToSetFactory(csManager.getObjectIndexer());
        propTypes = new PropagateTypes(
                (List<String>) options.get("propagate-types"),
                typeSystem);
        onlyApp = options.getBoolean("only-app");
        jdkSummaryOnly = "summary-only".equals(options.getString("jdk-analysis-mode"));
        jdkBoundaryClassifier = new JdkBoundaryClassifier(
                (List<String>) options.get("jdk-boundary-extra-includes"),
                (List<String>) options.get("jdk-boundary-extra-excludes"));
        summaryFrontierOnlyMethods = loadSummaryFrontierOnlyMethods(
                options.has("pta-summary-frontier-summary-only-methods-file")
                        ? options.getString("pta-summary-frontier-summary-only-methods-file")
                        : null);
        timeLimit = options.getInt("time-limit");
        summaryGlobalReapplyFallback = options.has("summary-global-reapply-fallback")
                && options.getBoolean("summary-global-reapply-fallback");
        summaryNonQueryReapply = !options.has("summary-non-query-reapply")
                || options.getBoolean("summary-non-query-reapply");
    }

    @Override
    public AnalysisOptions getOptions() {
        return options;
    }

    @Override
    public HeapModel getHeapModel() {
        return heapModel;
    }

    @Override
    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    @Override
    public CSManager getCSManager() {
        return csManager;
    }

    @Override
    public ClassHierarchy getHierarchy() {
        return hierarchy;
    }

    @Override
    public TypeSystem getTypeSystem() {
        return typeSystem;
    }

    @Override
    public CSCallGraph getCallGraph() {
        return callGraph;
    }

    @Override
    public PointsToSet getPointsToSetOf(Pointer pointer) {
        PointsToSet pts = pointer.getPointsToSet();
        if (pts == null) {
            pts = ptsFactory.make();
            pointer.setPointsToSet(pts);
        }
        return pts;
    }

    @Override
    public PointsToSet makePointsToSet() {
        return ptsFactory.make();
    }

    @Override
    public void setPlugin(Plugin plugin) {
        this.plugin = plugin;
    }

    // ---------- solver logic starts ----------

    /**
     * Runs pointer analysis algorithm.
     */
    @Override
    public void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph(csManager);
        workList = new WorkList();
        reachableMethods = Sets.newSet();
        initializedClasses = Sets.newSet();
        ignoredMethods = Sets.newSet();
        ignoredMethodReasons = Maps.newMap();
        stmtProcessor = new StmtProcessor();
        //code summary: 初始化摘要管理器
        summaryManager = new SummaryManager(this);
        pollutionProfiler = new PtaPollutionProfiler(options, jdkBoundaryClassifier);
        summaryFrontierProfiler =
                new PtaSummaryFrontierProfiler(options, jdkBoundaryClassifier);
        heavyMethodProfiler =
                new PtaHeavyMethodProfiler(options, jdkBoundaryClassifier);
        //code summary: 加载硬编码的测试摘要规则（包括 getter/setter 和 JDK 容器方法）
        summaryManager.initHardcodedSummaries();
        loadYamlSummaryConfig();
        // code summary: 将所有有摘要的方法注册为 ignored
        // 效果：processCallEdge 中 isIgnored(method) 返回 true 时：
        //   - addCSMethod() 跳过方法体分析（不进入 JDK 方法内部）
        //   - 跳过参数传递和返回值的 PFG 边创建（消除指针流双重传播）
        //   - 但 plugin.onNewCallEdge(edge) 仍然执行（在 isIgnored 判断之外）
        //     → TransferHandler 的 taint 传播规则不受影响
        Set<JMethod> summarizedMethods = summaryManager.getSummarizedMethods();
        // 对所有带摘要的方法统一走 ignored 机制：
        //   - 非应用方法（如 JDK）用摘要替代方法体分析
        //   - 应用类 getter/setter 也用摘要替代方法体分析，避免“方法体分析 + 摘要传播”双重开销
        summarizedMethods.forEach(this::addIgnoredMethod);
        long appSummarizedCount = summarizedMethods.stream()
                .filter(JMethod::isApplication)
                .count();
        logger.info("[code summary] Registered {} summarized methods as ignored (app: {}, non-app: {})",
                summarizedMethods.size(), appSummarizedCount, summarizedMethods.size() - appSummarizedCount);
        isTimeout = false;
        if (timeLimit != UNLIMITED) {
            timeLimiter = new TimeLimiter(timeLimit);
            timeLimiter.countDown();
        }
        plugin.onStart();
    }

    private void loadYamlSummaryConfig() {
        String summaryConfig = options.getString("summary-config");
        if (summaryConfig == null || summaryConfig.isBlank()) {
            return;
        }
        var provider = new YamlSummaryConfigProvider(hierarchy, typeSystem);
        provider.setPath(summaryConfig);
        summaryManager.mergeConfig(provider.get());
    }

    private class TimeLimiter {

        private static final long MILLIS_FACTOR = 1000;

        private final Thread thread;

        /**
         * @param seconds the time limit.
         */
        private TimeLimiter(long seconds) {
            thread = new Thread(() -> {
                try {
                    Thread.sleep(seconds * MILLIS_FACTOR);
                } catch (InterruptedException ignored) {
                }
                isTimeout = true;
            });
        }

        /**
         * Starts count down.
         */
        private void countDown() {
            thread.start();
        }

        /**
         * Stops count down.
         */
        private void stop() {
            thread.interrupt();
        }
    }

    /**
     * Processes work list entries until the work list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty() && !isTimeout) {
            // phase starts
            while (!workList.isEmpty() && !isTimeout) {
                WorkList.Entry entry = workList.pollEntry();
                if (entry instanceof WorkList.PointerEntry pEntry) {
                    Pointer p = pEntry.pointer();
                    PointsToSet pts = pEntry.pointsToSet();

                    PointsToSet diff = propagate(p, pts);
                    if (!diff.isEmpty() && p instanceof CSVar v) {

                        processInstanceStore(v, diff);
                        processInstanceLoad(v, diff);
                        processArrayStore(v, diff);
                        processArrayLoad(v, diff);

                        // codesummary
                        processSummary(v, diff);

                        plugin.onNewPointsToSet(v, diff);
                    }
                } else if (entry instanceof WorkList.CallEdgeEntry eEntry) {
                    processCallEdge(eEntry.edge());
                }
            }
            plugin.onPhaseFinish();

            if (workList.isEmpty()) {
                long queryReapplyStart = System.nanoTime();
                summaryManager.reapplyDirtyQueryReadSites();
                summaryManager.reapplyRegisteredQuerySummaries();
                queryReapplyNanos += System.nanoTime() - queryReapplyStart;

                if (summaryNonQueryReapply) {
                    summaryManager.reapplyRegisteredNonQuerySummaries();
                }

                if (summaryGlobalReapplyFallback) {
                    long fallbackStart = System.nanoTime();
                    summaryManager.reapplyRegisteredSummaries();
                    queryFallbackScanNanos += System.nanoTime() - fallbackStart;
                }
            }
        }

        if (!workList.isEmpty() && isTimeout) {
            logger.warn("Pointer analysis stops early as it reaches time limit ({} seconds)," +
                    " and the result may be unsound!", timeLimit);
        } else if (timeLimiter != null) { // finish normally but time limiter is still running
            timeLimiter.stop();
        }
        plugin.onFinish();
    }



    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        logger.trace("Propagate {} to {}", pointsToSet, pointer);
        Set<Predicate<CSObj>> filters = pointer.getFilters();
        if (!filters.isEmpty()) {
            // apply filters (of the pointer) on pointsToSet
            pointsToSet = pointsToSet.objects()
                    .filter(o -> filters.stream().allMatch(f -> f.test(o)))
                    .collect(ptsFactory::make, PointsToSet::addObject, PointsToSet::addAll);
        }

        PointsToSet diff = getPointsToSetOf(pointer).addAllDiff(pointsToSet);
        if (!diff.isEmpty()) {
            pollutionProfiler.recordPropagate(pointer, diff);
            summaryFrontierProfiler.recordPropagate(pointer, diff);
            heavyMethodProfiler.recordPropagate(pointer, diff);
            TaintProvenanceDebug.logPropagate("SummarySolver", pointer, diff);
            pointerFlowGraph.getOutEdgesOf(pointer).forEach(edge -> {
                Pointer target = edge.target();
                edge.getTransfers().forEach(transfer -> {
                    PointsToSet targetSet = transfer.apply(edge, diff);
                    TaintProvenanceDebug.logEdge("SummarySolver", edge, diff, targetSet);
                    addPointsTo(target, targetSet);
                });
            });


        }
        return diff;
    }

    /**
     * Processes instance stores when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceStore(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (StoreField store : var.getStoreFields()) {
            Var fromVar = store.getRValue();
            if (propTypes.isAllowed(fromVar)) {
                CSVar from = csManager.getCSVar(context, fromVar);
                //javaparser debug: resolveNullable 避免解析失败
                JField field = store.getFieldRef().resolveNullable();
                if (field == null) continue;
                pts.forEach(baseObj -> {
                    if (baseObj.getObject().isFunctional()) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        addPFGEdge(from, instField, FlowKind.INSTANCE_STORE);
                    }
                });
            }
        }
    }


    /**
     * Processes instance loads when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceLoad(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (LoadField load : var.getLoadFields()) {
            Var toVar = load.getLValue();
            if (propTypes.isAllowed(toVar)) {
                CSVar to = csManager.getCSVar(context, toVar);
                //javaparser debug: resolveNullable 避免解析失败
                JField field = load.getFieldRef().resolveNullable();
                if (field == null) continue;
                pts.forEach(baseObj -> {
                    if (baseObj.getObject().isFunctional()) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        addPFGEdge(instField, to, FlowKind.INSTANCE_LOAD);
                    }
                });
            }
        }
    }

    /**
     * Processes array stores when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     */
    private void processArrayStore(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (StoreArray store : var.getStoreArrays()) {
            Var rvalue = store.getRValue();
            if (propTypes.isAllowed(rvalue)) {
                CSVar from = csManager.getCSVar(context, rvalue);
                pts.forEach(array -> {
                    if (array.getObject().isFunctional()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                        // we need type guard for array stores as Java arrays
                        // are covariant
                        try {
                            addPFGEdge(new PointerFlowEdge(FlowKind.ARRAY_STORE, from, arrayIndex), arrayIndex.getType());
                        } catch (Exception e) {
                            addPFGEdge(from, arrayIndex, FlowKind.ARRAY_STORE);
                        }

                    }
                });
            }
        }
    }

    /**
     * Processes array loads when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     */
    private void processArrayLoad(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (LoadArray load : var.getLoadArrays()) {
            Var lvalue = load.getLValue();
            if (propTypes.isAllowed(lvalue)) {
                CSVar to = csManager.getCSVar(context, lvalue);
                pts.forEach(array -> {
                    if (array.getObject().isFunctional()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                        addPFGEdge(arrayIndex, to, FlowKind.ARRAY_LOAD);
                    }
                });
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv the receiver variable
     * @param pts  set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, PointsToSet pts) {
        Context context = recv.getContext();
        Var var = recv.getVar();
        for (Invoke callSite : var.getInvokes()) {
            pts.forEach(recvObj -> {
                // resolve callee
                JMethod callee = CallGraphs.resolveCallee(
                        recvObj.getObject().getType(), callSite);
                if (callee != null) {
                    // select context
                    CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                    Context calleeContext = contextSelector.selectContext(
                            csCallSite, recvObj, callee);
                    // build call edge
                    CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                    addCallEdge(new Edge<>(CallGraphs.getCallKind(callSite),
                            csCallSite, csCallee));
                    // pass receiver object to *this* variable
                    if (!isIgnored(callee)) {
                        CSVar receiverVar = csManager.getCSVar(context, var);
                        CSVar calleeThis = csManager.getCSVar(
                                calleeContext, callee.getIR().getThis());
                        summaryFrontierProfiler.recordReceiverOrigin(
                                callSite, callee, receiverVar, calleeThis);
                        addVarPointsTo(calleeContext, callee.getIR().getThis(),
                                recvObj);
                    }
                } else {
                    plugin.onUnresolvedCall(recvObj, context, callSite);
                }
            });
        }
    }

    private void processSummary(CSVar recv, PointsToSet pts) {
        Context context = recv.getContext();
        Var var = recv.getVar();
        if (shouldDebugSummaryProbe(var)) {
            logger.info("[summary-probe] enter processSummary recvVar={} invokes={}",
                    var, describeInvokeTargets(var));
        }
        for (Invoke callSite : var.getInvokes()) {
            pts.forEach(recvObj -> {
                CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                debugSummaryProbe(var, callSite, recvObj, null, "before-resolve");
                // resolve callee
                JMethod callee = CallGraphs.resolveCallee(
                        recvObj.getObject().getType(), callSite);
                debugSummaryProbe(var, callSite, recvObj, callee, "after-resolve");
                MethodRef summaryMethodRef = callee != null
                        ? callee.getRef()
                        : callSite.getMethodRef();
                if (summaryManager.hasSummary(summaryMethodRef)) {
                    boolean isQuerySummary = summaryManager.hasQuerySummary(summaryMethodRef);
                    long queryApplyStart = isQuerySummary ? System.nanoTime() : 0L;
                    boolean applied = summaryManager.applySummary(
                            csCallSite, summaryMethodRef, context);
                    if (isQuerySummary) {
                        queryApplySummaryNanos += System.nanoTime() - queryApplyStart;
                    }
                    if (applied) {
                        if (callee != null) {
                            Context calleeContext = contextSelector.selectContext(
                                    csCallSite, recvObj, callee);
                            // code summary: 摘要已处理指针传播，但仍需创建 call edge
                            // 原因：TransferHandler.onNewCallEdge() 依赖 call edge 触发
                            //       taint transfer 规则。如果不创建 call edge，taint 传播
                            //       将完全失效。
                            // 流程：addCallEdge → worklist → processCallEdge:
                            //   1. callGraph.addEdge(edge) → call graph 边保留 ✓
                            //   2. addCSMethod → isIgnored → 跳过方法体分析 ✓
                            //   3. isIgnored → 跳过参数/返回 PFG 边 ✓
                            //   4. plugin.onNewCallEdge(edge) → TransferHandler 触发 ✓
                            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                            addCallEdge(new Edge<>(CallGraphs.getCallKind(callSite),
                                    csCallSite, csCallee));
                            if (!isIgnored(callee)) {
                                // Criteria-like summaries still rely on the callee body
                                // to expose allocations/returns, so preserve receiver flow.
                                CSVar receiverVar = csManager.getCSVar(context, var);
                                CSVar calleeThis = csManager.getCSVar(
                                        calleeContext, callee.getIR().getThis());
                                summaryFrontierProfiler.recordReceiverOrigin(
                                        callSite, callee, receiverVar, calleeThis);
                                addVarPointsTo(calleeContext, callee.getIR().getThis(),
                                        recvObj);
                            }
                        }
                        return;
                    }
                }
                if (callee != null) {
                    // select context
                    Context calleeContext = contextSelector.selectContext(
                            csCallSite, recvObj, callee);

                    // build call edge
                    CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                    addCallEdge(new Edge<>(CallGraphs.getCallKind(callSite),
                            csCallSite, csCallee));
                    // pass receiver object to *this* variable
                    if (!isIgnored(callee)) {
                        CSVar receiverVar = csManager.getCSVar(context, var);
                        CSVar calleeThis = csManager.getCSVar(
                                calleeContext, callee.getIR().getThis());
                        summaryFrontierProfiler.recordReceiverOrigin(
                                callSite, callee, receiverVar, calleeThis);
                        addVarPointsTo(calleeContext, callee.getIR().getThis(),
                                recvObj);
                    }
                } else {
                    plugin.onUnresolvedCall(recvObj, context, callSite);
                }
            });
        }


    }

    private void processCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (callGraph.addEdge(edge)) {
            // process new call edge
            CSMethod csCallee = edge.getCallee();
            addCSMethod(csCallee);
            CSCallSite csCallSite = edge.getCallSite();
            Context callerCtx = csCallSite.getContext();
            Invoke callSite = csCallSite.getCallSite();
            JMethod callee = csCallee.getMethod();
            TaintProvenanceDebug.logCallEdge("SummarySolver", callSite, callee, "process");
            pollutionProfiler.recordCallEdge(edge,
                    receiverPointsToSize(callerCtx, callSite),
                    argumentPointsToTotal(callerCtx, callSite),
                    callSite != null && callSite.getResult() != null);
            summaryFrontierProfiler.recordCallEdge(edge);
            heavyMethodProfiler.recordCallEdge(edge);
            if (edge.getKind() != CallKind.OTHER
                    && callSite != null
                    && callSite.isStatic()
                    && summaryManager.hasSummary(callee.getRef())) {
                boolean isQuerySummary = summaryManager.hasQuerySummary(callee.getRef());
                long queryApplyStart = isQuerySummary ? System.nanoTime() : 0L;
                summaryManager.applySummary(csCallSite, callee.getRef(), callerCtx);
                if (isQuerySummary) {
                    queryApplySummaryNanos += System.nanoTime() - queryApplyStart;
                }
            }
            if (edge.getKind() != CallKind.OTHER
                    && !isIgnored(callee)) {
                Context calleeCtx = csCallee.getContext();
                InvokeExp invokeExp = callSite.getInvokeExp();
                // pass arguments to parameters
                // 检查参数数量是否匹配，避免 IndexOutOfBoundsException
                int argCount = invokeExp.getArgCount();
                int paramCount = callee.getIR().getParams().size();
                if (argCount != paramCount) {
                    // 参数数量不匹配，可能是由于方法解析错误（常见于 phantom 方法）
                    // 记录警告并跳过参数传递，避免崩溃
                    logger.warn("[processCallEdge] 参数数量不匹配！调用有 {} 个参数，但目标方法 {} 有 {} 个参数",
                            argCount, callee.getSignature(), paramCount);
                    logger.warn("  调用点: {} @ {}", invokeExp, callSite);
                    logger.warn("  → 跳过参数传递以避免 IndexOutOfBoundsException");
                } else {
                    for (int i = 0; i < argCount; ++i) {
                        Var arg = invokeExp.getArg(i);
                        if (propTypes.isAllowed(arg)) {
                            Var param = callee.getIR().getParam(i);
                            CSVar argVar = csManager.getCSVar(callerCtx, arg);
                            CSVar paramVar = csManager.getCSVar(calleeCtx, param);
                            summaryFrontierProfiler.recordCallArgumentOrigin(
                                    edge, argVar, paramVar);
                            addPFGEdge(argVar, paramVar, FlowKind.PARAMETER_PASSING);
                        }
                    }
                }
                // pass results to LHS variable
                Var lhs = callSite.getResult();
                if (lhs != null && propTypes.isAllowed(lhs)) {
                    CSVar csLHS = csManager.getCSVar(callerCtx, lhs);
                    for (Var ret : callee.getIR().getReturnVars()) {
                        if (propTypes.isAllowed(ret)) {
                            CSVar csRet = csManager.getCSVar(calleeCtx, ret);
                            summaryFrontierProfiler.recordReturnOrigin(
                                    edge, csRet, csLHS);
                            addPFGEdge(csRet, csLHS, FlowKind.RETURN);
                        }
                    }
                }
            }
            plugin.onNewCallEdge(edge);
        }
    }

    private boolean shouldDebugSummaryProbe(Var var) {
        if (var == null || var.getMethod() == null) {
            return false;
        }
        if (!SummaryDebugConfig.matchesMethod(var.getMethod())) {
            return false;
        }
        if ("$r13".equals(var.getName())) {
            return true;
        }
        for (Invoke invoke : var.getInvokes()) {
            if (shouldDebugSummaryProbe(invoke)) {
                return true;
            }
        }
        return false;
    }

    private boolean shouldDebugSummaryProbe(Invoke callSite) {
        if (callSite == null || callSite.getContainer() == null) {
            return false;
        }
        if (!SummaryDebugConfig.matchesMethod(callSite.getContainer())) {
            return false;
        }
        return callSite.getMethodRef().getName().contains("ByExample");
    }

    private String describeInvokeTargets(Var var) {
        StringBuilder builder = new StringBuilder("[");
        boolean first = true;
        for (Invoke invoke : var.getInvokes()) {
            if (!first) {
                builder.append(", ");
            }
            builder.append(invoke.getMethodRef());
            first = false;
        }
        builder.append(']');
        return builder.toString();
    }

    private int receiverPointsToSize(Context callerCtx, Invoke callSite) {
        if (callSite == null || !(callSite.getInvokeExp() instanceof InvokeInstanceExp instanceExp)) {
            return 0;
        }
        Var base = instanceExp.getBase();
        if (!propTypes.isAllowed(base)) {
            return 0;
        }
        return getPointsToSetOf(csManager.getCSVar(callerCtx, base)).size();
    }

    private int argumentPointsToTotal(Context callerCtx, Invoke callSite) {
        if (callSite == null) {
            return 0;
        }
        int total = 0;
        InvokeExp invokeExp = callSite.getInvokeExp();
        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            Var arg = invokeExp.getArg(i);
            if (propTypes.isAllowed(arg)) {
                total += getPointsToSetOf(csManager.getCSVar(callerCtx, arg)).size();
            }
        }
        return total;
    }

    private void debugSummaryProbe(Var recvVar, Invoke callSite, CSObj recvObj,
                                   JMethod callee, String phase) {
        if (!shouldDebugSummaryProbe(callSite)) {
            return;
        }
        logger.info("[summary-probe] {} recvVar={} recvObj={} invokeMethodRef={} resolvedCallee={} hasSummary={}",
                phase,
                recvVar,
                recvObj.getObject(),
                callSite.getMethodRef(),
                callee == null ? "null" : callee.getSignature(),
                callee != null && summaryManager.hasSummary(callee.getRef()));
    }

    private boolean isIgnored(JMethod method) {
        IgnoredReason reason = getIgnoredReason(method);
        if (reason != null) {
            ignoredMethodReasons.put(method, reason);
            return true;
        }
        return false;
    }

    private IgnoredReason getIgnoredReason(JMethod method) {
        if (ignoredMethods.contains(method)) {
            return IgnoredReason.EXPLICIT_SUMMARY;
        }
        if (onlyApp && !method.isApplication()) {
            return IgnoredReason.ONLY_APP;
        }
        if (jdkSummaryOnly && jdkBoundaryClassifier.isJdkPlatformMethod(method)) {
            return IgnoredReason.JDK_SUMMARY_ONLY;
        }
        if (summaryFrontierOnlyMethods.contains(method.getSignature())) {
            return IgnoredReason.SUMMARY_FRONTIER_ONLY;
        }
        return null;
    }

    private enum IgnoredReason {
        EXPLICIT_SUMMARY,
        ONLY_APP,
        JDK_SUMMARY_ONLY,
        SUMMARY_FRONTIER_ONLY
    }

    private static Set<String> loadSummaryFrontierOnlyMethods(String path) {
        if (path == null || path.isBlank()) {
            return Set.of();
        }
        Path file = Path.of(path);
        if (!Files.isRegularFile(file)) {
            logger.warn("[pta-summary-frontier] selected method file not found: {}", file);
            return Set.of();
        }
        try {
            String text = Files.readString(file);
            Set<String> methods = Sets.newLinkedSet();
            String trimmed = text.trim();
            if (trimmed.startsWith("{") || trimmed.startsWith("[")) {
                collectMethodSignatures(JSON.readTree(text), methods);
            } else {
                for (String line : text.split("\\R")) {
                    String signature = line.trim();
                    if (!signature.isEmpty() && !signature.startsWith("#")) {
                        methods.add(signature);
                    }
                }
            }
            logger.info("[pta-summary-frontier] Loaded {} selected summary frontier methods from {}",
                    methods.size(), file);
            return Collections.unmodifiableSet(methods);
        } catch (IOException e) {
            throw new UncheckedIOException(
                    "Failed to read summary frontier selected method file: " + file, e);
        }
    }

    private static void collectMethodSignatures(JsonNode node,
                                                Set<String> methods) {
        if (node == null || node.isNull()) {
            return;
        }
        if (node.isTextual()) {
            String value = node.asText();
            if (value.startsWith("<") && value.endsWith(">")) {
                methods.add(value);
            }
            return;
        }
        if (node.isArray()) {
            node.forEach(child -> collectMethodSignatures(child, methods));
            return;
        }
        if (node.isObject()) {
            JsonNode signature = node.get("method_signature");
            if (signature != null && signature.isTextual()) {
                methods.add(signature.asText());
            }
            JsonNode selectedMethods = node.get("selected_methods");
            if (selectedMethods != null) {
                collectMethodSignatures(selectedMethods, methods);
            }
        }
    }

    /**
     * Processes new reachable methods.
     */
    private void processNewMethod(JMethod method) {
        if (reachableMethods.add(method)) {
            plugin.onNewMethod(method);
            method.getIR().forEach(stmt -> plugin.onNewStmt(stmt, method));
        }
    }

    private class StmtProcessor {

        /**
         * Information shared by all visitors.
         */
        private final Map<NewMultiArray, Obj[]> newArrays = Maps.newMap();

        private final Map<New, Invoke> registerInvokes = Maps.newMap();

        private final JMethod finalize = Objects.requireNonNull(
                hierarchy.getJREMethod(FINALIZE));

        private final MethodRef finalizeRef = finalize.getRef();

        private final MethodRef registerRef = Objects.requireNonNull(
                hierarchy.getJREMethod(FINALIZER_REGISTER)).getRef();

        /**
         * Processes given Stmts in given CSMethod.
         */
        private void process(CSMethod csMethod, Collection<Stmt> stmts) {
            StmtVisitor<Void> visitor = new Visitor(csMethod);
            stmts.forEach(stmt -> stmt.accept(visitor));
        }

        /**
         * Visitor that contains actual processing logics.
         */
        private class Visitor implements StmtVisitor<Void> {

            private final CSMethod csMethod;

            private final Context context;

            private Visitor(CSMethod csMethod) {
                this.csMethod = csMethod;
                this.context = csMethod.getContext();
            }

            @Override
            public Void visit(New stmt) {
                // obtain context-sensitive heap object
                NewExp rvalue = stmt.getRValue();
                Obj obj = heapModel.getObj(stmt);
                pollutionProfiler.recordAllocation(csMethod.getMethod(), obj);
                summaryFrontierProfiler.recordAllocation(
                        csMethod.getMethod(), obj);
                heavyMethodProfiler.recordAllocation(
                        csMethod.getMethod(), obj);
                Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
                addVarPointsTo(context, stmt.getLValue(), heapContext, obj);
                if (rvalue instanceof NewMultiArray) {
                    processNewMultiArray(stmt, heapContext, obj);
                }
                if (hasOverriddenFinalize(rvalue)) {
                    processFinalizer(stmt);
                }
                return null;
            }

            private void processNewMultiArray(
                    New allocSite, Context arrayContext, Obj array) {
                NewMultiArray newMultiArray = (NewMultiArray) allocSite.getRValue();
                Obj[] arrays = newArrays.computeIfAbsent(newMultiArray, nma -> {
                    ArrayType type = nma.getType();
                    Obj[] newArrays = new MockObj[nma.getLengthCount() - 1];
                    for (int i = 1; i < nma.getLengthCount(); ++i) {
                        type = (ArrayType) type.elementType();
                        newArrays[i - 1] = heapModel.getMockObj(MULTI_ARRAY_DESC,
                                allocSite, type, allocSite.getContainer());
                    }
                    return newArrays;
                });
                for (Obj newArray : arrays) {
                    Context elemContext = contextSelector
                            .selectHeapContext(csMethod, newArray);
                    CSObj arrayObj = csManager.getCSObj(arrayContext, array);
                    ArrayIndex arrayIndex = csManager.getArrayIndex(arrayObj);
                    addPointsTo(arrayIndex, elemContext, newArray);
                    array = newArray;
                    arrayContext = elemContext;
                }
            }

            private boolean hasOverriddenFinalize(NewExp newExp) {
                return !finalize.equals(
                        hierarchy.dispatch(newExp.getType(), finalizeRef));
            }

            /**
             * Call Finalizer.register() at allocation sites of objects
             * which override Object.finalize() method.
             * NOTE: finalize() has been deprecated since Java 9, and
             * will eventually be removed.
             */
            private void processFinalizer(New stmt) {
                Invoke registerInvoke = registerInvokes.computeIfAbsent(stmt, s -> {
                    InvokeStatic callSite = new InvokeStatic(registerRef,
                            Collections.singletonList(s.getLValue()));
                    Invoke invoke = new Invoke(csMethod.getMethod(), callSite);
                    invoke.setLineNumber(stmt.getLineNumber());
                    return invoke;
                });
                processInvokeStatic(registerInvoke);
            }

            private void processInvokeStatic(Invoke callSite) {
                JMethod callee = CallGraphs.resolveCallee(null, callSite);
                if (callee != null) {
                    CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                    Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
                    CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
                    addCallEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee));
                }
            }

            @Override
            public Void visit(AssignLiteral stmt) {
                Literal literal = stmt.getRValue();
                Type type = literal.getType();
                if (type instanceof ClassType) {
                    // here we only generate objects of ClassType
                    Obj obj = heapModel.getConstantObj((ReferenceLiteral) literal);
                    Context heapContext = contextSelector
                            .selectHeapContext(csMethod, obj);
                    addVarPointsTo(context, stmt.getLValue(), heapContext, obj);
                }
                return null;
            }

            @Override
            public Void visit(Copy stmt) {
                Var rvalue = stmt.getRValue();
                if (propTypes.isAllowed(rvalue)) {
                    CSVar from = csManager.getCSVar(context, rvalue);
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(from, to, FlowKind.LOCAL_ASSIGN);
                }
                return null;
            }

            @Override
            public Void visit(Cast stmt) {
                CastExp cast = stmt.getRValue();
                if (propTypes.isAllowed(cast.getValue())) {
                    CSVar from = csManager.getCSVar(context, cast.getValue());
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(new PointerFlowEdge(
                                    FlowKind.CAST, from, to),
                            cast.getType());
                }
                return null;
            }

            /**
             * Processes static load.
             */
            @Override
            public Void visit(LoadField stmt) {
                if (stmt.isStatic() && propTypes.isAllowed(stmt.getRValue())) {
                    //javaparser debug: resolveNullable 避免解析失败
                    JField field = stmt.getFieldRef().resolveNullable();
                    if (field == null) return null;
                    StaticField sfield = csManager.getStaticField(field);
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(sfield, to, FlowKind.STATIC_LOAD);
                }
                return null;
            }

            /**
             * Processes static store.
             */
            @Override
            public Void visit(StoreField stmt) {
                if (stmt.isStatic() && propTypes.isAllowed(stmt.getRValue())) {
                    //javaparser debug: resolveNullable 避免解析失败
                    JField field = stmt.getFieldRef().resolveNullable();
                    if (field == null) return null;
                    StaticField sfield = csManager.getStaticField(field);
                    CSVar from = csManager.getCSVar(context, stmt.getRValue());
                    addPFGEdge(from, sfield, FlowKind.STATIC_STORE);
                }
                return null;
            }

            /**
             * Processes static invocation.
             */
            @Override
            public Void visit(Invoke stmt) {
                if (stmt.isStatic()) {
                    processInvokeStatic(stmt);
                }
                return null;
            }
        }
    }

    // ---------- solver logic ends ----------

    @Override
    public void addPointsTo(Pointer pointer, PointsToSet pts) {
        workList.addEntry(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, CSObj csObj) {
        PointsToSet pts = makePointsToSet();
        pts.addObject(csObj);
        addPointsTo(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, Context heapContext, Obj obj) {
        addPointsTo(pointer, csManager.getCSObj(heapContext, obj));
    }

    @Override
    public void addVarPointsTo(Context context, Var var, PointsToSet pts) {
        addPointsTo(csManager.getCSVar(context, var), pts);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, CSObj csObj) {
        addPointsTo(csManager.getCSVar(context, var), csObj);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, Context heapContext, Obj obj) {
        addPointsTo(csManager.getCSVar(context, var), heapContext, obj);
    }

    @Override
    public void addPointerFilter(Pointer pointer, Predicate<CSObj> filter) {
        pointer.addFilter(filter);
    }

    @Override
    public void addPFGEdge(PointerFlowEdge edge, Transfer transfer) {
        edge = pointerFlowGraph.addEdge(edge);
        if (edge != null && edge.addTransfer(transfer)) {
            pollutionProfiler.recordPFGEdge(edge);
            summaryFrontierProfiler.recordPFGEdge(edge);
            heavyMethodProfiler.recordPFGEdge(edge);
            PointsToSet sourceSet = getPointsToSetOf(edge.source());
            PointsToSet targetSet = transfer.apply(edge, sourceSet);
            TaintProvenanceDebug.logEdge("SummarySolver", edge, sourceSet, targetSet);
            if (!targetSet.isEmpty()) {
                addPointsTo(edge.target(), targetSet);
            }
        }
    }

    @Override
    public void addEntryPoint(EntryPoint entryPoint) {
        Context entryCtx = contextSelector.getEmptyContext();
        JMethod entryMethod = entryPoint.method();
        CSMethod csEntryMethod = csManager.getCSMethod(entryCtx, entryMethod);
        callGraph.addEntryMethod(csEntryMethod);
        addCSMethod(csEntryMethod);
        IR ir = entryMethod.getIR();
        ParamProvider paramProvider = entryPoint.paramProvider();
        // pass this objects
        if (!entryMethod.isStatic()) {
            for (Obj thisObj : paramProvider.getThisObjs()) {
                addVarPointsTo(entryCtx, ir.getThis(), entryCtx, thisObj);
            }
        }
        // pass parameter objects
        for (int i = 0; i < entryMethod.getParamCount(); ++i) {
            Var param = ir.getParam(i);
            if (propTypes.isAllowed(param)) {
                for (Obj paramObj : paramProvider.getParamObjs(i)) {
                    addVarPointsTo(entryCtx, param, entryCtx, paramObj);
                }
            }
        }
        // pass field objects
        paramProvider.getFieldObjs().forEach((base, field, obj) -> {
            CSObj csBase = csManager.getCSObj(entryCtx, base);
            InstanceField iField = csManager.getInstanceField(csBase, field);
            addPointsTo(iField, entryCtx, obj);
        });
        // pass array objects
        paramProvider.getArrayObjs().forEach((array, elem) -> {
            CSObj csArray = csManager.getCSObj(entryCtx, array);
            ArrayIndex arrayIndex = csManager.getArrayIndex(csArray);
            addPointsTo(arrayIndex, entryCtx, elem);
        });
    }

    @Override
    public void addCallEdge(Edge<CSCallSite, CSMethod> edge) {
        workList.addEntry(edge);
    }

    @Override
    public void addCSMethod(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            // process new reachable context-sensitive method
            JMethod method = csMethod.getMethod();
            if (isIgnored(method)) {
                pollutionProfiler.recordReachableMethod(method, false,
                        ignoredMethodReasons.get(method).name());
                summaryFrontierProfiler.recordReachableMethod(method, false,
                        ignoredMethodReasons.get(method).name());
                heavyMethodProfiler.recordReachableMethod(method, false,
                        ignoredMethodReasons.get(method).name());
                return;
            }
            pollutionProfiler.recordReachableMethod(method, true, null);
            summaryFrontierProfiler.recordReachableMethod(method, true, null);
            heavyMethodProfiler.recordReachableMethod(method, true, null);
            processNewMethod(method);
            addStmts(csMethod, method.getIR().getStmts());
            plugin.onNewCSMethod(csMethod);
        }
    }

    @Override
    public void addStmts(CSMethod csMethod, Collection<Stmt> stmts) {
        stmtProcessor.process(csMethod, stmts);
    }

    @Override
    public void addIgnoredMethod(JMethod method) {
        ignoredMethods.add(method);
    }

    @Override
    public void initializeClass(JClass cls) {
        if (cls == null || initializedClasses.contains(cls)) {
            return;
        }

        // [调试] 打印每次调用的类名和调用深度
        int depth = Thread.currentThread().getStackTrace().length;
        if (depth > 100) {
            logger.error("[调试] initializeClass 调用深度过大 ({}): 当前类={}", depth, cls.getName());
            JClass sc = cls.getSuperClass();
            logger.error("[调试]   该类的父类: {}", sc != null ? sc.getName() : "null");
            // 打印继承链
            StringBuilder chain = new StringBuilder();
            JClass current = cls;
            int count = 0;
            while (current != null && count < 20) {
                chain.append(current.getName()).append(" -> ");
                current = current.getSuperClass();
                count++;
            }
            logger.error("[调试]   继承链: {}", chain);
        }

        // initialize super class
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeClass(superclass);
        }
        // TODO: initialize the superinterfaces which
        //  declare default methods
        JMethod clinit = cls.getClinit();
        if (clinit != null) {
            // addCSMethod() may trigger initialization of more
            // classes. So cls must be added before addCSMethod(),
            // otherwise, infinite recursion may occur.
            initializedClasses.add(cls);
            CSMethod csMethod = csManager.getCSMethod(
                    contextSelector.getEmptyContext(), clinit);
            addCSMethod(csMethod);
        }
    }

    @Override
    public PointerAnalysisResult getResult() {
        if (result == null) {
            // //code summary: 在返回结果前，输出摘要统计信息
            logger.info(summaryManager.getStatistics());
            logger.info("[summary-query-stats] applySummary(query)={}ms reapply(query)={}ms fallback-scan={}ms",
                    queryApplySummaryNanos / 1_000_000.0,
                    queryReapplyNanos / 1_000_000.0,
                    queryFallbackScanNanos / 1_000_000.0);
            result = new PointerAnalysisResultImpl(
                    propTypes, csManager, heapModel,
                    callGraph, pointerFlowGraph);
            result.storeResult(IGNORED_METHOD_SIGNATURES_KEY,
                    ignoredMethods.stream()
                            .map(JMethod::getSignature)
                            .collect(java.util.stream.Collectors.toUnmodifiableSet()));
            result.storeResult(IGNORED_METHOD_REASONS_KEY,
                    collectIgnoredMethodReasons());
            result.storeResult(SUMMARY_APPLIED_COUNT_KEY,
                    summaryManager.getSummaryAppliedCount());
            result.storeResult(JDK_SUMMARY_CATALOG_STATS_KEY,
                    summaryManager.getJdkSummaryCatalogStats());
            result.storeResult(JDK_SUMMARY_CATALOG_METHOD_SIGNATURES_KEY,
                    summaryManager.getJdkSummaryCatalogMethodSignatures());
            Map<String, String> profilingArtifacts =
                    Maps.newLinkedHashMap();
            profilingArtifacts.putAll(pollutionProfiler.writeArtifacts());
            profilingArtifacts.putAll(summaryFrontierProfiler.writeArtifacts());
            profilingArtifacts.putAll(heavyMethodProfiler.writeArtifacts());
            result.storeResult(PTA_PROFILING_ARTIFACTS_KEY,
                    profilingArtifacts);
            result.storeResult(PTA_CLASS_PROFILE_PATH_KEY,
                    profilingArtifacts.get("pta_class_pollution_profile"));
            result.storeResult(PTA_BOUNDARY_DELTA_PATH_KEY,
                    profilingArtifacts.get("pta_class_boundary_delta"));
            result.storeResult(PTA_SHARED_HUBS_PATH_KEY,
                    profilingArtifacts.get("pta_shared_hubs"));
            result.storeResult(PTA_CULPRIT_RANKING_PATH_KEY,
                    profilingArtifacts.get("pta_culprit_ranking"));
            result.storeResult(PTA_APP_FRONTIER_METHODS_PATH_KEY,
                    profilingArtifacts.get("pta_app_frontier_methods"));
            result.storeResult(PTA_APP_ORIGIN_HUBS_PATH_KEY,
                    profilingArtifacts.get("pta_app_origin_hubs"));
            result.storeResult(PTA_FRONTIER_SLICES_PATH_KEY,
                    profilingArtifacts.get("pta_frontier_slices"));
            result.storeResult(PTA_METHOD_HUB_ATTRIBUTION_PATH_KEY,
                    profilingArtifacts.get("pta_method_hub_attribution"));
            result.storeResult(PTA_SUMMARY_FRONTIER_RANKING_PATH_KEY,
                    profilingArtifacts.get("pta_summary_frontier_ranking"));
            result.storeResult(PTA_FRONTIER_HUB_COVERAGE_PATH_KEY,
                    profilingArtifacts.get("pta_frontier_hub_coverage"));
            result.storeResult(PTA_CI_METHOD_PROFILE_PATH_KEY,
                    profilingArtifacts.get("pta_ci_method_profile"));
            result.storeResult(PTA_METHOD_CG_PTA_METRICS_PATH_KEY,
                    profilingArtifacts.get("pta_method_cg_pta_metrics"));
            result.storeResult(PTA_HEAVY_POLLUTING_METHODS_PATH_KEY,
                    profilingArtifacts.get("pta_heavy_polluting_methods"));
            result.storeResult(PTA_HEAVY_POLLUTING_METHODS_MARKDOWN_PATH_KEY,
                    profilingArtifacts.get(
                            "pta_heavy_polluting_methods_markdown"));
            result.storeResult(PTA_HEAVY_METHOD_CALLGRAPH_PATH_KEY,
                    profilingArtifacts.get("pta_heavy_method_callgraph"));
            result.storeResult(PTA_TOP_POLLUTING_METHODS_PATH_KEY,
                    profilingArtifacts.get("pta_top_polluting_methods"));
        }
        return result;
    }

    private Map<String, String> collectIgnoredMethodReasons() {
        Map<String, String> reasons = new TreeMap<>();
        ignoredMethodReasons.forEach((method, reason) ->
                reasons.put(method.getSignature(), reason.name()));
        callGraph.reachableMethods()
                .map(CSMethod::getMethod)
                .forEach(method -> {
                    IgnoredReason reason = getIgnoredReason(method);
                    if (reason != null) {
                        reasons.put(method.getSignature(), reason.name());
                    }
                });
        return Collections.unmodifiableMap(reasons);
    }

    // //code summary: 获取摘要管理器（供外部插件使用）
    public SummaryManager getSummaryManager() {
        return summaryManager;
    }
}
