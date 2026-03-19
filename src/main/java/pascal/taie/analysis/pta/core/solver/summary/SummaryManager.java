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
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.VoidType;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import soot.JastAddJ.Access;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.Objects;
import java.util.Set;
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
     * 活跃调用点注册表
     * <p>用于追踪哪些调用点正在使用摘要，以便参数变化时重新计算
     * <p>Key: CSVar (参数变量)
     * <p>Value: 使用该参数的调用点集合
     */
    private final MultiMap<CSVar, ActiveCall> argToActiveCalls = Maps.newMultiMap();

    private final Solver solver;
    private final CSManager csManager;

    /**
     * 活跃调用点记录
     */
    public record ActiveCall(
            CSCallSite csCallSite,
            Context callerContext,
            JMethod callee,
            SummaryDetail summaryDetail
    ) {}

    public SummaryManager(Solver solver) {
        this.solver = solver;
        this.csManager = solver.getCSManager();
    }

    // ==================== 配置管理 ====================

    /**
     * 初始化硬编码的测试摘要规则
     * 需要在 ClassHierarchy 可用后调用
     */
    public void initHardcodedSummaries() {
        var hierarchy = solver.getHierarchy();
        var parser = new AccessPathParser(hierarchy);

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

        for (JClass clazz : hierarchy.allClasses().toList()) {
            if (clazz.isApplication()) {  // Only analyze application classes
                for (JMethod method : clazz.getDeclaredMethods()) {
                    if (method.isAbstract() || method.isNative()) {
                        continue;
                    }

                    // 拿到一个 method 判断是否是 getter setter
                    String methodType = checkGSetterMethod(method);
                    if(methodType.equals("Getter")) {
                        JField field = findFieldInClass(method.getDeclaringClass(), inferFieldNameFromGetter(method), method.getReturnType());
                        if(field != null) {
                            String sourceStr = "base." + field.getName().toString();
                            String targetStr = "result";

                            AccessPath source = parser.parse(method, sourceStr);
                            AccessPath target = parser.parse(method, "result");
                            if(source != null && target != null) {
                                summaries.add(SummaryDetail.of(method, sourceStr, targetStr, source, target));
                                logger.info("Registered hardcoded summary: {}", method.getSignature());
                            }
                        }
                    } else if(methodType.equals("Setter")) {
                        JField field = findFieldInClass(method.getDeclaringClass(), inferFieldNameFromSetter(method), method.getReturnType());
                        if(field != null) {
                            String sourceStr = "0";
                            String targetStr = "base." + field.getName().toString();

                            AccessPath source = parser.parse(method, sourceStr);
                            AccessPath target = parser.parse(method, targetStr);

                            if(source != null && target != null) {
                                summaries.add(SummaryDetail.of(method, sourceStr, targetStr, source, target));
                                logger.info("Registered hardcoded summary: {}", method.getSignature());
                            }
                        }
                    }


                }
            }
        }

        // ==================== JDK 容器方法摘要 ====================
        // 目的：当 only-app=false 时，阻止 PTA 进入 JDK 容器方法体进行分析，
        //       用 summary 替代方法体的指针传播语义，消除 transfer 规则 + PTA 指针流的双重传播。
        // 注意：这些 summary 只处理 PTA 层面的指针传播。Taint 传播仍由 TransferHandler
        //       通过 onNewCallEdge 回调独立处理，不受 summary 影响。
        addJdkContainerSummaries(hierarchy, parser, summaries);

        if (!summaries.isEmpty()) {
            SummaryConfig hardcodedConfig = new SummaryConfig(summaries);
            mergeConfig(hardcodedConfig);
            logger.info("Initialized {} hardcoded summary rules (including JDK container summaries)", summaries.size());
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
    }

    // ==================== 查询接口 ====================

    /**
     * 判断方法是否有摘要规则
     */
    public boolean hasSummary(MethodRef methodref) {
        return methodToSummaries.containsKey(methodref);
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
        Set<SummaryDetail> summaries = methodToSummaries.get(calleeMethodRef);
        if (summaries.isEmpty()) {
            return false;
        }

        Invoke callSite = csCallSite.getCallSite();
        logger.info("Applying {} summary rules for {} @ {}",
                summaries.size(), calleeMethodRef.getName(), callSite);

        for (SummaryDetail summary : summaries) {
            applySingleSummary(csCallSite, callerContext, callSite, summary);
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

        // 注册活跃调用点（用于增量更新）
//        registerActiveCall(csCallSite, context, summary, callSite);

        // 解析 source 的 pts
        PointsToSet sourcePts = resolveSourcePts(callSite, context, source);
//        logger.info("source pts: {}, context: {}, target: {}, callsite: {}",
//                sourcePts, context, target, callSite);

        if (sourcePts == null || sourcePts.isEmpty()) {
            return;
        }


        // 将 source pts 传播到 target
        propagateToTarget(callSite, context, target, sourcePts);


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
        // 检查是否有摘要规则
        Set<SummaryDetail> summaries = methodToSummaries.get(methodRef);
        if (summaries.isEmpty()) {
            return false;
        }

        boolean applied = false;

        for (SummaryDetail summary : summaries) {
            final JMethod targetMethod = summary.method();
            if (targetMethod == null) {
                continue;
            }

            // 方案：直接从 CSManager 获取所有 CSCallSite
            Collection<CSCallSite> allCallSites = csManager.getCSCallSites();

            for (CSCallSite csCallSite : allCallSites) {
                // 空指针检查
                if (csCallSite == null) {
                    continue;
                }

                Invoke callSite = csCallSite.getCallSite();
                if (callSite == null) {
                    continue;
                }

                InvokeExp invokeExp = callSite.getInvokeExp();
                if (invokeExp == null) {
                    continue;
                }

                // 检查这个调用点是否调用了目标方法
                MethodRef calleeRef = invokeExp.getMethodRef();
                if (calleeRef == null || !calleeRef.equals(methodRef)) {
                    continue;
                }

                // 提取上下文和调用点信息
                Context callerContext = csCallSite.getContext();
                if (callerContext == null) {
                    continue;
                }

                // 重新应用摘要
                applySingleSummary(csCallSite, callerContext, callSite, summary);
                applied = true;

                logger.debug("Reapplied summary for {} at {}",
                    methodRef.getName(), callSite);
            }
        }

        if (applied) {
            logger.info("Reapplied {} summary rules for method {}",
                summaries.size(), methodRef.getName());
        }

        return applied;
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

            PointsToSet diff = solver.getPointsToSetOf(csManager.getCSVar(context, targetBaseVar)).addAllDiff(sourcePts);
            if(!diff.isEmpty()) {
                diff.forEach(obj ->solver.addPointsTo(csManager.getCSVar(context, targetBaseVar), obj));
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

                PointsToSet diff = solver.getPointsToSetOf(instField).addAllDiff(sourcePts);
                if(!diff.isEmpty()) {
                    diff.forEach(obj ->solver.addPointsTo(instField, obj));
                }
            });

        } else if (target.hasArrayAccess()) {
            // 数组访问：添加到 base[*] 的 pts
            // 用于支持容器 add/put 类摘要规则（如 from: 0, to: base[*]）
            CSVar csTargetBase = csManager.getCSVar(context, targetBaseVar);
            PointsToSet targetBasePts = solver.getPointsToSetOf(csTargetBase);
            targetBasePts.forEach(baseObj -> {
                var arrayIndex = csManager.getArrayIndex(baseObj);
                PointsToSet diff = solver.getPointsToSetOf(arrayIndex).addAllDiff(sourcePts);
                if (!diff.isEmpty()) {
                    diff.forEach(obj -> solver.addPointsTo(arrayIndex, obj));
                }
            });
        }
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

    /**
     * 为 JDK 容器核心方法添加 summary 规则。
     * 这些方法在 only-app=false 时会被 PTA 深入分析方法体，导致指针流大量扩散（过污染）。
     * 通过 summary 替代方法体分析，只保留输入输出的指针传播关系。
     */
    private void addJdkContainerSummaries(pascal.taie.language.classes.ClassHierarchy hierarchy,
                                          AccessPathParser parser,
                                          java.util.List<SummaryDetail> summaries) {
        // ---- HashMap / Map ----
        // HashMap.get(key) → base → result（容器对象的 pts 流向返回值）
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.HashMap: java.lang.Object get(java.lang.Object)>",
                "base", "result");
        // HashMap.put(key, value) → value(arg1) → result（旧值返回）
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                "1", "result");
        // HashMap.getOrDefault → base → result
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.HashMap: java.lang.Object getOrDefault(java.lang.Object,java.lang.Object)>",
                "base", "result");
        // HashMap.remove → base → result
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.HashMap: java.lang.Object remove(java.lang.Object)>",
                "base", "result");

        // ---- ArrayList / List ----
        // ArrayList.get(int) → base → result
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.ArrayList: java.lang.Object get(int)>",
                "base", "result");
        // ArrayList.set(int, Object) → arg1 → result（旧值返回）
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.ArrayList: java.lang.Object set(int,java.lang.Object)>",
                "1", "result");
        // ArrayList.remove(int) → base → result
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.ArrayList: java.lang.Object remove(int)>",
                "base", "result");

        // ---- LinkedList ----
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.LinkedList: java.lang.Object get(int)>",
                "base", "result");
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.LinkedList: java.lang.Object getFirst()>",
                "base", "result");
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.LinkedList: java.lang.Object getLast()>",
                "base", "result");

        // ---- Iterator ----
        // Iterator.next() → base → result
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.Iterator: java.lang.Object next()>",
                "base", "result");

        // ---- Collections utility ----
        // Collections.unmodifiableList/Map/Set 等 → arg0 → result
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.Collections: java.util.List unmodifiableList(java.util.List)>",
                "0", "result");
        addJdkSummary(hierarchy, parser, summaries,
                "<java.util.Collections: java.util.Map unmodifiableMap(java.util.Map)>",
                "0", "result");

        // ---- Object.toString() ----
        // 这是过污染的最大单一来源，任何对象的 toString 都会传播
        addJdkSummary(hierarchy, parser, summaries,
                "<java.lang.Object: java.lang.String toString()>",
                "base", "result");

        // ---- StringBuilder/StringBuffer ----
        // append(String) → base → result（返回 this）
        addJdkSummary(hierarchy, parser, summaries,
                "<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>",
                "base", "result");
        addJdkSummary(hierarchy, parser, summaries,
                "<java.lang.StringBuilder: java.lang.String toString()>",
                "base", "result");
        addJdkSummary(hierarchy, parser, summaries,
                "<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>",
                "base", "result");
        addJdkSummary(hierarchy, parser, summaries,
                "<java.lang.StringBuffer: java.lang.String toString()>",
                "base", "result");

        logger.info("Added {} JDK container summary rules",
                summaries.size()); // 注意：此时 summaries 也包含 getter/setter，但日志仅供参考
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
        return config.summaryDetails().stream()
                .map(SummaryDetail::method)
                .filter(Objects::nonNull)
                .collect(Collectors.toSet());
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
                        "  - Active call mappings: %d",
                config.summaryDetails().size(),
                methodToSummaries.keySet().size(),
                argToActiveCalls.size()
        );
    }

    /**
     * 清理（用于分析结束后）
     */
    public void clear() {
        argToActiveCalls.clear();
    }
}
