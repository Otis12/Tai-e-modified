package pascal.taie.analysis.pta.plugin.container;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.HostPointer;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.CutShortcutSolver;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.container.HostMap.HostList;
import pascal.taie.analysis.pta.plugin.container.HostMap.HostSet;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.New;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.collection.Sets;

import java.util.Map;
import java.util.Objects;
import java.util.Set;

import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.ClassificationOf;
import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.isEnumerationClass;
import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.isHashtableType;
import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.isIteratorClass;
import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.isMapEntryClass;
import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.isVectorType;
import static pascal.taie.analysis.pta.core.solver.DefaultSolver.isConcerned;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.COL_0;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.COL_ITR;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.ALL;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_0;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_ENTRY;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_ENTRY_SET;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_KEY_ITR;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_KEY_SET;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_VALUES;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_VALUE_ITR;

public class ContainerAccessHandler implements Plugin {
    private static final Logger logger = LogManager.getLogger(ContainerAccessHandler.class);

    private static final String CSC_RECOVER_LOG = "[csc-recover]";

    private CutShortcutSolver solver;

    private CSManager csManager;

    private HeapModel heapModel;

    private Context emptyContext;

    private TypeSystem typeSystem;

    private static ContainerConfig containerConfig;

    private CallGraph<CSCallSite, CSMethod> callGraph;

    private final String[] categories = new String[]{"Map-Key", "Map-Value", "Col-Value"};

    private final HostList.Kind[] SetKindsInMap = new HostList.Kind[]{MAP_KEY_SET, MAP_VALUES, MAP_ENTRY_SET};

    private final MultiMap<Var, Var> ArrayVarToVirtualArrayVar = Maps.newMultiMap();

    private final MultiMap<Var, Var> CollectionVarToVirtualArrayVar = Maps.newMultiMap();

    private final MultiMap<Var, Var> ExtenderLargerToSmaller = Maps.newMultiMap();
    private final MultiMap<Var, Var> ExtenderSmallerToLarger = Maps.newMultiMap();

    private final MultiMap<Pair<HostList.Kind, CSVar>, Pair<HostList.Kind, CSVar>> HostPropagater = Maps.newMultiMap();

    private final Map<JClass, Var> VirtualArgsOfEntrySet = Maps.newMap();

    private final MultiMap<Host, Invoke> hostToExits = Maps.newMultiMap();

    private final Map<JClass, JMethod> abstractListToGet = Maps.newMap();

    private static String describeHost(Host host) {
        return "host#" + host.getIndex() +
                "{type=" + host.getType() +
                ",class=" + host.getClassification() +
                ",tainted=" + host.getTaint() +
                ",obj=" + host.getObject() + "}";
    }

    private static String describeInvoke(Invoke invoke) {
        return "container=" + invoke.getContainer() + ", invoke=" + invoke;
    }

    private static String subsetFlags(boolean newHost, boolean keySet, boolean values) {
        return "newHost=" + newHost + ",keySet=" + keySet + ",values=" + values;
    }

    private static String propagationReason(String direction, Var largerVar, Var smallerVar,
                                            HostList.Kind largerKind, HostList.Kind smallerKind) {
        return "propagation direction=" + direction +
                ", largerVar=" + largerVar +
                ", smallerVar=" + smallerVar +
                ", largerKind=" + largerKind +
                ", smallerKind=" + smallerKind;
    }

    private static String correlationReason(Invoke callSite, JMethod callee, Var largerArg, Var smallerArg) {
        return "correlation-extender callee=" + callee +
                ", callSite={" + describeInvoke(callSite) + "}" +
                ", largerArg=" + largerArg +
                ", smallerArg=" + smallerArg;
    }

    public void setSolver(Solver solver) {
        if (solver instanceof CutShortcutSolver cutShortcutSolver) {
            this.solver = cutShortcutSolver;
            csManager = solver.getCSManager();
            emptyContext = solver.getContextSelector().getEmptyContext();
            typeSystem = solver.getTypeSystem();
            heapModel = solver.getHeapModel();
            containerConfig = ContainerConfig.config;
            if (containerConfig == null)
                throw new AnalysisException("No containerConfig for Host Manager!");
            callGraph = solver.getCallGraph();
        }
        else {
            throw new AnalysisException("Invalid solver!");
        }
    }

    private JMethod resolveMethod(JClass clz, Subsignature subSig) {
        if (clz == null)
            return null;
        if (clz.getDeclaredMethod(subSig) != null)
            return clz.getDeclaredMethod(subSig);
        return resolveMethod(clz.getSuperClass(), subSig);
    }

    @Override
    public void onStart() {
        containerConfig.getAllEntrySetClasses().forEach(c -> {
            Var argVar = new Var(null, c + "/arg", typeSystem.getType("java.lang.Object"), -1, true);
            VirtualArgsOfEntrySet.put(c, argVar);
        });
        containerConfig.taintAbstractListClasses().forEach(jClass -> {
            JMethod getMethod = resolveMethod(jClass, Subsignature.get("java.lang.Object get(int)"));
            if (getMethod != null) {
                abstractListToGet.put(jClass, getMethod);
            }
        });
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        HostSet colSet = solver.getEmptyHostSet(), mapSet = solver.getEmptyHostSet();
        pts.forEach(csObj -> {
            Obj obj = csObj.getObject();
            Type objType = obj.getType();
            if (containerConfig.isHostType(objType)) {
                switch (ClassificationOf(objType)) {
                    case MAP -> mapSet.addHost(containerConfig.getObjectHost(obj, Host.Classification.MAP));
                    case COLLECTION -> colSet.addHost(containerConfig.getObjectHost(obj, Host.Classification.COLLECTION));
                }
            }
            ArrayVarToVirtualArrayVar.get(csVar.getVar()).forEach(virtualArray -> {
                CSVar csVirtualArray = csManager.getCSVar(emptyContext, virtualArray);
                ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                solver.addPFGEdge(arrayIndex, csVirtualArray, PointerFlowEdge.Kind.VIRTUAL_ARRAY, virtualArray.getType());
            });
        });
        if (!mapSet.isEmpty()) {
            csVar.getHostList().addHostSet(MAP_0, mapSet);
            onNewHostEntry(csVar, MAP_0, mapSet);
        }
        if (!colSet.isEmpty()) {
            csVar.getHostList().addHostSet(COL_0, colSet);
            onNewHostEntry(csVar, COL_0, colSet);
        }
    }

    @Override
    public void onNewHostEntry(CSVar csVar, HostList.Kind kind, HostSet hostSet) {
        propagateHostAndKind(csVar, hostSet, kind);
        ProcessMustRelatedInvokes(csVar, hostSet);
        Var base = csVar.getVar();
        base.getInvokes().forEach(invoke -> {
            if (isRelatedEntranceInvoke(invoke)) {
                CSCallSite csCallSite = csManager.getCSCallSite(emptyContext, invoke);
                InvokeExp invokeExp = invoke.getInvokeExp();
                callGraph.getCalleesOf(csCallSite).forEach(csMethod -> {
                    JMethod method = csMethod.getMethod();
                    int npara = method.getParamCount();
                    for (int i = 0; i < npara; i++) {
                        relateSourceToHosts(invokeExp, method, i, hostSet);
                    }
                });
            }
        });
        CollectionVarToVirtualArrayVar.get(base).forEach(virtualArray -> {
            if (kind == COL_0)
                hostSet.forEach(host -> addSourceToHost(virtualArray, host, "Col-Value"));
            else {
                hostSet.forEach(host -> addSourceToHost(virtualArray, host, "Map-Value"));
                hostSet.forEach(host -> addSourceToHost(virtualArray, host, "Map-Key"));
            }
            });
        ExtenderLargerToSmaller.get(base).forEach(smaller -> {
            CSVar smallerPointer = csManager.getCSVar(emptyContext, smaller);
            HostList hostMap = smallerPointer.getHostList();
            if (kind == COL_0) {
                if (hostMap.hasKind(COL_0)) {
                    addHostSubsetRelation(hostSet, Objects.requireNonNull(hostMap.getHostSetOf(COL_0)),
                            true, false, false,
                            propagationReason("extender-larger-to-smaller", base, smaller, COL_0, COL_0));
                }
                if (hostMap.hasKind(MAP_KEY_SET)) {
                    addHostSubsetRelation(hostSet, Objects.requireNonNull(hostMap.getHostSetOf(MAP_KEY_SET)),
                            false, true, false,
                            propagationReason("extender-larger-to-smaller", base, smaller, COL_0, MAP_KEY_SET));
                }
                if (hostMap.hasKind(MAP_VALUES)) {
                    addHostSubsetRelation(hostSet, Objects.requireNonNull(hostMap.getHostSetOf(MAP_VALUES)),
                            false, false, true,
                            propagationReason("extender-larger-to-smaller", base, smaller, COL_0, MAP_VALUES));
                }
            } else if (kind == MAP_0) {
                if (hostMap.hasKind(MAP_0)) {
                    addHostSubsetRelation(hostSet, Objects.requireNonNull(hostMap.getHostSetOf(MAP_0)),
                            true, false, false,
                            propagationReason("extender-larger-to-smaller", base, smaller, MAP_0, MAP_0));
                }
            }
        });
        ExtenderSmallerToLarger.get(base).forEach(larger -> {
            CSVar largerPointer = csManager.getCSVar(emptyContext, larger);
            HostList hostMap = largerPointer.getHostList();
            if (hostMap.hasKind(COL_0)) {
                HostSet set = hostMap.getHostSetOf(COL_0);
                if (kind == COL_0) {
                    addHostSubsetRelation(set, hostSet, true, false, false,
                            propagationReason("extender-smaller-to-larger", larger, base, COL_0, COL_0));
                }
                else if (kind == MAP_KEY_SET) {
                    addHostSubsetRelation(set, hostSet, false, true, false,
                            propagationReason("extender-smaller-to-larger", larger, base, COL_0, MAP_KEY_SET));
                }
                else if (kind == MAP_VALUES) {
                    addHostSubsetRelation(set, hostSet, false, false, true,
                            propagationReason("extender-smaller-to-larger", larger, base, COL_0, MAP_VALUES));
                }
            }
            if (kind == MAP_0) {
                if (hostMap.hasKind(MAP_0)) {
                    addHostSubsetRelation(Objects.requireNonNull(hostMap.getHostSetOf(MAP_0)), hostSet,
                        true, false, false,
                            propagationReason("extender-smaller-to-larger", larger, base, MAP_0, MAP_0));
                }
            }
        });
        HostPropagater.get(new Pair<>(kind, csVar)).forEach(kindCSVarPair -> {
                solver.addHostEntry(kindCSVarPair.second(), kindCSVarPair.first(), hostSet);
        });
        HostPropagater.get(new Pair<>(ALL, csVar)).forEach(kindCSVarPair -> {
            solver.addHostEntry(kindCSVarPair.second(), kind, hostSet);
        });
        for (HostList.Kind k: SetKindsInMap) {
            if (k == kind) {
                base.getInvokes().forEach(callSite -> {
                    CSCallSite csCallSite = csManager.getCSCallSite(emptyContext, callSite);
                    callGraph.getCalleesOf(csCallSite).forEach(csCallee -> {
                        Var thisVar = csCallee.getMethod().getIR().getThis();
                        if (thisVar != null) {
                            CSVar csThis = csManager.getCSVar(emptyContext, thisVar);
                            solver.addHostEntry(csThis, kind, hostSet);
                        }
                    });
                });
            }
        }
    }

    private void processArrayInitializer(Invoke callSite, JMethod callee) {
        solver.addSelectedMethod(callee);
        Pair<Integer, Integer> arrayCollectionPair = containerConfig.getArrayInitializer(callee);
        InvokeExp invoke = callSite.getInvokeExp();
        Var arrayVar = getArgument(invoke, arrayCollectionPair.first()),
            collectionVar = getArgument(invoke, arrayCollectionPair.second());
        if (!(arrayVar.getType() instanceof ArrayType)) {
            throw new AnalysisException("Not Array Type!");
        }
        Type elementType = ((ArrayType) arrayVar.getType()).elementType();
        Var virtualArrayVar = new Var(callSite.getContainer(), "virtualArrayVar", elementType, -1, true);
        ArrayVarToVirtualArrayVar.put(arrayVar, virtualArrayVar);
        CollectionVarToVirtualArrayVar.put(collectionVar, virtualArrayVar);
        CSVar csArray = csManager.getCSVar(emptyContext, arrayVar);
        solver.getPointsToSetOf(csArray).forEach(csObj -> {
            ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
            solver.addPFGEdge(arrayIndex, csManager.getCSVar(emptyContext, virtualArrayVar), PointerFlowEdge.Kind.VIRTUAL_ARRAY, elementType);
        });
        CSVar csCollection = csManager.getCSVar(emptyContext, collectionVar);
        HostList hostMap = csCollection.getHostList();
        if (hostMap.hasKind(COL_0)) {
            hostMap.getHostSetOf(COL_0).forEach(host -> {
                addSourceToHost(virtualArrayVar, host, "Col-Value");
            });
        }
        else if (hostMap.hasKind(MAP_0)) {
            hostMap.getHostSetOf(MAP_0).forEach(host -> {
                addSourceToHost(virtualArrayVar, host, "Map-Key");
                addSourceToHost(virtualArrayVar, host, "Map-Value");
            });
        }
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (edge.getKind() != CallKind.OTHER) {
            CSMethod csCallee = edge.getCallee();
            Invoke callSite = edge.getCallSite().getCallSite();
            JMethod callee = csCallee.getMethod();
            InvokeExp invokeExp = callSite.getInvokeExp();
            if (invokeExp instanceof InvokeInstanceExp instanceExp) {
                Var base = instanceExp.getBase(), thisVar = callee.getIR().getThis();
                CSVar csBase = csManager.getCSVar(emptyContext, base);
                CSVar csThis = csManager.getCSVar(emptyContext, thisVar);
                HostList hostMap = csBase.getHostList();
                for (HostList.Kind k: SetKindsInMap) {
                    if (hostMap.hasKind(k)) {
                        solver.addHostEntry(csThis, k, hostMap.getHostSetOf(k));
                        HostPropagater.put(new Pair<>(k, csBase), new Pair<>(k, csThis));
                    }
                }
            }
            if (containerConfig.isCorrelationExtender(callee)) {
                processCorrelationExtender(callSite, callee);
            }
            if (containerConfig.getArrayInitializer(callee) != null) {
                processArrayInitializer(callSite, callee);
            }
            for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                Var arg = invokeExp.getArg(i);
                if (isConcerned(arg)) {
                    if (isRelatedEntranceInvoke(callSite) && invokeExp instanceof InvokeInstanceExp instanceExp) {
                        Var base = instanceExp.getBase();
                        CSVar csBase = csManager.getCSVar(emptyContext, base);
                        int finalI = i;
                        csBase.getHostList().forEach((x, s) -> relateSourceToHosts(invokeExp, callee, finalI, s));
                    }
                }
            }
            processCollectionOutInvoke(callSite, callee);
        }
    }

    private static JClass getOuterClass(JClass inner) {
        if (inner != null) {
            if (inner.hasOuterClass())
                inner = inner.getOuterClass();
            return inner;
        }
        return null;
    }

    private static boolean isIteratorPollMethod(JMethod method) {
        String sig = method.getSubsignature().toString();
        return containerConfig.isIteratorClass(method.getDeclaringClass()) && (sig.contains("next()") ||
                sig.contains("previous()"));
    }

    private static boolean isEnumerationPollMethod(JMethod method) {
        return isEnumerationClass(method.getDeclaringClass())
                && method.getSubsignature().toString().contains("nextElement()");
    }

    public static boolean CutReturnEdge(Invoke invoke, JMethod method) {
        String methodKind = containerConfig.CategoryOfExit(method);
        JClass calleeClass = method.getDeclaringClass();
        String signature = method.getSubsignature().toString();
        if (!Objects.equals(methodKind, "Other")) return true;
        if (invoke.getInvokeExp() instanceof InvokeInstanceExp e && !e.getBase().getName().equals("%this")) {
            if (!isIteratorClass(invoke.getContainer().getDeclaringClass()) &&
                    isMapEntryClass(calleeClass) && (signature.contains("getValue(") || signature.contains("getKey("))) {
                return true;
            }
            if (isIteratorPollMethod(method))
                return true;
            if (isEnumerationPollMethod(method)) {
                Type outerType = getOuterClass(calleeClass).getType();
                return containerConfig.isHostType(outerType) || outerType.getName().equals("java.util.Collections");
            }
        }
        return false;
    }

    @Override
    public void onNewMethod(JMethod method) {
        method.getIR().forEach(s -> {
            if (s instanceof New stmt) {
                Obj obj = heapModel.getObj(stmt);
                Type objType = obj.getType();
                JClass clz = method.getDeclaringClass();
                if (objType instanceof ClassType clzType && isMapEntryClass(clzType.getJClass())) {
                    containerConfig.getRelatedEntrySetClassesOf(clz).forEach(entry -> {
                        Var arg = VirtualArgsOfEntrySet.get(entry);
                        CSVar csArg = csManager.getCSVar(emptyContext, arg);
                        solver.addPointsTo(csArg, csManager.getCSObj(emptyContext, obj));
                    });
                }
                if (containerConfig.isHostType(objType)) {
                    Host newHost = null;
                    switch (ClassificationOf(objType)) {
                        case MAP -> newHost = containerConfig.getObjectHost(obj, Host.Classification.MAP);
                        case COLLECTION -> newHost = containerConfig.getObjectHost(obj, Host.Classification.COLLECTION);
                    }
                    JClass hostClass = ((ClassType) objType).getJClass();
                    if (containerConfig.isEntrySetClass(hostClass)) {
                        Var arg = VirtualArgsOfEntrySet.get(hostClass);
                        addSourceToHost(arg, newHost, "Col-Value");
                    }
                    if (containerConfig.isTaintAbstractListType(objType)) {
                        JMethod get = abstractListToGet.get(hostClass);
                        final Host temp = newHost;
                        get.getIR().getReturnVars().forEach(ret -> {
                            addSourceToHost(ret, temp, "Col-Value");
                        });
                    }
                }
                if (!method.isStatic()) {
                    CSVar csThis = csManager.getCSVar(emptyContext, method.getIR().getThis());
                    CSVar csLHS = csManager.getCSVar(emptyContext, stmt.getLValue());
                    if (containerConfig.isKeySetClass(objType.getName())) {
                        HostPropagater.put(new Pair<>(MAP_0, csThis), new Pair<>(MAP_KEY_SET, csLHS));
                    }
                    if (containerConfig.isValueSetClass(objType.getName())) {
                        HostPropagater.put(new Pair<>(MAP_0, csThis), new Pair<>(MAP_VALUES, csLHS));
                    }
                }
            }
        });
    }

    private void processCollectionOutInvoke(Invoke callSite, JMethod callee) {
        Var lhs = callSite.getLValue();
        String calleeSig = callee.getMethodSource().toString();
        if (lhs != null && isConcerned(lhs) && callSite.getInvokeExp() instanceof InvokeInstanceExp instanceExp) {
            String methodKind = containerConfig.CategoryOfExit(callee);
            Var base = instanceExp.getBase();
            CSVar csBase = csManager.getCSVar(emptyContext, base);
            HostList hostMap = csBase.getHostList();
            if (!Objects.equals(methodKind, "Other")) {
                solver.addSelectedMethod(callee);
                csBase.addMustRelatedInvoke(callSite, methodKind);
                if (Objects.equals(methodKind, "Col-Value")) {
                    if (hostMap.hasKind(COL_0)) {
                        hostMap.getHostSetOf(COL_0).forEach(host -> {
                            if (typeSystem.isSubtype(base.getType(), host.getType()))
                                checkHostRelatedExit(callSite, host, methodKind);
                        });
                    }
                }
                else {
                    if (hostMap.hasKind(MAP_0)) {
                        hostMap.getHostSetOf(MAP_0).forEach(host -> {
                            if (typeSystem.isSubtype(base.getType(), host.getType()))
                                checkHostRelatedExit(callSite, host, methodKind);
                        });
                    }
                }
            }
            if (isMapEntryClass(callee.getDeclaringClass()) && hostMap.hasKind(MAP_ENTRY)) {
                HostSet set = hostMap.getHostSetOf(MAP_ENTRY);
                if (set != null) {
                    if (calleeSig.contains("getValue(")) {
                        solver.addSelectedMethod(callee);
                        set.forEach(host -> checkHostRelatedExit(callSite, host, "Map-Value"));
                    }
                    if (calleeSig.contains("getKey(")) {
                        solver.addSelectedMethod(callee);
                        set.forEach(host -> checkHostRelatedExit(callSite, host, "Map-Key"));
                    }
                }
            }
            if (isIteratorClass(callee.getDeclaringClass()) && (calleeSig.contains("next()") ||
                    calleeSig.contains("previous()"))) {
                solver.addSelectedMethod(callee);
                if (hostMap.hasKind(MAP_VALUE_ITR))
                    hostMap.getHostSetOf(MAP_VALUE_ITR).forEach(host -> checkHostRelatedExit(callSite, host, "Map-Value"));
                if (hostMap.hasKind(MAP_KEY_ITR))
                    hostMap.getHostSetOf(MAP_KEY_ITR).forEach(host -> checkHostRelatedExit(callSite, host, "Map-Key"));
                if (hostMap.hasKind(COL_ITR))
                    hostMap.getHostSetOf(COL_ITR).forEach(host -> checkHostRelatedExit(callSite, host, "Col-Value"));
            }
            if (isEnumerationClass(callee.getDeclaringClass()) && calleeSig.contains("nextElement()")) {
                solver.addSelectedMethod(callee);
                if (hostMap.hasKind(MAP_VALUE_ITR))
                    hostMap.getHostSetOf(MAP_VALUE_ITR).forEach(host -> checkHostRelatedExit(callSite, host, "Map-Value"));
                if (hostMap.hasKind(MAP_KEY_ITR))
                    hostMap.getHostSetOf(MAP_KEY_ITR).forEach(host -> checkHostRelatedExit(callSite, host, "Map-Key"));
                if (hostMap.hasKind(COL_ITR))
                    hostMap.getHostSetOf(COL_ITR).forEach(host -> checkHostRelatedExit(callSite, host, "Col-Value"));
            }
        }
    }

    private boolean isRelatedEntranceInvoke(Invoke invoke) {
        return !containerConfig.isUnrelatedInInvoke(invoke);
    }

    private Var getArgument(InvokeExp invokeExp, int index) {
        return index == -1 ? ((InvokeInstanceExp) invokeExp).getBase()
                : invokeExp.getArg(index);
    }

    private Set<JMethod> coes = Sets.newSet();

    private void processCorrelationExtender(Invoke callSite, JMethod callee) {
        solver.addSelectedMethod(callee);
        containerConfig.getCorrelationExtender(callee).forEach(indexPair -> {
            if (callSite.getInvokeExp() instanceof InvokeInstanceExp instanceExp && !instanceExp.getBase().equals(callee.getIR().getThis())) {
                coes.add(callee);
                int largerIndex = indexPair.first(), smallerIndex = indexPair.second();
                Var arg1 = getArgument(instanceExp, largerIndex);
                Var arg2 = getArgument(instanceExp, smallerIndex);
                if (isConcerned(arg1) && isConcerned(arg2)) {
                    ExtenderLargerToSmaller.put(arg1, arg2);
                    ExtenderSmallerToLarger.put(arg2, arg1);
                    CSVar smallerPointer = csManager.getCSVar(emptyContext, arg2), largerPointer = csManager.getCSVar(emptyContext, arg1);
                    HostList largerMap = largerPointer.getHostList(), smallerMap = smallerPointer.getHostList();

                    if (largerMap.hasKind(COL_0)) {
                        HostSet set = largerMap.getHostSetOf(COL_0);
                        if (smallerMap.hasKind(COL_0)) {
                            addHostSubsetRelation(set, smallerMap.getHostSetOf(COL_0), true, false, false,
                                    correlationReason(callSite, callee, arg1, arg2) +
                                            ", largerKind=" + COL_0 + ", smallerKind=" + COL_0);
                        }
                        if (smallerMap.hasKind(MAP_KEY_SET)) {
                            addHostSubsetRelation(set, smallerMap.getHostSetOf(MAP_KEY_SET), false, true, false,
                                    correlationReason(callSite, callee, arg1, arg2) +
                                            ", largerKind=" + COL_0 + ", smallerKind=" + MAP_KEY_SET);
                        }
                        if (smallerMap.hasKind(MAP_VALUES)) {
                            addHostSubsetRelation(set, smallerMap.getHostSetOf(MAP_VALUES), false, false, true,
                                    correlationReason(callSite, callee, arg1, arg2) +
                                            ", largerKind=" + COL_0 + ", smallerKind=" + MAP_VALUES);
                        }
                    }
                    if (largerMap.hasKind(MAP_0) && smallerMap.hasKind(MAP_0)) {
                        addHostSubsetRelation(largerMap.getHostSetOf(MAP_0),
                            smallerMap.getHostSetOf(MAP_0), true, false, false,
                                correlationReason(callSite, callee, arg1, arg2) +
                                        ", largerKind=" + MAP_0 + ", smallerKind=" + MAP_0);
                    }
                }
            }
        });
    }

    private void addHostSubsetRelation(HostSet largerHosts, HostSet smallerHosts,
                                       boolean newHost, boolean keySet, boolean values, String reason) {
        smallerHosts.forEach(host -> {
                    largerHosts.forEach(largerHost -> {
                        boolean taint = containerConfig.isTaintType(host.getType());
                        if (!largerHost.getTaint() && !largerHost.getType().getName().contains("java.util.Collections$Empty")) {
                            if (!taint && !host.getTaint()) {
                                if (newHost) {
                                    if (host.getClassification() == Host.Classification.COLLECTION
                                            && largerHost.getClassification() == Host.Classification.COLLECTION) {
                                        HostPointer smallerPointer = csManager.getHostPointer(host, "Col-Value"),
                                                largerPointer = csManager.getHostPointer(largerHost, "Col-Value");
                                        solver.addPFGEdge(smallerPointer, largerPointer, PointerFlowEdge.Kind.SUBSET);
                                    }
                                    if (host.getClassification() == Host.Classification.MAP
                                            && largerHost.getClassification() == Host.Classification.MAP) {
                                        HostPointer smallerPointer = csManager.getHostPointer(host, "Map-Key"),
                                                largerPointer = csManager.getHostPointer(largerHost, "Map-Key");
                                        solver.addPFGEdge(smallerPointer, largerPointer, PointerFlowEdge.Kind.SUBSET);

                                        smallerPointer = csManager.getHostPointer(host, "Map-Value");
                                        largerPointer = csManager.getHostPointer(largerHost, "Map-Value");
                                        solver.addPFGEdge(smallerPointer, largerPointer, PointerFlowEdge.Kind.SUBSET);
                                    }
                                }
                                if (keySet && host.getClassification() == Host.Classification.MAP
                                        && largerHost.getClassification() == Host.Classification.COLLECTION) {
                                    HostPointer smallerPointer = csManager.getHostPointer(host, "Map-Key"),
                                            largerPointer = csManager.getHostPointer(largerHost, "Col-Value");
                                    solver.addPFGEdge(smallerPointer, largerPointer, PointerFlowEdge.Kind.SUBSET);
                                }
                                if (values && host.getClassification() == Host.Classification.MAP
                                        && largerHost.getClassification() == Host.Classification.COLLECTION) {
                                    HostPointer smallerPointer = csManager.getHostPointer(host, "Map-Value"),
                                            largerPointer = csManager.getHostPointer(largerHost, "Col-Value");
                                    solver.addPFGEdge(smallerPointer, largerPointer, PointerFlowEdge.Kind.SUBSET);
                                }
                            }
                            else {
                                String trigger = taint ? "smaller-host-type-is-taint" : "smaller-host-already-tainted";
                                logger.info("{} subset-taint-trigger reason={}, trigger={}, largerHost={}, smallerHost={}, flags={}",
                                        CSC_RECOVER_LOG, reason, trigger,
                                        describeHost(largerHost), describeHost(host),
                                        subsetFlags(newHost, keySet, values));
                                taintHost(largerHost,
                                        reason + ", trigger=" + trigger + ", smallerHost#" + host.getIndex());
                            }
                        }
                    });
                });
    }

    private void propagateHostAndKind(CSVar csVar, HostSet hostSet, HostList.Kind kind) {
        Var varBase = csVar.getVar();
        varBase.getInvokes().forEach(invoke -> {
            Var lhs = invoke.getLValue();
            if (lhs != null && isConcerned(lhs)) {
                InvokeExp invokeExp = invoke.getInvokeExp();
                String invokeString = invokeExp.getMethodRef().getName();
                CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
                ContainerConfig.getHostGenerators().forEach((kind_ori, keyString, kind_gen) -> {
                    if (kind == kind_ori && invokeString.contains(keyString)) {
                        solver.addHostEntry(csLHS, kind_gen, hostSet);
                    }
                });
                ContainerConfig.getNonContainerExits().forEach((kind_required, invoke_str, category) -> {
                    if (kind == kind_required && invokeString.contains(invoke_str))
                        hostSet.forEach(host -> checkHostRelatedExit(invoke, host, category));
                });
                switch (kind) {
                    case COL_0 -> {
                        if (invokeString.equals("elements") && isVectorType(varBase.getType())) {
                            solver.addHostEntry(csLHS, COL_ITR, hostSet);
                        }
                    }
                    case MAP_0 -> {
                        if ((invokeString.equals("elements") && isHashtableType(varBase.getType()))) {
                            solver.addHostEntry(csLHS, MAP_VALUE_ITR, hostSet);
                        }
                    }
                }
            }
        });
    }

    private void ProcessMustRelatedInvokes(CSVar csVar, HostSet hostSet) {
        Var varBase = csVar.getVar();
        csVar.getMustRelatedInvokes().forEach(invokeCategoryPair -> { // out invokes
            Var lhs = invokeCategoryPair.first().getLValue();
            if (lhs != null && isConcerned(lhs)) {
                hostSet.forEach(host -> {
                    if (typeSystem.isSubtype(varBase.getType(), host.getType()))
                        checkHostRelatedExit(invokeCategoryPair.first(), host, invokeCategoryPair.second());
                });
            }
        });
    }

    private void recoverCallSite(Invoke callSite) {
        recoverCallSite(callSite, "unspecified");
    }

    private void recoverCallSite(Invoke callSite, String reason) {
        Var lhs = callSite.getLValue();
        if (lhs != null && solver.addRecoveredCallSite(callSite)) {
            CSCallSite csCallSite = csManager.getCSCallSite(emptyContext, callSite);
            CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
            Set<CSMethod> callees = callGraph.getCalleesOf(csCallSite);
            logger.info("{} recover-callsite reason={}, lhs={}, {}, calleeCount={}",
                    CSC_RECOVER_LOG, reason, lhs, describeInvoke(callSite), callees.size());
            callees.forEach(csCallee -> {
                JMethod callee = csCallee.getMethod();
                callee.getIR().getReturnVars().forEach(ret -> {
                    CSVar csRet = csManager.getCSVar(emptyContext, ret);
                    solver.addPFGEdge(csRet, csLHS, PointerFlowEdge.Kind.RETURN);
                });
            });
        }
    }

    private void taintHost(Host host) {
        taintHost(host, "unspecified");
    }

    private void taintHost(Host host, String reason) {
        if (!host.getTaint() && !containerConfig.isTaintAbstractListType(host.getType())) {
            host.setTaint();
            Set<Invoke> cachedExits = hostToExits.get(host);
            logger.info("{} taint-host host={}, reason={}, cachedExitCount={}",
                    CSC_RECOVER_LOG, describeHost(host), reason, cachedExits.size());
            cachedExits.forEach(exit ->
                    recoverCallSite(exit, "recovered-by=" + describeHost(host) + ", cause={" + reason + "}"));
            for (String cat: categories) {
                csManager.getHostPointer(host, cat).getOutEdges().forEach(outEdge -> {
                    Pointer succ = outEdge.getTarget();
                    if (succ instanceof HostPointer hostPointer) {
                        taintHost(hostPointer.getHost(),
                                "propagated-from-host#" + host.getIndex() + ", category=" + cat +
                                        ", upstreamCause={" + reason + "}");
                    }
                });
            }
        }
    }

    private void checkHostRelatedExit(Invoke callSite, Host host, String category) {
        Var lhs = callSite.getLValue();
        if (lhs != null && isConcerned(lhs) && !solver.isRecoveredCallSite(callSite)) {
            if (host.getTaint()) {
                logger.info("{} eager-recover category={}, host={}, lhs={}, {}",
                        CSC_RECOVER_LOG, category, describeHost(host), lhs, describeInvoke(callSite));
                recoverCallSite(callSite,
                        "host-already-tainted category=" + category + ", host=" + describeHost(host));
            }
            else {
                if (hostToExits.put(host, callSite)) {
                    logger.info("{} cache-exit category={}, host={}, lhs={}, {}",
                            CSC_RECOVER_LOG, category, describeHost(host), lhs, describeInvoke(callSite));
                }
                addTargetToHost(lhs, host, category);
            }
        }

    }

    private void addTargetToHost(Var result, Host host, String category) {
        if (result != null && isConcerned(result) && host.addOutResult(result, category)) {
            HostPointer hostPointer = csManager.getHostPointer(host, category);
            CSVar target = csManager.getCSVar(emptyContext, result);
            solver.addPFGEdge(hostPointer, target, //result.getType(),
                    PointerFlowEdge.Kind.HOST_TO_RESULT);
        }
    }

    private void relateSourceToHosts(InvokeExp invokeExp, JMethod callee, int index, HostSet hostSet) {
        ClassType classType;
        for (String category: categories) {
            if ((classType = containerConfig.getTypeConstraintOf(callee, index, category)) != null) {
                solver.addSelectedMethod(callee);
                Var argument = invokeExp.getArg(index);
                ClassType type = classType;
                hostSet.hosts().filter(d -> !d.getTaint() && typeSystem.isSubtype(type, d.getType()))
                        .forEach(d -> addSourceToHost(argument, d, category));
            }
        }
    }

    private void addSourceToHost(Var arg, Host host, String category) {
        if (host.getTaint())
            return;
        if (arg != null && isConcerned(arg) && host.addInArgument(arg, category)) {
            CSVar source = csManager.getCSVar(emptyContext, arg);
            HostPointer hostPointer = csManager.getHostPointer(host, category);
            solver.addPFGEdge(source, hostPointer, PointerFlowEdge.Kind.ARG_TO_HOST);
        }
    }

    @Override
    public void onNewPFGEdge(PointerFlowEdge edge) {
        Pointer source = edge.getSource(), target = edge.getTarget();
        PointerFlowEdge.Kind kind = edge.getKind();
        if (solver.needPropagateHost(source, kind)) {
            HostList hostMap = source.getHostList();
            if (!hostMap.isEmpty()) {
                hostMap.forEach((k, set) -> solver.addHostEntry(target, k, set));
            }
        }
    }
}
