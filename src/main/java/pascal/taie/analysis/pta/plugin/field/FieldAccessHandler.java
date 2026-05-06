package pascal.taie.analysis.pta.plugin.field;

import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.solver.CutShortcutSolver;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.container.ContainerAccessHandler;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Sets;

import java.util.List;
import java.util.Set;

import static pascal.taie.analysis.pta.core.solver.DefaultSolver.isConcerned;
import static pascal.taie.analysis.pta.plugin.field.ParameterIndex.THISINDEX;
import static pascal.taie.analysis.pta.plugin.field.ParameterIndex.getRealParameterIndex;

public class FieldAccessHandler implements Plugin {

    private final MultiMap<JMethod, SetStatement> setStatements = Maps.newMultiMap();

    private final MultiMap<JMethod, GetStatement> getStatements = Maps.newMultiMap();

    private final Set<Var> bannedReturnVars = Sets.newSet();

    private CutShortcutSolver solver;

    private TypeSystem typeSystem;

    private CSManager csManager;

    private CallGraph<CSCallSite, CSMethod> callGraph;

    private Context emptyContext;

    @Override
    public void setSolver(Solver solver) {
        if (solver instanceof CutShortcutSolver cutShortcutSolver) {
            this.solver = cutShortcutSolver;
            typeSystem = World.get().getTypeSystem();
            callGraph = solver.getCallGraph();
            csManager = solver.getCSManager();
            emptyContext = solver.getContextSelector().getEmptyContext();
        }
        else {
            throw new AnalysisException("Invalid Solver to " + getClass());
        }
    }

    public boolean addSetStatement(JMethod container, ParameterIndex baseIndex, FieldRef fieldRef, ParameterIndex rhsIndex) {
        SetStatement setStatement = new SetStatement(baseIndex, fieldRef, rhsIndex);
        if (setStatements.get(container).contains(setStatement))
            return false;
        setStatements.put(container, setStatement);
        return true;
    }

    public Set<SetStatement> getSetStatementsOf(JMethod method) { // 得到一个方法里所有的SetStatement
        return setStatements.get(method);
    }

    public Set<GetStatement> getGetStatementsOf(JMethod method) {
        return getStatements.get(method);
    }

    public boolean addGetStatement(JMethod container, int lhsIndex,  ParameterIndex baseIndex, FieldRef fieldRef) {
        GetStatement getStatement = new GetStatement(lhsIndex, baseIndex, fieldRef);
        if (getStatements.get(container).contains(getStatement))
            return false;
        getStatements.put(container, getStatement);
        return true;
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        processAbstractInstanceLoad(csVar, pts);
        processAbstractInstanceStore(csVar, pts);
    }

    private void processAbstractInstanceLoad(CSVar csVar, PointsToSet pts) {
        Var base = csVar.getVar();
        base.getAbstractLoadFields().forEach(load -> {
            Var lhs = load.getLValue();
            JField field = load.getFieldRef().resolve();
            if (isConcerned(lhs) && field != null) {
                CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
                pts.forEach(baseObj -> {
                    if (typeSystem.isSubtype(field.getDeclaringClass().getType(), baseObj.getObject().getType())) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        solver.addPFGEdge(instField, csLHS, //lhs.getType(),
                            load.isNonRelay() ? PointerFlowEdge.Kind.NON_RELAY_GET : PointerFlowEdge.Kind.GET);
                    }
                });
            }
        });
    }

    private void processAbstractInstanceStore(CSVar csVar, PointsToSet pts) {
        Var base = csVar.getVar();
        base.getAbstractStoreFields().forEach(store -> {
            Var rhs = store.getRValue();
            JField field = store.getFieldRef().resolve();
            if (isConcerned(rhs) && field != null) {
                CSVar csRHS = csManager.getCSVar(emptyContext, rhs);
                pts.forEach(baseObj -> {
                    if (typeSystem.isSubtype(field.getDeclaringClass().getType(), baseObj.getObject().getType())) {
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        solver.addPFGEdge(csRHS, instField, PointerFlowEdge.Kind.SET, field.getType());
                    }
                });
            }
        });
    }

    @Override
    public void onNewMethod(JMethod method) {
        if (!method.isAbstract()) {
            IR methodIR = method.getIR();
            methodIR.forEach(stmt -> {
                if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var def) {
                    def.setDefined();
                }
            });
            if (methodIR.getThis() != null) {
                methodIR.getThis().setParameterIndex(THISINDEX);
            }
            List<Var> params = methodIR.getParams();
            for (int i = 0; i < params.size(); i ++) {
                params.get(i).setParameterIndex(getRealParameterIndex(i));
            }
            JClass declaringClass = method.getDeclaringClass();
            method.getIR().forEach(stmt -> {
                if (!declaringClass.getName().equals("java.awt.Component")
                    && !declaringClass.getName().equals("javax.swing.JComponent")
                && stmt instanceof LoadField load
                        && load.getFieldAccess() instanceof InstanceFieldAccess fieldAccess) {
                    // x = y.f;
                    Var x = load.getLValue(), y = fieldAccess.getBase();
                    if (isConcerned(x)) {
                        int retIndex = ParameterIndex.GetReturnVariableIndex(x);
                        ParameterIndex baseIndex = y.getParameterIndex();
                        if (retIndex >= 0 && baseIndex != null && !y.isDefined()) {
                            load.disableRelay();
                            addBannedReturnVar(method, x);
                            solver.addGetStmtEntry(method, retIndex, baseIndex, load.getFieldRef());
                        }
                    }
                }
                else
                    if (!callGraph.isEntry(csManager.getCSMethod(emptyContext, method))
                && stmt instanceof StoreField store
                        && store.getFieldAccess() instanceof InstanceFieldAccess fieldAccess) {
                    // x.f = y;
                    Var x = fieldAccess.getBase(), y = store.getRValue();
                    if (isConcerned(y)) {
                        ParameterIndex baseIndex = x.getParameterIndex(), rhsIndex = y.getParameterIndex();
                        if (baseIndex != null && rhsIndex != null && !x.isDefined() && !y.isDefined()) {
                            solver.addIgnoredStoreField(store);
                            solver.addSetStmtEntry(method, store.getFieldRef(), baseIndex, rhsIndex);
                        }
                    }
                }
            });
        }
    }

    @Override
    public void onNewSetStatement(JMethod method, FieldRef fieldRef, ParameterIndex baseIndex, ParameterIndex rhsIndex) {
        // when a new SetStatement is found
        if (addSetStatement(method, baseIndex, fieldRef, rhsIndex)) {
            callGraph.edgesInTo(csManager.getCSMethod(emptyContext, method))
                    .forEach(edge -> {
                            processSetStatementOnCallEdge(edge, fieldRef, baseIndex, rhsIndex);
                    });
        }
    }

    public void processSetStatementOnNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        // when a new call edge found, process callSite with previous found SetStatement in the callee
        JMethod callee = edge.getCallee().getMethod();
        getSetStatementsOf(callee)
                .forEach(setStatement -> processSetStatementOnCallEdge(edge, setStatement.fieldRef(),
                        setStatement.baseIndex(), setStatement.rhsIndex()));
    }

    private void processSetStatementOnCallEdge(Edge<CSCallSite, CSMethod> edge, FieldRef fieldRef, ParameterIndex baseIndex, ParameterIndex rhsIndex) {
        Var base = ParameterIndex.getCorrespondingArgument(edge, baseIndex), // 得到SetStatement在callSite处的arg
            rhs = ParameterIndex.getCorrespondingArgument(edge, rhsIndex);
        if (base != null && rhs != null && isConcerned(rhs)) {
            JMethod caller = base.getMethod();
            ParameterIndex baseIndexAtCaller = base.getParameterIndex(), rhsIndexAtCaller = rhs.getParameterIndex();
            if (baseIndexAtCaller != null && rhsIndexAtCaller != null && !base.isDefined() && !rhs.isDefined()) {
                solver.addSelectedMethod(edge.getCallee().getMethod());
                solver.addSetStmtEntry(caller, fieldRef, baseIndexAtCaller, rhsIndexAtCaller);
            } else {
                processNewAbstractStoreField(base, fieldRef, rhs);
            }
        }
    }

    private void processNewAbstractStoreField(Var base, FieldRef fieldRef, Var rhs) {
        CSVar csBase = csManager.getCSVar(emptyContext, base), csRHS = csManager.getCSVar(emptyContext, rhs);
        JField field = fieldRef.resolve();
        new AbstractStoreField(new InstanceFieldAccess(fieldRef, base), rhs);
        solver.getPointsToSetOf(csBase).forEach(csObj -> {
            if (typeSystem.isSubtype(field.getDeclaringClass().getType(), csObj.getObject().getType()))
                solver.addPFGEdge(csRHS, csManager.getInstanceField(csObj, field), PointerFlowEdge.Kind.SET, field.getType());
        });
    }

    @Override
    public void onNewGetStatement(JMethod method, Integer lhsIndex, ParameterIndex baseIndex, FieldRef fieldRef) {
        if (addGetStatement(method, lhsIndex, baseIndex, fieldRef)) {
            // add deleted return vars (only do it when a new set statement is found)
            for (Edge<CSCallSite, CSMethod> edge: callGraph.edgesInTo(csManager.getCSMethod(emptyContext, method)).toList()) {
                processGetStatementOnCallEdge(edge, baseIndex, fieldRef);
            }
        }
    }

    public void processGetStatementOnNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        JMethod callee = edge.getCallee().getMethod();
        for (GetStatement get: getGetStatementsOf(callee)) {
            processGetStatementOnCallEdge(edge, get.baseIndex(), get.fieldRef());
        }
    }

    /**
     * @param baseIndex base of the Set Statement, it should be a parameter of the callee, and thus has a parameter index
     * @param fieldRef fieldRef of the Set Statement
     */
    private void processGetStatementOnCallEdge(Edge<CSCallSite, CSMethod> edge, ParameterIndex baseIndex, FieldRef fieldRef) {
        Invoke callSite = edge.getCallSite().getCallSite();
        JMethod callee = edge.getCallee().getMethod();
        Var base = ParameterIndex.getCorrespondingArgument(edge, baseIndex),
                lhs = callSite.getLValue();
        if (!ContainerAccessHandler.CutReturnEdge(callSite, callee)) {
            if (base != null && lhs != null && isConcerned(lhs)) {
                JMethod caller = base.getMethod();
                int lhsIndexAtCaller = ParameterIndex.GetReturnVariableIndex(lhs);
                ParameterIndex baseIndexAtCaller = base.getParameterIndex();
                solver.addSelectedMethod(edge.getCallee().getMethod());
                if (lhsIndexAtCaller != -1 && baseIndexAtCaller != null) {
                    addBannedReturnVar(caller, lhs); // 每一层GetStatement的retVar都需要删除
                    solver.addGetStmtEntry(caller, lhsIndexAtCaller, baseIndexAtCaller, fieldRef);
                    processNewAbstractLoadField(lhs, base, fieldRef, false);

                }
                else {
                    processNewAbstractLoadField(lhs, base, fieldRef, true);
                }
            }
        }
    }

    private void processNewAbstractLoadField(Var lhs, Var base, FieldRef fieldRef, boolean terminate) {
        CSVar csBase = csManager.getCSVar(emptyContext, base), csLHS = csManager.getCSVar(emptyContext, lhs);
        JField field = fieldRef.resolve();
        new AbstractLoadField(lhs, new InstanceFieldAccess(fieldRef, base), terminate);
        solver.getPointsToSetOf(csBase).forEach(csObj -> {
            if (typeSystem.isSubtype(field.getDeclaringClass().getType(), csObj.getObject().getType()))
                solver.addPFGEdge(csManager.getInstanceField(csObj, field), csLHS, //lhs.getType(),
                        terminate ? PointerFlowEdge.Kind.GET : PointerFlowEdge.Kind.NON_RELAY_GET);
        });
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        Invoke callSite = edge.getCallSite().getCallSite();
        processSetStatementOnNewCallEdge(edge);
        Var lhs = callSite.getLValue();
        if (lhs != null && isConcerned(lhs)) {
            processGetStatementOnNewCallEdge(edge);
            CSMethod csCallee = edge.getCallee();
            JMethod callee = csCallee.getMethod();
            CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
            if (!ContainerAccessHandler.CutReturnEdge(callSite, callee)) {
                for (Var ret: callee.getIR().getReturnVars()) {
                    if (bannedReturnVars.contains(ret)) {
                        CSVar csRet = csManager.getCSVar(emptyContext, ret);
                        csRet.getInEdges().forEach(inEdge -> {
                            if (inEdge.getKind() != PointerFlowEdge.Kind.NON_RELAY_GET) {
                                solver.addPFGEdge(inEdge.getSource(), csLHS, inEdge.getKind(), inEdge.getTransfer());
                            }
                        });
                    }
                }
            }
        }
    }

    @Override
    public void onNewPFGEdge(PointerFlowEdge edge) {
        Pointer source = edge.getSource(), target = edge.getTarget();
        PointerFlowEdge.Kind kind = edge.getKind();
        if (target instanceof CSVar csVar && bannedReturnVars.contains(csVar.getVar()) && kind != PointerFlowEdge.Kind.NON_RELAY_GET) {
            CSMethod csMethod = csManager.getCSMethod(emptyContext, csVar.getVar().getMethod());
            callGraph.getCallersOf(csMethod).forEach(csCallSite -> {
                Var lhs = csCallSite.getCallSite().getLValue();
                if (lhs != null && isConcerned(lhs)) {
                    CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
                    solver.addPFGEdge(source, csLHS, kind, edge.getTransfer());
                }
            });
        }
    }

    private void addBannedReturnVar(JMethod method, Var ret) {
        bannedReturnVars.add(ret);
        CSVar csRet = csManager.getCSVar(emptyContext, ret);
        csRet.getInEdges().forEach(edge -> {
            if (edge.getKind() != PointerFlowEdge.Kind.NON_RELAY_GET) {
                callGraph.getCallersOf(csManager.getCSMethod(emptyContext, method))
                        .forEach(csCallSite -> {
                            Var lhs = csCallSite.getCallSite().getLValue();
                            if (lhs != null && isConcerned(lhs)) {
                                CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
                                solver.addPFGEdge(edge.getSource(), csLHS, edge.getKind(), edge.getTransfer());
                            }
                        });
            }
        });
        solver.addSpecialHandledRetVar(ret);
    }
}
