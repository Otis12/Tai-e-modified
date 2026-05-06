package pascal.taie.analysis.pta.plugin.localflow;

import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.solver.CutShortcutSolver;
import pascal.taie.analysis.pta.plugin.field.ParameterIndex;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Cast;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.List;

import static pascal.taie.analysis.pta.plugin.field.ParameterIndex.THISINDEX;
import static pascal.taie.analysis.pta.plugin.field.ParameterIndex.getCorrespondingArgument;
import static pascal.taie.analysis.pta.plugin.field.ParameterIndex.getRealParameterIndex;
import static pascal.taie.analysis.pta.core.solver.DefaultSolver.isConcerned;
import static pascal.taie.analysis.pta.plugin.localflow.ParameterIndexOrNewObj.INDEX_THIS;

public class LocalFlowHandler implements Plugin {

    private CutShortcutSolver solver;

    private CSManager csManager;

    private Context emptyContext;

    private HeapModel heapModel;

    private int totIDMethod = 0;

    private final MultiMap<JMethod, ParameterIndexOrNewObj> directlyReturnParams = Maps.newMultiMap();

    public void setSolver(Solver solver) {
        if (solver instanceof CutShortcutSolver cutShortcutSolver) {
            this.solver = cutShortcutSolver;
            csManager = solver.getCSManager();
            emptyContext = solver.getContextSelector().getEmptyContext();
            heapModel = solver.getHeapModel();
        }
        else {
            throw new AnalysisException("Invalid solver");
        }
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        Var base = csVar.getVar();
        for (Invoke callSite : base.getInvokes()) {
            Var lhs = callSite.getLValue();
            if (lhs != null && isConcerned(lhs)) {
                CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
                pts.forEach(recvObj -> {
                    JMethod callee = CallGraphs.resolveCallee(
                            recvObj.getObject().getType(), callSite);
                    if (callee != null && directlyReturnParams.get(callee).contains(INDEX_THIS)) {
                        solver.addPointsTo(csLHS, recvObj);
                    }
                });
            }
        }
    }

    @Override
    public void onNewMethod(JMethod method) {
        if (!method.isAbstract()) {
            List<Var> retVars = method.getIR().getReturnVars();
            MultiMap<Var, ParameterIndexOrNewObj> result = getVariablesAssignedFromParameters(method);
            for (Var ret: retVars) {
                if (!result.get(ret).isEmpty()) {
                    totIDMethod ++;
                    break;
                }
            }
            result.forEach((var, index) -> {
                if (retVars.contains(var)) {
                    solver.addSelectedMethod(method);
                    directlyReturnParams.put(method, index);
                    solver.addSpecialHandledRetVar(var);
                }
            });
        }
    }

    private MultiMap<Var, ParameterIndexOrNewObj> getVariablesAssignedFromParameters(JMethod method) {
        MultiMap<Var, ParameterIndexOrNewObj> result = Maps.newMultiMap();
        MultiMap<Var, Stmt> definitions = Maps.newMultiMap();
        method.getIR().forEach(stmt -> {
            stmt.getDef().ifPresent(def -> {
                if (def instanceof Var varDef) {
                    definitions.put(varDef, stmt);
                }
            });
        });
        for (int i = 0; i < method.getParamCount(); i++) {
            Var param = method.getIR().getParam(i);
            if (isConcerned(param)) { // parameter which is not redefined in the method body
                if (definitions.get(param).isEmpty() || definitions.get(param).stream().allMatch(stmt -> stmt instanceof New)) {
                    result.put(param, new ParameterIndexOrNewObj(false, getRealParameterIndex(i), null));
                    definitions.get(param).forEach(stmt -> {
                        result.put(param, new ParameterIndexOrNewObj(true, null, heapModel.getObj((New) stmt)));
                    });
                }
            }
        }
        Var thisVar = method.getIR().getThis();
        if (thisVar != null) {
            result.put(thisVar, INDEX_THIS);
        }
        boolean changed = true;
        int size = result.size();
        while (size > 0 && changed) {
            method.getIR().getVars().forEach(var -> {
                boolean flag = true;
                for (Stmt def: definitions.get(var)) {
                    if (def instanceof Copy copy) {
                        Var rhs = copy.getRValue();
                        if (result.get(rhs).isEmpty()) {
                            flag = false;
                            break;
                        }
                    } else if (def instanceof Cast cast) {
                        Var rhs = cast.getRValue().getValue();
                        if (result.get(rhs).isEmpty()) {
                            flag = false;
                            break;
                        }
                    } else if (!(def instanceof New)) {
                        flag = false;
                        break;
                    }
                }
                if (flag) {
                    for (Stmt def: definitions.get(var)) {
                        Var rhs;
                        if (def instanceof Copy copy)
                            rhs = copy.getRValue();
                        else if (def instanceof Cast cast)
                            rhs = cast.getRValue().getValue();
                        else if (def instanceof New stmt) {
                            Obj obj = heapModel.getObj(stmt);
                            result.put(var, new ParameterIndexOrNewObj(true, null, obj));
                            continue;
                        }
                        else
                            throw new AnalysisException("Neither Copy not Cast: " + def + "!");
                        result.get(rhs).forEach(index -> result.put(var, index));
                    }
                }
            });
            changed = result.size() != size;
            size = result.size();
        }
        return result;
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        CSMethod csCallee = edge.getCallee();
        JMethod callee = csCallee.getMethod();
        CSCallSite csCallSite = edge.getCallSite();
        Invoke callSite = csCallSite.getCallSite();
        InvokeExp invokeExp = callSite.getInvokeExp();
        Var lhs = callSite.getLValue();
        if (lhs != null && isConcerned(lhs)) {
            CSVar csLHS = csManager.getCSVar(emptyContext, lhs);
            directlyReturnParams.get(callee).forEach(indexOrObj -> {
                if (indexOrObj.isObj()) {
                    solver.addPointsTo(csLHS, csManager.getCSObj(emptyContext, indexOrObj.obj()));
                }
                else {
                    ParameterIndex index = indexOrObj.index();
                    if (index == THISINDEX && invokeExp instanceof InvokeInstanceExp instanceExp) {
                        CSVar csBase = csManager.getCSVar(emptyContext, instanceExp.getBase());
                        solver.getPointsToSetOf(csBase).forEach(csObj -> {
                            JMethod realCallee = CallGraphs.resolveCallee(csObj.getObject().getType(), callSite);
                            if (callee.equals(realCallee))
                                solver.addPointsTo(csLHS, csObj);
                        });
                    }
                    if (index != THISINDEX) {
                        assert index != null;
                        Var arg = getCorrespondingArgument(edge, index);
                        if (arg != null && isConcerned(arg))
                            solver.addPFGEdge(csManager.getCSVar(emptyContext, arg), csLHS, PointerFlowEdge.Kind.ID, lhs.getType());
                    }
                }

            });
        }
    }

}
