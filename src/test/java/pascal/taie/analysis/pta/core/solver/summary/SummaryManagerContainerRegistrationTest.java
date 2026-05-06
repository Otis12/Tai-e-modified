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

package pascal.taie.analysis.pta.core.solver.summary;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.EntryPoint;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.core.solver.Transfer;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.container.HostMap.HostSet;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Collection;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SummaryManagerContainerRegistrationTest {

    private static final String CLASSPATH = "src/test/resources/world";

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-pp", "-cp", CLASSPATH, "--input-classes",
                "ConstVar,"
                        + "javax.servlet.ServletRequest,"
                        + "javax.servlet.http.HttpSession,"
                        + "jakarta.servlet.ServletRequest,"
                        + "jakarta.servlet.http.HttpSession");
    }

    @AfterAll
    static void resetWorld() {
        World.reset();
    }

    @Test
    void jdkContainerMethodsAreRegisteredOutsideTransferSummaryRules() {
        SummaryManager manager = new SummaryManager(new StubSolver());
        manager.initHardcodedSummaries();

        JMethod hashMapGet = World.get().getClassHierarchy().getMethod(
                "<java.util.HashMap: java.lang.Object get(java.lang.Object)>");
        JMethod arrayListGet = World.get().getClassHierarchy().getMethod(
                "<java.util.ArrayList: java.lang.Object get(int)>");
        JMethod iteratorNext = World.get().getClassHierarchy().getMethod(
                "<java.util.Iterator: java.lang.Object next()>");
        JMethod iterableIterator = World.get().getClassHierarchy().getMethod(
                "<java.lang.Iterable: java.util.Iterator iterator()>");

        assertNotNull(hashMapGet);
        assertNotNull(arrayListGet);
        assertNotNull(iteratorNext);
        assertNotNull(iterableIterator);

        assertTrue(manager.hasSummary(hashMapGet.getRef()));
        assertTrue(manager.hasSummary(arrayListGet.getRef()));
        assertTrue(manager.hasSummary(iteratorNext.getRef()));
        assertTrue(manager.hasSummary(iterableIterator.getRef()));
        assertTrue(manager.getSummaries(hashMapGet.getRef()).isEmpty(),
                "JDK container methods should no longer use AccessPath transfer summaries");
        assertTrue(manager.getSummaries(arrayListGet.getRef()).isEmpty(),
                "JDK container methods should no longer use AccessPath transfer summaries");
        assertTrue(manager.getSummaries(iteratorNext.getRef()).isEmpty(),
                "Iterator.next should be modeled by container summaries instead of base->result transfer");
        assertTrue(manager.getSummaries(iterableIterator.getRef()).isEmpty(),
                "Iterable.iterator should be modeled by container summaries instead of base->result transfer");
        assertTrue(manager.getSummarizedMethods().containsAll(
                Set.of(hashMapGet, arrayListGet, iteratorNext, iterableIterator)));
    }

    @Test
    void objectToStringIsNoLongerRegisteredAsTransferSummary() {
        SummaryManager manager = new SummaryManager(new StubSolver());
        manager.initHardcodedSummaries();

        JMethod objectToString = World.get().getClassHierarchy().getMethod(
                "<java.lang.Object: java.lang.String toString()>");

        assertNotNull(objectToString);
        assertTrue(!manager.hasSummary(objectToString.getRef()));
        assertTrue(manager.getSummaries(objectToString.getRef()).isEmpty());
        assertTrue(!manager.getSummarizedMethods().contains(objectToString));
    }

    @Test
    void servletAttributeMethodsAreRegisteredAsContainerSummaries() {
        SummaryManager manager = new SummaryManager(new StubSolver());
        manager.initHardcodedSummaries();

        JMethod javaxRequestSet = World.get().getClassHierarchy().getMethod(
                "<javax.servlet.ServletRequest: void setAttribute(java.lang.String,java.lang.Object)>");
        JMethod javaxRequestGet = World.get().getClassHierarchy().getMethod(
                "<javax.servlet.ServletRequest: java.lang.Object getAttribute(java.lang.String)>");
        JMethod javaxSessionSet = World.get().getClassHierarchy().getMethod(
                "<javax.servlet.http.HttpSession: void setAttribute(java.lang.String,java.lang.Object)>");
        JMethod javaxSessionGet = World.get().getClassHierarchy().getMethod(
                "<javax.servlet.http.HttpSession: java.lang.Object getAttribute(java.lang.String)>");
        JMethod jakartaRequestSet = World.get().getClassHierarchy().getMethod(
                "<jakarta.servlet.ServletRequest: void setAttribute(java.lang.String,java.lang.Object)>");
        JMethod jakartaRequestGet = World.get().getClassHierarchy().getMethod(
                "<jakarta.servlet.ServletRequest: java.lang.Object getAttribute(java.lang.String)>");
        JMethod jakartaSessionSet = World.get().getClassHierarchy().getMethod(
                "<jakarta.servlet.http.HttpSession: void setAttribute(java.lang.String,java.lang.Object)>");
        JMethod jakartaSessionGet = World.get().getClassHierarchy().getMethod(
                "<jakarta.servlet.http.HttpSession: java.lang.Object getAttribute(java.lang.String)>");

        assertNotNull(javaxRequestSet);
        assertNotNull(javaxRequestGet);
        assertNotNull(javaxSessionSet);
        assertNotNull(javaxSessionGet);
        assertNotNull(jakartaRequestSet);
        assertNotNull(jakartaRequestGet);
        assertNotNull(jakartaSessionSet);
        assertNotNull(jakartaSessionGet);

        Set<JMethod> attributeMethods = Set.of(
                javaxRequestSet, javaxRequestGet,
                javaxSessionSet, javaxSessionGet,
                jakartaRequestSet, jakartaRequestGet,
                jakartaSessionSet, jakartaSessionGet);
        for (JMethod method : attributeMethods) {
            assertTrue(manager.hasSummary(method.getRef()),
                    () -> "Expected attribute summary registration for " + method.getSignature());
            assertTrue(manager.getSummaries(method.getRef()).isEmpty(),
                    () -> "Attribute methods should be modeled by container summaries: "
                            + method.getSignature());
        }
        assertTrue(manager.getSummarizedMethods().containsAll(attributeMethods));
    }

    @Test
    void lowLevelContainerSummaryRegistrationHonorsFamilyFlags() {
        java.util.Map<String, Object> options = new java.util.HashMap<>();
        options.put("summary-container-map", false);
        options.put("summary-container-list", true);
        options.put("summary-container-collection", false);
        options.put("summary-container-iterator", false);
        SummaryManager manager = new SummaryManager(new StubSolver(options));
        manager.initHardcodedSummaries();

        JMethod hashMapGet = World.get().getClassHierarchy().getMethod(
                "<java.util.HashMap: java.lang.Object get(java.lang.Object)>");
        JMethod arrayListGet = World.get().getClassHierarchy().getMethod(
                "<java.util.ArrayList: java.lang.Object get(int)>");
        JMethod arrayListAdd = World.get().getClassHierarchy().getMethod(
                "<java.util.ArrayList: boolean add(java.lang.Object)>");
        JMethod iteratorNext = World.get().getClassHierarchy().getMethod(
                "<java.util.Iterator: java.lang.Object next()>");
        JMethod iterableIterator = World.get().getClassHierarchy().getMethod(
                "<java.lang.Iterable: java.util.Iterator iterator()>");
        JMethod servletRequestGet = World.get().getClassHierarchy().getMethod(
                "<jakarta.servlet.ServletRequest: java.lang.Object getAttribute(java.lang.String)>");

        assertNotNull(hashMapGet);
        assertNotNull(arrayListGet);
        assertNotNull(arrayListAdd);
        assertNotNull(iteratorNext);
        assertNotNull(iterableIterator);
        assertNotNull(servletRequestGet);

        assertFalse(manager.hasSummary(hashMapGet.getRef()));
        assertTrue(manager.hasSummary(arrayListGet.getRef()));
        assertFalse(manager.hasSummary(arrayListAdd.getRef()));
        assertFalse(manager.hasSummary(iteratorNext.getRef()));
        assertFalse(manager.hasSummary(iterableIterator.getRef()));
        assertTrue(manager.hasSummary(servletRequestGet.getRef()),
                "Servlet attribute carriers should stay enabled when low-level families are disabled");
    }

    private static final class StubSolver implements Solver {

        private final CSManager csManager = new MapBasedCSManager();

        private final PointsToSetFactory pointsToSetFactory =
                new PointsToSetFactory(csManager.getObjectIndexer());

        private final AnalysisOptions options;

        private StubSolver() {
            this(new java.util.HashMap<>());
        }

        private StubSolver(java.util.Map<String, Object> options) {
            this.options = new AnalysisOptions(options);
        }

        @Override
        public AnalysisOptions getOptions() {
            return options;
        }

        @Override
        public ClassHierarchy getHierarchy() {
            return World.get().getClassHierarchy();
        }

        @Override
        public pascal.taie.language.type.TypeSystem getTypeSystem() {
            return World.get().getTypeSystem();
        }

        @Override
        public HeapModel getHeapModel() {
            throw unsupported();
        }

        @Override
        public CSManager getCSManager() {
            return csManager;
        }

        @Override
        public ContextSelector getContextSelector() {
            throw unsupported();
        }

        @Override
        public HostSet getEmptyHostSet() {
            throw unsupported();
        }

        @Override
        public CallGraph<CSCallSite, CSMethod> getCallGraph() {
            throw unsupported();
        }

        @Override
        public PointsToSet getPointsToSetOf(Pointer pointer) {
            return pointsToSetFactory.make();
        }

        @Override
        public PointsToSet makePointsToSet() {
            return pointsToSetFactory.make();
        }

        @Override
        public void setPlugin(Plugin plugin) {
            throw unsupported();
        }

        @Override
        public void solve() {
            throw unsupported();
        }

        @Override
        public void addPointsTo(Pointer pointer, PointsToSet pts) {
            throw unsupported();
        }

        @Override
        public void addPointsTo(Pointer pointer, CSObj csObj) {
            throw unsupported();
        }

        @Override
        public void addPointsTo(Pointer pointer, Context heapContext, Obj obj) {
            throw unsupported();
        }

        @Override
        public void addVarPointsTo(Context context, Var var, PointsToSet pts) {
            throw unsupported();
        }

        @Override
        public void addVarPointsTo(Context context, Var var, CSObj csObj) {
            throw unsupported();
        }

        @Override
        public void addVarPointsTo(Context context, Var var, Context heapContext, Obj obj) {
            throw unsupported();
        }

        @Override
        public void addPointerFilter(Pointer pointer, Predicate<CSObj> filter) {
            throw unsupported();
        }

        @Override
        public void addPFGEdge(PointerFlowEdge edge, Transfer transfer) {
            throw unsupported();
        }

        @Override
        public void addEntryPoint(EntryPoint entryPoint) {
            throw unsupported();
        }

        @Override
        public void addCallEdge(Edge<CSCallSite, CSMethod> edge) {
            throw unsupported();
        }

        @Override
        public void addCSMethod(CSMethod csMethod) {
            throw unsupported();
        }

        @Override
        public void addStmts(CSMethod csMethod, Collection<Stmt> stmts) {
            throw unsupported();
        }

        @Override
        public void addIgnoredMethod(JMethod method) {
            throw unsupported();
        }

        @Override
        public void initializeClass(JClass cls) {
            throw unsupported();
        }

        @Override
        public PointerAnalysisResult getResult() {
            throw unsupported();
        }

        private UnsupportedOperationException unsupported() {
            return new UnsupportedOperationException("not needed in this test");
        }
    }
}
