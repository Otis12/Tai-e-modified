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
import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
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
import pascal.taie.ir.exp.StringLiteral;
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.IntType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.VoidType;
import pascal.taie.util.collection.Maps;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SummaryManagerContainerExecutionTest {

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
    void arrayListAddAndGetRemainSeparatedByContainerObject() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod arrayListAdd = hierarchy.getMethod(
                "<java.util.ArrayList: boolean add(java.lang.Object)>");
        JMethod arrayListGet = hierarchy.getMethod(
                "<java.util.ArrayList: java.lang.Object get(int)>");

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("ContainerCaller", "driveSummaries");
        Type arrayListType = World.get().getTypeSystem().getClassType("java.util.ArrayList");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var list1 = new Var(caller, "list1", arrayListType, 0);
        Var list2 = new Var(caller, "list2", arrayListType, 1);
        Var value1 = new Var(caller, "value1", objectType, 2);
        Var value2 = new Var(caller, "value2", objectType, 3);
        Var index1 = new Var(caller, "index1", IntType.INT, 4);
        Var index2 = new Var(caller, "index2", IntType.INT, 5);
        Var result1 = new Var(caller, "result1", objectType, 6);
        Var result2 = new Var(caller, "result2", objectType, 7);

        CSObj listObj1 = solver.newObject("list-1", arrayListType);
        CSObj listObj2 = solver.newObject("list-2", arrayListType);
        CSObj valueObj1 = solver.newObject("value-1", objectType);
        CSObj valueObj2 = solver.newObject("value-2", objectType);

        solver.seedVarPointsTo(context, list1, listObj1);
        solver.seedVarPointsTo(context, list2, listObj2);
        solver.seedVarPointsTo(context, value1, valueObj1);
        solver.seedVarPointsTo(context, value2, valueObj2);

        Invoke add1 = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list1, List.of(value1)));
        Invoke add2 = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list2, List.of(value2)));
        Invoke get1 = new Invoke(caller, new InvokeVirtual(arrayListGet.getRef(), list1, List.of(index1)), result1);
        Invoke get2 = new Invoke(caller, new InvokeVirtual(arrayListGet.getRef(), list2, List.of(index2)), result2);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add1),
                arrayListAdd.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add2),
                arrayListAdd.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, get1),
                arrayListGet.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, get2),
                arrayListGet.getRef(),
                context));

        assertEquals(Set.of(valueObj1), solver.pointsToOf(context, result1).getObjects());
        assertEquals(Set.of(valueObj2), solver.pointsToOf(context, result2).getObjects());
    }

    @Test
    void hashMapGetUsesConstantKeyBucketsWithinSameContainer() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod hashMapPut = hierarchy.getMethod(
                "<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>");
        JMethod hashMapGet = hierarchy.getMethod(
                "<java.util.HashMap: java.lang.Object get(java.lang.Object)>");

        assertNotNull(hashMapPut);
        assertNotNull(hashMapGet);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("MapCaller", "driveMapSummaries");
        Type hashMapType = World.get().getTypeSystem().getClassType("java.util.HashMap");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");
        Type stringType = World.get().getTypeSystem().getClassType("java.lang.String");

        Var map = new Var(caller, "map", hashMapType, 0);
        Var taintedValue = new Var(caller, "taintedValue", objectType, 1);
        Var safeValue = new Var(caller, "safeValue", objectType, 2);
        Var userKey = newConstStringVar(caller, "userKey", 3, "user");
        Var captchaKey = newConstStringVar(caller, "captchaKey", 4, "captcha");
        Var userResult = new Var(caller, "userResult", objectType, 5);
        Var captchaResult = new Var(caller, "captchaResult", objectType, 6);

        CSObj mapObj = solver.newObject("map-1", hashMapType);
        CSObj taintedObj = solver.newObject("tainted-1", stringType);
        CSObj safeObj = solver.newObject("safe-1", stringType);

        solver.seedVarPointsTo(context, map, mapObj);
        solver.seedVarPointsTo(context, taintedValue, taintedObj);
        solver.seedVarPointsTo(context, safeValue, safeObj);

        Invoke putUser = new Invoke(
                caller,
                new InvokeVirtual(hashMapPut.getRef(), map, List.of(userKey, taintedValue)));
        Invoke putCaptcha = new Invoke(
                caller,
                new InvokeVirtual(hashMapPut.getRef(), map, List.of(captchaKey, safeValue)));
        Invoke getUser = new Invoke(
                caller,
                new InvokeVirtual(hashMapGet.getRef(), map, List.of(userKey)),
                userResult);
        Invoke getCaptcha = new Invoke(
                caller,
                new InvokeVirtual(hashMapGet.getRef(), map, List.of(captchaKey)),
                captchaResult);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, putUser),
                hashMapPut.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, putCaptcha),
                hashMapPut.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getUser),
                hashMapGet.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getCaptcha),
                hashMapGet.getRef(),
                context));

        assertEquals(Set.of(taintedObj), solver.pointsToOf(context, userResult).getObjects());
        assertEquals(Set.of(safeObj), solver.pointsToOf(context, captchaResult).getObjects());
    }

    @Test
    void hashMapWildcardKeyConservativelyPollutesConcreteLookup() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod hashMapPut = hierarchy.getMethod(
                "<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>");
        JMethod hashMapGet = hierarchy.getMethod(
                "<java.util.HashMap: java.lang.Object get(java.lang.Object)>");

        assertNotNull(hashMapPut);
        assertNotNull(hashMapGet);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("MapCaller", "driveWildcardMapSummaries");
        Type hashMapType = World.get().getTypeSystem().getClassType("java.util.HashMap");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");
        Type stringType = World.get().getTypeSystem().getClassType("java.lang.String");

        Var map = new Var(caller, "map", hashMapType, 0);
        Var dynamicKey = new Var(caller, "dynamicKey", stringType, 1);
        Var taintedValue = new Var(caller, "taintedValue", objectType, 2);
        Var userKey = newConstStringVar(caller, "userKey", 3, "user");
        Var result = new Var(caller, "result", objectType, 4);

        CSObj mapObj = solver.newObject("map-1", hashMapType);
        CSObj taintedObj = solver.newObject("tainted-1", stringType);

        solver.seedVarPointsTo(context, map, mapObj);
        solver.seedVarPointsTo(context, taintedValue, taintedObj);

        Invoke putDynamic = new Invoke(
                caller,
                new InvokeVirtual(hashMapPut.getRef(), map, List.of(dynamicKey, taintedValue)));
        Invoke getUser = new Invoke(
                caller,
                new InvokeVirtual(hashMapGet.getRef(), map, List.of(userKey)),
                result);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, putDynamic),
                hashMapPut.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getUser),
                hashMapGet.getRef(),
                context));

        assertEquals(Set.of(taintedObj), solver.pointsToOf(context, result).getObjects());
    }

    @Test
    void servletRequestAttributesUseSameKeyedBucketsAsMapSummaries() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod setAttribute = hierarchy.getMethod(
                "<javax.servlet.ServletRequest: void setAttribute(java.lang.String,java.lang.Object)>");
        JMethod getAttribute = hierarchy.getMethod(
                "<javax.servlet.ServletRequest: java.lang.Object getAttribute(java.lang.String)>");

        assertNotNull(setAttribute);
        assertNotNull(getAttribute);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("AttributeCaller", "driveAttributeSummaries");
        Type requestType = World.get().getTypeSystem().getClassType("javax.servlet.ServletRequest");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");
        Type stringType = World.get().getTypeSystem().getClassType("java.lang.String");

        Var request = new Var(caller, "request", requestType, 0);
        Var taintedValue = new Var(caller, "taintedValue", objectType, 1);
        Var safeValue = new Var(caller, "safeValue", objectType, 2);
        Var userKey = newConstStringVar(caller, "userKey", 3, "user");
        Var captchaKey = newConstStringVar(caller, "captchaKey", 4, "captcha");
        Var userResult = new Var(caller, "userResult", objectType, 5);
        Var captchaResult = new Var(caller, "captchaResult", objectType, 6);

        CSObj requestObj = solver.newObject("request-1", requestType);
        CSObj taintedObj = solver.newObject("tainted-1", stringType);
        CSObj safeObj = solver.newObject("safe-1", stringType);

        solver.seedVarPointsTo(context, request, requestObj);
        solver.seedVarPointsTo(context, taintedValue, taintedObj);
        solver.seedVarPointsTo(context, safeValue, safeObj);

        Invoke setUser = new Invoke(
                caller,
                new InvokeVirtual(setAttribute.getRef(), request, List.of(userKey, taintedValue)));
        Invoke setCaptcha = new Invoke(
                caller,
                new InvokeVirtual(setAttribute.getRef(), request, List.of(captchaKey, safeValue)));
        Invoke getUser = new Invoke(
                caller,
                new InvokeVirtual(getAttribute.getRef(), request, List.of(userKey)),
                userResult);
        Invoke getCaptcha = new Invoke(
                caller,
                new InvokeVirtual(getAttribute.getRef(), request, List.of(captchaKey)),
                captchaResult);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setUser),
                setAttribute.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setCaptcha),
                setAttribute.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getUser),
                getAttribute.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getCaptcha),
                getAttribute.getRef(),
                context));

        assertEquals(Set.of(taintedObj), solver.pointsToOf(context, userResult).getObjects());
        assertEquals(Set.of(safeObj), solver.pointsToOf(context, captchaResult).getObjects());
    }

    @Test
    void iteratorNextLoadsValuesFromItsOwnBoundContainer() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod arrayListAdd = hierarchy.getMethod(
                "<java.util.ArrayList: boolean add(java.lang.Object)>");
        JMethod arrayListIterator = hierarchy.getMethod(
                "<java.util.ArrayList: java.util.Iterator iterator()>");
        JMethod iteratorNext = hierarchy.getMethod(
                "<java.util.Iterator: java.lang.Object next()>");

        assertNotNull(arrayListAdd);
        assertNotNull(arrayListIterator);
        assertNotNull(iteratorNext);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("IteratorCaller", "driveIteratorSummaries");
        Type arrayListType = World.get().getTypeSystem().getClassType("java.util.ArrayList");
        Type iteratorType = World.get().getTypeSystem().getClassType("java.util.Iterator");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var list1 = new Var(caller, "list1", arrayListType, 0);
        Var list2 = new Var(caller, "list2", arrayListType, 1);
        Var value1 = new Var(caller, "value1", objectType, 2);
        Var value2 = new Var(caller, "value2", objectType, 3);
        Var iterator1 = new Var(caller, "iterator1", iteratorType, 4);
        Var iterator2 = new Var(caller, "iterator2", iteratorType, 5);
        Var result1 = new Var(caller, "result1", objectType, 6);
        Var result2 = new Var(caller, "result2", objectType, 7);

        CSObj listObj1 = solver.newObject("list-1", arrayListType);
        CSObj listObj2 = solver.newObject("list-2", arrayListType);
        CSObj valueObj1 = solver.newObject("value-1", objectType);
        CSObj valueObj2 = solver.newObject("value-2", objectType);
        CSObj iteratorObj1 = solver.newObject("iterator-1", iteratorType);
        CSObj iteratorObj2 = solver.newObject("iterator-2", iteratorType);

        solver.seedVarPointsTo(context, list1, listObj1);
        solver.seedVarPointsTo(context, list2, listObj2);
        solver.seedVarPointsTo(context, value1, valueObj1);
        solver.seedVarPointsTo(context, value2, valueObj2);
        solver.seedVarPointsTo(context, iterator1, iteratorObj1);
        solver.seedVarPointsTo(context, iterator2, iteratorObj2);

        Invoke add1 = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list1, List.of(value1)));
        Invoke add2 = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list2, List.of(value2)));
        Invoke bindIterator1 = new Invoke(
                caller,
                new InvokeVirtual(arrayListIterator.getRef(), list1, List.of()),
                iterator1);
        Invoke bindIterator2 = new Invoke(
                caller,
                new InvokeVirtual(arrayListIterator.getRef(), list2, List.of()),
                iterator2);
        Invoke next1 = new Invoke(
                caller,
                new InvokeVirtual(iteratorNext.getRef(), iterator1, List.of()),
                result1);
        Invoke next2 = new Invoke(
                caller,
                new InvokeVirtual(iteratorNext.getRef(), iterator2, List.of()),
                result2);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add1),
                arrayListAdd.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add2),
                arrayListAdd.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, bindIterator1),
                arrayListIterator.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, bindIterator2),
                arrayListIterator.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, next1),
                iteratorNext.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, next2),
                iteratorNext.getRef(),
                context));

        assertEquals(Set.of(valueObj1), solver.pointsToOf(context, result1).getObjects());
        assertEquals(Set.of(valueObj2), solver.pointsToOf(context, result2).getObjects());
    }

    @Test
    void iteratorNextUsesIteratorVariableBindingWhenIteratorObjectIsUnavailable() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod arrayListAdd = hierarchy.getMethod(
                "<java.util.ArrayList: boolean add(java.lang.Object)>");
        JMethod arrayListIterator = hierarchy.getMethod(
                "<java.util.ArrayList: java.util.Iterator iterator()>");
        JMethod iteratorNext = hierarchy.getMethod(
                "<java.util.Iterator: java.lang.Object next()>");

        assertNotNull(arrayListAdd);
        assertNotNull(arrayListIterator);
        assertNotNull(iteratorNext);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("IteratorVarCaller", "driveIteratorVarBinding");
        Type arrayListType = World.get().getTypeSystem().getClassType("java.util.ArrayList");
        Type iteratorType = World.get().getTypeSystem().getClassType("java.util.Iterator");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var list = new Var(caller, "list", arrayListType, 0);
        Var value = new Var(caller, "value", objectType, 1);
        Var iterator = new Var(caller, "iterator", iteratorType, 2);
        Var result = new Var(caller, "result", objectType, 3);

        CSObj listObj = solver.newObject("list-1", arrayListType);
        CSObj valueObj = solver.newObject("value-1", objectType);

        solver.seedVarPointsTo(context, list, listObj);
        solver.seedVarPointsTo(context, value, valueObj);

        Invoke add = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list, List.of(value)));
        Invoke bindIterator = new Invoke(
                caller,
                new InvokeVirtual(arrayListIterator.getRef(), list, List.of()),
                iterator);
        Invoke next = new Invoke(
                caller,
                new InvokeVirtual(iteratorNext.getRef(), iterator, List.of()),
                result);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add),
                arrayListAdd.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, bindIterator),
                arrayListIterator.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, next),
                iteratorNext.getRef(),
                context));

        assertEquals(Set.of(valueObj), solver.pointsToOf(context, result).getObjects());
    }

    @Test
    void iteratorNextBackfillsWhenCollectionGetsValueAfterLoadSite() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod arrayListAdd = hierarchy.getMethod(
                "<java.util.ArrayList: boolean add(java.lang.Object)>");
        JMethod arrayListIterator = hierarchy.getMethod(
                "<java.util.ArrayList: java.util.Iterator iterator()>");
        JMethod iteratorNext = hierarchy.getMethod(
                "<java.util.Iterator: java.lang.Object next()>");

        assertNotNull(arrayListAdd);
        assertNotNull(arrayListIterator);
        assertNotNull(iteratorNext);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("IteratorBackfillCaller", "driveIteratorBackfill");
        Type arrayListType = World.get().getTypeSystem().getClassType("java.util.ArrayList");
        Type iteratorType = World.get().getTypeSystem().getClassType("java.util.Iterator");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var list = new Var(caller, "list", arrayListType, 0);
        Var value = new Var(caller, "value", objectType, 1);
        Var iterator = new Var(caller, "iterator", iteratorType, 2);
        Var result = new Var(caller, "result", objectType, 3);

        CSObj listObj = solver.newObject("list-1", arrayListType);
        CSObj valueObj = solver.newObject("value-1", objectType);
        CSObj iteratorObj = solver.newObject("iterator-1", iteratorType);

        solver.seedVarPointsTo(context, list, listObj);
        solver.seedVarPointsTo(context, iterator, iteratorObj);

        Invoke add = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list, List.of(value)));
        Invoke bindIterator = new Invoke(
                caller,
                new InvokeVirtual(arrayListIterator.getRef(), list, List.of()),
                iterator);
        Invoke next = new Invoke(
                caller,
                new InvokeVirtual(iteratorNext.getRef(), iterator, List.of()),
                result);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, bindIterator),
                arrayListIterator.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, next),
                iteratorNext.getRef(),
                context));
        assertTrue(solver.pointsToOf(context, result).isEmpty());

        solver.seedVarPointsTo(context, value, valueObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add),
                arrayListAdd.getRef(),
                context));

        assertEquals(Set.of(valueObj), solver.pointsToOf(context, result).getObjects());
    }

    @Test
    void iteratorNextKeepsIteratorVarsSeparatedEvenIfTheyShareOneIteratorObject() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod arrayListAdd = hierarchy.getMethod(
                "<java.util.ArrayList: boolean add(java.lang.Object)>");
        JMethod arrayListIterator = hierarchy.getMethod(
                "<java.util.ArrayList: java.util.Iterator iterator()>");
        JMethod iteratorNext = hierarchy.getMethod(
                "<java.util.Iterator: java.lang.Object next()>");

        assertNotNull(arrayListAdd);
        assertNotNull(arrayListIterator);
        assertNotNull(iteratorNext);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("IteratorAliasCaller", "driveIteratorAliasBinding");
        Type arrayListType = World.get().getTypeSystem().getClassType("java.util.ArrayList");
        Type iteratorType = World.get().getTypeSystem().getClassType("java.util.Iterator");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var list1 = new Var(caller, "list1", arrayListType, 0);
        Var list2 = new Var(caller, "list2", arrayListType, 1);
        Var value1 = new Var(caller, "value1", objectType, 2);
        Var value2 = new Var(caller, "value2", objectType, 3);
        Var iterator1 = new Var(caller, "iterator1", iteratorType, 4);
        Var iterator2 = new Var(caller, "iterator2", iteratorType, 5);
        Var result1 = new Var(caller, "result1", objectType, 6);
        Var result2 = new Var(caller, "result2", objectType, 7);

        CSObj listObj1 = solver.newObject("list-1", arrayListType);
        CSObj listObj2 = solver.newObject("list-2", arrayListType);
        CSObj valueObj1 = solver.newObject("value-1", objectType);
        CSObj valueObj2 = solver.newObject("value-2", objectType);
        CSObj sharedIteratorObj = solver.newObject("iterator-shared", iteratorType);

        solver.seedVarPointsTo(context, list1, listObj1);
        solver.seedVarPointsTo(context, list2, listObj2);
        solver.seedVarPointsTo(context, value1, valueObj1);
        solver.seedVarPointsTo(context, value2, valueObj2);
        solver.seedVarPointsTo(context, iterator1, sharedIteratorObj);
        solver.seedVarPointsTo(context, iterator2, sharedIteratorObj);

        Invoke add1 = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list1, List.of(value1)));
        Invoke add2 = new Invoke(caller, new InvokeVirtual(arrayListAdd.getRef(), list2, List.of(value2)));
        Invoke bindIterator1 = new Invoke(
                caller,
                new InvokeVirtual(arrayListIterator.getRef(), list1, List.of()),
                iterator1);
        Invoke bindIterator2 = new Invoke(
                caller,
                new InvokeVirtual(arrayListIterator.getRef(), list2, List.of()),
                iterator2);
        Invoke next1 = new Invoke(
                caller,
                new InvokeVirtual(iteratorNext.getRef(), iterator1, List.of()),
                result1);
        Invoke next2 = new Invoke(
                caller,
                new InvokeVirtual(iteratorNext.getRef(), iterator2, List.of()),
                result2);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add1),
                arrayListAdd.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, add2),
                arrayListAdd.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, bindIterator1),
                arrayListIterator.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, bindIterator2),
                arrayListIterator.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, next1),
                iteratorNext.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, next2),
                iteratorNext.getRef(),
                context));

        assertEquals(Set.of(valueObj1), solver.pointsToOf(context, result1).getObjects());
        assertEquals(Set.of(valueObj2), solver.pointsToOf(context, result2).getObjects());
    }

    private static JMethod newMethod(String className, String methodName) {
        JClass owner = new JClass(DUMMY_LOADER, className);
        return new JMethod(
                owner,
                methodName,
                Set.of(Modifier.PUBLIC),
                List.of(),
                VoidType.VOID,
                List.of(),
                null,
                AnnotationHolder.emptyHolder(),
                null,
                null,
                methodName);
    }

    private static Var newConstStringVar(JMethod owner, String name, int index, String value) {
        Type stringType = World.get().getTypeSystem().getClassType("java.lang.String");
        return new Var(owner, name, stringType, index, StringLiteral.get(value), true);
    }

    private static final JClassLoader DUMMY_LOADER = new JClassLoader() {
        @Override
        public JClass loadClass(String name) {
            return new JClass(this, name);
        }

        @Override
        public Collection<JClass> getLoadedClasses() {
            return List.of();
        }
    };

    private static final class RecordingSolver implements Solver {

        private final CSManager csManager = new MapBasedCSManager();

        private final PointsToSetFactory pointsToSetFactory =
                new PointsToSetFactory(csManager.getObjectIndexer());

        private final Map<Pointer, PointsToSet> pointsToSets = Maps.newMap();

        private void seedVarPointsTo(Context context, Var var, CSObj obj) {
            addPointsTo(csManager.getCSVar(context, var), obj);
        }

        private PointsToSet pointsToOf(Context context, Var var) {
            return getPointsToSetOf(csManager.getCSVar(context, var));
        }

        private CSObj newObject(String allocation, Type type) {
            Obj obj = new MockObj(Descriptor.ENTRY_DESC, allocation, type, null, true);
            return csManager.getCSObj(new TrieContext.Factory<>().getEmptyContext(), obj);
        }

        @Override
        public AnalysisOptions getOptions() {
            throw unsupported();
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
            return pointsToSets.computeIfAbsent(pointer, __ -> pointsToSetFactory.make());
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
            getPointsToSetOf(pointer).addAll(pts);
        }

        @Override
        public void addPointsTo(Pointer pointer, CSObj csObj) {
            getPointsToSetOf(pointer).addObject(csObj);
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
