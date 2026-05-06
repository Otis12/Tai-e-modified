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
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
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
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.VoidType;
import pascal.taie.util.collection.Maps;

import java.lang.reflect.Field;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class QuerySummaryConnectivityTest {

    private static final String CLASSPATH = "src/test/resources/world";

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-pp", "-cp", CLASSPATH, "--input-classes",
                "MbgCriteriaFixture,MbgExample,MbgGeneratedCriteria,MbgCriteria,"
                        + "MbgCriterion,MbgMapper,MbgRecord,MbgCaller,"
                        + "MbgInheritedExample,MbgInheritedGeneratedCriteria,"
                        + "MbgInheritedCriteria,MbgInheritedMapper,MbgInheritedCaller,"
                        + "MyBatisPlusQueryFixture,MbpEntity,MbpMapper,MbpService,"
                        + "GridBinderQueryFixture,GridBinder,GridBinderCaller,"
                        + "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper,"
                        + "com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper,"
                        + "com.baomidou.mybatisplus.core.toolkit.Wrappers,"
                        + "com.baomidou.mybatisplus.core.toolkit.support.SFunction");
    }

    @AfterAll
    static void resetWorld() {
        World.reset();
    }

    @Test
    void queryBuilderMethodsAreRegisteredWithoutIgnoringBodies() {
        SummaryManager manager = new SummaryManager(new RecordingSolver());
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod createCriteria = hierarchy.getMethod(
                "<MbgExample: MbgCriteria createCriteria()>");
        JMethod andIdEqualTo = hierarchy.getMethod(
                "<MbgGeneratedCriteria: MbgCriteria andIdEqualTo(java.lang.Object)>");
        JMethod updateByExampleSelective = hierarchy.getMethod(
                "<MbgMapper: void updateByExampleSelective(java.lang.Object,MbgExample)>");

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);
        assertNotNull(updateByExampleSelective);

        assertTrue(manager.hasSummary(createCriteria.getRef()));
        assertTrue(manager.hasSummary(andIdEqualTo.getRef()));
        assertTrue(manager.hasSummary(updateByExampleSelective.getRef()));
        assertTrue(manager.hasQuerySummary(createCriteria.getRef()));
        assertTrue(manager.hasQuerySummary(andIdEqualTo.getRef()));
        assertTrue(manager.hasQuerySummary(updateByExampleSelective.getRef()));

        assertFalse(manager.getSummarizedMethods().contains(createCriteria));
        assertFalse(manager.getSummarizedMethods().contains(andIdEqualTo));
        assertFalse(manager.getSummarizedMethods().contains(updateByExampleSelective));
    }

    @Test
    void criteriaQueryValuesFlowToByExampleConsumer() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod createCriteria = hierarchy.getMethod(
                "<MbgExample: MbgCriteria createCriteria()>");
        JMethod andIdEqualTo = hierarchy.getMethod(
                "<MbgGeneratedCriteria: MbgCriteria andIdEqualTo(java.lang.Object)>");
        JMethod updateByExampleSelective = hierarchy.getMethod(
                "<MbgMapper: void updateByExampleSelective(java.lang.Object,MbgExample)>");

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);
        assertNotNull(updateByExampleSelective);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "directQueryFlow");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example = new Var(caller, "example", exampleType, 0);
        Var criteria = new Var(caller, "criteria", criteriaType, 1);
        Var value = new Var(caller, "value", objectType, 2);
        Var record = new Var(caller, "record", objectType, 3);
        Var mapper = new Var(caller, "mapper", mapperType, 4);

        CSObj exampleObj = solver.newObject("example-1", exampleType);
        CSObj criteriaObj = solver.newObject("criteria-1", criteriaType);
        CSObj valueObj = solver.newObject("value-1", objectType);
        CSObj recordObj = solver.newObject("record-1", objectType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, value, valueObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke create = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example, List.of()),
                criteria);
        Invoke and = new Invoke(
                caller,
                new InvokeVirtual(andIdEqualTo.getRef(), criteria, List.of(value)),
                criteria);
        Invoke update = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record, example)));

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and),
                andIdEqualTo.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, update),
                updateByExampleSelective.getRef(),
                context));

        assertTrue(solver.pointsToOf(context, example).getObjects().contains(valueObj));
    }

    @Test
    void queryWriteDoesNotBackfillExistingReadSiteUntilDirtyReadReplay() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod createCriteria = hierarchy.getMethod(
                "<MbgExample: MbgCriteria createCriteria()>");
        JMethod andIdEqualTo = hierarchy.getMethod(
                "<MbgGeneratedCriteria: MbgCriteria andIdEqualTo(java.lang.Object)>");
        JMethod updateByExampleSelective = hierarchy.getMethod(
                "<MbgMapper: void updateByExampleSelective(java.lang.Object,MbgExample)>");

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);
        assertNotNull(updateByExampleSelective);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "dirtyReadReplay");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example = new Var(caller, "example", exampleType, 0);
        Var criteria = new Var(caller, "criteria", criteriaType, 1);
        Var value = new Var(caller, "value", objectType, 2);
        Var record = new Var(caller, "record", objectType, 3);
        Var mapper = new Var(caller, "mapper", mapperType, 4);

        CSObj exampleObj = solver.newObject("example-1", exampleType);
        CSObj criteriaObj = solver.newObject("criteria-1", criteriaType);
        CSObj valueObj = solver.newObject("value-1", objectType);
        CSObj recordObj = solver.newObject("record-1", objectType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke create = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example, List.of()),
                criteria);
        Invoke and = new Invoke(
                caller,
                new InvokeVirtual(andIdEqualTo.getRef(), criteria, List.of(value)),
                criteria);
        Invoke update = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record, example)));

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, update),
                updateByExampleSelective.getRef(),
                context));

        solver.seedVarPointsTo(context, value, valueObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and),
                andIdEqualTo.getRef(),
                context));
        assertFalse(
                solver.pointsToOf(context, example).getObjects().contains(valueObj),
                "query writes should only update state; they should not backfill historical read sites inline");

        assertTrue(manager.reapplyDirtyQueryReadSites());
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(valueObj),
                "dirty query read-site replay should pull the stored values into the registered consumer");
    }

    @Test
    void indexedQueryReplayHandlesLateCriterionValue() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod createCriteria = hierarchy.getMethod(
                "<MbgExample: MbgCriteria createCriteria()>");
        JMethod andIdEqualTo = hierarchy.getMethod(
                "<MbgGeneratedCriteria: MbgCriteria andIdEqualTo(java.lang.Object)>");
        JMethod updateByExampleSelective = hierarchy.getMethod(
                "<MbgMapper: void updateByExampleSelective(java.lang.Object,MbgExample)>");

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);
        assertNotNull(updateByExampleSelective);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "indexedReplay");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example = new Var(caller, "example", exampleType, 0);
        Var criteria = new Var(caller, "criteria", criteriaType, 1);
        Var value = new Var(caller, "value", objectType, 2);
        Var record = new Var(caller, "record", objectType, 3);
        Var mapper = new Var(caller, "mapper", mapperType, 4);

        CSObj exampleObj = solver.newObject("example-1", exampleType);
        CSObj criteriaObj = solver.newObject("criteria-1", criteriaType);
        CSObj valueObj = solver.newObject("value-1", objectType);
        CSObj recordObj = solver.newObject("record-1", objectType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke create = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example, List.of()),
                criteria);
        Invoke and = new Invoke(
                caller,
                new InvokeVirtual(andIdEqualTo.getRef(), criteria, List.of(value)),
                criteria);
        Invoke update = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record, example)));

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, update),
                updateByExampleSelective.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and),
                andIdEqualTo.getRef(),
                context));
        assertFalse(solver.pointsToOf(context, example).getObjects().contains(valueObj));

        solver.seedVarPointsTo(context, value, valueObj);
        assertTrue(manager.reapplyRegisteredQuerySummaries());
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(valueObj),
                "indexed query-summary replay should revisit late value arrivals without a global callsite scan");
    }

    @Test
    void mergedCriteriaReceiverDoesNotLeakAcrossDistinctExamples() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod createCriteria = hierarchy.getMethod(
                "<MbgExample: MbgCriteria createCriteria()>");
        JMethod andIdEqualTo = hierarchy.getMethod(
                "<MbgGeneratedCriteria: MbgCriteria andIdEqualTo(java.lang.Object)>");
        JMethod updateByExampleSelective = hierarchy.getMethod(
                "<MbgMapper: void updateByExampleSelective(java.lang.Object,MbgExample)>");

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);
        assertNotNull(updateByExampleSelective);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "mergedCriteriaReceiverLeak");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example1 = new Var(caller, "example1", exampleType, 0);
        Var example2 = new Var(caller, "example2", exampleType, 1);
        Var criteria1 = new Var(caller, "criteria1", criteriaType, 2);
        Var criteria2 = new Var(caller, "criteria2", criteriaType, 3);
        Var value = new Var(caller, "value", objectType, 4);
        Var record1 = new Var(caller, "record1", objectType, 5);
        Var record2 = new Var(caller, "record2", objectType, 6);
        Var mapper = new Var(caller, "mapper", mapperType, 7);

        CSObj exampleObj1 = solver.newObject("example-1", exampleType);
        CSObj exampleObj2 = solver.newObject("example-2", exampleType);
        CSObj mergedCriteriaObj = solver.newObject("criteria-merged", criteriaType);
        CSObj valueObj = solver.newObject("value-1", objectType);
        CSObj recordObj1 = solver.newObject("record-1", objectType);
        CSObj recordObj2 = solver.newObject("record-2", objectType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example1, exampleObj1);
        solver.seedVarPointsTo(context, example2, exampleObj2);
        solver.seedVarPointsTo(context, criteria1, mergedCriteriaObj);
        solver.seedVarPointsTo(context, criteria2, mergedCriteriaObj);
        solver.seedVarPointsTo(context, value, valueObj);
        solver.seedVarPointsTo(context, record1, recordObj1);
        solver.seedVarPointsTo(context, record2, recordObj2);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke create1 = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example1, List.of()),
                criteria1);
        Invoke create2 = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example2, List.of()),
                criteria2);
        Invoke and1 = new Invoke(
                caller,
                new InvokeVirtual(andIdEqualTo.getRef(), criteria1, List.of(value)),
                criteria1);
        Invoke update1 = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record1, example1)));
        Invoke update2 = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record2, example2)));

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create1),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create2),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and1),
                andIdEqualTo.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, update1),
                updateByExampleSelective.getRef(),
                context));

        assertTrue(
                solver.pointsToOf(context, example1).getObjects().contains(valueObj),
                "the owning Example should still receive its own criterion value");
        assertFalse(
                solver.pointsToOf(context, example2).getObjects().contains(valueObj),
                "before reading example2, no value should appear on the unrelated Example variable");

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, update2),
                updateByExampleSelective.getRef(),
                context));

        assertFalse(
                solver.pointsToOf(context, example2).getObjects().contains(valueObj),
                "criterion values written through criteria1 must not leak into example2 "
                        + "just because PTA merged the underlying Criteria receiver object");
    }

    @Test
    void hasSummaryCachesInheritedCriteriaLookupResults() {
        SummaryManager manager = new SummaryManager(new RecordingSolver());
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod generatedAndIdEqualTo = hierarchy.getMethod(
                "<MbgInheritedGeneratedCriteria: MbgInheritedCriteria andIdEqualTo(java.lang.Object)>");
        assertNotNull(generatedAndIdEqualTo);

        Type criteriaType = generatedAndIdEqualTo.getDeclaringClass().getType();
        MethodRef inheritedCallRef = MethodRef.get(
                ((ClassType) criteriaType).getJClass(),
                generatedAndIdEqualTo.getName(),
                generatedAndIdEqualTo.getParamTypes(),
                generatedAndIdEqualTo.getReturnType(),
                generatedAndIdEqualTo.isStatic());

        assertTrue(manager.hasSummary(inheritedCallRef));
        assertTrue(manager.hasQuerySummary(inheritedCallRef));
        assertTrue(resolvedSummaryMethodRefCache(manager).containsKey(inheritedCallRef));
        assertTrue(summaryLookupCache(manager).containsKey(inheritedCallRef));
        assertTrue(
                generatedAndIdEqualTo.getRef().equals(
                        resolvedSummaryMethodRefCache(manager).get(inheritedCallRef)));
    }

    @Test
    void reapplyRegisteredQuerySummariesReplaysTrackedInheritedCriteriaCallSites() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod createCriteria = hierarchy.getMethod(
                "<MbgInheritedExample: MbgInheritedCriteria createCriteria()>");
        JMethod generatedAndIdEqualTo = hierarchy.getMethod(
                "<MbgInheritedGeneratedCriteria: MbgInheritedCriteria andIdEqualTo(java.lang.Object)>");
        JMethod updateByExampleSelective = hierarchy.getMethod(
                "<MbgInheritedMapper: void updateByExampleSelective(java.lang.Object,MbgInheritedExample)>");

        assertNotNull(createCriteria);
        assertNotNull(generatedAndIdEqualTo);
        assertNotNull(updateByExampleSelective);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "inheritedIndexedReplay");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example = new Var(caller, "example", exampleType, 0);
        Var criteria = new Var(caller, "criteria", criteriaType, 1);
        Var value = new Var(caller, "value", objectType, 2);
        Var record = new Var(caller, "record", objectType, 3);
        Var mapper = new Var(caller, "mapper", mapperType, 4);

        MethodRef inheritedCallRef = MethodRef.get(
                ((ClassType) criteriaType).getJClass(),
                generatedAndIdEqualTo.getName(),
                generatedAndIdEqualTo.getParamTypes(),
                generatedAndIdEqualTo.getReturnType(),
                generatedAndIdEqualTo.isStatic());

        CSObj exampleObj = solver.newObject("inherited-example-1", exampleType);
        CSObj criteriaObj = solver.newObject("inherited-criteria-1", criteriaType);
        CSObj valueObj = solver.newObject("inherited-value-1", objectType);
        CSObj recordObj = solver.newObject("inherited-record-1", objectType);
        CSObj mapperObj = solver.newObject("inherited-mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke create = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example, List.of()),
                criteria);
        Invoke and = new Invoke(
                caller,
                new InvokeVirtual(inheritedCallRef, criteria, List.of(value)),
                criteria);
        Invoke update = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record, example)));

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, update),
                updateByExampleSelective.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and),
                generatedAndIdEqualTo.getRef(),
                context));
        assertFalse(solver.pointsToOf(context, example).getObjects().contains(valueObj));

        solver.seedVarPointsTo(context, value, valueObj);
        assertTrue(manager.reapplyRegisteredQuerySummaries());
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(valueObj),
                "tracked inherited callsites should replay through the raw subclass-view method ref");
    }

    @Test
    void myBatisPlusQueryMethodsAreRegistered() {
        SummaryManager manager = new SummaryManager(new RecordingSolver());
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod eq = hierarchy.getMethod(
                "<com.baomidou.mybatisplus.core.conditions.query.QueryWrapper: "
                        + "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper "
                        + "eq(java.lang.String,java.lang.Object)>");
        JMethod last = hierarchy.getMethod(
                "<com.baomidou.mybatisplus.core.conditions.query.QueryWrapper: "
                        + "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper "
                        + "last(java.lang.String)>");
        JMethod lambdaEq = hierarchy.getMethod(
                "<com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper: "
                        + "com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper "
                        + "eq(com.baomidou.mybatisplus.core.toolkit.support.SFunction,java.lang.Object)>");
        JMethod selectOne = hierarchy.getMethod(
                "<MbpMapper: java.lang.Object "
                        + "selectOne(com.baomidou.mybatisplus.core.conditions.query.QueryWrapper)>");

        assertNotNull(eq);
        assertNotNull(last);
        assertNotNull(lambdaEq);
        assertNotNull(selectOne);

        assertTrue(manager.hasSummary(eq.getRef()));
        assertTrue(manager.hasSummary(last.getRef()));
        assertTrue(manager.hasSummary(lambdaEq.getRef()));
        assertTrue(manager.hasSummary(selectOne.getRef()));
        assertTrue(manager.hasQuerySummary(eq.getRef()));
        assertTrue(manager.hasQuerySummary(last.getRef()));
        assertTrue(manager.hasQuerySummary(lambdaEq.getRef()));
        assertTrue(manager.hasQuerySummary(selectOne.getRef()));
    }

    @Test
    void myBatisPlusQueryWrapperFlowsConditionValuesToReadSite() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod eq = hierarchy.getMethod(
                "<com.baomidou.mybatisplus.core.conditions.query.QueryWrapper: "
                        + "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper "
                        + "eq(java.lang.String,java.lang.Object)>");
        JMethod selectOne = hierarchy.getMethod(
                "<MbpMapper: java.lang.Object "
                        + "selectOne(com.baomidou.mybatisplus.core.conditions.query.QueryWrapper)>");

        assertNotNull(eq);
        assertNotNull(selectOne);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("QueryWrapperCaller", "queryWrapperFlow");
        Type wrapperType = eq.getDeclaringClass().getType();
        Type mapperType = selectOne.getDeclaringClass().getType();
        Type stringType = World.get().getTypeSystem().getClassType("java.lang.String");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var wrapper = new Var(caller, "wrapper", wrapperType, 0);
        Var column = new Var(caller, "column", stringType, 1);
        Var value = new Var(caller, "value", objectType, 2);
        Var mapper = new Var(caller, "mapper", mapperType, 3);
        Var result = new Var(caller, "result", objectType, 4);

        CSObj wrapperObj = solver.newObject("mbp-wrapper-1", wrapperType);
        CSObj columnObj = solver.newObject("mbp-column-1", stringType);
        CSObj valueObj = solver.newObject("mbp-value-1", objectType);
        CSObj mapperObj = solver.newObject("mbp-mapper-1", mapperType);

        solver.seedVarPointsTo(context, wrapper, wrapperObj);
        solver.seedVarPointsTo(context, column, columnObj);
        solver.seedVarPointsTo(context, value, valueObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke eqInvoke = new Invoke(
                caller,
                new InvokeVirtual(eq.getRef(), wrapper, List.of(column, value)),
                wrapper);
        Invoke selectInvoke = new Invoke(
                caller,
                new InvokeVirtual(selectOne.getRef(), mapper, List.of(wrapper)),
                result);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, eqInvoke),
                eq.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, selectInvoke),
                selectOne.getRef(),
                context));

        assertTrue(solver.pointsToOf(context, result).getObjects().contains(valueObj));
        assertTrue(solver.pointsToOf(context, wrapper).getObjects().contains(valueObj));
    }

    @Test
    void myBatisPlusQueryMetaFlowsToReadSite() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod last = hierarchy.getMethod(
                "<com.baomidou.mybatisplus.core.conditions.query.QueryWrapper: "
                        + "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper "
                        + "last(java.lang.String)>");
        JMethod selectOne = hierarchy.getMethod(
                "<MbpMapper: java.lang.Object "
                        + "selectOne(com.baomidou.mybatisplus.core.conditions.query.QueryWrapper)>");

        assertNotNull(last);
        assertNotNull(selectOne);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("QueryWrapperCaller", "queryMetaFlow");
        Type wrapperType = last.getDeclaringClass().getType();
        Type mapperType = selectOne.getDeclaringClass().getType();
        Type stringType = World.get().getTypeSystem().getClassType("java.lang.String");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var wrapper = new Var(caller, "wrapper", wrapperType, 0);
        Var sql = new Var(caller, "sql", stringType, 1);
        Var mapper = new Var(caller, "mapper", mapperType, 2);
        Var result = new Var(caller, "result", objectType, 3);

        CSObj wrapperObj = solver.newObject("mbp-wrapper-2", wrapperType);
        CSObj sqlObj = solver.newObject("mbp-sql-1", stringType);
        CSObj mapperObj = solver.newObject("mbp-mapper-2", mapperType);

        solver.seedVarPointsTo(context, wrapper, wrapperObj);
        solver.seedVarPointsTo(context, sql, sqlObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke lastInvoke = new Invoke(
                caller,
                new InvokeVirtual(last.getRef(), wrapper, List.of(sql)),
                wrapper);
        Invoke selectInvoke = new Invoke(
                caller,
                new InvokeVirtual(selectOne.getRef(), mapper, List.of(wrapper)),
                result);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, lastInvoke),
                last.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, selectInvoke),
                selectOne.getRef(),
                context));

        assertTrue(
                solver.pointsToOf(context, result).getObjects().contains(sqlObj),
                "QB_WRITE_META values should remain visible at the query read site");
    }

    @Test
    void myBatisPlusLambdaQueryWrapperFlowsConditionValuesToReadSite() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod lambdaEq = hierarchy.getMethod(
                "<com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper: "
                        + "com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper "
                        + "eq(com.baomidou.mybatisplus.core.toolkit.support.SFunction,java.lang.Object)>");
        JMethod selectOne = hierarchy.getMethod(
                "<MbpMapper: java.lang.Object "
                        + "selectOne(com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper)>");

        assertNotNull(lambdaEq);
        assertNotNull(selectOne);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("LambdaQueryWrapperCaller", "lambdaQueryWrapperFlow");
        Type wrapperType = lambdaEq.getDeclaringClass().getType();
        Type functionType = hierarchy.getClass(
                "com.baomidou.mybatisplus.core.toolkit.support.SFunction").getType();
        Type mapperType = selectOne.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var wrapper = new Var(caller, "wrapper", wrapperType, 0);
        Var getter = new Var(caller, "getter", functionType, 1);
        Var value = new Var(caller, "value", objectType, 2);
        Var mapper = new Var(caller, "mapper", mapperType, 3);
        Var result = new Var(caller, "result", objectType, 4);

        CSObj wrapperObj = solver.newObject("mbp-lambda-wrapper-1", wrapperType);
        CSObj getterObj = solver.newObject("mbp-getter-1", functionType);
        CSObj valueObj = solver.newObject("mbp-lambda-value-1", objectType);
        CSObj mapperObj = solver.newObject("mbp-lambda-mapper-1", mapperType);

        solver.seedVarPointsTo(context, wrapper, wrapperObj);
        solver.seedVarPointsTo(context, getter, getterObj);
        solver.seedVarPointsTo(context, value, valueObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke eqInvoke = new Invoke(
                caller,
                new InvokeVirtual(lambdaEq.getRef(), wrapper, List.of(getter, value)),
                wrapper);
        Invoke selectInvoke = new Invoke(
                caller,
                new InvokeVirtual(selectOne.getRef(), mapper, List.of(wrapper)),
                result);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, eqInvoke),
                lambdaEq.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, selectInvoke),
                selectOne.getRef(),
                context));

        assertTrue(solver.pointsToOf(context, result).getObjects().contains(valueObj));
        assertTrue(solver.pointsToOf(context, wrapper).getObjects().contains(valueObj));
    }

    @Test
    void gridBinderMethodsAreRegistered() {
        SummaryManager manager = new SummaryManager(new RecordingSolver());
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod setWrapper = hierarchy.getMethod(
                "<GridBinder: void setWrapper(" +
                        "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper)>");
        JMethod queryPage = hierarchy.getMethod(
                "<GridBinder: java.lang.Object queryPage()>");

        assertNotNull(setWrapper);
        assertNotNull(queryPage);

        assertTrue(manager.hasSummary(setWrapper.getRef()));
        assertTrue(manager.hasSummary(queryPage.getRef()));
        assertTrue(manager.hasQuerySummary(setWrapper.getRef()));
        assertTrue(manager.hasQuerySummary(queryPage.getRef()));
    }

    @Test
    void gridBinderQueryReadPullsValuesFromAttachedWrapper() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod eq = hierarchy.getMethod(
                "<com.baomidou.mybatisplus.core.conditions.query.QueryWrapper: "
                        + "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper "
                        + "eq(java.lang.String,java.lang.Object)>");
        JMethod setWrapper = hierarchy.getMethod(
                "<GridBinder: void setWrapper(" +
                        "com.baomidou.mybatisplus.core.conditions.query.QueryWrapper)>");
        JMethod queryPage = hierarchy.getMethod(
                "<GridBinder: java.lang.Object queryPage()>");

        assertNotNull(eq);
        assertNotNull(setWrapper);
        assertNotNull(queryPage);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("GridBinderCaller", "gridBinderFlow");
        Type wrapperType = eq.getDeclaringClass().getType();
        Type binderType = setWrapper.getDeclaringClass().getType();
        Type stringType = World.get().getTypeSystem().getClassType("java.lang.String");
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var wrapper = new Var(caller, "wrapper", wrapperType, 0);
        Var binder = new Var(caller, "binder", binderType, 1);
        Var column = new Var(caller, "column", stringType, 2);
        Var value = new Var(caller, "value", objectType, 3);
        Var result = new Var(caller, "result", objectType, 4);

        CSObj wrapperObj = solver.newObject("grid-wrapper-1", wrapperType);
        CSObj binderObj = solver.newObject("grid-binder-1", binderType);
        CSObj columnObj = solver.newObject("grid-column-1", stringType);
        CSObj valueObj = solver.newObject("grid-value-1", objectType);

        solver.seedVarPointsTo(context, wrapper, wrapperObj);
        solver.seedVarPointsTo(context, binder, binderObj);
        solver.seedVarPointsTo(context, column, columnObj);
        solver.seedVarPointsTo(context, value, valueObj);

        Invoke eqInvoke = new Invoke(
                caller,
                new InvokeVirtual(eq.getRef(), wrapper, List.of(column, value)),
                wrapper);
        Invoke setWrapperInvoke = new Invoke(
                caller,
                new InvokeVirtual(setWrapper.getRef(), binder, List.of(wrapper)));
        Invoke queryPageInvoke = new Invoke(
                caller,
                new InvokeVirtual(queryPage.getRef(), binder, List.of()),
                result);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, eqInvoke),
                eq.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setWrapperInvoke),
                setWrapper.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, queryPageInvoke),
                queryPage.getRef(),
                context));

        assertTrue(
                solver.pointsToOf(context, result).getObjects().contains(valueObj),
                "binder.queryPage() should pull wrapper slot values through QB_ATTACH + QB_READ");
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

    @SuppressWarnings("unchecked")
    private static Map<MethodRef, MethodRef> resolvedSummaryMethodRefCache(SummaryManager manager) {
        try {
            Field field = SummaryManager.class.getDeclaredField("resolvedSummaryMethodRefCache");
            field.setAccessible(true);
            return (Map<MethodRef, MethodRef>) field.get(manager);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("failed to inspect resolved summary method ref cache", e);
        }
    }

    @SuppressWarnings("unchecked")
    private static Map<MethodRef, ?> summaryLookupCache(SummaryManager manager) {
        try {
            Field field = SummaryManager.class.getDeclaredField("summaryLookupCache");
            field.setAccessible(true);
            return (Map<MethodRef, ?>) field.get(manager);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("failed to inspect summary lookup cache", e);
        }
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
        public void addStmts(CSMethod csMethod, Collection<pascal.taie.ir.stmt.Stmt> stmts) {
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
        public pascal.taie.analysis.pta.PointerAnalysisResult getResult() {
            throw unsupported();
        }

        private UnsupportedOperationException unsupported() {
            return new UnsupportedOperationException("not needed in query summary unit tests");
        }
    }
}
