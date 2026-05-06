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
import org.junit.jupiter.api.Disabled;
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
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.ClassType;
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

@Disabled("Legacy deferred/backfill criteria tests are superseded by lightweight query connectivity tests")
class SummaryManagerCriteriaExecutionTest {

    private static final String CLASSPATH = "src/test/resources/world";

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-pp", "-cp", CLASSPATH, "--input-classes",
                "MbgCriteriaFixture,MbgExample,MbgGeneratedCriteria,MbgCriteria,"
                        + "MbgCriterion,MbgMapper,MbgRecord,MbgCaller,"
                        + "MbgInheritedExample,MbgInheritedGeneratedCriteria,"
                        + "MbgInheritedCriteria,MbgInheritedMapper,MbgInheritedCaller");
    }

    @AfterAll
    static void resetWorld() {
        World.reset();
    }

    @Test
    void criteriaBuilderMethodsAreRegisteredWithoutIgnoringBodies() {
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

        assertFalse(manager.getSummarizedMethods().contains(createCriteria));
        assertFalse(manager.getSummarizedMethods().contains(andIdEqualTo));
        assertFalse(manager.getSummarizedMethods().contains(updateByExampleSelective));
    }

    @Test
    void criteriaValuesFlowToExampleArgumentAtByExampleConsumer() {
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
        JMethod caller = newMethod("CriteriaCaller", "driveSummaries");
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
    void byExampleConsumerBackfillsWhenCriterionValueArrivesLater() {
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
        JMethod caller = newMethod("CriteriaCaller", "deferredCriterionFlow");
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
        assertFalse(solver.pointsToOf(context, example).getObjects().contains(valueObj));

        solver.seedVarPointsTo(context, value, valueObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and),
                andIdEqualTo.getRef(),
                context));

        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(valueObj),
                "existing ByExample consumer should be backfilled when criterion values arrive later");
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

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "mergedCriteriaReceiver");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example1 = new Var(caller, "example1", exampleType, 0);
        Var example2 = new Var(caller, "example2", exampleType, 1);
        Var criteria1 = new Var(caller, "criteria1", criteriaType, 2);
        Var criteria2 = new Var(caller, "criteria2", criteriaType, 3);
        Var value = new Var(caller, "value", objectType, 4);

        CSObj exampleObj1 = solver.newObject("example-1", exampleType);
        CSObj exampleObj2 = solver.newObject("example-2", exampleType);
        CSObj mergedCriteriaObj = solver.newObject("criteria-merged", criteriaType);
        CSObj valueObj = solver.newObject("value-1", objectType);

        solver.seedVarPointsTo(context, example1, exampleObj1);
        solver.seedVarPointsTo(context, example2, exampleObj2);
        solver.seedVarPointsTo(context, criteria1, mergedCriteriaObj);
        solver.seedVarPointsTo(context, criteria2, mergedCriteriaObj);
        solver.seedVarPointsTo(context, value, valueObj);

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

        assertTrue(exampleValuesOf(manager, exampleObj1).getObjects().contains(valueObj));
        assertFalse(
                exampleValuesOf(manager, exampleObj2).getObjects().contains(valueObj),
                "criterion values should stay scoped to the Example that owns the builder variable, " +
                        "even when PTA merges the underlying Criteria receiver objects");
    }

    @Test
    void lateCreateCriteriaReapplyDoesNotReplayMergedCriteriaBucketAcrossExamples() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod createCriteria = hierarchy.getMethod(
                "<MbgExample: MbgCriteria createCriteria()>");
        JMethod andIdEqualTo = hierarchy.getMethod(
                "<MbgGeneratedCriteria: MbgCriteria andIdEqualTo(java.lang.Object)>");

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "lateMergedCriteriaReplay");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example1 = new Var(caller, "example1", exampleType, 0);
        Var example2 = new Var(caller, "example2", exampleType, 1);
        Var criteria1 = new Var(caller, "criteria1", criteriaType, 2);
        Var criteria2 = new Var(caller, "criteria2", criteriaType, 3);
        Var value1 = new Var(caller, "value1", objectType, 4);
        Var value2 = new Var(caller, "value2", objectType, 5);

        CSObj exampleObj1 = solver.newObject("example-1", exampleType);
        CSObj exampleObj2 = solver.newObject("example-2", exampleType);
        CSObj mergedCriteriaObj = solver.newObject("criteria-merged", criteriaType);
        CSObj valueObj1 = solver.newObject("value-1", objectType);
        CSObj valueObj2 = solver.newObject("value-2", objectType);

        solver.seedVarPointsTo(context, example1, exampleObj1);
        solver.seedVarPointsTo(context, example2, exampleObj2);
        solver.seedVarPointsTo(context, value1, valueObj1);
        solver.seedVarPointsTo(context, value2, valueObj2);

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
                new InvokeVirtual(andIdEqualTo.getRef(), criteria1, List.of(value1)),
                criteria1);
        Invoke and2 = new Invoke(
                caller,
                new InvokeVirtual(andIdEqualTo.getRef(), criteria2, List.of(value2)),
                criteria2);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create1),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create2),
                createCriteria.getRef(),
                context));

        solver.seedVarPointsTo(context, criteria1, mergedCriteriaObj);
        solver.seedVarPointsTo(context, criteria2, mergedCriteriaObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and1),
                andIdEqualTo.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and2),
                andIdEqualTo.getRef(),
                context));

        assertFalse(exampleValuesOf(manager, exampleObj1).getObjects().contains(valueObj1));
        assertFalse(exampleValuesOf(manager, exampleObj2).getObjects().contains(valueObj2));

        assertTrue(
                manager.reapplySummary(createCriteria.getRef()),
                "late createCriteria reapply should revisit both builder roots once the merged receiver object becomes available");
        assertTrue(
                exampleValuesOf(manager, exampleObj1).getObjects().contains(valueObj1),
                "replaying the first createCriteria should recover its own deferred criterion value");
        assertFalse(
                exampleValuesOf(manager, exampleObj1).getObjects().contains(valueObj2),
                "replaying the first createCriteria must not import values that were written through another merged builder variable");
        assertTrue(
                exampleValuesOf(manager, exampleObj2).getObjects().contains(valueObj2),
                "replaying the second createCriteria should recover its own deferred criterion value");
        assertFalse(
                exampleValuesOf(manager, exampleObj2).getObjects().contains(valueObj1),
                "replaying the second createCriteria must stay isolated from the first merged builder variable");
    }

    @Test
    void accessorAndCriteriaSummariesComposeIntoByExampleFlow() {
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
        JMethod setId = hierarchy.getMethod(
                "<MbgRecord: void setId(java.lang.Object)>");
        JMethod getId = hierarchy.getMethod(
                "<MbgRecord: java.lang.Object getId()>");

        assertNotNull(createCriteria);
        assertNotNull(andIdEqualTo);
        assertNotNull(updateByExampleSelective);
        assertNotNull(setId);
        assertNotNull(getId);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "accessorCriteriaChain");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type recordType = setId.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example = new Var(caller, "example", exampleType, 0);
        Var criteria = new Var(caller, "criteria", criteriaType, 1);
        Var orderId = new Var(caller, "orderId", objectType, 2);
        Var record = new Var(caller, "record", recordType, 3);
        Var extractedId = new Var(caller, "extractedId", objectType, 4);
        Var mapper = new Var(caller, "mapper", mapperType, 5);

        CSObj exampleObj = solver.newObject("example-1", exampleType);
        CSObj criteriaObj = solver.newObject("criteria-1", criteriaType);
        CSObj orderIdObj = solver.newObject("value-1", objectType);
        CSObj recordObj = solver.newObject("record-1", recordType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, orderId, orderIdObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        Invoke create = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example, List.of()),
                criteria);
        Invoke setter = new Invoke(
                caller,
                new InvokeVirtual(setId.getRef(), record, List.of(orderId)));
        Invoke getter = new Invoke(
                caller,
                new InvokeVirtual(getId.getRef(), record, List.of()),
                extractedId);
        Invoke and = new Invoke(
                caller,
                new InvokeVirtual(andIdEqualTo.getRef(), criteria, List.of(extractedId)),
                criteria);
        Invoke update = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record, example)));

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, create),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setter),
                setId.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getter),
                getId.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, and),
                andIdEqualTo.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, update),
                updateByExampleSelective.getRef(),
                context));

        assertTrue(
                solver.pointsToOf(context, extractedId).getObjects().contains(orderIdObj),
                "getter summary should read back the id written by the setter summary");
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(orderIdObj),
                "criteria summary should carry the getter result into the ByExample consumer");
    }

    @Test
    void reapplySummaryBackfillsCreateCriteriaWhenResultArrivesLate() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod caller = hierarchy.getMethod(
                "<MbgCaller: void drive(MbgExample,MbgRecord,java.lang.Object,MbgMapper)>");

        assertNotNull(caller);

        Invoke setIdCall = null;
        Invoke getIdCall = null;
        Invoke createCriteriaCall = null;
        Invoke andIdEqualToCall = null;
        Invoke updateByExampleCall = null;
        for (Stmt stmt : caller.getIR().getStmts()) {
            if (!(stmt instanceof Invoke invoke)) {
                continue;
            }
            String signature = invoke.getInvokeExp().getMethodRef().toString();
            if (signature.contains("setId")) {
                setIdCall = invoke;
            } else if (signature.contains("getId")) {
                getIdCall = invoke;
            } else if (signature.contains("createCriteria")) {
                createCriteriaCall = invoke;
            } else if (signature.contains("andIdEqualTo")) {
                andIdEqualToCall = invoke;
            } else if (signature.contains("updateByExampleSelective")) {
                updateByExampleCall = invoke;
            }
        }

        assertNotNull(setIdCall);
        assertNotNull(getIdCall);
        assertNotNull(createCriteriaCall);
        assertNotNull(andIdEqualToCall);
        assertNotNull(updateByExampleCall);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        Var example = caller.getIR().getParam(0);
        Var record = caller.getIR().getParam(1);
        Var orderId = caller.getIR().getParam(2);
        Var mapper = caller.getIR().getParam(3);
        Var criteria = createCriteriaCall.getResult();
        Var extractedId = getIdCall.getResult();
        Var criteriaReceiver = ((InvokeVirtual) andIdEqualToCall.getInvokeExp()).getBase();
        Var criterionValue = andIdEqualToCall.getInvokeExp().getArg(0);

        assertNotNull(criteria);
        assertNotNull(extractedId);
        assertNotNull(criteriaReceiver);
        assertNotNull(criterionValue);

        Type exampleType = example.getType();
        Type criteriaType = criteria.getType();
        Type recordType = record.getType();
        Type mapperType = mapper.getType();
        Type objectType = orderId.getType();

        CSObj exampleObj = solver.newObject("example-1", exampleType);
        CSObj criteriaObj = solver.newObject("criteria-1", criteriaType);
        CSObj orderIdObj = solver.newObject("value-1", objectType);
        CSObj recordObj = solver.newObject("record-1", recordType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, createCriteriaCall),
                createCriteriaCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, updateByExampleCall),
                updateByExampleCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(hasExampleLoadSite(manager, exampleObj),
                "ByExample consumer should register its example load site before the builder state is complete");

        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, criteriaReceiver, criteriaObj);
        solver.seedVarPointsTo(context, orderId, orderIdObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setIdCall),
                setIdCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getIdCall),
                getIdCall.getInvokeExp().getMethodRef(),
                context));
        // RecordingSolver does not model local copy edges in the caller IR,
        // so seed the invoke argument explicitly to isolate the summary logic.
        solver.seedVarPointsTo(context, criterionValue, orderIdObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, andIdEqualToCall),
                andIdEqualToCall.getInvokeExp().getMethodRef(),
                context));

        assertTrue(
                solver.pointsToOf(context, extractedId).getObjects().contains(orderIdObj),
                "getter summary should still recover the written id");
        assertFalse(
                solver.pointsToOf(context, example).getObjects().contains(orderIdObj),
                "without the example->criteria link, criterion values should not yet reach the ByExample consumer");

        assertTrue(
                manager.reapplySummary(createCriteriaCall.getInvokeExp().getMethodRef()),
                "phase-end reapply should revisit createCriteria once its result object becomes available");
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(orderIdObj),
                "reapplying createCriteria should restore the example->criteria link and backfill the registered ByExample consumer");
    }

    @Test
    void applySummaryBackfillsCreateCriteriaWhenResultArrivesLate() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod caller = hierarchy.getMethod(
                "<MbgCaller: void drive(MbgExample,MbgRecord,java.lang.Object,MbgMapper)>");

        assertNotNull(caller);

        Invoke setIdCall = null;
        Invoke getIdCall = null;
        Invoke createCriteriaCall = null;
        Invoke andIdEqualToCall = null;
        Invoke updateByExampleCall = null;
        for (Stmt stmt : caller.getIR().getStmts()) {
            if (!(stmt instanceof Invoke invoke)) {
                continue;
            }
            String signature = invoke.getInvokeExp().getMethodRef().toString();
            if (signature.contains("setId")) {
                setIdCall = invoke;
            } else if (signature.contains("getId")) {
                getIdCall = invoke;
            } else if (signature.contains("createCriteria")) {
                createCriteriaCall = invoke;
            } else if (signature.contains("andIdEqualTo")) {
                andIdEqualToCall = invoke;
            } else if (signature.contains("updateByExampleSelective")) {
                updateByExampleCall = invoke;
            }
        }

        assertNotNull(setIdCall);
        assertNotNull(getIdCall);
        assertNotNull(createCriteriaCall);
        assertNotNull(andIdEqualToCall);
        assertNotNull(updateByExampleCall);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        Var example = caller.getIR().getParam(0);
        Var record = caller.getIR().getParam(1);
        Var orderId = caller.getIR().getParam(2);
        Var mapper = caller.getIR().getParam(3);
        Var criteria = createCriteriaCall.getResult();
        Var extractedId = getIdCall.getResult();
        Var criteriaReceiver = ((InvokeVirtual) andIdEqualToCall.getInvokeExp()).getBase();
        Var criterionValue = andIdEqualToCall.getInvokeExp().getArg(0);

        assertNotNull(criteria);
        assertNotNull(extractedId);
        assertNotNull(criteriaReceiver);
        assertNotNull(criterionValue);

        Type exampleType = example.getType();
        Type criteriaType = criteria.getType();
        Type recordType = record.getType();
        Type mapperType = mapper.getType();
        Type objectType = orderId.getType();

        CSObj exampleObj = solver.newObject("example-1", exampleType);
        CSObj criteriaObj = solver.newObject("criteria-1", criteriaType);
        CSObj orderIdObj = solver.newObject("value-1", objectType);
        CSObj recordObj = solver.newObject("record-1", recordType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, createCriteriaCall),
                createCriteriaCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, updateByExampleCall),
                updateByExampleCall.getInvokeExp().getMethodRef(),
                context));

        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, criteriaReceiver, criteriaObj);
        solver.seedVarPointsTo(context, orderId, orderIdObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setIdCall),
                setIdCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getIdCall),
                getIdCall.getInvokeExp().getMethodRef(),
                context));
        // RecordingSolver does not model local copy edges in the caller IR,
        // so seed the invoke argument explicitly to isolate the summary logic.
        solver.seedVarPointsTo(context, criterionValue, orderIdObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, andIdEqualToCall),
                andIdEqualToCall.getInvokeExp().getMethodRef(),
                context));

        assertTrue(
                solver.pointsToOf(context, extractedId).getObjects().contains(orderIdObj),
                "getter summary should still recover the written id");
        assertTrue(criteriaValuesOf(manager, criteriaObj).getObjects().contains(orderIdObj),
                "criterion summary should store the extracted id on the Criteria receiver");
        assertFalse(
                solver.pointsToOf(context, example).getObjects().contains(orderIdObj),
                "without the example->criteria link, criterion values should not yet reach the ByExample consumer");

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, createCriteriaCall),
                createCriteriaCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(exampleValuesOf(manager, exampleObj).getObjects().contains(orderIdObj),
                "once createCriteria sees the late result object, the store should immediately expose the criterion value through the Example");
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(orderIdObj),
                "reapplying createCriteria via applySummary should restore the example->criteria link and backfill the registered ByExample consumer");
    }

    @Test
    void reapplySummaryMatchesBridgeCriteriaCallSites() {
        RecordingSolver solver = new RecordingSolver();
        SummaryManager manager = new SummaryManager(solver);
        manager.initHardcodedSummaries();

        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod caller = hierarchy.getMethod(
                "<MbgCaller: void drive(MbgExample,MbgRecord,java.lang.Object,MbgMapper)>");
        JMethod generatedAndIdEqualTo = hierarchy.getMethod(
                "<MbgGeneratedCriteria: MbgCriteria andIdEqualTo(java.lang.Object)>");

        assertNotNull(caller);
        assertNotNull(generatedAndIdEqualTo);

        Invoke setIdCall = null;
        Invoke getIdCall = null;
        Invoke createCriteriaCall = null;
        Invoke andIdEqualToCall = null;
        Invoke updateByExampleCall = null;
        for (Stmt stmt : caller.getIR().getStmts()) {
            if (!(stmt instanceof Invoke invoke)) {
                continue;
            }
            String signature = invoke.getInvokeExp().getMethodRef().toString();
            if (signature.contains("setId")) {
                setIdCall = invoke;
            } else if (signature.contains("getId")) {
                getIdCall = invoke;
            } else if (signature.contains("createCriteria")) {
                createCriteriaCall = invoke;
            } else if (signature.contains("andIdEqualTo")) {
                andIdEqualToCall = invoke;
            } else if (signature.contains("updateByExampleSelective")) {
                updateByExampleCall = invoke;
            }
        }

        assertNotNull(setIdCall);
        assertNotNull(getIdCall);
        assertNotNull(createCriteriaCall);
        assertNotNull(andIdEqualToCall);
        assertNotNull(updateByExampleCall);
        assertTrue(manager.hasSummary(andIdEqualToCall.getInvokeExp().getMethodRef()));

        Context context = new TrieContext.Factory<>().getEmptyContext();
        Var example = caller.getIR().getParam(0);
        Var record = caller.getIR().getParam(1);
        Var orderId = caller.getIR().getParam(2);
        Var mapper = caller.getIR().getParam(3);
        Var criteria = createCriteriaCall.getResult();
        Var extractedId = getIdCall.getResult();
        Var criteriaReceiver = ((InvokeVirtual) andIdEqualToCall.getInvokeExp()).getBase();
        Var criterionValue = andIdEqualToCall.getInvokeExp().getArg(0);

        assertNotNull(criteria);
        assertNotNull(extractedId);
        assertNotNull(criteriaReceiver);
        assertNotNull(criterionValue);

        Type exampleType = example.getType();
        Type criteriaType = criteria.getType();
        Type recordType = record.getType();
        Type mapperType = mapper.getType();
        Type objectType = orderId.getType();

        CSObj exampleObj = solver.newObject("example-1", exampleType);
        CSObj criteriaObj = solver.newObject("criteria-1", criteriaType);
        CSObj orderIdObj = solver.newObject("value-1", objectType);
        CSObj recordObj = solver.newObject("record-1", recordType);
        CSObj mapperObj = solver.newObject("mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, criteriaReceiver, criteriaObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, createCriteriaCall),
                createCriteriaCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(criteriaVarExamplesOf(manager, solver, context, criteria).getObjects().contains(exampleObj),
                "bridge createCriteria should bind its result variable to the owning Example");
        assertTrue(criteriaVarExamplesOf(manager, solver, context, criteriaReceiver).getObjects().contains(exampleObj),
                "bridge receiver should inherit the createCriteria Example binding before late reapply");
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, updateByExampleCall),
                updateByExampleCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, andIdEqualToCall),
                andIdEqualToCall.getInvokeExp().getMethodRef(),
                context));
        assertFalse(solver.pointsToOf(context, example).getObjects().contains(orderIdObj));

        solver.seedVarPointsTo(context, orderId, orderIdObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setIdCall),
                setIdCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getIdCall),
                getIdCall.getInvokeExp().getMethodRef(),
                context));
        assertTrue(solver.pointsToOf(context, extractedId).getObjects().contains(orderIdObj));
        solver.seedVarPointsTo(context, criterionValue, orderIdObj);

        assertTrue(
                manager.reapplySummary(andIdEqualToCall.getInvokeExp().getMethodRef()),
                "phase-end reapply should recognize inherited criteria call sites");
        assertTrue(criteriaValuesOf(manager, criteriaObj).getObjects().contains(orderIdObj),
                "bridge reapply should store the late value on the Criteria receiver");
        assertTrue(exampleValuesOf(manager, exampleObj).getObjects().contains(orderIdObj),
                "bridge reapply should expose the late value through the linked Example");
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(orderIdObj),
                "reapplySummary should backfill the ByExample consumer even when the call site method ref is inherited");
    }

    @Test
    void reapplySummaryMatchesInheritedCriteriaCallSites() {
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
        JMethod setId = hierarchy.getMethod("<MbgRecord: void setId(java.lang.Object)>");
        JMethod getId = hierarchy.getMethod("<MbgRecord: java.lang.Object getId()>");

        assertNotNull(createCriteria);
        assertNotNull(generatedAndIdEqualTo);
        assertNotNull(updateByExampleSelective);
        assertNotNull(setId);
        assertNotNull(getId);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "reapplyInherited");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type recordType = setId.getDeclaringClass().getType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example = new Var(caller, "example", exampleType, 0);
        Var criteria = new Var(caller, "criteria", criteriaType, 1);
        Var criterionValue = new Var(caller, "criterionValue", objectType, 2);
        Var record = new Var(caller, "record", recordType, 3);
        Var mapper = new Var(caller, "mapper", mapperType, 4);
        Var orderId = new Var(caller, "orderId", objectType, 5);
        Var extractedId = new Var(caller, "extractedId", objectType, 6);

        MethodRef inheritedCallRef = MethodRef.get(
                ((ClassType) criteriaType).getJClass(),
                generatedAndIdEqualTo.getName(),
                generatedAndIdEqualTo.getParamTypes(),
                generatedAndIdEqualTo.getReturnType(),
                generatedAndIdEqualTo.isStatic());
        assertFalse(inheritedCallRef.equals(generatedAndIdEqualTo.getRef()),
                "the synthetic callsite should use a raw subclass ref while the summary is registered on the superclass");
        assertTrue(manager.hasSummary(inheritedCallRef),
                "hierarchy-aware summary lookup should recognize subclass-view method refs");

        Invoke createCriteriaCall = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example, List.of()),
                criteria);
        Invoke andIdEqualToCall = new Invoke(
                caller,
                new InvokeVirtual(inheritedCallRef, criteria, List.of(criterionValue)),
                criteria);
        Invoke updateByExampleCall = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record, example)));
        Invoke setIdCall = new Invoke(
                caller,
                new InvokeVirtual(setId.getRef(), record, List.of(orderId)));
        Invoke getIdCall = new Invoke(
                caller,
                new InvokeVirtual(getId.getRef(), record, List.of()),
                extractedId);

        CSObj exampleObj = solver.newObject("inherited-example-1", exampleType);
        CSObj criteriaObj = solver.newObject("inherited-criteria-1", criteriaType);
        CSObj orderIdObj = solver.newObject("inherited-value-1", objectType);
        CSObj recordObj = solver.newObject("inherited-record-1", recordType);
        CSObj mapperObj = solver.newObject("inherited-mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, createCriteriaCall),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, updateByExampleCall),
                updateByExampleSelective.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, andIdEqualToCall),
                generatedAndIdEqualTo.getRef(),
                context));
        assertFalse(solver.pointsToOf(context, example).getObjects().contains(orderIdObj));

        solver.seedVarPointsTo(context, orderId, orderIdObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setIdCall),
                setId.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getIdCall),
                getId.getRef(),
                context));
        assertTrue(solver.pointsToOf(context, extractedId).getObjects().contains(orderIdObj));
        solver.seedVarPointsTo(context, criterionValue, orderIdObj);

        assertTrue(
                manager.reapplySummary(inheritedCallRef),
                "phase-end reapply should revisit raw callsite refs even when the summary is registered on a superclass");
        assertTrue(criteriaValuesOf(manager, criteriaObj).getObjects().contains(orderIdObj),
                "inherited reapply should store the late value on the Criteria receiver");
        assertTrue(exampleValuesOf(manager, exampleObj).getObjects().contains(orderIdObj),
                "inherited reapply should expose the late value through the linked Example");
        assertTrue(
                solver.pointsToOf(context, example).getObjects().contains(orderIdObj),
                "reapplySummary should backfill the ByExample consumer for inherited criteria call sites");
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
        assertTrue(resolvedSummaryMethodRefCache(manager).containsKey(inheritedCallRef),
                "inherited method refs should be memoized after the first lookup");
        assertTrue(summaryLookupCache(manager).containsKey(inheritedCallRef),
                "resolved summaries should be cached after the first lookup");
        assertTrue(
                generatedAndIdEqualTo.getRef().equals(
                        resolvedSummaryMethodRefCache(manager).get(inheritedCallRef)),
                "cache should normalize inherited criteria refs to the registered summary method");
    }

    @Test
    void reapplyRegisteredSummariesReplaysTrackedInheritedCriteriaCallSites() {
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
        JMethod setId = hierarchy.getMethod("<MbgRecord: void setId(java.lang.Object)>");
        JMethod getId = hierarchy.getMethod("<MbgRecord: java.lang.Object getId()>");

        assertNotNull(createCriteria);
        assertNotNull(generatedAndIdEqualTo);
        assertNotNull(updateByExampleSelective);
        assertNotNull(setId);
        assertNotNull(getId);

        Context context = new TrieContext.Factory<>().getEmptyContext();
        JMethod caller = newMethod("CriteriaCaller", "reapplyRegisteredInherited");
        Type exampleType = createCriteria.getDeclaringClass().getType();
        Type criteriaType = createCriteria.getReturnType();
        Type recordType = setId.getDeclaringClass().getType();
        Type mapperType = updateByExampleSelective.getDeclaringClass().getType();
        Type objectType = World.get().getTypeSystem().getClassType("java.lang.Object");

        Var example = new Var(caller, "example", exampleType, 0);
        Var criteria = new Var(caller, "criteria", criteriaType, 1);
        Var criterionValue = new Var(caller, "criterionValue", objectType, 2);
        Var record = new Var(caller, "record", recordType, 3);
        Var mapper = new Var(caller, "mapper", mapperType, 4);
        Var orderId = new Var(caller, "orderId", objectType, 5);
        Var extractedId = new Var(caller, "extractedId", objectType, 6);

        MethodRef inheritedCallRef = MethodRef.get(
                ((ClassType) criteriaType).getJClass(),
                generatedAndIdEqualTo.getName(),
                generatedAndIdEqualTo.getParamTypes(),
                generatedAndIdEqualTo.getReturnType(),
                generatedAndIdEqualTo.isStatic());

        Invoke createCriteriaCall = new Invoke(
                caller,
                new InvokeVirtual(createCriteria.getRef(), example, List.of()),
                criteria);
        Invoke andIdEqualToCall = new Invoke(
                caller,
                new InvokeVirtual(inheritedCallRef, criteria, List.of(criterionValue)),
                criteria);
        Invoke updateByExampleCall = new Invoke(
                caller,
                new InvokeVirtual(updateByExampleSelective.getRef(), mapper, List.of(record, example)));
        Invoke setIdCall = new Invoke(
                caller,
                new InvokeVirtual(setId.getRef(), record, List.of(orderId)));
        Invoke getIdCall = new Invoke(
                caller,
                new InvokeVirtual(getId.getRef(), record, List.of()),
                extractedId);

        CSObj exampleObj = solver.newObject("indexed-example-1", exampleType);
        CSObj criteriaObj = solver.newObject("indexed-criteria-1", criteriaType);
        CSObj orderIdObj = solver.newObject("indexed-value-1", objectType);
        CSObj recordObj = solver.newObject("indexed-record-1", recordType);
        CSObj mapperObj = solver.newObject("indexed-mapper-1", mapperType);

        solver.seedVarPointsTo(context, example, exampleObj);
        solver.seedVarPointsTo(context, criteria, criteriaObj);
        solver.seedVarPointsTo(context, record, recordObj);
        solver.seedVarPointsTo(context, mapper, mapperObj);

        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, createCriteriaCall),
                createCriteria.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, updateByExampleCall),
                updateByExampleSelective.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, andIdEqualToCall),
                generatedAndIdEqualTo.getRef(),
                context));
        assertFalse(solver.pointsToOf(context, example).getObjects().contains(orderIdObj));

        solver.seedVarPointsTo(context, orderId, orderIdObj);
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, setIdCall),
                setId.getRef(),
                context));
        assertTrue(manager.applySummary(
                solver.getCSManager().getCSCallSite(context, getIdCall),
                getId.getRef(),
                context));
        assertTrue(solver.pointsToOf(context, extractedId).getObjects().contains(orderIdObj));
        solver.seedVarPointsTo(context, criterionValue, orderIdObj);

        assertTrue(
                reapplyRegisteredSummaries(manager),
                "tracked summary callsites should be replayed without a global callsite scan");
        assertTrue(criteriaValuesOf(manager, criteriaObj).getObjects().contains(orderIdObj));
        assertTrue(exampleValuesOf(manager, exampleObj).getObjects().contains(orderIdObj));
        assertTrue(solver.pointsToOf(context, example).getObjects().contains(orderIdObj));
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
    private static boolean hasExampleLoadSite(SummaryManager manager, CSObj exampleObj) {
        try {
            Field field = SummaryManager.class.getDeclaredField("exampleToLoadSites");
            field.setAccessible(true);
            return ((pascal.taie.util.collection.MultiMap<CSObj, ?>) field.get(manager))
                    .containsKey(exampleObj);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("failed to inspect example load sites", e);
        }
    }

    private static PointsToSet criteriaValuesOf(SummaryManager manager, CSObj criteriaObj) {
        return criteriaStore(manager).loadCriteriaValues(criteriaObj);
    }

    private static PointsToSet exampleValuesOf(SummaryManager manager, CSObj exampleObj) {
        return criteriaStore(manager).loadExampleValues(exampleObj);
    }

    private static PointsToSet criteriaVarExamplesOf(
            SummaryManager manager, RecordingSolver solver, Context context, Var criteriaVar) {
        try {
            var method = SummaryManager.class.getDeclaredMethod(
                    "resolveCriteriaVarExamples", Context.class, Var.class);
            method.setAccessible(true);
            return (PointsToSet) method.invoke(manager, context, criteriaVar);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("failed to inspect criteria var bindings", e);
        }
    }

    private static CriteriaSummaryStore criteriaStore(SummaryManager manager) {
        try {
            Field field = SummaryManager.class.getDeclaredField("criteriaSummaryStore");
            field.setAccessible(true);
            return (CriteriaSummaryStore) field.get(manager);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("failed to inspect criteria summary store", e);
        }
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

    private static boolean reapplyRegisteredSummaries(SummaryManager manager) {
        try {
            var method = SummaryManager.class.getDeclaredMethod("reapplyRegisteredSummaries");
            method.setAccessible(true);
            return (boolean) method.invoke(manager);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("failed to invoke indexed summary reapply", e);
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
