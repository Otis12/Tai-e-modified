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

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysis;
import pascal.taie.analysis.pta.plugin.taint.TaintFlow;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SummaryCriteriaTaintRegressionTest {

    private static final String TAINT_CP = Path.of("src/test/resources/pta/taint")
            .toAbsolutePath()
            .normalize()
            .toString();
    private static final String TAINT_CONFIG = Path.of(
                    "src/test/resources/pta/taint/taint-config-criteria-summary.yml")
            .toAbsolutePath()
            .normalize()
            .toString();
    private static final String INPUT_CLASSES =
            "CriteriaSummaryRegression,CriteriaUnsafeBridgeNegativeRegression,"
                    + "CriteriaStringConcatDisconnectedRegression,"
                    + "CriteriaStringConcatCrossMethodRegression,"
                    + "CriteriaController,CriteriaService,CriteriaOrder,CriteriaExample,"
                    + "CriteriaGeneratedCriteria,Criteria,CriteriaCriterion,CriteriaMapper,"
                    + "CriteriaSource,CriteriaStringSource";
    private static final String[] CRITERIA_FIXTURE_SOURCES = {
            "CriteriaSummaryRegression.java",
            "CriteriaUnsafeBridgeNegativeRegression.java",
            "CriteriaStringConcatDisconnectedRegression.java",
            "CriteriaStringConcatCrossMethodRegression.java",
            "CriteriaController.java",
            "CriteriaService.java",
            "CriteriaOrder.java",
            "CriteriaExample.java",
            "CriteriaGeneratedCriteria.java",
            "Criteria.java",
            "CriteriaCriterion.java",
            "CriteriaMapper.java",
            "CriteriaSource.java",
            "CriteriaStringSource.java"
    };

    @Test
    void accessorBackedCriterionReachesByExampleSink() {
        try {
            AnalysisSnapshot snapshot = runAnalysis("CriteriaSummaryRegression");
            Set<TaintFlow> flows = snapshot.flows();

            assertTrue(
                    flows.stream().anyMatch(flow ->
                            flow.sourcePoint().toString().contains("CriteriaSource.source()") &&
                                    flow.sinkPoint().sink().method().getSignature().equals(
                                            "<CriteriaMapper: int updateByExampleSelective(" +
                                                    "CriteriaOrder,CriteriaExample)>") &&
                                    flow.sinkPoint().indexRef().index() == 1),
                    () -> "Expected taint flow into CriteriaMapper.updateByExampleSelective(...)/1, got:\n" +
                            flows + "\nCriteriaService vars:\n" + snapshot.servicePointsToDump());
        } finally {
            World.reset();
        }
    }

    @Test
    void accessorBackedCriterionKeepsConnectivityAcrossServiceLocals() {
        try {
            AnalysisSnapshot snapshot = runAnalysis("CriteriaSummaryRegression");
            PointerAnalysisResult pta = snapshot.pta();
            JMethod serviceMethod = requireDeclaredMethod("CriteriaService", "paySuccess");

            Var orderIdParam = serviceMethod.getIR().getParam(0);
            Invoke getIdCall = requireInvokeByName(serviceMethod, "getId");
            Invoke andIdCall = requireInvokeByName(serviceMethod, "andIdEqualTo");
            Invoke sinkCall = requireInvokeByName(serviceMethod, "updateByExampleSelective");

            Var getIdResult = getIdCall.getResult();
            InvokeExp andInvokeExp = andIdCall.getInvokeExp();
            InvokeExp sinkInvokeExp = sinkCall.getInvokeExp();
            Var andIdArg = andInvokeExp.getArg(0);
            Var sinkExampleArg = sinkInvokeExp.getArg(1);

            assertFalse(intersection(pta, orderIdParam, getIdResult).isEmpty(),
                    () -> "Expected service param to reach getId() result.\n"
                            + snapshot.servicePointsToDump());
            assertFalse(intersection(pta, getIdResult, andIdArg).isEmpty(),
                    () -> "Expected getId() result to reach andIdEqualTo(value).\n"
                            + snapshot.servicePointsToDump());
            assertFalse(intersection(pta, andIdArg, sinkExampleArg).isEmpty(),
                    () -> "Expected andIdEqualTo(value) to reconnect into updateByExampleSelective(..., example).\n"
                            + snapshot.servicePointsToDump());
        } finally {
            World.reset();
        }
    }

    @Test
    void renderingBridgeDoesNotReconnectByExampleSink() {
        try {
            Set<TaintFlow> flows = runAnalysis("CriteriaUnsafeBridgeNegativeRegression").flows();

            assertTrue(
                    flows.isEmpty(),
                    () -> "Expected rendering bridge shape to stay disconnected, got:\n" + flows);
        } finally {
            World.reset();
        }
    }

    @Test
    void disconnectedStringConcatBridgeDoesNotPolluteSafeByExampleSink() {
        try {
            Set<TaintFlow> flows = runAnalysis("CriteriaStringConcatDisconnectedRegression").flows();

            assertTrue(
                    flows.isEmpty(),
                    () -> "Expected disconnected string-concat bridge to stay isolated, got:\n" + flows);
        } finally {
            World.reset();
        }
    }

    @Test
    void unrelatedStringConcatSourceDoesNotJoinLegitimateByExampleStringConcatFlow() {
        try {
            Set<TaintFlow> flows = runAnalysis("CriteriaStringConcatCrossMethodRegression").flows();

            assertEquals(
                    1,
                    flows.size(),
                    () -> "Expected only the legitimate query method source to reach the sink, got:\n" + flows);
            assertTrue(
                    flows.iterator().next().sourcePoint().getContainer().getName()
                            .equals("queryWithLegitimateSource"),
                    () -> "Expected sink to keep only queryWithLegitimateSource() as source, got:\n" + flows);
        } finally {
            World.reset();
        }
    }

    private static AnalysisSnapshot runAnalysis(String mainClass) {
        Path compiledFixtureDir = compileCriteriaFixture();
        try {
            Main.main(
                    "-pp",
                    "-cp", compiledFixtureDir.toString(),
                    "--input-classes", INPUT_CLASSES,
                    "-m", mainClass,
                    "-a", "pta=implicit-entries:false;" +
                            "only-app:false;" +
                            "distinguish-string-constants:all;" +
                            "cs:ci;" +
                            "codesummary:codesummary;" +
                            "taint-config:" + TAINT_CONFIG
            );

            PointerAnalysisResult pta = World.get().getResult("pta", null);
            return new AnalysisSnapshot(
                    pta.getResult(TaintAnalysis.class.getName(), Set.of()),
                    pta,
                    describeMethodVarPointsTo("CriteriaService", "paySuccess"));
        } finally {
            deleteRecursively(compiledFixtureDir);
        }
    }

    private static JMethod requireDeclaredMethod(String className, String methodName) {
        JClass clazz = World.get().getClassHierarchy().getClass(className);
        assertTrue(clazz != null, () -> "Missing class " + className);
        JMethod method = clazz.getDeclaredMethod(methodName);
        assertTrue(method != null && method.getIR() != null,
                () -> "Missing method/IR " + className + "." + methodName);
        return method;
    }

    private static Invoke requireInvokeByName(JMethod method, String calleeName) {
        return method.getIR().invokes(false)
                .filter(invoke -> calleeName.equals(invoke.getMethodRef().getName()))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "Missing invoke named " + calleeName + " in " + method.getSignature()));
    }

    private static Set<String> intersection(PointerAnalysisResult pta, Var left, Var right) {
        Set<String> leftObjects = pta.getPointsToSet(left).stream()
                .map(Object::toString)
                .collect(Collectors.toSet());
        return pta.getPointsToSet(right).stream()
                .map(Object::toString)
                .filter(leftObjects::contains)
                .collect(Collectors.toSet());
    }

    private static String describeMethodVarPointsTo(String className, String methodName) {
        JMethod method = requireDeclaredMethod(className, methodName);
        PointerAnalysisResult pta = World.get().getResult("pta", null);
        return method.getIR().getVars().stream()
                .map(var -> var + " -> " + pta.getPointsToSet(var))
                .collect(Collectors.joining(System.lineSeparator()));
    }

    private static Path compileCriteriaFixture() {
        try {
            Path tmpRoot = Path.of("build", "tmp").toAbsolutePath().normalize();
            Files.createDirectories(tmpRoot);
            Path outDir = Files.createTempDirectory(tmpRoot, "criteria-summary-regression");
            JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
            assertNotNull(compiler, "Expected the JDK compiler to be available");
            ByteArrayOutputStream compilerOutput = new ByteArrayOutputStream();
            ArrayList<String> args = new ArrayList<>();
            args.add("-encoding");
            args.add("UTF-8");
            args.add("-d");
            args.add(outDir.toString());
            for (String source : CRITERIA_FIXTURE_SOURCES) {
                args.add(Path.of(TAINT_CP, source).toString());
            }
            int exitCode = compiler.run(
                    null,
                    compilerOutput,
                    compilerOutput,
                    args.toArray(String[]::new));
            assertEquals(0, exitCode,
                    "Failed to compile criteria regression fixture:\n"
                            + compilerOutput.toString(StandardCharsets.UTF_8));
            return outDir;
        } catch (IOException e) {
            throw new AssertionError("Failed to prepare compiled criteria fixture", e);
        }
    }

    private static void deleteRecursively(Path path) {
        if (path == null || !Files.exists(path)) {
            return;
        }
        try (var stream = Files.walk(path)) {
            stream.sorted((left, right) -> right.getNameCount() - left.getNameCount())
                    .forEach(current -> {
                        try {
                            Files.deleteIfExists(current);
                        } catch (IOException e) {
                            throw new AssertionError("Failed to clean temp fixture: " + current, e);
                        }
                    });
        } catch (IOException e) {
            throw new AssertionError("Failed to clean temp fixture root: " + path, e);
        }
    }

    private record AnalysisSnapshot(
            Set<TaintFlow> flows,
            PointerAnalysisResult pta,
            String servicePointsToDump) {
    }
}
