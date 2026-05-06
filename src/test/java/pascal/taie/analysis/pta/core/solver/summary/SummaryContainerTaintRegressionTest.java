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
import pascal.taie.ir.exp.Var;
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
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SummaryContainerTaintRegressionTest {

    private static final String TAINT_CP =
            Path.of("src/test/resources/pta/taint").toAbsolutePath().normalize().toString();

    private static final String TAINT_CONFIG =
            Path.of("src/test/resources/pta/taint/taint-config.yml")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    private static final String PTA_OPTIONS =
            "pta=implicit-entries:false;" +
                    "only-app:false;" +
                    "distinguish-string-constants:all;" +
                    "cs:ci;" +
                    "codesummary:codesummary;" +
                    "taint-config:" + TAINT_CONFIG;

    @Test
    void iteratorNextResultShouldReachSinkThroughCast() {
        try {
            AnalysisSnapshot snapshot = runAnalysis("IteratorSummaryRegression");
            Set<TaintFlow> flows = snapshot.flows();

            assertEquals(1, flows.size(),
                    () -> "Expected exactly one iterator().next() flow, got:\n" +
                            snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
            assertTrue(
                    flows.stream().anyMatch(flow ->
                            flow.sourcePoint().toString().contains("SourceSink.source()") &&
                                    flow.sinkPoint().sink().method().getSignature().equals(
                                            "<SourceSink: void sink(java.lang.String)>")),
                    () -> "Expected iterator().next() result to reach SourceSink.sink(String), got:\n" +
                            snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
        } finally {
            World.reset();
        }
    }

    @Test
    void iteratorNextShouldNotPolluteSafeIteratorLoad() {
        try {
            AnalysisSnapshot snapshot = runAnalysis("IteratorSummaryPrecisionRegression");
            Set<TaintFlow> flows = snapshot.flows();

            assertEquals(1, flows.size(),
                    () -> "Expected only the tainted iterator branch to reach the sink, got:\n" +
                            snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
            assertTrue(
                    flows.stream().allMatch(flow ->
                            flow.sourcePoint().toString().contains("SourceSink.source()") &&
                                    flow.sinkPoint().toString().contains("IteratorSummaryPrecisionRegression")),
                    () -> "Iterator precision regression should only report the positive branch, got:\n" +
                            snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
        } finally {
            World.reset();
        }
    }

    @Test
    void objectToStringShouldSkipObjectBaseButKeepOverrides() {
        try {
            AnalysisSnapshot snapshot = runAnalysis("ObjectToStringSummaryRegression");
            Set<TaintFlow> flows = snapshot.flows();

            assertEquals(1, flows.size(),
                    () -> "Expected only overridden toString() to propagate, got:\n" +
                            snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
            assertTrue(
                    flows.stream().allMatch(flow ->
                            flow.sourcePoint().toString().contains("SourceSink.source()") &&
                                    flow.sinkPoint().toString().contains("ObjectToStringSummaryRegression")),
                    () -> "Object.toString() regression should only report the override branch, got:\n" +
                            snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
        } finally {
            World.reset();
        }
    }

    @Test
    void servletAttributeSummariesShouldKeepSameNamePositiveButAvoidDifferentNamePollution() {
        try {
            AnalysisSnapshot snapshot = runAnalysis("AttributeSummaryRegression");
            Set<TaintFlow> flows = snapshot.flows();

            assertEquals(1, flows.size(),
                    () -> "Expected only same-name attribute lookup to propagate, got:\n"
                            + snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
            assertTrue(
                    flows.stream().allMatch(flow ->
                            flow.sourcePoint().toString().contains("SourceSink.source()") &&
                                    flow.sinkPoint().toString().contains("AttributeSummaryRegression")),
                    () -> "Attribute regression should only report the positive branch, got:\n"
                            + snapshot.flowDump() + "\nMain vars:\n" + snapshot.pointsToDump());
        } finally {
            World.reset();
        }
    }

    private static AnalysisSnapshot runAnalysis(String mainClass) {
        Path compiledFixtureDir = null;
        try {
            List<String> args = new ArrayList<>(List.of(
                    "-pp",
                    "-cp", TAINT_CP,
                    "-m", mainClass,
                    "-a", PTA_OPTIONS
            ));
            if ("AttributeSummaryRegression".equals(mainClass)) {
                compiledFixtureDir = compileAttributeRegressionFixture();
                args = new ArrayList<>(List.of(
                        "-pp",
                        "-cp", compiledFixtureDir.toString(),
                        "--input-classes",
                        "AttributeSummaryRegression,MockServletRequest,javax.servlet.ServletRequest",
                        "-m", mainClass,
                        "-a", PTA_OPTIONS
                ));
            }
            Main.main(args.toArray(new String[0]));
            PointerAnalysisResult pta = World.get().getResult("pta", null);
            Set<TaintFlow> flows = Set.copyOf(
                    pta.getResult(TaintAnalysis.class.getName(), Set.of()));
            return new AnalysisSnapshot(flows, describeMainVarPointsTo(mainClass, pta));
        } finally {
            if (compiledFixtureDir != null) {
                deleteRecursively(compiledFixtureDir);
            }
        }
    }

    private static Path compileAttributeRegressionFixture() {
        try {
            Path tmpRoot = Path.of("build", "tmp").toAbsolutePath().normalize();
            Files.createDirectories(tmpRoot);
            Path outDir = Files.createTempDirectory(tmpRoot, "attribute-summary-regression");
            JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
            assertNotNull(compiler, "Expected the JDK compiler to be available");
            ByteArrayOutputStream compilerOutput = new ByteArrayOutputStream();
            int exitCode = compiler.run(
                    null,
                    compilerOutput,
                    compilerOutput,
                    "-encoding", "UTF-8",
                    "-d", outDir.toString(),
                    Path.of(TAINT_CP, "SourceSink.java").toString(),
                    Path.of(TAINT_CP, "Sanitizer.java").toString(),
                    Path.of(TAINT_CP, "MockServletRequest.java").toString(),
                    Path.of(TAINT_CP, "AttributeSummaryRegression.java").toString(),
                    Path.of(TAINT_CP, "javax", "servlet", "ServletRequest.java").toString()
            );
            assertEquals(0, exitCode,
                    "Failed to compile attribute regression fixture:\n"
                            + compilerOutput.toString(StandardCharsets.UTF_8));
            return outDir;
        } catch (IOException e) {
            throw new AssertionError("Failed to prepare compiled attribute fixture", e);
        }
    }

    private static void deleteRecursively(Path path) {
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

    private static String describeMainVarPointsTo(String mainClass, PointerAnalysisResult pta) {
        JClass clazz = World.get().getClassHierarchy().getClass(mainClass);
        if (clazz == null) {
            return "<missing class>";
        }
        JMethod main = clazz.getDeclaredMethod("main");
        if (main == null || main.getIR() == null) {
            return "<missing main IR>";
        }
        return main.getIR().getVars().stream()
                .map(var -> describeVar(pta, var))
                .collect(Collectors.joining("\n"));
    }

    private static String describeVar(PointerAnalysisResult pta, Var var) {
        return var + " -> " + pta.getPointsToSet(var);
    }

    private record AnalysisSnapshot(Set<TaintFlow> flows, String pointsToDump) {

        private String flowDump() {
            return flows.stream()
                    .map(TaintFlow::toString)
                    .sorted()
                    .collect(Collectors.joining(System.lineSeparator()));
        }
    }
}
