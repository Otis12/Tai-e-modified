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
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.solver.SummarySolver;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import javax.tools.JavaCompiler;
import javax.tools.StandardJavaFileManager;
import javax.tools.StandardLocation;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JdkSummaryOnlyBoundaryTest {

    private static final Path APP_SOURCE_PATH =
            Path.of("src/test/resources/pta/jdk-summary-only/app")
                    .toAbsolutePath()
                    .normalize();

    private static final Path APP_CLASS_PATH =
            Path.of("build/test-jdk-summary-only-jb2-app-classes")
                    .toAbsolutePath()
                    .normalize();

    private static final Path LIB_SOURCE_PATH =
            Path.of("src/test/resources/pta/jdk-summary-only/lib")
                    .toAbsolutePath()
                    .normalize();

    private static final Path LIB_CLASS_PATH =
            Path.of("build/test-jdk-summary-only-jb2-lib-classes")
                    .toAbsolutePath()
                    .normalize();

    private static final String MAIN_CLASS = "JdkSummaryOnlyBoundaryMain";

    private static final String MAIN_SIGNATURE =
            "<JdkSummaryOnlyBoundaryMain: void main(java.lang.String[])>";

    private static final String JDK_TO_STRING =
            "<java.lang.String: java.lang.String toString()>";

    private static final String THIRD_PARTY_FORWARD =
            "<apple.laf.thirdparty.BoundaryHelper: java.lang.Object forward(java.lang.Object)>";

    private static final String SERVLET_FORWARD =
            "<javax.servlet.http.HttpServletRequest: java.lang.Object forward(java.lang.Object)>";

    private static final String BASE_OPTIONS =
            "pta=implicit-entries:false;"
                    + "distinguish-string-constants:all;"
                    + "cs:ci;"
                    + "codesummary:codesummary;";

    @Test
    void normalModeKeepsExistingJdkBodyBehavior() {
        try {
            PointerAnalysisResult pta = runBoundaryPTA(
                    BASE_OPTIONS
                            + "only-app:false;"
                            + "jdk-analysis-mode:normal");

            assertCallEdge(pta, JDK_TO_STRING);
            Invoke jdkCall = getMainInvoke(JDK_TO_STRING);
            assertContainsPointsTo(pta, jdkCall.getResult(), getBase(jdkCall),
                    "normal mode should keep java.lang.String.toString() body/ordinary return behavior");

            Map<String, String> ignoredReasons = pta.getResult(
                    SummarySolver.IGNORED_METHOD_REASONS_KEY, Map.of());
            assertFalse(ignoredReasons.containsKey(JDK_TO_STRING),
                    "normal mode should not ignore unsummarized JDK methods");
        } finally {
            World.reset();
        }
    }

    @Test
    void summaryOnlySkipsJdkBodyButKeepsCallEdgeAndThirdPartyBodies() {
        try {
            PointerAnalysisResult pta = runBoundaryPTA(
                    BASE_OPTIONS
                            + "only-app:false;"
                            + "jdk-analysis-mode:summary-only");

            assertCallEdge(pta, JDK_TO_STRING);

            Map<String, String> ignoredReasons = pta.getResult(
                    SummarySolver.IGNORED_METHOD_REASONS_KEY, Map.of());
            assertEquals("JDK_SUMMARY_ONLY", ignoredReasons.get(JDK_TO_STRING));

            Invoke jdkCall = getMainInvoke(JDK_TO_STRING);
            assertNoPointsTo(pta, jdkCall.getResult(),
                    "summary-only should not pass receiver/return through ordinary JDK PFG edges");

            assertNonApplicationMethod(THIRD_PARTY_FORWARD);
            Invoke helperCall = getMainInvoke(THIRD_PARTY_FORWARD);
            assertContainsPointsTo(pta, helperCall.getResult(),
                    helperCall.getInvokeExp().getArg(0),
                    "non-app third-party helper should still be analyzed when only-app=false");
            assertFalse(ignoredReasons.containsKey(THIRD_PARTY_FORWARD),
                    "third-party helper must not be treated as JDK summary-only");

            assertNonApplicationMethod(SERVLET_FORWARD);
            Invoke servletCall = getMainInvoke(SERVLET_FORWARD);
            assertContainsPointsTo(pta, servletCall.getResult(),
                    servletCall.getInvokeExp().getArg(0),
                    "javax.servlet.* must not be skipped by the JDK boundary");
            assertFalse(ignoredReasons.containsKey(SERVLET_FORWARD),
                    "javax.servlet.* must not be treated as JDK summary-only");
        } finally {
            World.reset();
        }
    }

    @Test
    void onlyAppReasonIsSeparateFromJdkSummaryOnlyReason() {
        try {
            PointerAnalysisResult pta = runBoundaryPTA(
                    BASE_OPTIONS
                            + "only-app:true;"
                            + "jdk-analysis-mode:summary-only");

            Map<String, String> ignoredReasons = pta.getResult(
                    SummarySolver.IGNORED_METHOD_REASONS_KEY, Map.of());
            assertEquals("ONLY_APP", ignoredReasons.get(THIRD_PARTY_FORWARD));
            assertFalse("JDK_SUMMARY_ONLY".equals(ignoredReasons.get(THIRD_PARTY_FORWARD)),
                    "only-app ignored methods must not be labeled as JDK summary-only");
        } finally {
            World.reset();
        }
    }

    @Test
    void summaryFrontierMethodBoundarySkipsOnlySelectedSignature()
            throws IOException {
        Path selectedMethods = Files.createTempFile(
                "pta-summary-frontier-selected-methods", ".json");
        Files.writeString(selectedMethods, """
                {
                  "selected_methods": [
                    {
                      "method_signature": "<java.lang.String: java.lang.String toString()>"
                    }
                  ]
                }
                """);
        try {
            PointerAnalysisResult pta = runBoundaryPTA(
                    BASE_OPTIONS
                            + "only-app:false;"
                            + "jdk-analysis-mode:normal;"
                            + "pta-summary-frontier-summary-only-methods-file:"
                            + selectedMethods.toAbsolutePath() + ";");

            assertCallEdge(pta, JDK_TO_STRING);

            Map<String, String> ignoredReasons = pta.getResult(
                    SummarySolver.IGNORED_METHOD_REASONS_KEY, Map.of());
            assertEquals("SUMMARY_FRONTIER_ONLY",
                    ignoredReasons.get(JDK_TO_STRING));

            Invoke jdkCall = getMainInvoke(JDK_TO_STRING);
            assertNoPointsTo(pta, jdkCall.getResult(),
                    "method frontier boundary should skip only selected method body");

            assertFalse(ignoredReasons.containsKey(THIRD_PARTY_FORWARD),
                    "method frontier boundary must not skip unselected non-app helpers");
            Invoke helperCall = getMainInvoke(THIRD_PARTY_FORWARD);
            assertContainsPointsTo(pta, helperCall.getResult(),
                    helperCall.getInvokeExp().getArg(0),
                    "unselected non-app helper should still be analyzed");
        } finally {
            Files.deleteIfExists(selectedMethods);
            World.reset();
        }
    }

    private static PointerAnalysisResult runBoundaryPTA(String ptaOptions) {
        Main.main(
                "-pp",
                "-cp", compileApplicationClassPath(),
                "-cp", compileLibraryClassPath(),
                "-m", MAIN_CLASS,
                "-a", ptaOptions);
        return World.get().getResult(PointerAnalysis.ID);
    }

    private static String compileApplicationClassPath() {
        compileLibraryClassPath();
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        assertNotNull(compiler, "JDK compiler is required to compile test fixtures");
        try {
            java.nio.file.Files.createDirectories(APP_CLASS_PATH);
            try (StandardJavaFileManager fileManager =
                         compiler.getStandardFileManager(null, null, null)) {
                fileManager.setLocation(StandardLocation.CLASS_OUTPUT,
                        List.of(APP_CLASS_PATH.toFile()));
                fileManager.setLocation(StandardLocation.CLASS_PATH,
                        List.of(LIB_CLASS_PATH.toFile()));
                List<File> sources = List.of(
                        APP_SOURCE_PATH.resolve(
                                "JdkSummaryOnlyBoundaryMain.java").toFile());
                Boolean success = compiler.getTask(null, fileManager, null,
                        List.of(), null,
                        fileManager.getJavaFileObjectsFromFiles(sources)).call();
                assertTrue(success, "Failed to compile jdk-summary-only app fixture");
            }
        } catch (IOException e) {
            throw new AssertionError("Failed to prepare jdk-summary-only app fixture", e);
        }
        return APP_CLASS_PATH.toString();
    }

    private static String compileLibraryClassPath() {
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        assertNotNull(compiler, "JDK compiler is required to compile test fixtures");
        try {
            java.nio.file.Files.createDirectories(LIB_CLASS_PATH);
            try (StandardJavaFileManager fileManager =
                         compiler.getStandardFileManager(null, null, null)) {
                fileManager.setLocation(StandardLocation.CLASS_OUTPUT,
                        List.of(LIB_CLASS_PATH.toFile()));
                List<File> sources = List.of(
                        LIB_SOURCE_PATH.resolve(
                                "apple/laf/thirdparty/BoundaryHelper.java").toFile(),
                        LIB_SOURCE_PATH.resolve(
                                "javax/servlet/http/HttpServletRequest.java").toFile());
                Boolean success = compiler.getTask(null, fileManager, null,
                        List.of(), null,
                        fileManager.getJavaFileObjectsFromFiles(sources)).call();
                assertTrue(success, "Failed to compile jdk-summary-only library fixtures");
            }
        } catch (IOException e) {
            throw new AssertionError("Failed to prepare jdk-summary-only library fixtures", e);
        }
        return LIB_CLASS_PATH.toString();
    }

    private static void assertCallEdge(PointerAnalysisResult pta,
                                       String calleeSignature) {
        Invoke invoke = getMainInvoke(calleeSignature);
        Set<JMethod> callees = pta.getCallGraph().getCalleesOf(invoke);
        assertTrue(callees.stream()
                        .map(JMethod::getSignature)
                        .anyMatch(calleeSignature::equals),
                () -> "Expected call edge to " + calleeSignature + ", got " + callees);
    }

    private static void assertContainsPointsTo(PointerAnalysisResult pta, Var resultVar,
                                               Var sourceVar,
                                               String message) {
        Set<?> resultPts = pta.getPointsToSet(resultVar);
        Set<?> sourcePts = pta.getPointsToSet(sourceVar);
        assertFalse(sourcePts.isEmpty(), () -> sourceVar + " should have points-to objects");
        assertTrue(resultPts.containsAll(sourcePts),
                () -> message + ", got " + resultVar + "=" + resultPts
                        + ", " + sourceVar + "=" + sourcePts);
    }

    private static void assertNoPointsTo(PointerAnalysisResult pta,
                                         Var var,
                                         String message) {
        Set<?> pointsToSet = pta.getPointsToSet(var);
        assertTrue(pointsToSet.isEmpty(),
                () -> message + ", got " + var + "=" + pointsToSet);
    }

    private static void assertNonApplicationMethod(String signature) {
        JMethod method = World.get().getClassHierarchy().getMethod(signature);
        assertNotNull(method, () -> signature + " should be loaded");
        assertFalse(method.isApplication(),
                () -> signature + " should be loaded as a non-application method");
    }

    private static Invoke getMainInvoke(String calleeSignature) {
        return getMain().getIR().getStmts()
                .stream()
                .filter(Invoke.class::isInstance)
                .map(Invoke.class::cast)
                .filter(invoke -> calleeSignature.equals(
                        invoke.getMethodRef().resolve().getSignature()))
                .findFirst()
                .orElseThrow();
    }

    private static Var getBase(Invoke invoke) {
        return ((InvokeInstanceExp) invoke.getInvokeExp()).getBase();
    }

    private static JMethod getMain() {
        return World.get().getClassHierarchy().getMethod(MAIN_SIGNATURE);
    }
}
