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
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.MergedObj;
import pascal.taie.analysis.pta.core.heap.NewObj;
import pascal.taie.analysis.pta.core.solver.SummarySolver;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysis;
import pascal.taie.analysis.pta.plugin.taint.TaintFlow;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.classes.JMethod;

import java.nio.file.Path;
import java.util.Collections;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JdkStringSummaryTest {

    private static final String CLASSPATH =
            Path.of("src/test/resources/pta/jdk-string-summary")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    private static final String TAINT_CLASSPATH =
            Path.of("src/test/resources/pta/taint")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    private static final String TAINT_CONFIG =
            Path.of("src/test/resources/pta/jdk-string-summary/taint-config.yml")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    @Test
    void jdkStringSummariesAreRegisteredAsIgnoredMethods() {
        try {
            PointerAnalysisResult pta = runJdkStringPTA(
                    "JdkStringSummaryIgnored",
                    "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary");
            Set<String> ignoredMethods = pta.getResult(
                    SummarySolver.IGNORED_METHOD_SIGNATURES_KEY, Set.of());

            assertTrue(ignoredMethods.contains(
                    "<java.lang.String: java.lang.String concat(java.lang.String)>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.StringBuilder: java.lang.String toString()>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.StringBuffer: java.lang.String toString()>"));
        } finally {
            World.reset();
        }
    }

    @Test
    void stringFamilyHeapObjectsUseAllocationSitesByDefault() {
        try {
            PointerAnalysisResult pta = runJdkStringPTA(
                    "JdkStringHeapIsolation",
                    "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary");
            assertOneAllocationSiteObject(pta, "string1");
            assertOneAllocationSiteObject(pta, "string2");
            assertOneAllocationSiteObject(pta, "builder1");
            assertOneAllocationSiteObject(pta, "builder2");
            assertOneAllocationSiteObject(pta, "buffer1");
            assertOneAllocationSiteObject(pta, "buffer2");
            assertDisjoint(pta, "string1", "string2");
            assertDisjoint(pta, "builder1", "builder2");
            assertDisjoint(pta, "buffer1", "buffer2");
        } finally {
            World.reset();
        }
    }

    @Test
    void ignoredJdkStringSummariesPropagateTaintToSinks() {
        try {
            PointerAnalysisResult pta = runJdkStringPTA(
                    "JdkStringSummaryPropagation",
                    "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary;"
                            + "taint-config:" + TAINT_CONFIG);
            Set<TaintFlow> flows = pta.getResult(TaintAnalysis.class.getName(), Set.of());

            assertEquals(3, flows.size(), () -> "Expected one concat, builder, and buffer flow, got " + flows);
            assertTrue(flows.stream().anyMatch(flow -> flow.toString().contains("concatSink")),
                    () -> "Expected String.concat summary flow, got " + flows);
            assertTrue(flows.stream().anyMatch(flow -> flow.toString().contains("builderSink")),
                    () -> "Expected StringBuilder append/toString summary flow, got " + flows);
            assertTrue(flows.stream().anyMatch(flow -> flow.toString().contains("bufferSink")),
                    () -> "Expected StringBuffer append/toString summary flow, got " + flows);
        } finally {
            World.reset();
        }
    }

    private static PointerAnalysisResult runJdkStringPTA(String mainClass, String ptaOptions) {
        Main.main(
                "-pp",
                "-cp", CLASSPATH,
                "-cp", TAINT_CLASSPATH,
                "-m", mainClass,
                "-a", ptaOptions);
        return World.get().getResult(PointerAnalysis.ID);
    }

    private static void assertOneAllocationSiteObject(PointerAnalysisResult pta, String varName) {
        Set<?> pointsToSet = pta.getPointsToSet(getMainVar(varName));
        assertEquals(1, pointsToSet.size(),
                () -> varName + " should point to one allocation-site object, got " + pointsToSet);
        Object obj = pointsToSet.iterator().next();
        assertInstanceOf(NewObj.class, obj,
                () -> varName + " should not be merged, got " + obj);
        assertTrue(!(obj instanceof MergedObj),
                () -> varName + " should not point to a merged string-family object, got " + obj);
    }

    private static void assertDisjoint(PointerAnalysisResult pta, String left, String right) {
        Set<?> leftPts = pta.getPointsToSet(getMainVar(left));
        Set<?> rightPts = pta.getPointsToSet(getMainVar(right));
        assertTrue(Collections.disjoint(leftPts, rightPts),
                () -> left + " and " + right + " should be allocation-site isolated, got "
                        + leftPts + " and " + rightPts);
    }

    private static Var getMainVar(String name) {
        JMethod main = World.get().getClassHierarchy().getMethod(
                "<JdkStringHeapIsolation: void main(java.lang.String[])>");
        return main.getIR().getVars()
                .stream()
                .filter(var -> name.equals(var.getName()))
                .findFirst()
                .orElseThrow();
    }
}
