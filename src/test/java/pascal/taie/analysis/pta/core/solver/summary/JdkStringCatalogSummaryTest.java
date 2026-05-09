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
import pascal.taie.analysis.pta.core.solver.SummarySolver;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysis;
import pascal.taie.analysis.pta.plugin.taint.TaintFlow;

import java.nio.file.Path;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JdkStringCatalogSummaryTest {

    private static final String CLASSPATH =
            Path.of("src/test/resources/pta/jdk-summary-only/catalog")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    private static final String TAINT_CONFIG =
            Path.of("src/test/resources/pta/jdk-summary-only/catalog/taint-config.yml")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    private static final String OPTIONS =
            "pta=implicit-entries:false;"
                    + "only-app:false;"
                    + "distinguish-string-constants:all;"
                    + "cs:ci;"
                    + "codesummary:codesummary;"
                    + "jdk-analysis-mode:summary-only;"
                    + "jdk-summary-profile:jdk17;"
                    + "jdk-summary-missing-signature:warn;"
                    + "taint-config:" + TAINT_CONFIG;

    @Test
    void catalogStringSummariesPropagateTaint() {
        try {
            PointerAnalysisResult pta = run("JdkStringCatalogSummaryMain");
            Set<TaintFlow> flows = pta.getResult(TaintAnalysis.class.getName(), Set.of());

            assertFlow(flows, "trimSink");
            assertFlow(flows, "substringSink");
            assertFlow(flows, "lowerSink");
            assertFlow(flows, "concatBaseSink");
            assertFlow(flows, "concatArgSink");
            assertFlow(flows, "builderSink");
            assertFlow(flows, "bufferSink");
            assertNoFlow(flows, "objectToStringSink");
            assertEquals(7, flows.size(), () -> "Expected catalog string flows only, got " + flows);
        } finally {
            World.reset();
        }
    }

    @Test
    void catalogMethodsEnterIgnoredSetAndJdkBodiesAreSkipped() {
        try {
            PointerAnalysisResult pta = run("JdkStringCatalogSummaryMain");
            Set<String> ignoredMethods = pta.getResult(
                    SummarySolver.IGNORED_METHOD_SIGNATURES_KEY, Set.of());
            Map<String, String> ignoredReasons = pta.getResult(
                    SummarySolver.IGNORED_METHOD_REASONS_KEY, Map.of());

            assertTrue(ignoredMethods.contains(
                    "<java.lang.String: java.lang.String trim()>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.String: java.lang.String substring(int)>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.String: java.lang.String toLowerCase()>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.String: java.lang.String concat(java.lang.String)>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>"));
            assertTrue(ignoredMethods.contains(
                    "<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>"));
            assertFalse(ignoredMethods.contains(
                    "<java.lang.Object: java.lang.String toString()>"));
            assertEquals("EXPLICIT_SUMMARY", ignoredReasons.get(
                    "<java.lang.String: java.lang.String trim()>"));
            assertEquals("JDK_SUMMARY_ONLY", ignoredReasons.get(
                    "<java.lang.String: java.lang.String toString()>"));
        } finally {
            World.reset();
        }
    }

    @Test
    void catalogStatsAreStoredInResult() {
        try {
            PointerAnalysisResult pta = run("JdkStringCatalogSummaryMain");
            JdkSummaryCatalogStats stats = pta.getResult(
                    SummarySolver.JDK_SUMMARY_CATALOG_STATS_KEY, null);
            Set<String> catalogMethods = pta.getResult(
                    SummarySolver.JDK_SUMMARY_CATALOG_METHOD_SIGNATURES_KEY, Set.of());

            assertEquals("jdk17", stats.selectedProfile());
            assertTrue(stats.loadedCatalogs().stream().anyMatch(name ->
                    name.endsWith("jdk-common.yml")));
            assertTrue(stats.loadedCatalogs().stream().anyMatch(name ->
                    name.endsWith("jdk17.yml")));
            assertTrue(catalogMethods.contains(
                    "<java.lang.String: java.lang.String trim()>"));
            assertTrue(catalogMethods.contains(
                    "<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>"));
        } finally {
            World.reset();
        }
    }

    private static PointerAnalysisResult run(String mainClass) {
        Main.main(
                "-pp",
                "-cp", CLASSPATH,
                "-m", mainClass,
                "-a", OPTIONS);
        return World.get().getResult(PointerAnalysis.ID);
    }

    private static void assertFlow(Set<TaintFlow> flows, String sinkName) {
        assertTrue(flows.stream().anyMatch(flow -> flow.toString().contains(sinkName)),
                () -> "Expected flow to " + sinkName + ", got " + flows);
    }

    private static void assertNoFlow(Set<TaintFlow> flows, String sinkName) {
        assertFalse(flows.stream().anyMatch(flow -> flow.toString().contains(sinkName)),
                () -> "Did not expect flow to " + sinkName + ", got " + flows);
    }
}
