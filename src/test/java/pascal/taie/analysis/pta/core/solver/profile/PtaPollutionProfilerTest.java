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

package pascal.taie.analysis.pta.core.solver.profile;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.SummarySolver;
import pascal.taie.analysis.pta.core.solver.summary.JdkBoundaryClassifier;
import pascal.taie.config.AnalysisOptions;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class PtaPollutionProfilerTest {

    private static final ObjectMapper JSON = new ObjectMapper();

    @TempDir
    Path tempDir;

    @Test
    void pollutionProfilerIsDisabledByDefault() {
        PtaPollutionProfiler profiler = new PtaPollutionProfiler(
                new AnalysisOptions(Map.of()), new JdkBoundaryClassifier());

        Map<String, String> artifacts = profiler.writeArtifacts();

        assertTrue(artifacts.isEmpty());
        assertDoesNotThrow(() -> profiler.recordPFGEdge(new ExplodingEdge()));
    }

    @Test
    void heavyMethodProfilerDoesNotInspectEdgesWhenDisabled() {
        PtaHeavyMethodProfiler profiler = new PtaHeavyMethodProfiler(
                new AnalysisOptions(Map.of()), new JdkBoundaryClassifier());

        assertDoesNotThrow(() -> profiler.recordPFGEdge(new ExplodingEdge()));
    }

    @Test
    void boundaryDeltaDoesNotTreatMissingSelectedProfileAsZero()
            throws Exception {
        Path baseline = tempDir.resolve("baseline.json");
        Path fullSummary = tempDir.resolve("full-summary.json");
        Path profile = tempDir.resolve("selected.json");
        writeProfile(baseline, 3.0, 10);
        writeProfile(fullSummary, 1.0, 0);

        PtaPollutionProfiler profiler = new PtaPollutionProfiler(
                options(profile, baseline, null, fullSummary),
                new JdkBoundaryClassifier());

        Path deltaPath = Path.of(profiler.writeArtifacts()
                .get("pta_class_boundary_delta"));
        JsonNode delta = JSON.readTree(deltaPath.toFile());
        JsonNode stringClass = delta.get("classes").get(0);

        assertTrue(delta.get("available").asBoolean());
        assertTrue(delta.get("full_summary_only_available").asBoolean());
        assertEquals("java.lang.String", stringClass.get("class_name").asText());
        assertTrue(stringClass.get("selected_score").isNull());
        assertTrue(stringClass.get("normal_vs_selected_string_delta").isNull());
        assertEquals(2.0,
                stringClass.get("normal_vs_full_summary_only_delta").asDouble());
    }

    @Test
    void boundaryDeltaCanUseCurrentProfileAsSelectedComparison()
            throws Exception {
        Path baseline = tempDir.resolve("baseline.json");
        Path profile = tempDir.resolve("selected.json");
        writeProfile(baseline, 3.0, 10);

        PtaPollutionProfiler profiler = new PtaPollutionProfiler(
                options(profile, baseline, profile, null),
                new JdkBoundaryClassifier());

        Path deltaPath = Path.of(profiler.writeArtifacts()
                .get("pta_class_boundary_delta"));
        JsonNode delta = JSON.readTree(deltaPath.toFile());
        JsonNode stringClass = delta.get("classes").get(0);

        assertTrue(delta.get("available").asBoolean());
        assertTrue(delta.get("selected_available").asBoolean());
        assertNotNull(stringClass.get("selected_score"));
        assertEquals(0.0, stringClass.get("selected_score").asDouble());
        assertEquals(3.0,
                stringClass.get("normal_vs_selected_string_delta").asDouble());
        assertEquals(1.0,
                stringClass.get("selected_body_metric_drop").asDouble());
    }

    @Test
    void heavyMethodProfileExportsProfileMetricsAndHeavyList()
            throws Exception {
        Path testDir = Files.createTempDirectory(
                Path.of("build/tmp").toAbsolutePath().normalize(),
                "pta-heavy-method-profile-");
        Path classes = testDir.resolve("classes");
        compileFixture(classes, "HeavyProfileApp", """
                public class HeavyProfileApp {
                    static Object a;
                    static Object b;
                    public static void main(String[] args) {
                        Object left = new Object();
                        Object right = new Object();
                        a = heavy(left);
                        b = heavy(right);
                        light(left);
                    }
                    static Object heavy(Object input) {
                        Object[] array = new Object[1];
                        array[0] = input;
                        Object out = array[0];
                        return out;
                    }
                    static Object light(Object input) {
                        return input;
                    }
                }
                """);
        Path heavyPath = testDir.resolve("pta-heavy-polluting-methods.json");
        try {
            Main.main(
                    "-pp",
                    "-cp", classes.toString(),
                    "-m", "HeavyProfileApp",
                    "--output-dir", testDir.resolve("output").toString(),
                    "-a", "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary;"
                            + "jdk-analysis-mode:normal;"
                            + "merge-string-objects:false;"
                            + "merge-string-builders:false;"
                            + "pta-heavy-method-profile:"
                            + heavyPath.toAbsolutePath() + ";");

            PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
            @SuppressWarnings("unchecked")
            Map<String, String> artifacts = pta.getResult(
                    SummarySolver.PTA_PROFILING_ARTIFACTS_KEY, Map.of());
            assertEquals(heavyPath.toString(),
                    artifacts.get("pta_heavy_polluting_methods"));
            assertTrue(Files.isRegularFile(heavyPath));
            Path profilePath = Path.of(artifacts.get("pta_ci_method_profile"));
            Path metricsPath = Path.of(artifacts.get("pta_method_cg_pta_metrics"));
            Path mdPath = Path.of(artifacts.get("pta_heavy_polluting_methods_markdown"));
            Path cgPath = Path.of(artifacts.get("pta_heavy_method_callgraph"));
            Path topPath = Path.of(artifacts.get("pta_top_polluting_methods"));
            assertTrue(Files.isRegularFile(profilePath));
            assertTrue(Files.isRegularFile(metricsPath));
            assertTrue(Files.isRegularFile(mdPath));
            assertTrue(Files.isRegularFile(cgPath));
            assertTrue(Files.isRegularFile(topPath));

            JsonNode profile = JSON.readTree(profilePath.toFile());
            JsonNode methods = profile.get("methods");
            JsonNode heavyProfile = findMethod(methods,
                    "<HeavyProfileApp: java.lang.Object heavy(java.lang.Object)>");
            assertEquals("app", heavyProfile.get("category").asText());
            assertTrue(heavyProfile.get("reachable").asBoolean());
            assertTrue(heavyProfile.get("body_processed").asBoolean());
            assertTrue(heavyProfile.get("is_app").asBoolean());
            assertFalse(heavyProfile.get("is_non_app").asBoolean());

            JsonNode metrics = JSON.readTree(metricsPath.toFile());
            JsonNode heavyMetrics = findMethod(metrics.get("methods"),
                    "<HeavyProfileApp: java.lang.Object heavy(java.lang.Object)>");
            assertEquals(2, heavyMetrics.get("incoming_call_edge_count").asInt());
            assertEquals(2, heavyMetrics.get("app_reachable_callsite_count").asInt());
            assertTrue(heavyMetrics.get("return_pts_size").asInt() >= 2);
            assertTrue(heavyMetrics.get("local_pts_max").asInt() >= 2);
            assertTrue(heavyMetrics.get("method_pts_total").asInt() >= 2);
            assertTrue(heavyMetrics.get("field_store_load_edge_count").asInt() >= 0);
            assertTrue(heavyMetrics.get("array_store_load_edge_count").asInt() >= 2);
            assertTrue(heavyMetrics.get("pfg_in_degree_sum").asInt() > 0);
            assertTrue(heavyMetrics.get("pfg_out_degree_sum").asInt() > 0);
            assertEquals(0, heavyMetrics.get("return_taint_obj_count").asInt());
            assertFalse(heavyMetrics.get("receiver_state_effect").asBoolean());
            assertFalse(heavyMetrics.get("allocated_object_pts_fanout_metric_available").asBoolean());
            assertTrue(heavyMetrics.get("allocated_object_pts_fanout").isNull());

            JsonNode heavy = JSON.readTree(heavyPath.toFile());
            assertFalse(containsMethod(heavy.get("heavy_polluting_methods"),
                    "<HeavyProfileApp: java.lang.Object heavy(java.lang.Object)>"));

            JsonNode cg = JSON.readTree(cgPath.toFile());
            assertEquals(0, cg.get("heavy_method_edge_count").asInt());
            JsonNode topWithApp = cg.get("top_level_callers_with_app");
            JsonNode topWithoutApp = cg.get("top_level_callers_without_app");
            assertFalse(containsMethod(topWithApp,
                    "<HeavyProfileApp: void main(java.lang.String[])>"));
            assertTrue(topWithoutApp.isArray());

            JsonNode top = JSON.readTree(topPath.toFile());
            assertEquals(0, top.get("top_method_count").asInt());
        } finally {
            World.reset();
        }
    }

    @Test
    void heavyMethodProfileIncludesTaintedReturnWrappers()
            throws Exception {
        Path testDir = Files.createTempDirectory(
                Path.of("build/tmp").toAbsolutePath().normalize(),
                "pta-heavy-method-taint-filter-");
        Path classes = testDir.resolve("classes");
        compileFixture(classes, "TaintHeavyProfileApp", """
                public class TaintHeavyProfileApp {
                    static Object sink;
                    public static void main(String[] args) {
                        Object taint = source();
                        sink = caller0(taint);
                        sink = caller1(taint);
                        sink = caller2(taint);
                        sink = caller3(taint);
                        sink = caller4(taint);
                        sink = caller5(taint);
                        sink = tinyTaintedReturn(taint);
                        sink = inflatedTaintedReturn(taint);
                    }
                    static Object source() {
                        return new Object();
                    }
                    static Object caller0(Object input) {
                        return sharedTaintedReturn(input);
                    }
                    static Object caller1(Object input) {
                        return sharedTaintedReturn(input);
                    }
                    static Object caller2(Object input) {
                        return sharedTaintedReturn(input);
                    }
                    static Object caller3(Object input) {
                        return sharedTaintedReturn(input);
                    }
                    static Object caller4(Object input) {
                        return sharedTaintedReturn(input);
                    }
                    static Object caller5(Object input) {
                        return sharedTaintedReturn(input);
                    }
                    static Object sharedTaintedReturn(Object input) {
                        return input;
                    }
                    static Object tinyTaintedReturn(Object input) {
                        return input;
                    }
                    static Object inflatedTaintedReturn(Object input) {
                        Object[] a0 = new Object[1];
                        Object[] a1 = new Object[1];
                        Object[] a2 = new Object[1];
                        Object[] a3 = new Object[1];
                        Object[] a4 = new Object[1];
                        Object[] a5 = new Object[1];
                        a0[0] = input;
                        a1[0] = a0[0];
                        a2[0] = a1[0];
                        a3[0] = a2[0];
                        a4[0] = a3[0];
                        a5[0] = a4[0];
                        return a5[0];
                    }
                }
                """);
        Path taintConfig = testDir.resolve("taint-config.yml");
        Files.writeString(taintConfig, """
                sources:
                  - { kind: call, method: "<TaintHeavyProfileApp: java.lang.Object source()>", index: result }
                sinks: []
                """, StandardCharsets.UTF_8);
        Path heavyPath = testDir.resolve("pta-heavy-polluting-methods.json");
        try {
            Main.main(
                    "-pp",
                    "-cp", classes.toString(),
                    "-m", "TaintHeavyProfileApp",
                    "--output-dir", testDir.resolve("output").toString(),
                    "-a", "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary;"
                            + "jdk-analysis-mode:normal;"
                            + "merge-string-objects:false;"
                            + "merge-string-builders:false;"
                            + "taint-config:" + taintConfig.toAbsolutePath()
                            + ";pta-heavy-method-profile:"
                            + heavyPath.toAbsolutePath() + ";");

            JsonNode heavy = JSON.readTree(heavyPath.toFile());
            JsonNode selected = findMethod(heavy.get("heavy_polluting_methods"),
                    "<TaintHeavyProfileApp: java.lang.Object inflatedTaintedReturn(java.lang.Object)>");
            assertTrue(selected.get("return_taint_obj_count").asInt() > 0);
            assertTrue(hasReason(selected, "return_taint_obj_count > 0"));
            assertTrue(hasReason(selected, "method_pts_total >= p95"));
            JsonNode wrapper = findMethod(heavy.get("heavy_polluting_methods"),
                    "<TaintHeavyProfileApp: java.lang.Object tinyTaintedReturn(java.lang.Object)>");
            assertTrue(wrapper.get("return_taint_obj_count").asInt() > 0);
            assertTrue(hasReason(wrapper, "return_taint_obj_count > 0"));
            assertFalse(hasReason(wrapper, "method_pts_total >= p95"));
            JsonNode shared = findMethod(heavy.get("heavy_polluting_methods"),
                    "<TaintHeavyProfileApp: java.lang.Object sharedTaintedReturn(java.lang.Object)>");
            assertTrue(shared.get("return_taint_obj_count").asInt() > 0);
            assertTrue(shared.get("incoming_call_edge_count").asInt() >= 5);

            Path topPath = testDir.resolve("pta-top-polluting-methods.json");
            JsonNode top = JSON.readTree(topPath.toFile());
            assertEquals(1, top.get("top_method_count").asInt());
            assertTrue(containsMethod(top.get("top_polluting_methods"),
                    "<TaintHeavyProfileApp: java.lang.Object sharedTaintedReturn(java.lang.Object)>"));
            assertFalse(containsMethod(top.get("top_polluting_methods"),
                    "<TaintHeavyProfileApp: java.lang.Object inflatedTaintedReturn(java.lang.Object)>"));
            assertFalse(containsMethod(top.get("top_polluting_methods"),
                    "<TaintHeavyProfileApp: java.lang.Object tinyTaintedReturn(java.lang.Object)>"));
        } finally {
            World.reset();
        }
    }

    @Test
    void topPollutingMethodsSelectSccEntryAndExposeMembers()
            throws Exception {
        Path testDir = Files.createTempDirectory(
                Path.of("build/tmp").toAbsolutePath().normalize(),
                "pta-heavy-method-scc-entry-");
        Path classes = testDir.resolve("classes");
        compileFixture(classes, "SccTopHeavyProfileApp", """
                public class SccTopHeavyProfileApp {
                    static Object sink;
                    public static void main(String[] args) {
                        Object taint = source();
                        sink = entry0(taint);
                        sink = entry1(taint);
                        sink = entry2(taint);
                        sink = entry3(taint);
                        sink = entry4(taint);
                    }
                    static Object source() {
                        return new Object();
                    }
                    static Object entry0(Object input) { return cycleEntry(input); }
                    static Object entry1(Object input) { return cycleEntry(input); }
                    static Object entry2(Object input) { return cycleEntry(input); }
                    static Object entry3(Object input) { return cycleEntry(input); }
                    static Object entry4(Object input) { return cycleEntry(input); }
                    static Object cycleEntry(Object input) {
                        Object r0 = cycleMember(input);
                        Object r1 = cycleMember(r0);
                        Object r2 = cycleMember(r1);
                        Object r3 = cycleMember(r2);
                        return cycleMember(r3);
                    }
                    static Object cycleMember(Object input) {
                        if (input == null) {
                            return cycleEntry(input);
                        }
                        return input;
                    }
                }
                """);
        Path taintConfig = testDir.resolve("taint-config.yml");
        Files.writeString(taintConfig, """
                sources:
                  - { kind: call, method: "<SccTopHeavyProfileApp: java.lang.Object source()>", index: result }
                sinks: []
                """, StandardCharsets.UTF_8);
        Path heavyPath = testDir.resolve("pta-heavy-polluting-methods.json");
        try {
            Main.main(
                    "-pp",
                    "-cp", classes.toString(),
                    "-m", "SccTopHeavyProfileApp",
                    "--output-dir", testDir.resolve("output").toString(),
                    "-a", "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary;"
                            + "jdk-analysis-mode:normal;"
                            + "merge-string-objects:false;"
                            + "merge-string-builders:false;"
                            + "taint-config:" + taintConfig.toAbsolutePath()
                            + ";pta-heavy-method-profile:"
                            + heavyPath.toAbsolutePath() + ";");

            JsonNode top = JSON.readTree(
                    testDir.resolve("pta-top-polluting-methods.json").toFile());
            JsonNode selected = findMethod(top.get("top_polluting_methods"),
                    "<SccTopHeavyProfileApp: java.lang.Object cycleEntry(java.lang.Object)>");
            assertEquals("<SccTopHeavyProfileApp: java.lang.Object cycleEntry(java.lang.Object)>",
                    selected.get("signature").asText());
            assertEquals("app", selected.get("category").asText());
            assertTrue(selected.get("scc_entry_selected").asBoolean());
            assertTrue(containsMethod(selected.get("scc_members"),
                    "<SccTopHeavyProfileApp: java.lang.Object cycleMember(java.lang.Object)>"));
            assertTrue(selected.has("heavy_score"));
            assertTrue(selected.has("downstream_heavy_count"));
            assertTrue(selected.has("callers"));
            assertTrue(selected.has("callees"));
        } finally {
            World.reset();
        }
    }

    @Test
    void topPollutingMethodsRecordSharedDownstreamHelpers()
            throws Exception {
        Path testDir = Files.createTempDirectory(
                Path.of("build/tmp").toAbsolutePath().normalize(),
                "pta-heavy-method-shared-helper-");
        Path classes = testDir.resolve("classes");
        compileFixture(classes, "SharedHelperTopHeavyProfileApp", """
                public class SharedHelperTopHeavyProfileApp {
                    static Object sink;
                    public static void main(String[] args) {
                        Object taint = source();
                        sink = a0(taint);
                        sink = a1(taint);
                        sink = a2(taint);
                        sink = a3(taint);
                        sink = a4(taint);
                        sink = b0(taint);
                        sink = b1(taint);
                        sink = b2(taint);
                        sink = b3(taint);
                        sink = b4(taint);
                    }
                    static Object source() { return new Object(); }
                    static Object a0(Object input) { return topA(input); }
                    static Object a1(Object input) { return topA(input); }
                    static Object a2(Object input) { return topA(input); }
                    static Object a3(Object input) { return topA(input); }
                    static Object a4(Object input) { return topA(input); }
                    static Object b0(Object input) { return topB(input); }
                    static Object b1(Object input) { return topB(input); }
                    static Object b2(Object input) { return topB(input); }
                    static Object b3(Object input) { return topB(input); }
                    static Object b4(Object input) { return topB(input); }
                    static Object topA(Object input) { return sharedHelper(input); }
                    static Object topB(Object input) { return sharedHelper(input); }
                    static Object sharedHelper(Object input) { return input; }
                }
                """);
        Path taintConfig = testDir.resolve("taint-config.yml");
        Files.writeString(taintConfig, """
                sources:
                  - { kind: call, method: "<SharedHelperTopHeavyProfileApp: java.lang.Object source()>", index: result }
                sinks: []
                """, StandardCharsets.UTF_8);
        Path heavyPath = testDir.resolve("pta-heavy-polluting-methods.json");
        try {
            Main.main(
                    "-pp",
                    "-cp", classes.toString(),
                    "-m", "SharedHelperTopHeavyProfileApp",
                    "--output-dir", testDir.resolve("output").toString(),
                    "-a", "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary;"
                            + "jdk-analysis-mode:normal;"
                            + "merge-string-objects:false;"
                            + "merge-string-builders:false;"
                            + "taint-config:" + taintConfig.toAbsolutePath()
                            + ";pta-heavy-method-profile:"
                            + heavyPath.toAbsolutePath() + ";");

            JsonNode top = JSON.readTree(
                    testDir.resolve("pta-top-polluting-methods.json").toFile());
            JsonNode topA = findMethod(top.get("top_polluting_methods"),
                    "<SharedHelperTopHeavyProfileApp: java.lang.Object topA(java.lang.Object)>");
            JsonNode topB = findMethod(top.get("top_polluting_methods"),
                    "<SharedHelperTopHeavyProfileApp: java.lang.Object topB(java.lang.Object)>");
            String helper = "<SharedHelperTopHeavyProfileApp: java.lang.Object sharedHelper(java.lang.Object)>";
            assertTrue(containsMethod(topA.get("downstream_heavy_method_details"), helper));
            assertTrue(containsMethod(topB.get("downstream_heavy_method_details"), helper));
            assertTrue(findMethod(topA.get("downstream_heavy_method_details"), helper)
                    .get("shared").asBoolean());
            assertTrue(findMethod(topB.get("downstream_heavy_method_details"), helper)
                    .get("shared").asBoolean());
            assertTrue(containsMethod(top.get("shared_downstream_heavy_methods"), helper));
        } finally {
            World.reset();
        }
    }

    @Test
    void heavyMethodProfileWorksWithoutCodeSummary()
            throws Exception {
        Path testDir = Files.createTempDirectory(
                Path.of("build/tmp").toAbsolutePath().normalize(),
                "pta-heavy-method-default-solver-");
        Path classes = testDir.resolve("classes");
        compileFixture(classes, "DefaultSolverTaintHeavyProfileApp", """
                public class DefaultSolverTaintHeavyProfileApp {
                    static Object sink;
                    public static void main(String[] args) {
                        Object taint = source();
                        sink = sharedTaintedReturn(taint);
                    }
                    static Object source() {
                        return new Object();
                    }
                    static Object sharedTaintedReturn(Object input) {
                        return input;
                    }
                }
                """);
        Path taintConfig = testDir.resolve("taint-config.yml");
        Files.writeString(taintConfig, """
                sources:
                  - { kind: call, method: "<DefaultSolverTaintHeavyProfileApp: java.lang.Object source()>", index: result }
                sinks: []
                """, StandardCharsets.UTF_8);
        Path heavyPath = testDir.resolve("pta-heavy-polluting-methods.json");
        try {
            Main.main(
                    "-pp",
                    "-cp", classes.toString(),
                    "-m", "DefaultSolverTaintHeavyProfileApp",
                    "--output-dir", testDir.resolve("output").toString(),
                    "-a", "pta=implicit-entries:false;"
                            + "only-app:false;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:none;"
                            + "merge-string-objects:false;"
                            + "merge-string-builders:false;"
                            + "taint-config:" + taintConfig.toAbsolutePath()
                            + ";pta-heavy-method-profile:"
                            + heavyPath.toAbsolutePath() + ";");

            assertTrue(Files.isRegularFile(heavyPath));
            JsonNode heavy = JSON.readTree(heavyPath.toFile());
            assertEquals("none",
                    heavy.get("options").get("codesummary").asText());
            JsonNode selected = findMethod(heavy.get("heavy_polluting_methods"),
                    "<DefaultSolverTaintHeavyProfileApp: java.lang.Object sharedTaintedReturn(java.lang.Object)>");
            assertTrue(selected.get("return_taint_obj_count").asInt() > 0);
            Path topPath = testDir.resolve("pta-top-polluting-methods.json");
            assertTrue(Files.isRegularFile(topPath));
        } finally {
            World.reset();
        }
    }

    private static AnalysisOptions options(Path profile, Path baseline,
                                           Path selected, Path fullSummary) {
        return new AnalysisOptions(Map.of(
                "cs", "ci",
                "only-app", false,
                "codesummary", "codesummary",
                "jdk-analysis-mode", "summary-only",
                "merge-string-objects", false,
                "merge-string-builders", false,
                "pta-profile-output", profile.toString(),
                "pta-boundary-baseline", baseline.toString(),
                "pta-boundary-selected", selected == null
                        ? "" : selected.toString(),
                "pta-boundary-full-summary", fullSummary == null
                        ? "" : fullSummary.toString()));
    }

    private static void writeProfile(Path path, double score,
                                     int bodyProcessedMethods)
            throws Exception {
        Files.writeString(path, """
                {
                  "classes": [ {
                    "class_name": "java.lang.String",
                    "pollution_score": %s,
                    "body_processed_methods": %d,
                    "return_fan_out": %d,
                    "local_pts_total": %d,
                    "allocated_object_count": %d,
                    "shared_allocation_count": %d,
                    "array_index_pts_total": %d,
                    "instance_field_pts_total": %d,
                    "shared_array_index_count": %d,
                    "shared_hub_count": %d,
                    "pfg_in_degree": %d,
                    "pfg_out_degree": %d
                  } ]
                }
                """.formatted(
                score,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods,
                bodyProcessedMethods));
    }

    private static void compileFixture(Path classes, String className,
                                       String source) throws Exception {
        Files.createDirectories(classes);
        Path sourcePath = classes.resolve(className + ".java");
        Files.writeString(sourcePath, source, StandardCharsets.UTF_8);
        javax.tools.JavaCompiler compiler =
                javax.tools.ToolProvider.getSystemJavaCompiler();
        assertNotNull(compiler, "JDK compiler is required");
        int exit = compiler.run(null, null, null,
                "-d", classes.toString(),
                sourcePath.toString());
        assertEquals(0, exit, "Failed to compile heavy method profile fixture");
    }

    private static JsonNode findMethod(JsonNode methods, String signature) {
        for (JsonNode method : methods) {
            if (signature.equals(method.get("method_signature").asText())) {
                return method;
            }
        }
        throw new AssertionError("Missing method " + signature + " in " + methods);
    }

    private static boolean hasReason(JsonNode method, String reason) {
        return hasReason(method, "selection_reasons", reason);
    }

    private static boolean hasReason(JsonNode method, String field,
                                     String reason) {
        for (JsonNode item : method.get(field)) {
            if (reason.equals(item.asText())) {
                return true;
            }
        }
        return false;
    }

    private static boolean containsEdge(JsonNode edges, String caller,
                                        String callee) {
        for (JsonNode edge : edges) {
            if (caller.equals(edge.get("caller").get("method_signature").asText())
                    && callee.equals(edge.get("callee")
                    .get("method_signature").asText())) {
                return true;
            }
        }
        return false;
    }

    private static boolean containsMethod(JsonNode methods, String signature) {
        for (JsonNode method : methods) {
            if (signature.equals(method.get("method_signature").asText())) {
                return true;
            }
        }
        return false;
    }

    private static class ExplodingEdge extends PointerFlowEdge {

        ExplodingEdge() {
            super(FlowKind.LOCAL_ASSIGN, null, null);
        }

        @Override
        public Pointer source() {
            throw new AssertionError("disabled profiler inspected source");
        }

        @Override
        public Pointer target() {
            throw new AssertionError("disabled profiler inspected target");
        }
    }
}
