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
import pascal.taie.analysis.pta.core.solver.summary.JdkBoundaryClassifier;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.VoidType;

import java.lang.reflect.Field;
import java.nio.file.Path;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class PtaSummaryFrontierProfilerTest {

    private static final ObjectMapper JSON = new ObjectMapper();

    @TempDir
    Path tempDir;

    @Test
    void profilerIsDisabledByDefault() {
        PtaSummaryFrontierProfiler profiler = new PtaSummaryFrontierProfiler(
                new AnalysisOptions(Map.of(
                        "cs", "ci",
                        "only-app", false,
                        "codesummary", "codesummary",
                        "jdk-analysis-mode", "normal",
                        "merge-string-objects", false,
                        "merge-string-builders", false,
                        "pta-summary-frontier-profile",
                        tempDir.resolve("disabled-ranking.json").toString())),
                new JdkBoundaryClassifier());
        JMethod caller = method("com.acme.Controller", "handle", true);
        JMethod frontier = method("java.lang.String", "split", false);

        profiler.recordDirectFrontier(caller, frontier,
                "com.acme.Controller.handle#12@L34", 34);

        Map<String, String> artifacts = profiler.writeArtifacts();

        assertTrue(artifacts.isEmpty());
        assertFalse(tempDir.resolve("disabled-ranking.json").toFile().exists());
    }

    @Test
    void helperHubIsAttributedToAppUsedFrontierNotSelectedAsMethod()
            throws Exception {
        PtaSummaryFrontierProfiler profiler = new PtaSummaryFrontierProfiler(
                options(tempDir.resolve("pta-summary-frontier-ranking.json")),
                new JdkBoundaryClassifier());
        JMethod caller = method("com.acme.Controller", "handle", true);
        JMethod frontier = method("java.lang.String", "split", false);
        JMethod helper = method("java.util.regex.Pattern$Node", "match", false);

        profiler.recordDirectFrontier(caller, frontier,
                "com.acme.Controller.handle#12@L34", 34);
        profiler.recordReachableMethod(frontier, true, null);
        profiler.recordReachableMethod(helper, true, null);
        profiler.recordNonAppCall(frontier, helper, "VIRTUAL", false);
        profiler.recordSyntheticHub(
                "hub:pattern-node-match",
                helper,
                "local",
                12,
                3,
                2,
                1,
                4,
                Set.of("RETURN"),
                List.of(
                        origin(caller, "site-a", null, frontier),
                        origin(caller, "site-b", null, frontier),
                        origin(caller, "site-c", null, frontier)));

        Map<String, String> artifacts = profiler.writeArtifacts();
        JsonNode frontiers = JSON.readTree(Path.of(
                artifacts.get("pta_app_frontier_methods")).toFile());
        JsonNode ranking = JSON.readTree(Path.of(
                artifacts.get("pta_summary_frontier_ranking")).toFile());
        JsonNode attribution = JSON.readTree(Path.of(
                artifacts.get("pta_method_hub_attribution")).toFile());

        assertEquals(1, frontiers.get("frontier_methods").size());
        assertEquals(frontier.getSignature(), frontiers.get("frontier_methods")
                .get(0).get("method_signature").asText());
        assertEquals(frontier.getSignature(), ranking.get("selected_methods")
                .get(0).get("method_signature").asText());
        for (JsonNode selected : ranking.get("selected_methods")) {
            assertFalse(helper.getSignature().equals(
                    selected.get("method_signature").asText()));
        }
        assertEquals("DOMINATED_HELPER", attribution.get("attributions")
                .get(0).get("coverage_reason").asText());
    }

    @Test
    void coverageReportsUncoveredHubInsteadOfInventingFullRecall()
            throws Exception {
        PtaSummaryFrontierProfiler profiler = new PtaSummaryFrontierProfiler(
                options(tempDir.resolve("ranking.json")),
                new JdkBoundaryClassifier());
        JMethod caller = method("com.acme.Controller", "handle", true);
        JMethod frontier = method("java.lang.StringBuilder", "append", false);
        JMethod coveredHelper = method("java.lang.AbstractStringBuilder",
                "appendChars", false);
        JMethod uncoveredOwner = method("java.util.HashMap", "resize", false);

        profiler.recordDirectFrontier(caller, frontier,
                "com.acme.Controller.handle#20@L51", 51);
        profiler.recordNonAppCall(frontier, coveredHelper, "VIRTUAL", false);
        profiler.recordSyntheticHub("hub:covered", coveredHelper, "local",
                9, 2, 1, 0, 3, Set.of("INSTANCE_STORE"),
                List.of(
                        origin(caller, "site-a", null, frontier),
                        origin(caller, "site-b", null, frontier)));
        profiler.recordSyntheticHub("hub:uncovered", uncoveredOwner, "local",
                9, 2, 1, 0, 3, Set.of("RETURN"),
                List.of(
                        origin(caller, "site-c", null, uncoveredOwner),
                        origin(caller, "site-d", null, uncoveredOwner)));

        JsonNode coverage = JSON.readTree(Path.of(profiler.writeArtifacts()
                .get("pta_frontier_hub_coverage")).toFile());

        assertTrue(coverage.get("recall").asDouble() < 1.0);
        assertEquals("hub:uncovered", coverage.get("uncovered_hubs")
                .get(0).get("hub_id").asText());
    }

    @Test
    void originSetMergesDistinctCallsitesAndHonorsCap() {
        JMethod caller = method("com.acme.Controller", "handle", true);
        JMethod boundary = method("java.lang.String", "trim", false);
        OriginSet origins = new OriginSet(2);

        origins.add(origin(caller, "site-a", null, boundary));
        origins.add(origin(caller, "site-b", null, boundary));
        origins.add(origin(caller, "site-c", null, boundary));

        assertEquals(2, origins.size());
        assertTrue(origins.isCapped());
        assertEquals(2, origins.appCallsiteCount());
        assertEquals(1, origins.boundaryMethodCounts().size());
    }

    private static AnalysisOptions options(Path rankingPath) {
        return new AnalysisOptions(Map.ofEntries(
                Map.entry("cs", "ci"),
                Map.entry("only-app", false),
                Map.entry("codesummary", "codesummary"),
                Map.entry("jdk-analysis-mode", "normal"),
                Map.entry("merge-string-objects", false),
                Map.entry("merge-string-builders", false),
                Map.entry("pta-summary-frontier-profile-enabled", true),
                Map.entry("pta-summary-frontier-profile",
                        rankingPath.toString()),
                Map.entry("pta-summary-frontier-target-recall", 1.0),
                Map.entry("pta-summary-frontier-max-slice-depth", 8),
                Map.entry("pta-summary-frontier-origin-cap", 2)));
    }

    private static AppOrigin origin(JMethod appMethod, String callsite,
                                    String alloc, JMethod boundary) {
        return new AppOrigin(
                appMethod.getSignature(),
                callsite,
                alloc,
                boundary.getSignature());
    }

    private static JMethod method(String declaringClassName, String name,
                                  boolean application) {
        try {
            JClass owner = new JClass(DUMMY_LOADER, declaringClassName);
            Field field = JClass.class.getDeclaredField("isApplication");
            field.setAccessible(true);
            field.setBoolean(owner, application);
            return new JMethod(
                    owner,
                    name,
                    Set.of(Modifier.PUBLIC),
                    List.of(),
                    VoidType.VOID,
                    List.of(),
                    null,
                    AnnotationHolder.emptyHolder(),
                    null,
                    null,
                    "test");
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
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
}
