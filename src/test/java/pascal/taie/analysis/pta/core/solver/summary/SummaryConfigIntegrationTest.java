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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Path;
import java.util.Set;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.solver.SummarySolver;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysis;
import pascal.taie.analysis.pta.plugin.taint.TaintFlow;
import pascal.taie.language.classes.JMethod;

class SummaryConfigIntegrationTest {

    private static final String CLASSPATH =
            Path.of("src/test/resources/pta/summary-config")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    private static final String TAINT_CONFIG =
            Path.of("src/test/resources/pta/summary-config/taint-config.yml")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    private static final String SUMMARY_CONFIG =
            Path.of("src/test/resources/pta/summary-config/summary-config.yml")
                    .toAbsolutePath()
                    .normalize()
                    .toString();

    @Test
    void yamlSummaryConfigIsLoadedAndAppliedBySummarySolver() {
        try {
            Main.main(
                    "-pp",
                    "-cp", CLASSPATH,
                    "-m", "SummaryConfigTaint",
                    "-a", "pta=implicit-entries:false;"
                            + "only-app:true;"
                            + "distinguish-string-constants:all;"
                            + "cs:ci;"
                            + "codesummary:codesummary;"
                            + "summary-config:" + SUMMARY_CONFIG + ";"
                            + "taint-config:" + TAINT_CONFIG);

            PointerAnalysisResult pta = World.get().getResult("pta", null);
            Set<TaintFlow> flows = pta.getResult(TaintAnalysis.class.getName(), Set.of());
            JMethod wrapper = World.get().getClassHierarchy().getMethod(
                    "<SummaryConfigTaint: java.lang.String passthrough(java.lang.String)>");

            assertEquals(1, flows.size(), () -> "Expected summary-config wrapper flow, got " + flows);
            Set<String> ignoredMethods = pta.getResult(
                    SummarySolver.IGNORED_METHOD_SIGNATURES_KEY, Set.of());
            assertTrue(ignoredMethods.contains(wrapper.getSignature()),
                    "Summary-config methods should be registered as ignored by SummarySolver.");
            assertTrue(flows.stream().anyMatch(flow ->
                            flow.sourcePoint().toString().contains("SourceSink.source()")
                                    && flow.sinkPoint().sink().method().getSignature().equals(
                                    "<SourceSink: void sink(java.lang.String)>")),
                    () -> "Expected source to reach sink via YAML summary, got " + flows);
        } finally {
            World.reset();
        }
    }
}
