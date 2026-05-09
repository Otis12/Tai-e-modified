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
import org.junit.jupiter.api.io.TempDir;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.config.ConfigException;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JdkSummaryCatalogLoaderTest {

    private static final String CLASSPATH = "src/test/resources/world";

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-pp", "-cp", CLASSPATH, "--input-classes", "ConstVar");
    }

    @AfterAll
    static void resetWorld() {
        World.reset();
    }

    @TempDir
    Path tempDir;

    @Test
    void loadCommonCatalog() {
        JdkSummaryCatalog catalog = load("jdk8", "warn");

        assertTrue(catalog.summaryConfig().summaryDetails().stream().anyMatch(summary ->
                summary.method().getSignature().equals(
                        "<java.lang.String: java.lang.String trim()>")
                        && summary.sourceStr().equals("base")
                        && summary.targetStr().equals("result")));
        assertTrue(catalog.noops().stream().anyMatch(noop ->
                noop.selector().equals("sun.*")));
        assertTrue(catalog.stats().loadedCatalogs().stream().anyMatch(catalogName ->
                catalogName.endsWith("jdk-common.yml")));
        assertEquals("jdk8", catalog.stats().selectedProfile());
    }

    @Test
    void explicitJdk8ProfileLoadsCommonAndJdk8() {
        JdkSummaryCatalog catalog = load("jdk8", "warn");

        assertTrue(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith("jdk-common.yml")));
        assertTrue(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith("jdk8.yml")));
        assertFalse(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith("jdk17.yml")));
    }

    @Test
    void explicitJdk17ProfileLoadsCommonAndJdk17() {
        JdkSummaryCatalog catalog = load("jdk17", "warn");

        assertTrue(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith("jdk-common.yml")));
        assertTrue(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith("jdk17.yml")));
        assertFalse(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith("jdk8.yml")));
        assertTrue(catalog.summaryConfig().summaryDetails().stream().anyMatch(summary ->
                summary.method().getSignature().equals(
                        "<java.lang.String: java.lang.String strip()>")));
    }

    @Test
    void autoProfileSelectsOneBuiltInProfile() {
        JdkSummaryCatalog catalog = load("auto", "warn");

        assertTrue(Set.of("jdk8", "jdk17").contains(catalog.stats().selectedProfile()));
        assertTrue(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith("jdk-common.yml")));
        assertTrue(catalog.stats().loadedCatalogs().stream().anyMatch(name ->
                name.endsWith(catalog.stats().selectedProfile() + ".yml")));
    }

    @Test
    void warnMissingSignatureSkipsAndRecords() throws IOException {
        Path extra = writeCatalog("""
                schema_version: 1
                id: missing-warn
                scope: jdk
                summaries:
                  - method: "<java.lang.String: java.lang.String definitelyMissing()>"
                    effects:
                      - transfer: { from: base, to: result }
                noops: []
                """);

        JdkSummaryCatalog catalog = load("jdk8", "warn", List.of(extra.toString()));

        assertTrue(catalog.stats().skippedMissingSignatures().stream().anyMatch(skip ->
                skip.method().equals(
                        "<java.lang.String: java.lang.String definitelyMissing()>")));
    }

    @Test
    void errorMissingSignatureFails() throws IOException {
        Path extra = writeCatalog("""
                schema_version: 1
                id: missing-error
                scope: jdk
                summaries:
                  - method: "<java.lang.String: java.lang.String definitelyMissing()>"
                    effects:
                      - transfer: { from: base, to: result }
                noops: []
                """);

        assertThrows(ConfigException.class,
                () -> load("jdk8", "error", List.of(extra.toString())));
    }

    @Test
    void ignoreMissingSignatureSkipsQuietly() throws IOException {
        Path extra = writeCatalog("""
                schema_version: 1
                id: missing-ignore
                scope: jdk
                summaries:
                  - method: "<java.lang.String: java.lang.String definitelyMissing()>"
                    effects:
                      - transfer: { from: base, to: result }
                noops: []
                """);

        JdkSummaryCatalog catalog = load("jdk8", "ignore", List.of(extra.toString()));

        assertTrue(catalog.stats().skippedMissingSignatures().isEmpty());
        assertFalse(catalog.summaryConfig().summaryDetails().stream().anyMatch(summary ->
                summary.method().getSignature().contains("definitelyMissing")));
    }

    @Test
    void prefixSelectorInTransferSummaryIsRejected() throws IOException {
        Path extra = writeCatalog("""
                schema_version: 1
                id: bad-prefix
                scope: jdk
                summaries:
                  - method: "sun.*"
                    effects:
                      - transfer: { from: base, to: result }
                noops: []
                """);

        assertThrows(ConfigException.class,
                () -> load("jdk8", "warn", List.of(extra.toString())));
    }

    @Test
    void prefixSelectorInNoopIsAllowed() throws IOException {
        Path extra = writeCatalog("""
                schema_version: 1
                id: prefix-noop
                scope: jdk
                summaries: []
                noops:
                  - selector: "sun.*"
                    reason: "test no-op"
                """);

        JdkSummaryCatalog catalog = load("jdk8", "warn", List.of(extra.toString()));

        assertTrue(catalog.noops().stream().anyMatch(noop ->
                noop.selector().equals("sun.*")
                        && noop.reason().equals("test no-op")));
    }

    private JdkSummaryCatalog load(String profile, String missingSignature) {
        return load(profile, missingSignature, List.of());
    }

    private JdkSummaryCatalog load(String profile,
                                   String missingSignature,
                                   List<String> extraCatalogs) {
        return new JdkSummaryCatalogLoader(
                World.get().getClassHierarchy(),
                profile,
                missingSignature,
                extraCatalogs).load();
    }

    private Path writeCatalog(String content) throws IOException {
        Path catalog = Files.createTempFile(tempDir, "jdk-catalog-", ".yml");
        Files.writeString(catalog, content);
        return catalog;
    }
}
