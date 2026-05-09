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

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.config.ConfigException;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

/**
 * Loads built-in and user-supplied JDK summary catalogs.
 */
public class JdkSummaryCatalogLoader {

    private static final Logger logger =
            LogManager.getLogger(JdkSummaryCatalogLoader.class);

    private static final String RESOURCE_ROOT = "pta-summaries/jdk/";

    private final ClassHierarchy hierarchy;

    private final String requestedProfile;

    private final String missingSignatureMode;

    private final List<String> extraCatalogs;

    private final AccessPathParser accessPathParser;

    private final ObjectMapper mapper = new ObjectMapper(new YAMLFactory());

    public JdkSummaryCatalogLoader(ClassHierarchy hierarchy,
                                   String requestedProfile,
                                   String missingSignatureMode,
                                   List<String> extraCatalogs) {
        this.hierarchy = hierarchy;
        this.requestedProfile = normalizeProfile(requestedProfile);
        this.missingSignatureMode = normalizeMissingSignatureMode(missingSignatureMode);
        this.extraCatalogs = List.copyOf(extraCatalogs == null ? List.of() : extraCatalogs);
        this.accessPathParser = new AccessPathParser(hierarchy);
    }

    public JdkSummaryCatalog load() {
        String selectedProfile = selectProfile(requestedProfile);
        Accumulator acc = new Accumulator(selectedProfile);
        loadResource("jdk-common.yml", acc);
        loadResource(selectedProfile + ".yml", acc);
        extraCatalogs.forEach(path -> loadFile(Path.of(path), acc));
        JdkSummaryCatalogStats stats = new JdkSummaryCatalogStats(
                selectedProfile,
                List.copyOf(acc.loadedCatalogs),
                acc.summaryDetails.size(),
                acc.noops.size(),
                List.copyOf(acc.skippedMissingSignatures));
        logger.info("Loaded JDK summary catalog profile={} catalogs={} summaries={} noops={} skipped={}",
                selectedProfile,
                stats.loadedCatalogs(),
                stats.summaryCount(),
                stats.noopCount(),
                stats.skippedMissingSignatures().size());
        return new JdkSummaryCatalog(
                new SummaryConfig(List.copyOf(acc.summaryDetails)),
                List.copyOf(acc.noops),
                stats);
    }

    private void loadResource(String fileName, Accumulator acc) {
        String resource = RESOURCE_ROOT + fileName;
        try (InputStream in = JdkSummaryCatalogLoader.class
                .getClassLoader()
                .getResourceAsStream(resource)) {
            if (in == null) {
                throw new ConfigException("Cannot find built-in JDK summary catalog: " + resource);
            }
            loadCatalog(mapper.readTree(in), resource, acc);
        } catch (IOException e) {
            throw new ConfigException("Failed to load JDK summary catalog: " + resource, e);
        }
    }

    private void loadFile(Path path, Accumulator acc) {
        try (InputStream in = Files.newInputStream(path)) {
            loadCatalog(mapper.readTree(in), path.toString(), acc);
        } catch (IOException e) {
            throw new ConfigException("Failed to load JDK summary catalog: " + path, e);
        }
    }

    private void loadCatalog(JsonNode root, String catalogName, Accumulator acc) {
        acc.loadedCatalogs.add(catalogName);
        loadSummaries(root.get("summaries"), catalogName, acc);
        loadNoops(root.get("noops"), catalogName, acc);
    }

    private void loadSummaries(JsonNode summariesNode, String catalogName, Accumulator acc) {
        if (!(summariesNode instanceof ArrayNode summaries)) {
            return;
        }
        for (JsonNode summaryNode : summaries) {
            String methodSignature = requiredText(summaryNode, "method", catalogName);
            rejectPrefixSelector(methodSignature, catalogName);
            JMethod method = resolveJdkMethod(methodSignature);
            if (method == null) {
                handleMissingSignature(methodSignature, catalogName, acc);
                continue;
            }
            JsonNode effectsNode = summaryNode.get("effects");
            if (!(effectsNode instanceof ArrayNode effects)) {
                throw new ConfigException("JDK summary missing effects in "
                        + catalogName + ": " + methodSignature);
            }
            for (JsonNode effectNode : effects) {
                JsonNode transfer = effectNode.get("transfer");
                if (transfer == null) {
                    throw new ConfigException("Unsupported JDK summary effect in "
                            + catalogName + ": " + effectNode);
                }
                String from = requiredText(transfer, "from", catalogName);
                String to = requiredText(transfer, "to", catalogName);
                SummaryDetail detail = createSummaryDetail(method, from, to, catalogName);
                acc.summaryDetails.add(detail);
            }
        }
    }

    private void loadNoops(JsonNode noopsNode, String catalogName, Accumulator acc) {
        if (!(noopsNode instanceof ArrayNode noops)) {
            return;
        }
        for (JsonNode noopNode : noops) {
            JsonNode selectorNode = noopNode.get("selector");
            String selector = selectorNode != null
                    ? selectorNode.asText()
                    : requiredText(noopNode, "method", catalogName);
            String reason = noopNode.hasNonNull("reason")
                    ? noopNode.get("reason").asText()
                    : "";
            if (isPrefixSelector(selector) || resolveJdkMethod(selector) != null) {
                acc.noops.add(new JdkNoOpSummary(selector, reason, catalogName));
            } else {
                handleMissingSignature(selector, catalogName, acc);
            }
        }
    }

    private JMethod resolveJdkMethod(String signature) {
        JMethod method = hierarchy.getJREMethod(signature);
        return method != null ? method : hierarchy.getMethod(signature);
    }

    private SummaryDetail createSummaryDetail(JMethod method,
                                              String from,
                                              String to,
                                              String catalogName) {
        AccessPath source = accessPathParser.parse(method, from);
        AccessPath target = accessPathParser.parse(method, to);
        if (source == null || target == null) {
            throw new ConfigException("Failed to parse JDK summary access path in "
                    + catalogName + ": " + method.getSignature() + " "
                    + from + " -> " + to);
        }
        return SummaryDetail.of(method, from, to, source, target);
    }

    private void handleMissingSignature(String signature,
                                        String catalogName,
                                        Accumulator acc) {
        switch (missingSignatureMode) {
            case "warn" -> {
                logger.warn("Skipping missing JDK summary signature in {}: {}",
                        catalogName, signature);
                acc.skippedMissingSignatures.add(new JdkSummaryCatalogStats.SkippedSignature(
                        signature, catalogName, "method not found"));
            }
            case "error" -> throw new ConfigException(
                    "Missing JDK summary signature in " + catalogName + ": " + signature);
            case "ignore" -> {
                // intentionally silent
            }
            default -> throw new ConfigException(
                    "Unsupported jdk-summary-missing-signature: " + missingSignatureMode);
        }
    }

    private static void rejectPrefixSelector(String selector, String catalogName) {
        if (isPrefixSelector(selector)) {
            throw new ConfigException("Prefix selector is only allowed in noops, not summaries: "
                    + selector + " in " + catalogName);
        }
    }

    private static boolean isPrefixSelector(String selector) {
        return selector != null
                && !selector.startsWith("<")
                && selector.endsWith(".*");
    }

    private static String requiredText(JsonNode node, String field, String catalogName) {
        JsonNode value = node.get(field);
        if (value == null || value.isNull()) {
            throw new ConfigException("Missing field '" + field
                    + "' in JDK summary catalog " + catalogName);
        }
        return value.asText();
    }

    private static String normalizeProfile(String profile) {
        String normalized = profile == null || profile.isBlank()
                ? "auto"
                : profile.trim().toLowerCase(Locale.ROOT);
        if (!normalized.equals("auto")
                && !normalized.equals("jdk8")
                && !normalized.equals("jdk17")) {
            throw new ConfigException("Unsupported jdk-summary-profile: " + profile);
        }
        return normalized;
    }

    private static String normalizeMissingSignatureMode(String mode) {
        String normalized = mode == null || mode.isBlank()
                ? "warn"
                : mode.trim().toLowerCase(Locale.ROOT);
        if (!normalized.equals("warn")
                && !normalized.equals("error")
                && !normalized.equals("ignore")) {
            throw new ConfigException("Unsupported jdk-summary-missing-signature: " + mode);
        }
        return normalized;
    }

    private static String selectProfile(String profile) {
        if (!profile.equals("auto")) {
            return profile;
        }
        int feature = Runtime.version().feature();
        return feature >= 11 ? "jdk17" : "jdk8";
    }

    private static final class Accumulator {

        private final String selectedProfile;

        private final List<SummaryDetail> summaryDetails = new ArrayList<>();

        private final List<JdkNoOpSummary> noops = new ArrayList<>();

        private final List<String> loadedCatalogs = new ArrayList<>();

        private final List<JdkSummaryCatalogStats.SkippedSignature> skippedMissingSignatures =
                new ArrayList<>();

        private Accumulator(String selectedProfile) {
            this.selectedProfile = selectedProfile;
        }
    }
}
