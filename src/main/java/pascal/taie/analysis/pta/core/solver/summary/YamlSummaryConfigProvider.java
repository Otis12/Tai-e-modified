/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.core.ObjectCodec;
import com.fasterxml.jackson.databind.DeserializationContext;
import com.fasterxml.jackson.databind.JsonDeserializer;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.module.SimpleModule;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.config.ConfigException;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.SignatureMatcher;
import pascal.taie.language.type.TypeSystem;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Loads {@link SummaryConfig} from YAML files.
 *
 * <p>This provider supports loading from a single file or a directory.
 * When loading from a directory, all YAML files are loaded and merged.
 *
 * <p>Expected YAML format:
 * <pre>
 * summaries:
 *   # Getter pattern: this.field -> result
 *   - { method: "&lt;Person: String getName()&gt;", from: base.name, to: result }
 *
 *   # Setter pattern: arg0 -> this.field
 *   - { method: "&lt;Person: void setName(String)&gt;", from: 0, to: base.name }
 *
 *   # Identity pattern: arg0 -> result
 *   - { method: "&lt;Utils: Object identity(Object)&gt;", from: 0, to: result }
 *
 *   # This-return pattern (Builder): this -> result
 *   - { method: "&lt;Builder: Builder set*(*)&gt;", from: base, to: result }
 *
 *   # Container add: arg0 -> this[*]
 *   - { method: "&lt;java.util.Collection^: boolean add(Object)&gt;", from: 0, to: "base[*]" }
 *
 *   # Container get: this[*] -> result
 *   - { method: "&lt;java.util.List^: Object get(int)&gt;", from: "base[*]", to: result }
 * </pre>
 *
 * <p>Method signature patterns support wildcards:
 * <ul>
 *   <li>{@code *} - matches any sequence of characters</li>
 *   <li>{@code ^} after class name - includes subclasses</li>
 *   <li>{@code (*)} - matches any parameters</li>
 * </ul>
 */
public class YamlSummaryConfigProvider extends SummaryConfigProvider {

    private static final Logger logger = LogManager.getLogger(YamlSummaryConfigProvider.class);

    private String path;

    public YamlSummaryConfigProvider(ClassHierarchy hierarchy, TypeSystem typeSystem) {
        super(hierarchy, typeSystem);
    }

    /**
     * Sets the path where the summary configuration is loaded.
     * If the path is a file, loads config from the file;
     * if the path is a directory, loads all YAML files and merges them.
     *
     * @param path the path to the configuration file or directory
     */
    public void setPath(String path) {
        this.path = path;
    }

    /**
     * Loads and returns the summary configuration.
     *
     * @return the loaded summary configuration
     * @throws ConfigException if failed to load the config
     */
    @Override
    public SummaryConfig get() {
        if (path == null || path.isBlank()) {
            return SummaryConfig.EMPTY;
        }

        ObjectMapper mapper = new ObjectMapper(new YAMLFactory());
        SimpleModule module = new SimpleModule();
        module.addDeserializer(SummaryConfig.class,
                new Deserializer(matcher, accessPathParser));
        mapper.registerModule(module);

        File file = new File(path);
        logger.info("Loading summary config from {}", file.getAbsolutePath());

        if (file.isFile()) {
            return loadSingle(mapper, file);
        } else if (file.isDirectory()) {
            // Load all YAML files in the directory and merge them
            SummaryConfig[] result = new SummaryConfig[]{ SummaryConfig.EMPTY };
            try (Stream<Path> paths = Files.walk(file.toPath())) {
                paths.filter(YamlSummaryConfigProvider::isYAML)
                        .map(p -> loadSingle(mapper, p.toFile()))
                        .forEach(sc -> result[0] = result[0].mergeWith(sc));
                return result[0];
            } catch (IOException e) {
                throw new ConfigException("Failed to load summary config from " + file, e);
            }
        } else {
            throw new ConfigException(path + " is neither a file nor a directory");
        }
    }

    /**
     * Loads summary config from a single file.
     */
    private static SummaryConfig loadSingle(ObjectMapper mapper, File file) {
        try {
            logger.debug("Loading summary config from file: {}", file);
            return mapper.readValue(file, SummaryConfig.class);
        } catch (IOException e) {
            throw new ConfigException("Failed to load summary config from " + file, e);
        }
    }

    /**
     * Checks if a path is a YAML file.
     */
    private static boolean isYAML(Path path) {
        String pathStr = path.toString();
        return pathStr.endsWith(".yml") || pathStr.endsWith(".yaml");
    }

    /**
     * JSON deserializer for {@link SummaryConfig}.
     */
    private static class Deserializer extends JsonDeserializer<SummaryConfig> {

        private final SignatureMatcher matcher;
        private final AccessPathParser accessPathParser;

        private Deserializer(SignatureMatcher matcher, AccessPathParser accessPathParser) {
            this.matcher = matcher;
            this.accessPathParser = accessPathParser;
        }

        @Override
        public SummaryConfig deserialize(JsonParser p, DeserializationContext ctxt)
                throws IOException {
            ObjectCodec oc = p.getCodec();
            JsonNode node = oc.readTree(p);
            List<SummaryDetail> summaries = deserializeSummaries(node.get("summaries"));
            return new SummaryConfig(summaries);
        }

        /**
         * Deserializes the "summaries" array node to a list of SummaryDetail.
         */
        private List<SummaryDetail> deserializeSummaries(JsonNode node) {
            if (!(node instanceof ArrayNode arrayNode)) {
                return List.of();
            }

            List<SummaryDetail> result = new ArrayList<>();
            for (JsonNode elem : arrayNode) {
                List<SummaryDetail> details = deserializeSingleSummary(elem);
                result.addAll(details);
            }
            return Collections.unmodifiableList(result);
        }

        /**
         * Deserializes a single summary rule element.
         */
        private List<SummaryDetail> deserializeSingleSummary(JsonNode elem) {
            JsonNode methodNode = elem.get("method");
            JsonNode fromNode = elem.get("from");
            JsonNode toNode = elem.get("to");

            if (methodNode == null || fromNode == null || toNode == null) {
                logger.warn("Ignoring incomplete summary rule: {}", elem);
                return List.of();
            }

            String methodSig = methodNode.asText();
            String fromStr = fromNode.asText();
            String toStr = toNode.asText();

            // Match methods using signature pattern
            Set<JMethod> methods = matcher.getMethods(methodSig);
            if (methods.isEmpty()) {
                logger.warn("Cannot find method matching '{}' for summary rule", methodSig);
                return List.of();
            }

            // Create SummaryDetail for each matched method
            List<SummaryDetail> result = new ArrayList<>();
            for (JMethod method : methods) {
                SummaryDetail detail = createSummaryDetail(method, fromStr, toStr);
                if (detail != null) {
                    result.add(detail);
                    logger.debug("Loaded summary rule: {}", detail);
                }
            }
            return result;
        }

        /**
         * Creates a SummaryDetail for the given method and access path strings.
         */
        private SummaryDetail createSummaryDetail(JMethod method, String fromStr, String toStr) {
            AccessPath source = accessPathParser.parse(method, fromStr);
            AccessPath target = accessPathParser.parse(method, toStr);

            if (source == null || target == null) {
                logger.warn("Failed to parse access path for method {}: from='{}', to='{}'",
                        method, fromStr, toStr);
                return null;
            }

            return SummaryDetail.of(method, fromStr, toStr, source, target);
        }
    }
}
