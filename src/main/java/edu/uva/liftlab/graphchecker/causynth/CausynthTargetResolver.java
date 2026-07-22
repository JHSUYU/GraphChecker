package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/** Resolves workflow properties and target YAML into a target context. */
final class CausynthTargetResolver {
    private CausynthTargetResolver() {
    }

    static CausynthTargetContext resolve(GraphCheckerOptions options)
            throws IOException {
        return resolve(options.getConfigFilePath());
    }

    static CausynthTargetContext resolve(String configPath)
            throws IOException {
        Map<String, String> config = readConfig(configPath);
        Path specPath = Paths.get(firstNonBlank(
                System.getProperty("causynth.target.spec"),
                config.get("causynth_target_spec"),
                "target.yaml")).toAbsolutePath().normalize();
        TargetSpec spec = TargetSpec.load(specPath);
        Path repo = Paths.get(firstNonBlank(
                System.getProperty("causynth.repo"),
                config.get("causynth_repo"),
                config.get("system_dir_path"),
                ".")).toAbsolutePath().normalize();
        Path module = Paths.get(firstNonBlank(
                System.getProperty("causynth.module.dir"),
                config.get("causynth_module_dir"),
                repo.toString())).toAbsolutePath().normalize();
        Path output = Paths.get(firstNonBlank(
                System.getProperty("causynth.output.dir"),
                config.get("causynth_output_dir"),
                "causynth-output/seed-backward"))
                .toAbsolutePath().normalize();
        String scope = firstNonBlank(
                System.getProperty("causynth.analysis.scope"),
                config.get("causynth_analysis_scope"),
                config.get("causynth_scope"),
                "");
        String rpcMapping = firstNonBlank(
                System.getProperty("causynth.rpc.mapping.file"),
                System.getenv("CAUSYNTH_RPC_MAPPING_FILE"),
                config.get("rpc_mapping_file"),
                config.get("causynth_rpc_mapping_file"));
        return new CausynthTargetContext(repo, module, output, specPath,
                spec.seedVariables, spec.seedFunction,
                spec.exceptionTargetId, null, scope,
                rpcMapping == null ? null : Paths.get(rpcMapping)
                .toAbsolutePath().normalize());
    }

    static Map<String, String> readConfig(String configPath)
            throws IOException {
        if (configPath == null || configPath.trim().isEmpty()) {
            return Collections.emptyMap();
        }
        Path path = Paths.get(configPath);
        if (!Files.isRegularFile(path)) {
            return Collections.emptyMap();
        }
        Map<String, String> values = new LinkedHashMap<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")
                        || !trimmed.contains("=")) {
                    continue;
                }
                int index = trimmed.indexOf('=');
                values.put(trimmed.substring(0, index).trim(),
                        trimmed.substring(index + 1).trim());
            }
        }
        return values;
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
    }

    private static final class TargetSpec {
        private final List<String> seedVariables;
        private final String seedFunction;
        private final String exceptionTargetId;

        private TargetSpec(List<String> seedVariables, String seedFunction,
                           String exceptionTargetId) {
            this.seedVariables = seedVariables;
            this.seedFunction = seedFunction;
            this.exceptionTargetId = exceptionTargetId;
        }

        private static TargetSpec load(Path path) throws IOException {
            if (!Files.isRegularFile(path)) {
                return new TargetSpec(Collections.emptyList(), null, null);
            }
            List<String> variables = new ArrayList<>();
            String seedFunction = null;
            String exceptionTargetId = null;
            boolean inSeedVariables = false;
            for (String line : Files.readAllLines(path,
                    StandardCharsets.UTF_8)) {
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                if (!line.startsWith(" ") && trimmed.contains(":")
                        && !trimmed.endsWith(":")) {
                    String key = trimmed.substring(0,
                            trimmed.indexOf(':')).trim();
                    String value = unquote(trimmed.substring(
                            trimmed.indexOf(':') + 1).trim());
                    if ("seed_function".equals(key)
                            || "seed_method".equals(key)) {
                        seedFunction = value;
                    }
                    if ("exception_target_id".equals(key)) {
                        exceptionTargetId = value;
                    }
                    if ("seed_exception".equals(key)
                            || "target_exception".equals(key)
                            || "exception".equals(key)) {
                        throw new IOException(key + " was removed; annotate "
                                + "the exact construction with "
                                + "@CausynthExceptionTarget instead");
                    }
                    inSeedVariables = false;
                    continue;
                }
                if (!line.startsWith(" ") && trimmed.endsWith(":")) {
                    inSeedVariables = "seed_variables".equals(
                            trimmed.substring(0, trimmed.length() - 1));
                    continue;
                }
                if (inSeedVariables && trimmed.startsWith("- ")) {
                    String variable = trimmed.substring(2).trim();
                    if (!variable.isEmpty()) {
                        variables.add(variable);
                    }
                }
            }
            return new TargetSpec(variables, seedFunction,
                    exceptionTargetId);
        }

        private static String unquote(String value) {
            if ((value.startsWith("\"") && value.endsWith("\""))
                    || (value.startsWith("'") && value.endsWith("'"))) {
                return value.substring(1, value.length() - 1);
            }
            return value;
        }
    }
}
