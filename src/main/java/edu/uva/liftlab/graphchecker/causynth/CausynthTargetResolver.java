package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashMap;
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
        Path output = Paths.get(firstNonBlank(
                System.getProperty("causynth.output.dir"),
                config.get("causynth_output_dir"),
                "causynth-output/seed-backward"))
                .toAbsolutePath().normalize();
        String scope = firstNonBlank(
                System.getProperty("causynth.analysis.scope"),
                config.get("causynth_analysis_scope"),
                "");
        return new CausynthTargetContext(output, specPath,
                spec.exceptionTargetId, null, scope);
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
        private final String exceptionTargetId;

        private TargetSpec(String exceptionTargetId) {
            this.exceptionTargetId = exceptionTargetId;
        }

        private static TargetSpec load(Path path) throws IOException {
            if (!Files.isRegularFile(path)) {
                return new TargetSpec(null);
            }
            String exceptionTargetId = null;
            for (String line : Files.readAllLines(path,
                    StandardCharsets.UTF_8)) {
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                int separator = trimmed.indexOf(':');
                if (line.startsWith(" ") || separator <= 0
                        || trimmed.endsWith(":")) {
                    throw new IOException("Unsupported target specification "
                            + "entry: " + trimmed);
                }
                String key = trimmed.substring(0, separator).trim();
                if (!"exception_target_id".equals(key)
                        || exceptionTargetId != null) {
                    throw new IOException("Target specification accepts only "
                            + "one exception_target_id");
                }
                exceptionTargetId = unquote(trimmed.substring(
                        separator + 1).trim());
            }
            return new TargetSpec(exceptionTargetId);
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
