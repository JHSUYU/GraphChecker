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
import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/** Resolves workflow properties and target YAML into a target context. */
final class CausynthTargetResolver {
    private CausynthTargetResolver() {
    }

    static CausynthTargetContext resolve(GraphCheckerOptions options)
            throws IOException {
        Map<String, String> config = readConfig(options.getConfigFilePath());
        Path specPath = Paths.get(firstNonBlank(
                System.getProperty("causynth.target.spec"),
                config.get("causynth_target_spec"),
                "target.yaml")).toAbsolutePath().normalize();
        String exceptionTargetId = exceptionTargetId(specPath);
        Path output = Paths.get(firstNonBlank(
                System.getProperty("causynth.output.dir"),
                config.get("causynth_output_dir"),
                "causynth-output/seed-backward"))
                .toAbsolutePath().normalize();
        return new CausynthTargetContext(output, exceptionTargetId, null);
    }

    private static Map<String, String> readConfig(String configPath)
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

    /** The single {@code exception_target_id} of a target specification, or
     *  null when the file is absent. */
    private static String exceptionTargetId(Path path) throws IOException {
        if (!Files.isRegularFile(path)) {
            return null;
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
            if (!"exception_target_id".equals(
                    trimmed.substring(0, separator).trim())
                    || exceptionTargetId != null) {
                throw new IOException("Target specification accepts only "
                        + "one exception_target_id");
            }
            exceptionTargetId = trimmed.substring(separator + 1).trim();
            if ((exceptionTargetId.startsWith("\"")
                    && exceptionTargetId.endsWith("\""))
                    || (exceptionTargetId.startsWith("'")
                    && exceptionTargetId.endsWith("'"))) {
                exceptionTargetId = exceptionTargetId.substring(1,
                        exceptionTargetId.length() - 1);
            }
        }
        return exceptionTargetId;
    }
}
