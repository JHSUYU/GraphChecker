package edu.uva.liftlab.graphchecker.grey;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public final class GreyStateSpecLoader {
    public boolean looksLikeGreyStateConfig(Path path) {
        if (path == null) {
            return false;
        }
        try {
            for (String line : Files.readAllLines(path)) {
                String stripped = stripComment(line).trim();
                if ("fatal_seeds:".equals(stripped) || stripped.startsWith("fatal_seeds:")) {
                    return true;
                }
            }
            return false;
        } catch (IOException exception) {
            return false;
        }
    }

    public GreyStateSpec load(Path path) {
        if (path == null) {
            throw new IllegalArgumentException("Config path must not be null");
        }
        try {
            return parse(Files.readAllLines(path));
        } catch (IOException exception) {
            throw new IllegalArgumentException("Failed to read config file " + path, exception);
        }
    }

    private GreyStateSpec parse(List<String> lines) {
        List<GreyStateSpec.FatalSeed> seeds = new ArrayList<GreyStateSpec.FatalSeed>();
        List<String> analysisClasses = new ArrayList<String>();
        String outputDir = "grey-output";
        int bound = 4;

        String activeList = null;
        Map<String, String> currentSeed = null;

        for (String raw : lines) {
            String line = stripComment(raw);
            if (line.trim().isEmpty()) {
                continue;
            }
            String trimmed = line.trim();

            if (trimmed.endsWith(":") && !trimmed.startsWith("- ")) {
                activeList = trimmed.substring(0, trimmed.length() - 1);
                continue;
            }

            if ("output_dir".equals(keyOf(trimmed))) {
                outputDir = valueOf(trimmed);
                activeList = null;
                continue;
            }
            if ("bound".equals(keyOf(trimmed))) {
                bound = parseInt(valueOf(trimmed), 4);
                activeList = null;
                continue;
            }

            if ("analysis_classes".equals(activeList) && trimmed.startsWith("- ")) {
                analysisClasses.add(trimmed.substring(2).trim());
                continue;
            }

            if ("fatal_seeds".equals(activeList)) {
                if (trimmed.startsWith("- ")) {
                    if (currentSeed != null) {
                        seeds.add(toSeed(currentSeed));
                    }
                    currentSeed = new LinkedHashMap<String, String>();
                    String remainder = trimmed.substring(2).trim();
                    if (!remainder.isEmpty() && remainder.contains(":")) {
                        currentSeed.put(keyOf(remainder), valueOf(remainder));
                    }
                    continue;
                }
                if (currentSeed != null && trimmed.contains(":")) {
                    currentSeed.put(keyOf(trimmed), valueOf(trimmed));
                }
            }
        }

        if (currentSeed != null) {
            seeds.add(toSeed(currentSeed));
        }
        return new GreyStateSpec(seeds, analysisClasses, outputDir, bound);
    }

    private GreyStateSpec.FatalSeed toSeed(Map<String, String> values) {
        return new GreyStateSpec.FatalSeed(
                values.get("id"),
                firstNonNull(values.get("class"), values.get("className")),
                firstNonNull(values.get("method"), values.get("methodName")),
                values.get("exception"));
    }

    private static String firstNonNull(String first, String second) {
        return first != null ? first : second;
    }

    private static String keyOf(String line) {
        int separator = line.indexOf(':');
        if (separator < 0) {
            return "";
        }
        return line.substring(0, separator).trim();
    }

    private static String valueOf(String line) {
        int separator = line.indexOf(':');
        if (separator < 0) {
            return "";
        }
        String value = line.substring(separator + 1).trim();
        if ((value.startsWith("\"") && value.endsWith("\""))
                || (value.startsWith("'") && value.endsWith("'"))) {
            return value.substring(1, value.length() - 1);
        }
        return value;
    }

    private static int parseInt(String raw, int fallback) {
        try {
            return Integer.parseInt(raw.trim());
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String stripComment(String line) {
        int comment = line.indexOf('#');
        return comment >= 0 ? line.substring(0, comment) : line;
    }
}
