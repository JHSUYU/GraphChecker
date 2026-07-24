package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Plans the deterministic branch-flip frontier for one captured output
 * closure. Solving and executing an exact task belong to
 * {@link ConcolicPathFlipSolver}; keeping those operations separate lets one
 * immutable frontier feed many independent worker processes.
 */
public final class ConcolicPathFlipPlanner {
    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ConcolicPathFlipPlanner() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        RegionPathWorklist.Result result = plan(arguments);
        writeOutputs(arguments.outputDirectory, result);
        System.out.println(PRETTY.toJson(result.manifest));
        String state = string(result.manifest, "state");
        if (RegionPathWorklist.State.GAPPED.name().equals(state)
                || RegionPathWorklist.State.NOT_STARTED.name().equals(state)) {
            System.exit(2);
        }
    }

    static RegionPathWorklist.Result plan(Arguments arguments)
            throws IOException {
        List<JsonObject> allActivations = readJsonl(arguments.activations);
        List<JsonObject> allSummaries = readJsonl(arguments.summaries);
        List<JsonObject> records = arguments.records == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.records);

        List<JsonObject> activations = filterActivations(allActivations,
                arguments.regionId);
        Map<String, JsonObject> activationById = uniqueIndex(activations,
                "activationId");
        List<JsonObject> summaries = filterSummaries(allSummaries,
                activationById, arguments.regionId);
        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                summaries, activations, records, arguments.pathBounds);
        Collections.sort(result.tasks, Comparator.comparing(
                task -> string(task, "queryKey")));
        return result;
    }

    static void writeOutputs(Path directory, RegionPathWorklist.Result result)
            throws IOException {
        writeJsonl(directory.resolve("region_path_worklist.jsonl"),
                result.tasks);
        ArtifactIO.replace(directory.resolve("region_path_manifest.json"),
                PRETTY.toJson(result.manifest) + System.lineSeparator());
    }

    private static List<JsonObject> filterActivations(
            List<JsonObject> source, String regionId) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject activation : source) {
            if (!regionId.isEmpty()
                    && !regionId.equals(string(activation, "regionId"))) {
                continue;
            }
            result.add(activation.deepCopy());
        }
        return result;
    }

    private static List<JsonObject> filterSummaries(
            List<JsonObject> source, Map<String, JsonObject> activations,
            String regionId) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject summary : source) {
            if (!activations.containsKey(string(summary, "activationId"))) {
                continue;
            }
            if (!regionId.isEmpty()
                    && !regionId.equals(string(summary, "regionId"))) {
                continue;
            }
            result.add(summary.deepCopy());
        }
        return result;
    }

    private static Map<String, JsonObject> uniqueIndex(
            List<JsonObject> rows, String field) throws IOException {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            String key = string(row, field);
            if (key.isEmpty()) continue;
            JsonObject previous = result.put(key, row);
            if (previous != null && !previous.equals(row)) {
                throw new IOException("Conflicting duplicate " + field
                        + ": " + key);
            }
        }
        return result;
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        return ArtifactIO.readJsonl(path, "Malformed JSONL %1$s:%2$d",
                "Non-object JSONL row %1$s:%2$d");
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder content = new StringBuilder();
        for (JsonObject row : rows) {
            content.append(JSON.toJson(row)).append(System.lineSeparator());
        }
        ArtifactIO.replace(path, content.toString());
    }

    private static String string(JsonObject object, String field) {
        if (object == null) return "";
        JsonElement value = object.get(field);
        try {
            return value != null && value.isJsonPrimitive()
                    ? value.getAsString() : "";
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    static final class Arguments {
        private final Path summaries;
        private final Path activations;
        private final Path records;
        private final Path outputDirectory;
        private final RegionPathWorklist.Bounds pathBounds;
        private final String regionId;

        private Arguments(Path summaries, Path activations, Path records,
                          Path outputDirectory,
                          RegionPathWorklist.Bounds pathBounds,
                          String regionId) {
            this.summaries = summaries;
            this.activations = activations;
            this.records = records;
            this.outputDirectory = outputDirectory;
            this.pathBounds = pathBounds;
            this.regionId = regionId;
        }

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index++) {
                String option = argv[index];
                if (!option.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --name value, got " + option);
                }
                values.put(option.substring(2), argv[++index]);
            }
            Path summaries = required(values, "summaries");
            Path activations = required(values, "activations");
            Path output = required(values, "output-dir");
            Path records = optionalPath(values.get("records"));
            RegionPathWorklist.Bounds defaults =
                    RegionPathWorklist.Bounds.defaults();
            RegionPathWorklist.Bounds bounds =
                    new RegionPathWorklist.Bounds(
                            intValue(values, "max-paths-per-region",
                                    defaults.maxPathsPerRegion),
                            intValue(values, "max-flips-per-path",
                                    defaults.maxFlipsPerPath),
                            intValue(values, "max-tasks",
                                    defaults.maxTasks));
            return new Arguments(summaries, activations, records, output,
                    bounds, value(values, "region-id"));
        }

        private static Path required(Map<String, String> values,
                                     String name) {
            String value = values.get(name);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + name);
            }
            return Paths.get(value);
        }

        private static Path optionalPath(String value) {
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
        }

        private static String value(Map<String, String> values,
                                    String name) {
            String result = values.get(name);
            return result == null ? "" : result;
        }

        private static int intValue(Map<String, String> values, String name,
                                    int fallback) {
            String value = values.get(name);
            return value == null || value.trim().isEmpty()
                    ? fallback : Integer.parseInt(value);
        }

    }
}
