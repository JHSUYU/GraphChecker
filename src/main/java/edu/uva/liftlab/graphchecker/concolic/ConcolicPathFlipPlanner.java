package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Plans the deterministic branch-flip frontier for one captured output
 * closure. Solving and executing an exact task belong to
 * {@link ConcolicPathFlipSolver}; keeping those operations separate lets one
 * immutable frontier feed many independent worker processes.
 */
public final class ConcolicPathFlipPlanner {
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ConcolicPathFlipPlanner() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        RegionPathWorklist.Result result = plan(arguments);
        writeOutputs(arguments.outputDirectory, result);
        JsonObject display = result.manifest.deepCopy();
        display.remove(OutputClosureContract.FIELD);
        System.out.println(PRETTY.toJson(display));
        String state = string(result.manifest, "state");
        if (RegionPathWorklist.State.GAPPED.name().equals(state)
                || RegionPathWorklist.State.NOT_STARTED.name().equals(state)) {
            System.exit(2);
        }
    }

    static RegionPathWorklist.Result plan(Arguments arguments)
            throws IOException {
        List<JsonObject> allExecutionTasks = ArtifactIO.readJsonl(
                arguments.executionTasks);
        List<JsonObject> allSummaries = ArtifactIO.readJsonl(
                arguments.summaries);
        List<JsonObject> records = arguments.records == null
                ? Collections.<JsonObject>emptyList()
                : ArtifactIO.readJsonl(arguments.records);
        // The importer's own delta.  Absent means "no classification was
        // supplied"; an empty file means "classified, nothing changed".
        List<JsonObject> topologyDelta = arguments.topologyDelta == null
                ? Collections.<JsonObject>emptyList()
                : ArtifactIO.readJsonl(arguments.topologyDelta);

        List<JsonObject> executionTasks = filterExecutionTasks(
                allExecutionTasks,
                arguments.regionId, arguments.goalId);
        Map<String, JsonObject> taskById = ArtifactIO.uniqueIndex(
                executionTasks, "taskId");
        List<JsonObject> summaries = filterSummaries(allSummaries,
                taskById, arguments.regionId, arguments.goalId);
        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                summaries, executionTasks, records, arguments.pathBounds,
                topologyDelta);
        Collections.sort(result.tasks, Comparator.comparing(
                task -> string(task, "queryKey")));
        return result;
    }

    static void writeOutputs(Path directory, RegionPathWorklist.Result result)
            throws IOException {
        ArtifactIO.replaceJsonl(directory.resolve(
                "region_path_worklist.jsonl"), result.tasks);
        ArtifactIO.replaceJsonl(directory.resolve(
                "merged_region_summaries.jsonl"), result.relations);
        ArtifactIO.replace(directory.resolve("region_path_manifest.json"),
                PRETTY.toJson(result.manifest) + System.lineSeparator());
    }

    private static List<JsonObject> filterExecutionTasks(
            List<JsonObject> source, String regionId, String goalId) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject task : source) {
            if (!regionId.isEmpty()
                    && !regionId.equals(string(task, "regionId"))) {
                continue;
            }
            if (!goalId.equals(string(task, "goalId"))) continue;
            result.add(task.deepCopy());
        }
        return result;
    }

    private static List<JsonObject> filterSummaries(
            List<JsonObject> source, Map<String, JsonObject> executionTasks,
            String regionId, String goalId) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject summary : source) {
            if (!executionTasks.containsKey(string(summary, "taskId"))) {
                continue;
            }
            if (!regionId.isEmpty()
                    && !regionId.equals(string(summary, "regionId"))) {
                continue;
            }
            if (!goalId.equals(string(summary, "goalId"))) continue;
            result.add(summary.deepCopy());
        }
        return result;
    }

    static final class Arguments {
        private final Path summaries;
        private final Path executionTasks;
        private final Path records;
        private final Path topologyDelta;
        private final Path outputDirectory;
        private final RegionPathWorklist.Bounds pathBounds;
        private final String regionId;
        private final String goalId;

        private Arguments(Path summaries, Path executionTasks, Path records,
                          Path topologyDelta, Path outputDirectory,
                          RegionPathWorklist.Bounds pathBounds,
                          String regionId, String goalId) {
            this.summaries = summaries;
            this.executionTasks = executionTasks;
            this.records = records;
            this.topologyDelta = topologyDelta;
            this.outputDirectory = outputDirectory;
            this.pathBounds = pathBounds;
            this.regionId = regionId;
            this.goalId = goalId;
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
            Path executionTasks = required(values, "task-plan");
            Path output = required(values, "output-dir");
            Path records = optionalPath(values.get("records"));
            Path topologyDelta = optionalPath(
                    values.get("topology-delta"));
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
            return new Arguments(summaries, executionTasks, records,
                    topologyDelta, output,
                    bounds, value(values, "region-id"),
                    requiredValue(values, "goal-id"));
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

        private static String requiredValue(Map<String, String> values,
                                            String name) {
            String result = value(values, name);
            if (result.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + name);
            }
            return result;
        }

        private static int intValue(Map<String, String> values, String name,
                                    int fallback) {
            String value = values.get(name);
            return value == null || value.trim().isEmpty()
                    ? fallback : Integer.parseInt(value);
        }

    }
}
