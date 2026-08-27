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
        Map<String, String> options = options(argv);
        String regionId = optional(options, "region-id");
        String goalId = requiredValue(options, "goal-id");
        Path directory = requiredPath(options, "output-dir");

        List<JsonObject> executionTasks = new ArrayList<>();
        for (JsonObject task : ArtifactIO.readJsonl(
                requiredPath(options, "task-plan"))) {
            if ((regionId.isEmpty()
                    || regionId.equals(string(task, "regionId")))
                    && goalId.equals(string(task, "goalId"))) {
                executionTasks.add(task.deepCopy());
            }
        }
        Map<String, JsonObject> taskById = ArtifactIO.uniqueIndex(
                executionTasks, "taskId");
        List<JsonObject> summaries = new ArrayList<>();
        for (JsonObject summary : ArtifactIO.readJsonl(
                requiredPath(options, "summaries"))) {
            if (taskById.containsKey(string(summary, "taskId"))
                    && (regionId.isEmpty()
                    || regionId.equals(string(summary, "regionId")))
                    && goalId.equals(string(summary, "goalId"))) {
                summaries.add(summary.deepCopy());
            }
        }

        RegionPathWorklist.Bounds defaults =
                RegionPathWorklist.Bounds.defaults();
        RegionPathWorklist.Result result = RegionPathWorklist.plan(summaries,
                executionTasks, rows(options, "records"),
                new RegionPathWorklist.Bounds(
                        count(options, "max-paths-per-region",
                                defaults.maxPathsPerRegion),
                        count(options, "max-flips-per-path",
                                defaults.maxFlipsPerPath),
                        count(options, "max-tasks", defaults.maxTasks)),
                // The importer's own delta.  Absent means "no classification
                // was supplied"; an empty file means "classified, nothing
                // changed".
                rows(options, "topology-delta"));
        Collections.sort(result.tasks, Comparator.comparing(
                task -> string(task, "queryKey")));

        ArtifactIO.replaceJsonl(directory.resolve(
                "region_path_worklist.jsonl"), result.tasks);
        ArtifactIO.replaceJsonl(directory.resolve(
                "merged_region_summaries.jsonl"), result.relations);
        ArtifactIO.replace(directory.resolve("region_path_manifest.json"),
                PRETTY.toJson(result.manifest) + System.lineSeparator());

        JsonObject display = result.manifest.deepCopy();
        display.remove(OutputClosureContract.FIELD);
        System.out.println(PRETTY.toJson(display));
        String state = string(result.manifest, "state");
        if (RegionPathWorklist.State.GAPPED.name().equals(state)
                || RegionPathWorklist.State.NOT_STARTED.name().equals(state)) {
            System.exit(2);
        }
    }

    private static List<JsonObject> rows(Map<String, String> options,
                                         String name) throws IOException {
        String path = options.get(name);
        return path == null || path.trim().isEmpty()
                ? Collections.<JsonObject>emptyList()
                : ArtifactIO.readJsonl(Paths.get(path));
    }

    private static int count(Map<String, String> options, String name,
                             int fallback) {
        return Math.toIntExact(number(options, name, fallback));
    }

    /** The {@code --name value} pairs of one worker invocation; shared with
     *  {@link ConcolicPathFlipSolver}, which is launched the same way. */
    static Map<String, String> options(String[] argv) {
        Map<String, String> values = new LinkedHashMap<>();
        for (int index = 0; index < argv.length; index++) {
            String option = argv[index];
            if (!option.startsWith("--") || index + 1 >= argv.length) {
                throw new IllegalArgumentException(
                        "Expected --name value, got " + option);
            }
            values.put(option.substring(2), argv[++index]);
        }
        return values;
    }

    static String optional(Map<String, String> options, String name) {
        String value = options.get(name);
        return value == null ? "" : value;
    }

    static String requiredValue(Map<String, String> options, String name) {
        String value = optional(options, name);
        if (value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + name);
        }
        return value;
    }

    static Path requiredPath(Map<String, String> options, String name) {
        return Paths.get(requiredValue(options, name));
    }

    static long number(Map<String, String> options, String name,
                       long fallback) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty()
                ? fallback : Long.parseLong(value);
    }
}
