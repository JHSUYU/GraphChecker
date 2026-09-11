package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;

/**
 * Plans the deterministic branch-flip frontier for one region in a linked
 * dependency closure. Solving and executing an exact task belong to
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

        List<JsonObject> allExecutionTasks = ArtifactIO.readJsonl(
                requiredPath(options, "task-plan"));
        List<JsonObject> executionTasks = new ArrayList<>();
        for (JsonObject task : allExecutionTasks) {
            if ((regionId.isEmpty()
                    || regionId.equals(string(task, "regionId")))
                    && goalId.equals(string(task, "goalId"))) {
                executionTasks.add(task);
            }
        }
        Map<String, JsonObject> taskById = ArtifactIO.uniqueIndex(
                executionTasks, "taskId");
        List<JsonObject> observedSummaries = ArtifactIO.readJsonl(
                requiredPath(options, "summaries"));
        SymbolicPropagationClosure.Result propagation =
                SymbolicPropagationClosure.rewriteSummaryRows(
                        observedSummaries);
        List<JsonObject> allSummaries = propagation.summaries();
        List<JsonObject> summaries = new ArrayList<>();
        for (JsonObject summary : allSummaries) {
            if (taskById.containsKey(string(summary, "taskId"))
                    && (regionId.isEmpty()
                    || regionId.equals(string(summary, "regionId")))
                    && goalId.equals(string(summary, "goalId"))) {
                summaries.add(summary);
            }
        }

        RegionPathWorklist.Bounds defaults =
                RegionPathWorklist.Bounds.defaults();
        JsonArray caseDependencies = propagation.caseDependencies();
        String familyDigest = LinkedReplayBundle.familySnapshotDigest(
                caseDependencies);
        List<JsonObject> explorationRecords = new ArrayList<>();
        for (JsonObject record : rows(options, "records")) {
            if ((regionId.isEmpty()
                    || regionId.equals(string(record, "regionId")))
                    && goalId.equals(string(record, "goalId"))) {
                explorationRecords.add(record);
            }
        }
        RegionPathWorklist.Result result = RegionPathWorklist.plan(summaries,
                executionTasks, explorationRecords,
                new RegionPathWorklist.Bounds(
                        count(options, "max-paths-per-region",
                                defaults.maxPathsPerRegion),
                        count(options, "max-flips-per-path",
                                defaults.maxFlipsPerPath),
                        count(options, "max-tasks", defaults.maxTasks)),
                // The importer's own delta.  Absent means "no classification
                // was supplied"; an empty file means "classified, nothing
                // changed".
                rows(options, "topology-delta"), familyDigest);
        String topologyEpoch = optional(options, "topology-epoch");
        JsonObject sharedPropagation = new JsonObject();
        sharedPropagation.add(LinkedReplayBundle.CASE_DEPENDENCIES_FIELD,
                caseDependencies);
        sharedPropagation = SharedExpressionTable.compact(sharedPropagation);
        JsonArray compactDependencies = array(sharedPropagation,
                LinkedReplayBundle.CASE_DEPENDENCIES_FIELD);
        for (JsonObject task : result.tasks) {
            task.add(LinkedReplayBundle.CASE_DEPENDENCIES_FIELD,
                    compactDependencies);
            if (sharedPropagation.has(SharedExpressionTable.FIELD)) {
                task.add(SharedExpressionTable.FIELD,
                        sharedPropagation.get(SharedExpressionTable.FIELD));
            }
            JsonObject bundle = LinkedReplayBundle.create(
                    string(task, "sourceTaskId"), allExecutionTasks,
                    allSummaries, string(task, "sourceSummaryId"),
                    familyDigest, topologyEpoch);
            task.add(LinkedReplayBundle.FIELD, bundle);
        }
        result.manifest.addProperty(
                LinkedReplayBundle.FAMILY_DIGEST_FIELD, familyDigest);
        if (!topologyEpoch.isEmpty()) {
            result.manifest.addProperty(LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD,
                    topologyEpoch);
        }
        result.manifest.add("symbolicPropagationGaps",
                propagation.gaps());
        // A worklist repeats the same upstream PCs in several independent
        // flip rows.  Preserve the portable one-row contract while storing
        // their immutable expression DAG once per row as Merkle references.
        // Solver workers expand only the one query they select.
        for (int index = 0; index < result.tasks.size(); index++) {
            result.tasks.set(index, SharedExpressionTable.compact(
                    result.tasks.get(index)));
        }
        Collections.sort(result.tasks, Comparator.comparing(
                task -> string(task, "queryKey")));

        ArtifactIO.replaceJsonl(directory.resolve(
                "region_path_worklist.jsonl"), result.tasks);
        ArtifactIO.replace(directory.resolve("region_path_manifest.json"),
                PRETTY.toJson(result.manifest) + System.lineSeparator());

        System.out.println(PRETTY.toJson(result.manifest));
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
