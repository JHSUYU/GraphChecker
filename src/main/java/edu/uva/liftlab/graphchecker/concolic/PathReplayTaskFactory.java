package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;

import java.util.Map;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Builds one executable task for a solver-selected path replay. */
final class PathReplayTaskFactory {
    private PathReplayTaskFactory() {
    }

    static JsonObject create(JsonObject task, JsonObject source,
                             JsonArray assignments,
                             BranchReplayContract contract,
                             SelectedReadCut readCut) {
        ClosureGoalKind goalKind = ClosureGoalKind.fromTask(task);
        String queryKey = string(task, "queryKey");
        if (queryKey.isEmpty()) {
            throw new IllegalArgumentException("path queryKey is required");
        }

        JsonObject result = source.deepCopy();
        if (!string(task, "goalId").equals(string(source, "goalId"))) {
            throw new IllegalArgumentException(
                    "path task and source task goals differ");
        }
        JsonObject plan = readCut == null ? new JsonObject()
                : readCut.replayPlan();
        JsonArray mergedAssignments = overlayAssignments(
                source.getAsJsonArray("modelAssignments"), assignments);
        String taskId = "TASK.REPLAY." + ArtifactIO.sha256(queryKey + "\n"
                + CanonicalJson.render(mergedAssignments)
                + (plan.size() == 0 ? ""
                : "\n" + CanonicalJson.render(plan)));
        result.addProperty("taskId", taskId);
        goalKind.writeToTask(result);
        result.add("modelAssignments", mergedAssignments);
        result.add("replayContract", contract.toJson());
        result.addProperty("pathQueryKey", queryKey);
        if (plan.size() > 0) {
            // Two replays of one query that select different writers are two
            // different replays, so the cut belongs to the task identity as
            // much as the assignments do.
            result.add(SelectedReadCut.TASK_FIELD, plan);
        }
        return result;
    }

    /**
     * Keeps assignments that established the source prefix and overlays the
     * newly solved flip.  A later flip may replace the same model variable,
     * but it may not silently restore every earlier variable to its concrete
     * workload value.
     */
    private static JsonArray overlayAssignments(JsonArray source,
                                                JsonArray current) {
        Map<String, JsonObject> byKey = new TreeMap<>();
        addAssignments(byKey, source);
        addAssignments(byKey, current);
        JsonArray merged = new JsonArray();
        for (JsonObject assignment : byKey.values()) {
            merged.add(assignment.deepCopy());
        }
        return merged;
    }

    private static void addAssignments(Map<String, JsonObject> target,
                                       JsonArray assignments) {
        if (assignments == null) return;
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            String key = string(assignment, "modelAssignmentKey");
            if (key.isEmpty()) key = string(assignment, "engineSymbol");
            if (key.isEmpty()) {
                throw new IllegalArgumentException(
                        "model assignment has no stable key");
            }
            target.put(key, assignment.deepCopy());
        }
    }
}
