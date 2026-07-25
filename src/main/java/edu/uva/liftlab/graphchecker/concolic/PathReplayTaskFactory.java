package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Builds one executable task for a solver-selected path replay. */
final class PathReplayTaskFactory {
    private PathReplayTaskFactory() {
    }

    static JsonObject create(JsonObject task, JsonObject source,
                             JsonArray assignments) {
        if (source == null) {
            throw new IllegalArgumentException(
                "source execution task is required");
        }
        if (assignments == null) {
            throw new IllegalArgumentException(
                    "model assignments are required");
        }
        BranchReplayContract contract = BranchReplayContract.fromJson(
                requiredObject(task, "replayContract"));
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
        String taskId = "TASK.REPLAY." + ArtifactIO.sha256(queryKey + "\n"
                + CanonicalJson.render(assignments));
        result.addProperty("taskId", taskId);
        result.addProperty("executionPhase",
                goalKind.capturesOutputRelation()
                ? "REPLAY_OUTPUT_PATH_FLIP" : "REPLAY_TARGET_PATH_FLIP");
        goalKind.writeToTask(result);
        result.add("modelAssignments", assignments.deepCopy());
        result.add("replayContract", contract.toJson());
        result.addProperty("pathQueryKey", queryKey);
        result.addProperty("sourceTaskId",
                string(task, "sourceTaskId"));
        return result;
    }

    static JsonObject validationPlan(JsonObject task,
                                     JsonArray assignments) {
        BranchReplayContract.fromJson(requiredObject(task,
                "replayContract"));
        JsonObject result = task.deepCopy();
        result.add("modelAssignments", assignments == null
                ? new JsonArray() : assignments.deepCopy());
        return result;
    }
}
