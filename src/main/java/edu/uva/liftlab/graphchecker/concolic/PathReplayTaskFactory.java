package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Builds one executable task for a solver-selected path replay. */
final class PathReplayTaskFactory {
    private PathReplayTaskFactory() {
    }

    static JsonObject create(JsonObject task, JsonObject source,
                             JsonArray assignments,
                             BranchReplayContract contract) {
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
        goalKind.writeToTask(result);
        result.add("modelAssignments", assignments.deepCopy());
        result.add("replayContract", contract.toJson());
        result.addProperty("pathQueryKey", queryKey);
        return result;
    }
}
