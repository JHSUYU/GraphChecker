package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/** Builds the executable activation for one solver-selected path replay. */
final class ReplayActivationFactory {
    private ReplayActivationFactory() {
    }

    static JsonObject create(JsonObject task, JsonObject source,
                             JsonArray assignments) {
        if (source == null) {
            throw new IllegalArgumentException(
                    "source activation is required");
        }
        if (assignments == null) {
            throw new IllegalArgumentException(
                    "model assignments are required");
        }
        BranchReplayContract contract = supportedContract(task);
        RegionCaptureGoal goal = RegionCaptureGoal.from(task);
        String queryKey = string(task, "queryKey");
        if (queryKey.isEmpty()) {
            throw new IllegalArgumentException("path queryKey is required");
        }

        JsonObject result = source.deepCopy();
        String pathId = shortHash(queryKey);
        String activationId = "ACT.PATH." + pathId;
        String scheduleId = "SCHEDULE.PATH." + pathId;
        result.addProperty("activationId", activationId);
        result.addProperty("scheduleId", scheduleId);
        result.addProperty("executionPhase", goal.isOutputClosure()
                ? "REPLAY_OUTPUT_PATH_FLIP" : "REPLAY_TARGET_PATH_FLIP");
        JsonObject bundle = new JsonObject();
        bundle.addProperty("rootActivationId", activationId);
        bundle.addProperty("scheduleId", scheduleId);
        bundle.addProperty("role", "PRIMARY");
        bundle.addProperty("index", 0);
        bundle.addProperty("size", 1);
        bundle.addProperty("selection", activationId);
        result.add("bundle", bundle);
        result.add("captureGoal", goal.toJson());
        result.add("modelAssignments", assignments.deepCopy());
        result.add("replayContract", contract.toJson());
        result.addProperty("pathQueryKey", queryKey);
        result.addProperty("sourceActivationId",
                string(task, "sourceActivationId"));
        result.remove("summaryMode");
        return result;
    }

    static JsonObject validationPlan(JsonObject task,
                                     JsonArray assignments) {
        supportedContract(task);
        JsonObject result = task.deepCopy();
        result.add("modelAssignments", assignments == null
                ? new JsonArray() : assignments.deepCopy());
        return result;
    }

    private static BranchReplayContract supportedContract(JsonObject task) {
        JsonElement encoded = task == null ? null
                : task.get("replayContract");
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "path replay task requires replayContract");
        }
        return BranchReplayContract.fromJson(encoded.getAsJsonObject());
    }

    private static String string(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value == null || !value.isJsonPrimitive()
                ? "" : value.getAsString();
    }

    private static String shortHash(String value) {
        return ArtifactIO.sha256(value).substring(0, 16);
    }
}
