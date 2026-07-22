package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

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
        result.addProperty("executionPhase", "REPLAY_OUTPUT_PATH_FLIP");
        result.addProperty("activationSelectionRequired", activationId);
        result.addProperty("activationBundleRootActivationId",
                activationId);
        result.addProperty("activationBundleScheduleId", scheduleId);
        result.addProperty("activationBundleSize", 1);
        result.addProperty("activationBundleIndex", 0);
        result.addProperty("activationBundleMemberRole", "PRIMARY");
        result.remove("reachabilitySupportForActivationId");
        result.add("captureGoal", (RegionCaptureGoal.from(task)
                .isTransitionDiscovery()
                ? RegionCaptureGoal.transitionDiscovery()
                : RegionCaptureGoal.outputClosure()).toJson());
        result.add("modelAssignments", assignments.deepCopy());
        result.add("replayContract", contract.toJson());
        result.addProperty("pathQueryKey", queryKey);
        // A CERTIFIED_NO_PC contract is rejected above. Ordinary VM-PC
        // replay therefore needs no parallel concrete-guard proof protocol.
        result.add("concreteGuardReplayProofs", new JsonArray());
        result.remove("concreteGuardReplayProof");
        result.remove("forcedBranches");
        result.remove("replayMaterializations");
        result.remove("summaryMode");
        result.remove("targetBranch");
        result.remove("expectedBranchPrefix");
        result.remove("pathReplayConstraints");
        result.remove("pathReplayNegatedCondition");
        result.remove("pathReplayTargetConditionIndex");
        result.remove("branchOverrideProhibited");
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
        BranchReplayContract contract = BranchReplayContract.fromJson(
                encoded.getAsJsonObject());
        rejectConditionlessWitness(contract.source());
        for (BranchWitness witness : contract.orderedPrefix()) {
            rejectConditionlessWitness(witness);
        }
        return contract;
    }

    private static void rejectConditionlessWitness(BranchWitness witness) {
        if (BranchWitness.CERTIFIED_NO_PC.equals(witness.evidenceKind())) {
            throw new IllegalArgumentException(
                    "CERTIFIED_NO_PC_REPLAY_UNSUPPORTED:" + witness.siteId()
                            + "#" + witness.occurrence());
        }
    }

    private static String string(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value == null || !value.isJsonPrimitive()
                ? "" : value.getAsString();
    }

    private static String shortHash(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest((value == null ? "" : value)
                    .getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.substring(0, 16);
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 is unavailable",
                    impossible);
        }
    }
}
