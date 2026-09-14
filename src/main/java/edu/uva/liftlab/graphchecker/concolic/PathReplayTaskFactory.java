package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;

import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/** Builds one executable task for a solver-selected path replay. */
final class PathReplayTaskFactory {
    private PathReplayTaskFactory() {
    }

    private static JsonObject create(JsonObject task, JsonObject source,
                                     JsonArray assignments,
                                     JsonArray guardedReads,
                                     BranchReplayContract contract) {
        ClosureGoalKind goalKind = ClosureGoalKind.fromTask(task);
        String queryKey = optionalString(task, "queryKey");
        if (queryKey.isEmpty()) {
            throw new IllegalArgumentException("path queryKey is required");
        }

        JsonObject result = source.deepCopy();
        result.remove("solverPathContext");
        if (!optionalString(task, "goalId").equals(optionalString(source, "goalId"))) {
            throw new IllegalArgumentException(
                    "path task and source task goals differ");
        }
        // This solver result covers the new primary prefix and frontier.
        // Assignments from an older primary path may belong to a suffix that
        // the new flip no longer executes, so they are not replay obligations.
        JsonArray currentAssignments = overlayAssignments(null, assignments);
        String taskId = "TASK.REPLAY." + ArtifactIO.sha256(queryKey + "\n"
                + CanonicalJson.render(currentAssignments) + "\n"
                + CanonicalJson.render(guardedReads));
        result.addProperty("taskId", taskId);
        goalKind.writeToTask(result);
        result.add("modelAssignments", currentAssignments);
        result.add(ExecutionTask.GUARDED_READ_ASSIGNMENTS,
                guardedReads.deepCopy());
        result.add("replayContract", contract.toImmutableJsonView());
        result.addProperty("pathQueryKey", queryKey);
        applyTargetBranchOverride(result, task);
        return result;
    }

    /**
     * The one fresh-JVM replay plan this obligation asks for.
     *
     * <p>One occurrence is symbolic per replay: every other region runs
     * concretely, recording its exports and minting v_H at each attach, so
     * there is no second member for a model to be distributed over and no
     * causal prefix to keep alive in the same JVM.  The caller owns the
     * decode and hands over the source task row it already validated.</p>
     */
    static java.util.List<JsonObject> createFocused(
            JsonObject query, JsonObject source,
            JsonArray assignments, JsonArray guardedReads,
            BranchReplayContract contract) {
        String queryKey = optionalString(query, "queryKey");
        String groupId = "REPLAY.GROUP." + ArtifactIO.sha256(queryKey + "\n"
                + CanonicalJson.render(assignments) + "\n"
                + CanonicalJson.render(guardedReads));
        JsonObject replay = create(query, source, assignments, guardedReads,
                contract);
        replay.addProperty("replayGroupId", groupId);
        replay.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                optionalString(query, VmExpressionIr.TOPOLOGY_EPOCH));
        return java.util.Collections.singletonList(
                SharedExpressionTable.compact(replay));
    }

    /**
     * Advances a nested target from the flipped frontier to the next exact
     * failure guard.
     */
    private static void applyTargetBranchOverride(JsonObject result,
                                                  JsonObject query) {
        if (!query.has("targetBranch")
                || !query.get("targetBranch").isJsonObject()) {
            return;
        }
        JsonObject requested = query.getAsJsonObject("targetBranch");
        String siteId = optionalString(requested, "siteId");
        int occurrence = JsonFields.optionalInteger(requested,
                "occurrence", -1);
        if (siteId.isEmpty() || occurrence < 1) {
            throw new IllegalArgumentException(
                    "target frontier override is incomplete");
        }

        int matches = 0;
        JsonArray rewritten = new JsonArray();
        for (JsonElement element : result.getAsJsonArray("branches")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "target branch catalog entries must be objects");
            }
            JsonObject branch = element.getAsJsonObject().deepCopy();
            if (siteId.equals(optionalString(branch, "siteId"))) {
                JsonElement required = branch.get("requiredOutcome");
                if (!JsonFields.optionalBool(branch, "failureTarget", false)
                        || required == null || !required.isJsonPrimitive()
                        || !required.getAsJsonPrimitive().isBoolean()) {
                    throw new IllegalArgumentException(
                            "target frontier override is not an exact "
                                    + "failure guard: " + siteId);
                }
                branch.addProperty("policy", "EXPLORE");
                branch.addProperty("policyReason",
                        "TARGET_REPLAY_NEXT_FAILURE_GUARD");
                branch.addProperty("selectedOccurrence", occurrence);
                matches++;
            } else if ("EXPLORE".equals(optionalString(branch, "policy"))) {
                branch.addProperty("policy", "PATH_ASSUMPTION");
                branch.addProperty("policyReason",
                        "TARGET_REPLAY_FRONTIER_PREFIX");
            }
            rewritten.add(branch);
        }
        if (matches != 1) {
            throw new IllegalArgumentException(
                    "target frontier override must match one branch: "
                            + siteId + " (found " + matches + ')');
        }
        result.add("branches", rewritten);
        result.add("targetBranch", requested.deepCopy());
    }

    /**
     * Overlays newly solved values on the explicit assignments retained by a
     * linked companion.
     */
    private static JsonArray overlayAssignments(JsonArray source,
                                                JsonArray current) {
        Map<String, JsonObject> byKey = new TreeMap<>();
        addAssignments(byKey, source, "source");
        addAssignments(byKey, current, "current");
        JsonArray merged = new JsonArray();
        for (JsonObject assignment : byKey.values()) {
            merged.add(assignment.deepCopy());
        }
        return merged;
    }

    private static void addAssignments(Map<String, JsonObject> target,
                                       JsonArray assignments,
                                       String origin) {
        if (assignments == null) return;
        Set<String> keys = new TreeSet<>();
        for (JsonElement element : assignments) {
            if (element == null || !element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "model assignment must be an object");
            }
            JsonObject assignment = element.getAsJsonObject();
            String explicitKey = optionalString(assignment,
                    "modelAssignmentKey").trim();
            String engineSymbol = optionalString(assignment, "engineSymbol").trim();
            String key = firstNonBlank(explicitKey, engineSymbol);
            if (key.isEmpty()) {
                throw new IllegalArgumentException(
                        "model assignment has no stable key");
            }
            if (!keys.add(key)) {
                throw new IllegalArgumentException("duplicate " + origin
                        + " model assignment key: " + key);
            }
            JsonObject normalized = assignment.deepCopy();
            if (normalized.has("modelAssignmentKey")) {
                if (explicitKey.isEmpty()) {
                    normalized.remove("modelAssignmentKey");
                } else {
                    normalized.addProperty("modelAssignmentKey", explicitKey);
                }
            }
            if (normalized.has("engineSymbol")) {
                if (engineSymbol.isEmpty()) {
                    normalized.remove("engineSymbol");
                } else {
                    normalized.addProperty("engineSymbol", engineSymbol);
                }
            }
            // The two arrays are two precedence layers.  Uniqueness is local
            // to each layer; a current solver result deliberately replaces the
            // source-prefix assignment with the same normalized key.
            target.put(key, normalized);
        }
    }
}
