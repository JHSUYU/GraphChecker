package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;

import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
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
                modelAssignments(source), assignments);
        String taskId = "TASK.REPLAY." + ArtifactIO.sha256(queryKey + "\n"
                + CanonicalJson.render(mergedAssignments)
                + (plan.size() == 0 ? ""
                : "\n" + CanonicalJson.render(plan)));
        result.addProperty("taskId", taskId);
        goalKind.writeToTask(result);
        result.add("modelAssignments", mergedAssignments);
        result.add("replayContract", contract.toJson());
        result.addProperty("pathQueryKey", queryKey);
        applyTargetBranchOverride(result, task);
        if (plan.size() > 0) {
            // Two replays of one query that select different writers are two
            // different replays, so the cut belongs to the task identity as
            // much as the assignments do.
            result.add(SelectedReadCut.TASK_FIELD, plan);
        }
        return result;
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
        String siteId = string(requested, "siteId");
        int occurrence = JsonFields.integer(requested,
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
            if (siteId.equals(string(branch, "siteId"))) {
                JsonElement required = branch.get("requiredOutcome");
                if (!JsonFields.bool(branch, "failureTarget", false)
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
            } else if ("EXPLORE".equals(string(branch, "policy"))) {
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
     * Keeps assignments that established the source prefix and overlays the
     * newly solved flip.
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

    private static JsonArray modelAssignments(JsonObject source) {
        JsonElement encoded = source.get("modelAssignments");
        if (encoded == null) return null;
        if (!encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "source modelAssignments must be an array");
        }
        return encoded.getAsJsonArray();
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
            String explicitKey = string(assignment,
                    "modelAssignmentKey").trim();
            String engineSymbol = string(assignment, "engineSymbol").trim();
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
