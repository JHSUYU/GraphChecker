package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * One obligation's path condition, as the replay that produced it valued it.
 *
 * <p>An obligation is: take a replay's path condition, keep the prefix up to
 * a root-dependent branch, negate that branch, and ask for a root valuation
 * that satisfies the result.  For that question to be about roots, the
 * predicates have to be expressions over roots -- so each one is resolved
 * inside its own replay first, by {@link InSessionReadResolver}, exactly as
 * the composition resolves the path conditions it merges.</p>
 *
 * <p>Resolution happens here, in the planner, because this is where a
 * replay's own rows are: version ids are session-local, and a solver worker
 * holding one obligation row has no session to resolve against.  What the
 * worker receives is a value, not a placeholder to reconstruct.</p>
 *
 * <p>A predicate that does not resolve is not guessed at.  It is published
 * with its reason and the obligation is refused, because a flip query over a
 * value nothing determined would ask the solver to choose that value.</p>
 */
final class ResolvedFlipQuery {
    static final String FIELD = "resolvedFlipQuery";
    static final String KIND = "RESOLVED_FLIP_QUERY";
    static final int SCHEMA_VERSION = 1;
    static final String AUTHORITY = "IN_SESSION_RESOLVED_PATH_CONDITION_V1";

    /** Refusal reason of an obligation whose predicates did not resolve. */
    static final String UNRESOLVED_REASON =
            "FLIP_CONDITION_NOT_RESOLVED_IN_SESSION";

    private ResolvedFlipQuery() {
    }

    /**
     * Indexes one resolver per replay.
     *
     * <p>Rows of two replays must never share one resolver: a version id
     * means a different write in each session, so a mixed index would let
     * one execution answer another's read.</p>
     */
    static Map<String, InSessionReadResolver> resolversByReplay(
            Collection<JsonObject> summaries) {
        Map<String, List<JsonObject>> byReplay = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            if (summary == null) continue;
            String replay = replayKey(summary);
            List<JsonObject> rows = byReplay.get(replay);
            if (rows == null) {
                rows = new ArrayList<>();
                byReplay.put(replay, rows);
            }
            rows.add(summary);
            // The imported summary keeps its versions under the recorded
            // shared state; the resolver reads the runtime spelling.
            JsonObject versions = new JsonObject();
            versions.add("sharedFieldVersions",
                    array(object(summary, SharedStateEvidence.RECORDED_FIELD),
                            "versions"));
            rows.add(versions);
        }
        Map<String, InSessionReadResolver> result = new LinkedHashMap<>();
        for (Map.Entry<String, List<JsonObject>> entry
                : byReplay.entrySet()) {
            result.put(entry.getKey(),
                    InSessionReadResolver.of(entry.getValue()));
        }
        return result;
    }

    /** The replay one row belongs to. */
    static String replayKey(JsonObject row) {
        String replay = optionalString(row, "replayGroupId");
        return replay.isEmpty()
                ? optionalString(row, "boundarySessionScope") : replay;
    }

    /**
     * Attaches this obligation's resolved path condition.
     *
     * @param task     the obligation row, already carrying its replay
     *                 contract and solver path context
     * @param resolver the resolver of the replay the obligation was cut from
     */
    static void attach(JsonObject task, InSessionReadResolver resolver,
                       String replayKey) {
        JsonObject resolved = new JsonObject();
        resolved.addProperty("schemaVersion", SCHEMA_VERSION);
        resolved.addProperty("kind", KIND);
        resolved.addProperty("authority", AUTHORITY);
        resolved.addProperty("replayGroupId", replayKey);
        List<String> unresolved = new ArrayList<>();
        JsonObject contract = object(task, "replayContract");
        BranchReplayContract decoded =
                BranchReplayContract.fromImmutableJson(contract);
        resolved.add("predicates", resolveAll(resolver,
                decoded.requiredPathPredicates(), unresolved));
        resolved.add("context", resolveAll(resolver,
                SolverPathContext.fromJson(object(task, "solverPathContext"))
                        .expressions(), unresolved));
        JsonArray reasons = new JsonArray();
        for (String reason : unresolved) reasons.add(reason);
        resolved.add("unresolved", reasons);
        task.add(FIELD, resolved);
    }

    private static JsonArray resolveAll(InSessionReadResolver resolver,
                                        JsonArray expressions,
                                        List<String> unresolved) {
        JsonArray result = new JsonArray();
        for (JsonElement expression : expressions) {
            JsonElement value = resolver == null ? expression
                    : resolver.resolve(expression);
            collectUnresolved(value, unresolved);
            result.add(value);
        }
        return result;
    }

    /** Every undetermined leaf of a resolved tree, by its stated reason. */
    static void collectUnresolved(JsonElement resolved,
                                  List<String> reasons) {
        if (resolved == null || resolved.isJsonNull()) return;
        if (resolved.isJsonArray()) {
            for (JsonElement element : resolved.getAsJsonArray()) {
                collectUnresolved(element, reasons);
            }
            return;
        }
        if (!resolved.isJsonObject()) return;
        JsonObject node = resolved.getAsJsonObject();
        if (node.has(InSessionReadResolver.UNRESOLVED_TAG)) {
            String reason = optionalString(node,
                    InSessionReadResolver.UNRESOLVED_REASON);
            if (!reasons.contains(reason)) reasons.add(reason);
            return;
        }
        for (Map.Entry<String, JsonElement> field : node.entrySet()) {
            collectUnresolved(field.getValue(), reasons);
        }
    }

    /** The resolved query of one obligation, or null when it carries none. */
    static JsonObject of(JsonObject task) {
        JsonElement encoded = task == null ? null : task.get(FIELD);
        if (encoded == null || !encoded.isJsonObject()) return null;
        JsonObject resolved = encoded.getAsJsonObject();
        return KIND.equals(optionalString(resolved, "kind"))
                ? resolved : null;
    }
}
