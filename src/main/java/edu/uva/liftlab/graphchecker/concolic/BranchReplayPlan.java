package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Canonical branch and non-branch replay evidence extracted from one summary.
 *
 * <p>The branch contract is the only runtime branch authority.  The solver
 * context contains only positioned, non-branch constraints.  Keeping the two
 * immutable values together prevents schedulers from rebuilding a second
 * target-branch protocol out of loosely related JSON fields.</p>
 */
public final class BranchReplayPlan {
    private final BranchReplayContract replayContract;
    private final SolverPathContext solverPathContext;

    private BranchReplayPlan(BranchReplayContract replayContract,
                             SolverPathContext solverPathContext) {
        this.replayContract = replayContract;
        this.solverPathContext = solverPathContext;
    }

    public static BranchReplayPlan fromSummary(JsonObject summary,
                                               String siteId,
                                               int occurrence) {
        JsonObject selected = null;
        for (JsonElement element : array(summary, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (siteId.equals(string(mapping, "siteId"))
                    && occurrence == integer(mapping, "occurrence", -1)) {
                if (selected != null) {
                    throw new IllegalArgumentException(
                            "target branch mapping is not unique");
                }
                selected = mapping;
            }
        }
        if (selected == null) {
            throw new IllegalArgumentException(
                    "target branch mapping is missing");
        }
        return fromSummary(summary, selected);
    }

    public static BranchReplayPlan fromSummary(JsonObject summary,
                                               JsonObject selected) {
        JsonArray path = array(summary, "pathCondition");
        int targetPosition = integer(selected, "summaryPcIndex", -1);
        BranchWitness source = witness(selected);
        if (source == null || targetPosition < 0
                || targetPosition >= path.size()
                || !BranchPredicateAlgebra.equivalent(
                source.sourceSatisfiedPredicate(), path.get(targetPosition))) {
            throw new IllegalArgumentException(
                    "target witness does not own its summary path position");
        }

        List<JsonObject> prefixMappings = new ArrayList<>();
        for (JsonElement element : array(summary, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            int position = integer(mapping, "summaryPcIndex", -1);
            if (position >= 0 && position < targetPosition) {
                prefixMappings.add(mapping);
            }
        }
        Collections.sort(prefixMappings, Comparator.comparingInt(
                value -> integer(value, "summaryPcIndex", -1)));

        List<BranchWitness> prefix = new ArrayList<>();
        Set<Integer> branchPositions = new LinkedHashSet<>();
        for (JsonObject mapping : prefixMappings) {
            int position = integer(mapping, "summaryPcIndex", -1);
            BranchWitness witness = witness(mapping);
            if (!branchPositions.add(position) || witness == null
                    || !BranchPredicateAlgebra.equivalent(
                    witness.sourceSatisfiedPredicate(), path.get(position))) {
                throw new IllegalArgumentException(
                        "branch witness prefix does not partition the path");
            }
            prefix.add(witness);
        }
        return new BranchReplayPlan(BranchReplayContract.flip(prefix, source),
                SolverPathContext.fromPath(path, branchPositions,
                        targetPosition));
    }

    public BranchReplayContract replayContract() {
        return replayContract;
    }

    public SolverPathContext solverPathContext() {
        return solverPathContext;
    }

    /** All solver predicates; ordering is immaterial because they conjoin. */
    public JsonArray solverPredicates() {
        JsonArray result = solverPathContext.expressions();
        for (JsonElement predicate : replayContract.requiredPathPredicates()) {
            result.add(predicate);
        }
        return result;
    }

    private static BranchWitness witness(JsonObject mapping) {
        JsonElement encoded = mapping == null ? null : mapping.get("witness");
        if (encoded == null || !encoded.isJsonObject()) return null;
        try {
            return BranchWitness.fromJson(encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            return null;
        }
    }

    private static JsonArray array(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static int integer(JsonObject object, String name, int fallback) {
        JsonElement value = object == null ? null : object.get(name);
        try {
            return value == null || !value.isJsonPrimitive()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    private static String string(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        return value == null || !value.isJsonPrimitive()
                ? "" : value.getAsString();
    }
}
