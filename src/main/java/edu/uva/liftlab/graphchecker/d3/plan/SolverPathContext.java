package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.smt.VmExpressionIr;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.primitiveInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.primitiveString;

/**
 * Immutable solver-only context for path constraints that are not branches.
 *
 * <p>A {@link BranchReplayContract} owns the decision positions. This object
 * retains the non-branch constraints in the same symbol-dependency component
 * as the prefix decisions and target decision. IR support is still decided
 * by the constraint solver; related expressions are never dropped merely
 * because their operator is unfamiliar.</p>
 */
public final class SolverPathContext {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "NON_BRANCH_SOLVER_PATH_CONTEXT";
    public static final String AUTHORITY =
            "SOURCE_SUMMARY_SYMBOL_DEPENDENCY_SLICE_V1";
    private final List<PositionedConstraint> constraints;

    private SolverPathContext(List<PositionedConstraint> constraints) {
        List<PositionedConstraint> copy = new ArrayList<>();
        int previous = -1;
        if (constraints != null) {
            for (PositionedConstraint constraint : constraints) {
                if (constraint == null
                        || constraint.summaryPcIndex <= previous) {
                    throw new IllegalArgumentException(
                            "non-branch constraint positions must be "
                                    + "strictly increasing");
                }
                if (constraint.expression == null
                        || !constraint.expression.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "non-branch solver constraint must be an object");
                }
                // Expressions belong to the decoder/importer's immutable
                // expression DAG.  Retain that node identity: recursively
                // copying it here expands a shared DAG back into a tree for
                // every flip query.
                copy.add(new PositionedConstraint(
                        constraint.summaryPcIndex, constraint.expression));
                previous = constraint.summaryPcIndex;
            }
        }
        this.constraints = Collections.unmodifiableList(copy);
    }

    /** Partitions the retained source prefix by canonical decision position. */
    public static SolverPathContext fromPath(JsonArray pathCondition,
                                             Set<Integer> branchPositions,
                                             int targetPosition) {
        if (pathCondition == null || targetPosition < 0
                || targetPosition >= pathCondition.size()) {
            throw new IllegalArgumentException(
                    "target position is outside the path condition");
        }
        Set<Integer> branches = branchPositions == null
                ? Collections.<Integer>emptySet()
                : new LinkedHashSet<>(branchPositions);
        for (Integer position : branches) {
            if (position == null || position < 0
                    || position >= targetPosition) {
                throw new IllegalArgumentException(
                        "branch prefix position is outside retained prefix");
            }
        }
        List<PositionedConstraint> candidates = new ArrayList<>();
        for (int index = 0; index < targetPosition; index++) {
            if (branches.contains(index)) continue;
            candidates.add(new PositionedConstraint(index,
                    pathCondition.get(index)));
        }
        TokenMemo memo = new TokenMemo();
        Set<String> demanded = dependencyTokens(
                pathCondition.get(targetPosition), memo);
        for (Integer position : branches) {
            demanded.addAll(dependencyTokens(pathCondition.get(position),
                    memo));
        }
        Set<Integer> retainedPositions = new LinkedHashSet<>();
        Map<Integer, Set<String>> tokensByPosition = new LinkedHashMap<>();
        for (PositionedConstraint candidate : candidates) {
            tokensByPosition.put(candidate.summaryPcIndex,
                    dependencyTokens(candidate.expression, memo));
        }

        // Backward dependency closure.  A retained equality may introduce a
        // local alias for a region input, so repeat until no earlier
        // constraint adds a symbol used by the target slice.
        boolean changed;
        do {
            changed = false;
            for (int index = candidates.size() - 1; index >= 0; index--) {
                PositionedConstraint candidate = candidates.get(index);
                if (retainedPositions.contains(candidate.summaryPcIndex)) {
                    continue;
                }
                Set<String> tokens = tokensByPosition.get(
                        candidate.summaryPcIndex);
                if (!overlaps(tokens, demanded)) continue;
                retainedPositions.add(candidate.summaryPcIndex);
                if (demanded.addAll(tokens)) changed = true;
            }
        } while (changed);

        List<PositionedConstraint> result = new ArrayList<>();
        for (PositionedConstraint candidate : candidates) {
            if (retainedPositions.contains(candidate.summaryPcIndex)) {
                result.add(candidate);
            }
        }
        return new SolverPathContext(result);
    }

    public static SolverPathContext fromJson(JsonObject json) {
        if (primitiveInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(primitiveString(json, "kind"))
                || !AUTHORITY.equals(primitiveString(json, "authority"))) {
            throw new IllegalArgumentException(
                    "unsupported non-branch solver context schema");
        }
        JsonElement encoded = json.get("constraints");
        if (encoded == null || !encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "solver path constraints must be an array");
        }
        List<PositionedConstraint> constraints = new ArrayList<>();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "positioned solver constraint must be an object");
            }
            JsonObject row = element.getAsJsonObject();
            int position = primitiveInteger(row, "summaryPcIndex", -1);
            JsonElement expression = row.get("expression");
            constraints.add(new PositionedConstraint(position,
                    expression));
        }
        return new SolverPathContext(constraints);
    }

    public JsonObject toJson() {
        return coreJson();
    }

    public JsonArray expressions() {
        JsonArray result = new JsonArray();
        for (PositionedConstraint constraint : constraints) {
            result.add(constraint.expression);
        }
        return result;
    }

    private JsonObject coreJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        JsonArray rows = new JsonArray();
        for (PositionedConstraint constraint : constraints) {
            JsonObject row = new JsonObject();
            row.addProperty("summaryPcIndex",
                    constraint.summaryPcIndex);
            row.add("expression", constraint.expression);
            rows.add(row);
        }
        result.add("constraints", rows);
        result.addProperty("authority", AUTHORITY);
        return result;
    }

    private static boolean overlaps(Set<String> left, Set<String> right) {
        for (String value : left) {
            if (right.contains(value)) return true;
        }
        return false;
    }

    private static Set<String> dependencyTokens(JsonElement expression,
                                                TokenMemo memo) {
        Set<String> result = new LinkedHashSet<>();
        result.addAll(memo.tokensOf(expression));
        return result;
    }

    /**
     * Per-path memo for the symbol slice of one expression node.
     *
     * <p>Propagated path conditions are a shared DAG, not a tree: one upstream
     * node is referenced by every later constraint that consumed it. Walking
     * each constraint independently re-descended that shared history once per
     * incoming edge, so the slice cost grew with the square of the corpus.
     * A node's token slice is a pure function of the node, so it is computed
     * once and replayed.</p>
     *
     * <p>The replayed list is the node's own token sequence with repeats
     * removed, in first-emission order. Inserting it into the caller's
     * {@link LinkedHashSet} leaves exactly the set and iteration order the
     * former full descent produced, because re-adding a member never moves
     * it.</p>
     */
    private static final class TokenMemo {
        private final Map<JsonElement, List<String>> slices =
                new IdentityHashMap<>();
        /** One instance per distinct slice; sibling nodes usually agree. */
        private final Map<List<String>, List<String>> interned =
                new HashMap<>();

        private List<String> tokensOf(JsonElement expression) {
            if (expression == null || expression.isJsonNull()
                    || !(expression.isJsonArray()
                    || expression.isJsonObject())) {
                return Collections.emptyList();
            }
            List<String> held = slices.get(expression);
            if (held != null) return held;
            Set<String> collected = new LinkedHashSet<>();
            if (expression.isJsonArray()) {
                for (JsonElement child : expression.getAsJsonArray()) {
                    collected.addAll(tokensOf(child));
                }
            } else {
                JsonObject object = expression.getAsJsonObject();
                String type = primitiveString(object, "_type");
                if ("SymbolExpression".equals(type)) {
                    String symbol = primitiveString(object, "_exp");
                    if (!symbol.isEmpty()
                            && !VmExpressionIr.SYMBOLIC_NULL.equals(symbol)
                            && !"V".equals(symbol)) {
                        collected.add("SYMBOL:" + symbol);
                    }
                } else if ("PlaceholderExpression".equals(type)) {
                    String function = primitiveString(object,
                            "_place_holder_func");
                    int count = primitiveInteger(object, "_count", -1);
                    if (!function.isEmpty() && count >= 0) {
                        collected.add("PLACEHOLDER:" + function + "#" + count);
                    }
                }
                for (Map.Entry<String, JsonElement> entry
                        : object.entrySet()) {
                    collected.addAll(tokensOf(entry.getValue()));
                }
            }
            List<String> slice = collected.isEmpty()
                    ? Collections.<String>emptyList()
                    : Collections.unmodifiableList(
                            new ArrayList<>(collected));
            List<String> canonical = interned.get(slice);
            if (canonical == null) {
                interned.put(slice, slice);
                canonical = slice;
            }
            slices.put(expression, canonical);
            return canonical;
        }
    }

    private static final class PositionedConstraint {
        private final int summaryPcIndex;
        private final JsonElement expression;

        private PositionedConstraint(int summaryPcIndex,
                                     JsonElement expression) {
            this.summaryPcIndex = summaryPcIndex;
            this.expression = expression;
        }
    }
}
