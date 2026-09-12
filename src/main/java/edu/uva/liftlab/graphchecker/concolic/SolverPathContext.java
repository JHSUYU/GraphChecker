package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveString;

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
        Set<String> demanded = dependencyTokens(
                pathCondition.get(targetPosition));
        for (Integer position : branches) {
            demanded.addAll(dependencyTokens(pathCondition.get(position)));
        }
        Set<Integer> retainedPositions = new LinkedHashSet<>();
        Map<Integer, Set<String>> tokensByPosition = new LinkedHashMap<>();
        for (PositionedConstraint candidate : candidates) {
            tokensByPosition.put(candidate.summaryPcIndex,
                    dependencyTokens(candidate.expression));
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

    private static Set<String> dependencyTokens(JsonElement expression) {
        Set<String> result = new LinkedHashSet<>();
        collectDependencyTokens(expression, result);
        return result;
    }

    private static void collectDependencyTokens(JsonElement expression,
                                                Set<String> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                collectDependencyTokens(child, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        String type = primitiveString(object, "_type");
        if ("SymbolExpression".equals(type)) {
            String symbol = primitiveString(object, "_exp");
            if (!symbol.isEmpty()
                    && !VmExpressionIr.SYMBOLIC_NULL.equals(symbol)
                    && !"V".equals(symbol)) {
                result.add("SYMBOL:" + symbol);
            }
        } else if ("PlaceholderExpression".equals(type)) {
            String function = primitiveString(object,
                    "_place_holder_func");
            int count = primitiveInteger(object, "_count", -1);
            if (!function.isEmpty() && count >= 0) {
                result.add("PLACEHOLDER:" + function + "#" + count);
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectDependencyTokens(entry.getValue(), result);
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
