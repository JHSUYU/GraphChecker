package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Immutable solver-only context for path constraints that are not branches.
 *
 * <p>A {@link BranchReplayContract} remains the sole authority for branch
 * predicates and runtime branch replay.  VM array-load and method-relation
 * constraints can occur between those predicates, but they are not branch
 * witnesses and must never be converted into one.  This object preserves
 * only those positioned non-branch constraints for the path solver.</p>
 */
public final class SolverPathContext {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "NON_BRANCH_SOLVER_PATH_CONTEXT";
    public static final String AUTHORITY =
            "SOURCE_SUMMARY_POSITIONED_NON_BRANCH_CONSTRAINTS_V1";
    private static final String ID_PREFIX = "SOLVER.PATH.CONTEXT.";

    private final List<PositionedConstraint> constraints;
    private final String contextId;

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
                validateExpression(constraint.expression);
                copy.add(new PositionedConstraint(
                        constraint.summaryPcIndex,
                        CanonicalJson.copy(constraint.expression)));
                previous = constraint.summaryPcIndex;
            }
        }
        this.constraints = Collections.unmodifiableList(copy);
        this.contextId = ID_PREFIX + CanonicalJson.sha256(coreJson());
    }

    public static SolverPathContext empty() {
        return new SolverPathContext(Collections
                .<PositionedConstraint>emptyList());
    }

    /**
     * Partitions the retained source prefix without copying branch
     * predicates.  Any unmapped Boolean predicate is rejected; only explicit
     * VM relation nodes are admitted as non-branch solver context.
     */
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
        List<PositionedConstraint> result = new ArrayList<>();
        for (int index = 0; index < targetPosition; index++) {
            if (branches.contains(index)) continue;
            result.add(new PositionedConstraint(index,
                    pathCondition.get(index)));
        }
        return new SolverPathContext(result);
    }

    public static SolverPathContext fromJson(JsonObject json) {
        requireExactKeys(json, "solver path context", "schemaVersion",
                "kind", "contextId", "constraints", "authority");
        if (integer(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(json, "kind"))
                || !AUTHORITY.equals(string(json, "authority"))) {
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
            requireExactKeys(row, "positioned solver constraint",
                    "summaryPcIndex", "expression");
            int position = integer(row, "summaryPcIndex", -1);
            JsonElement expression = row.get("expression");
            constraints.add(new PositionedConstraint(position,
                    expression));
        }
        SolverPathContext result = new SolverPathContext(constraints);
        if (!result.contextId.equals(string(json, "contextId"))) {
            throw new IllegalArgumentException(
                    "solver path content hash does not match contextId");
        }
        return result;
    }

    public JsonObject toJson() {
        JsonObject result = coreJson();
        result.addProperty("contextId", contextId);
        return (JsonObject) CanonicalJson.copy(result);
    }

    public String contextId() {
        return contextId;
    }

    public int size() {
        return constraints.size();
    }

    public JsonArray expressions() {
        JsonArray result = new JsonArray();
        for (PositionedConstraint constraint : constraints) {
            result.add(CanonicalJson.copy(constraint.expression));
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
            row.add("expression", CanonicalJson.copy(
                    constraint.expression));
            rows.add(row);
        }
        result.add("constraints", rows);
        result.addProperty("authority", AUTHORITY);
        return (JsonObject) CanonicalJson.copy(result);
    }

    private static void validateExpression(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            throw new IllegalArgumentException(
                    "non-branch solver constraint must be an object");
        }
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if (!"_array_expr".equals(type)
                && !"MethodExpression".equals(type)) {
            throw new IllegalArgumentException(
                    "unwitnessed path predicate is not an admitted "
                            + "non-branch constraint: " + type);
        }
    }

    private static void requireExactKeys(JsonObject object, String label,
                                         String... allowed) {
        if (object == null) {
            throw new IllegalArgumentException(label + " is required");
        }
        Set<String> expected = new LinkedHashSet<>(Arrays.asList(allowed));
        Set<String> actual = new LinkedHashSet<>();
        for (java.util.Map.Entry<String, JsonElement> entry
                : object.entrySet()) {
            actual.add(entry.getKey());
        }
        if (!actual.equals(expected)) {
            throw new IllegalArgumentException(label + " keys must be "
                    + expected + " but were " + actual);
        }
    }

    private static int integer(JsonObject object, String name,
                               int fallback) {
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
