package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * The reason a region is captured.
 *
 * <p>This is deliberately a goal of one capture, not a type assigned to a
 * region.  The same region may be captured once for a directed target branch
 * and later for one or more requested outputs.</p>
 */
public final class RegionCaptureGoal {
    public static final String FIELD = "captureGoal";
    public static final String TARGET_BRANCH = "TARGET_BRANCH";
    public static final String OUTPUT_CLOSURE = "OUTPUT_CLOSURE";
    public static final String PURPOSE_FIELD = "purpose";
    public static final String RELATION_CLOSURE = "RELATION_CLOSURE";
    public static final String TRANSITION_DISCOVERY =
            "TRANSITION_DISCOVERY_ONLY";

    private final String kind;
    private final String purpose;

    private RegionCaptureGoal(String kind, String purpose) {
        if (!TARGET_BRANCH.equals(kind) && !OUTPUT_CLOSURE.equals(kind)) {
            throw new IllegalArgumentException(
                    "capture goal kind must be TARGET_BRANCH or OUTPUT_CLOSURE");
        }
        this.kind = kind;
        this.purpose = this.kind.equals(OUTPUT_CLOSURE)
                && TRANSITION_DISCOVERY.equals(purpose)
                ? TRANSITION_DISCOVERY : RELATION_CLOSURE;
    }

    public static RegionCaptureGoal targetBranch() {
        return new RegionCaptureGoal(TARGET_BRANCH, RELATION_CLOSURE);
    }

    public static RegionCaptureGoal outputClosure() {
        return new RegionCaptureGoal(OUTPUT_CLOSURE, RELATION_CLOSURE);
    }

    /**
     * Captures an output-reachability path only to discover a previously
     * unobserved runtime protocol transition.  Its kind deliberately remains
     * OUTPUT_CLOSURE so the capture/import machinery records the same engine
     * IR.  The distinct purpose is the cache/SMT quarantine boundary.
     */
    public static RegionCaptureGoal transitionDiscovery() {
        return new RegionCaptureGoal(OUTPUT_CLOSURE,
                TRANSITION_DISCOVERY);
    }

    /**
     * Reads the one maintained capture-goal schema.
     */
    public static RegionCaptureGoal from(JsonObject row) {
        JsonElement goalElement = row == null ? null : row.get(FIELD);
        if (goalElement == null || !goalElement.isJsonObject()) {
            throw new IllegalArgumentException("captureGoal is required");
        }
        JsonObject goal = goalElement.getAsJsonObject();
        return new RegionCaptureGoal(string(goal, "kind"),
                string(goal, PURPOSE_FIELD));
    }

    public String kind() {
        return kind;
    }

    public boolean isTargetBranch() {
        return TARGET_BRANCH.equals(kind);
    }

    public boolean isOutputClosure() {
        return OUTPUT_CLOSURE.equals(kind);
    }

    public String purpose() {
        return purpose;
    }

    public boolean isTransitionDiscovery() {
        return isOutputClosure() && TRANSITION_DISCOVERY.equals(purpose);
    }

    public JsonObject toJson() {
        JsonObject result = new JsonObject();
        result.addProperty("kind", kind);
        result.addProperty("scope", isTargetBranch()
                ? "ONE_DIRECTED_BRANCH" : "BOUNDED_OUTPUT_RELEVANT_PATHS");
        if (isTransitionDiscovery()) {
            result.addProperty(PURPOSE_FIELD, purpose);
            result.addProperty("cacheAdmission",
                    "QUARANTINED_UNTIL_SAME_EXECUTION_RUNTIME_EDGE");
        }
        return result;
    }

    public void writeTo(JsonObject row) {
        if (row != null) row.add(FIELD, toJson());
    }

    private static String string(JsonObject object, String name) {
        if (object == null) return "";
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }
}
