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
    private final boolean legacy;

    private RegionCaptureGoal(String kind, String purpose, boolean legacy) {
        this.kind = TARGET_BRANCH.equals(kind) ? TARGET_BRANCH
                : OUTPUT_CLOSURE.equals(kind) ? OUTPUT_CLOSURE
                : TARGET_BRANCH;
        this.purpose = this.kind.equals(OUTPUT_CLOSURE)
                && TRANSITION_DISCOVERY.equals(purpose)
                ? TRANSITION_DISCOVERY : RELATION_CLOSURE;
        this.legacy = legacy;
    }

    public static RegionCaptureGoal targetBranch() {
        return new RegionCaptureGoal(TARGET_BRANCH, RELATION_CLOSURE, false);
    }

    public static RegionCaptureGoal outputClosure() {
        return new RegionCaptureGoal(OUTPUT_CLOSURE, RELATION_CLOSURE, false);
    }

    /**
     * Captures an output-reachability path only to discover a previously
     * unobserved runtime protocol transition.  Its kind deliberately remains
     * OUTPUT_CLOSURE so the capture/import machinery records the same engine
     * IR.  The distinct purpose is the cache/SMT quarantine boundary.
     */
    public static RegionCaptureGoal transitionDiscovery() {
        return new RegionCaptureGoal(OUTPUT_CLOSURE,
                TRANSITION_DISCOVERY, false);
    }

    /**
     * Reads the neutral schema first.  Older artifacts are accepted only at
     * this boundary so the rest of the scheduler never branches on legacy
     * region-category strings.
     */
    public static RegionCaptureGoal from(JsonObject row) {
        if (row != null) {
            JsonElement goalElement = row.get(FIELD);
            if (goalElement != null && goalElement.isJsonObject()) {
                String parsed = string(goalElement.getAsJsonObject(), "kind");
                if (TARGET_BRANCH.equals(parsed)
                        || OUTPUT_CLOSURE.equals(parsed)) {
                    return new RegionCaptureGoal(parsed, string(
                            goalElement.getAsJsonObject(), PURPOSE_FIELD),
                            false);
                }
            }

            // Compatibility with P0-P6 artifacts.  No caller outside this
            // class should interpret these values.
            String oldMode = string(row, "summaryMode");
            if ("RELATIONAL_PRODUCER".equals(oldMode)
                    || "RELATIONAL_PROTOCOL".equals(oldMode)) {
                return new RegionCaptureGoal(OUTPUT_CLOSURE,
                        RELATION_CLOSURE, true);
            }
        }
        return new RegionCaptureGoal(TARGET_BRANCH, RELATION_CLOSURE, true);
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

    public boolean cameFromLegacySchema() {
        return legacy;
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
