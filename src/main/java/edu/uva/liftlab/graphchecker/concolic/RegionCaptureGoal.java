package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

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

    private final String kind;

    private RegionCaptureGoal(String kind) {
        if (!TARGET_BRANCH.equals(kind) && !OUTPUT_CLOSURE.equals(kind)) {
            throw new IllegalArgumentException(
                    "capture goal kind must be TARGET_BRANCH or OUTPUT_CLOSURE");
        }
        this.kind = kind;
    }

    public static RegionCaptureGoal targetBranch() {
        return new RegionCaptureGoal(TARGET_BRANCH);
    }

    public static RegionCaptureGoal outputClosure() {
        return new RegionCaptureGoal(OUTPUT_CLOSURE);
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
        return new RegionCaptureGoal(string(goal, "kind"));
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

    public JsonObject toJson() {
        JsonObject result = new JsonObject();
        result.addProperty("kind", kind);
        result.addProperty("scope", isTargetBranch()
                ? "ONE_DIRECTED_BRANCH" : "BOUNDED_OUTPUT_RELEVANT_PATHS");
        return result;
    }

    public void writeTo(JsonObject row) {
        if (row != null) row.add(FIELD, toJson());
    }

}
