package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** What one replay explores for a selected region occurrence. */
public enum ClosureGoalKind {
    /** Explore the complete region-local path condition. */
    REGION_PATH_CLOSURE,
    /** Explore the region-local path ending at the selected failure. */
    TARGET_REACH_CLOSURE;

    public static final String TASK_FIELD = "goalKind";

    public static ClosureGoalKind fromGoal(JsonObject goal) {
        return decode(optionalString(goal, "kind"));
    }

    public static ClosureGoalKind fromTask(JsonObject task) {
        return decode(optionalString(task, TASK_FIELD));
    }

    public void writeToTask(JsonObject task) {
        task.addProperty(TASK_FIELD, name());
    }

    public boolean capturesRegionPath() {
        return this == REGION_PATH_CLOSURE;
    }

    public boolean capturesTargetReach() {
        return this == TARGET_REACH_CLOSURE;
    }

    private static ClosureGoalKind decode(String value) {
        try {
            return valueOf(value);
        } catch (RuntimeException invalid) {
            throw new IllegalArgumentException("goal kind must be one of "
                    + java.util.Arrays.toString(values()));
        }
    }
}
