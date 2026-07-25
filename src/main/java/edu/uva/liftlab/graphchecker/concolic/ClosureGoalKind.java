package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The semantic relation a concolic campaign must close.
 *
 * <p>A branch flip is deliberately not a goal. It is one query produced while
 * exploring either an output relation or the target reach relation.</p>
 */
public enum ClosureGoalKind {
    OUTPUT_RELATION_CLOSURE,
    TARGET_REACH_CLOSURE;

    public static final String TASK_FIELD = "goalKind";

    public static ClosureGoalKind fromGoal(JsonObject goal) {
        return decode(string(goal, "kind"));
    }

    public static ClosureGoalKind fromTask(JsonObject task) {
        return decode(string(task, TASK_FIELD));
    }

    public void writeToTask(JsonObject task) {
        task.addProperty(TASK_FIELD, name());
    }

    public boolean capturesOutputRelation() {
        return this == OUTPUT_RELATION_CLOSURE;
    }

    public boolean capturesTargetReach() {
        return this == TARGET_REACH_CLOSURE;
    }

    private static ClosureGoalKind decode(String value) {
        try {
            return valueOf(value);
        } catch (RuntimeException invalid) {
            throw new IllegalArgumentException(
                    "goal kind must be OUTPUT_RELATION_CLOSURE or "
                            + "TARGET_REACH_CLOSURE");
        }
    }
}
