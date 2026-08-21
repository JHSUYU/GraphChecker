package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The semantic relation a concolic campaign must close for one region
 * occurrence.
 *
 * <p>A branch flip is an exploration task within a closure goal, not a
 * separate goal.</p>
 *
 * <ul>
 *   <li>{@link #OUTPUT_RELATION_CLOSURE} - an occurrence another occurrence
 *   demands a value from, so its relation is closed on that demanded
 *   output;</li>
 *   <li>{@link #TARGET_REACH_CLOSURE} - the occurrence carrying the target
 *   predicate.</li>
 * </ul>
 *
 * <p>There is no third kind.  A synchronous call does not split its caller,
 * so the frame that issues a request and reads its response is one coarse
 * occurrence with one relation; the remote handler is a separate occurrence
 * because it runs in another thread/source context.</p>
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
            throw new IllegalArgumentException("goal kind must be one of "
                    + java.util.Arrays.toString(values()));
        }
    }
}
