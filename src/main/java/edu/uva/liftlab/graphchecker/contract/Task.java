package edu.uva.liftlab.graphchecker.contract;

import java.util.List;

/**
 * CONTRACT-SPEC §3: one unit of exploration, one focused occurrence (the rest
 * runs concretely).  {@code factor}: state-connected co-occurrences run
 * symbolically with it, usually empty.
 */
public final class Task extends Value {
    private final String taskId;
    private final OccurrenceAddress focused;
    private final List<OccurrenceAddress> factor;
    private final String seedSessionId;

    private Task(String taskId, OccurrenceAddress focused,
                 List<OccurrenceAddress> factor, String seedSessionId) {
        this.taskId = taskId;
        this.focused = focused;
        this.factor = factor;
        this.seedSessionId = seedSessionId;
    }

    public static Task of(String taskId, OccurrenceAddress focused,
                          List<OccurrenceAddress> factor,
                          String seedSessionId) {
        return new Task(Fields.text(taskId, "taskId"),
                Fields.required(focused, "focused"), Fields.copy(factor),
                Fields.text(seedSessionId, "seedSessionId"));
    }

    public String taskId() {
        return taskId;
    }

    /** The occurrence this task explores symbolically. */
    public OccurrenceAddress focused() {
        return focused;
    }

    /** State-connected co-occurrences explored with it; may be empty. */
    public List<OccurrenceAddress> factor() {
        return factor;
    }

    /** The session whose recording this task was planned from. */
    public String seedSessionId() {
        return seedSessionId;
    }

    @Override
    Object[] parts() {
        return new Object[] {taskId, focused, factor, seedSessionId};
    }

    @Override
    public String toString() {
        return "Task{" + taskId + " " + focused
                + (factor.isEmpty() ? "}" : " +" + factor.size() + " factor}");
    }
}
