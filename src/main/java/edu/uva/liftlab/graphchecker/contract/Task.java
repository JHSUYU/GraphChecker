package edu.uva.liftlab.graphchecker.contract;

import java.util.List;

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

    public OccurrenceAddress focused() {
        return focused;
    }

    public List<OccurrenceAddress> factor() {
        return factor;
    }

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
