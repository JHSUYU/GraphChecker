package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one activation a replay session entered, with its address.
 *
 * <p>{@code focused} says the activation ran symbolically as the task's focused
 * region; every other activation of the session ran concretely with its exports
 * recorded and its attaches minting (the entry rule).</p>
 */
public final class ActivationRow {
    private final String sessionId;
    private final OccurrenceAddress occurrence;
    private final String taskId;
    private final boolean focused;

    private ActivationRow(String sessionId, OccurrenceAddress occurrence,
                          String taskId, boolean focused) {
        this.sessionId = sessionId;
        this.occurrence = occurrence;
        this.taskId = taskId;
        this.focused = focused;
    }

    public static ActivationRow of(String sessionId,
                                   OccurrenceAddress occurrence, String taskId,
                                   boolean focused) {
        return new ActivationRow(Fields.text(sessionId, "sessionId"),
                Fields.required(occurrence, "occurrence"),
                Fields.stated(taskId, "taskId"), focused);
    }

    public String sessionId() {
        return sessionId;
    }

    public OccurrenceAddress occurrence() {
        return occurrence;
    }

    public String taskId() {
        return taskId;
    }

    public boolean focused() {
        return focused;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ActivationRow)) return false;
        ActivationRow other = (ActivationRow) value;
        return focused == other.focused && sessionId.equals(other.sessionId)
                && occurrence.equals(other.occurrence)
                && taskId.equals(other.taskId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, occurrence, taskId, focused);
    }

    @Override
    public String toString() {
        return "ActivationRow{" + sessionId + " " + occurrence
                + " task=" + taskId + (focused ? " focused}" : "}");
    }
}
