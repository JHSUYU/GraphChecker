package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one activation a replay session entered, with its address.
 * {@code focused}: ran symbolically as the task's region (others run
 * concretely).  {@code instrumented=false}: entry hook only, so "no decisions"
 * is a hole, not evidence (INTERACTION-ID sec 8).  {@code threadKey}: same key
 * means program order (sec 7.1).
 *
 * <p>No thread-start edge: happens-before is {@code threadKey} plus the
 * {@link CausalContext.Anchor}; anything else is concurrent.  Re-add the edge
 * only with a producer that publishes it.</p>
 */
public final class ActivationRow {
    private final String sessionId;
    private final OccurrenceAddress occurrence;
    private final String taskId;
    private final boolean focused;
    private final boolean instrumented;
    private final String threadKey;

    private ActivationRow(String sessionId, OccurrenceAddress occurrence,
                          String taskId, boolean focused, boolean instrumented,
                          String threadKey) {
        this.sessionId = sessionId;
        this.occurrence = occurrence;
        this.taskId = taskId;
        this.focused = focused;
        this.instrumented = instrumented;
        this.threadKey = threadKey;
    }

    public static ActivationRow of(String sessionId,
                                   OccurrenceAddress occurrence, String taskId,
                                   boolean focused, boolean instrumented,
                                   String threadKey) {
        return new ActivationRow(Fields.text(sessionId, "sessionId"),
                Fields.required(occurrence, "occurrence"),
                Fields.stated(taskId, "taskId"), focused, instrumented,
                Fields.text(threadKey, "threadKey"));
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

    /** Whether this region was in the instrumented set at all. */
    public boolean instrumented() {
        return instrumented;
    }

    /** The session's stable key for the thread this activation ran on. */
    public String threadKey() {
        return threadKey;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ActivationRow)) return false;
        ActivationRow other = (ActivationRow) value;
        return focused == other.focused
                && instrumented == other.instrumented
                && sessionId.equals(other.sessionId)
                && occurrence.equals(other.occurrence)
                && taskId.equals(other.taskId)
                && threadKey.equals(other.threadKey);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, occurrence, taskId, focused,
                instrumented, threadKey);
    }

    @Override
    public String toString() {
        return "ActivationRow{" + sessionId + " " + occurrence
                + " task=" + taskId + " thread=" + threadKey
                + (focused ? " focused" : "")
                + (instrumented ? "" : " uninstrumented") + "}";
    }
}
