package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one activation a replay session entered, with its address.
 *
 * <p>{@code focused} says the activation ran symbolically as the task's focused
 * region; every other activation of the session ran concretely with its exports
 * recorded and its attaches minting (the entry rule).</p>
 *
 * <p>{@code instrumented} is false when the row comes from a lightweight entry
 * hook alone -- the region is not in the retained/instrumented set, so no
 * decision, export or attach row can exist for this occurrence.  A reader that
 * finds no decisions for an activation must be able to tell "this region was
 * not instrumented" from "this region decided nothing", because the second is
 * evidence and the first is a hole (INTERACTION-ID sec 8).</p>
 *
 * <p>{@code threadKey} is the recording's stable key for the executing thread
 * inside this session: two rows with the same key ran in program order, which
 * is the same-thread half of happens-before (sec 7.1).</p>
 *
 * <p>{@code startedBy} is the other half, and ONLY that: the intra-node
 * thread-creation edge -- the {@code Thread.start} or executor-submission
 * {@link Endpoint} whose frame this activation's thread inherited.  It is null
 * for a thread that already existed (a handler pool takes work off a queue; no
 * event in this recording started it) and null for an activation a message
 * started.  Message causality is the occurrence's
 * {@link CausalContext.Anchor} and stays there.</p>
 *
 * <p>The two are different happens-before relations -- thread start against
 * message receive -- and both may hold of one activation without disagreeing:
 * a thread started here can go on to receive a message, and an ancestor walk
 * ({@code Arms.ancestor}) follows both.  Reading {@code startedBy} as "who
 * caused this work" would collapse them and lose the message edge on every
 * pooled handler, which has no starter at all.</p>
 */
public final class ActivationRow {
    private final String sessionId;
    private final OccurrenceAddress occurrence;
    private final String taskId;
    private final boolean focused;
    private final boolean instrumented;
    private final String threadKey;
    private final Endpoint startedBy;

    private ActivationRow(String sessionId, OccurrenceAddress occurrence,
                          String taskId, boolean focused, boolean instrumented,
                          String threadKey, Endpoint startedBy) {
        this.sessionId = sessionId;
        this.occurrence = occurrence;
        this.taskId = taskId;
        this.focused = focused;
        this.instrumented = instrumented;
        this.threadKey = threadKey;
        this.startedBy = startedBy;
    }

    public static ActivationRow of(String sessionId,
                                   OccurrenceAddress occurrence, String taskId,
                                   boolean focused, boolean instrumented,
                                   String threadKey, Endpoint startedBy) {
        return new ActivationRow(Fields.text(sessionId, "sessionId"),
                Fields.required(occurrence, "occurrence"),
                Fields.stated(taskId, "taskId"), focused, instrumented,
                Fields.text(threadKey, "threadKey"), startedBy);
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

    /** The endpoint that started this thread, or {@code null}. */
    public Endpoint startedBy() {
        return startedBy;
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
                && threadKey.equals(other.threadKey)
                && Objects.equals(startedBy, other.startedBy);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, occurrence, taskId, focused,
                instrumented, threadKey, startedBy);
    }

    @Override
    public String toString() {
        return "ActivationRow{" + sessionId + " " + occurrence
                + " task=" + taskId + " thread=" + threadKey
                + (focused ? " focused" : "")
                + (instrumented ? "" : " uninstrumented") + "}";
    }
}
