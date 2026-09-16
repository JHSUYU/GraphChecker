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
 * <p>The OTHER half of happens-before -- the intra-node thread-creation
 * edge, a {@code startedBy} {@link Endpoint} whose frame the activation's
 * thread inherited -- is NOT a member of this row.  It was, and no runtime
 * ever published one: every producer passed a literal null, so the walks in
 * {@code smt.Arms} that followed it could only ever return "unordered", and
 * a member the recording never states is a relation the engine does not
 * have.  What the rows do carry is {@code threadKey} (same-thread program
 * order) and the occurrence's {@link CausalContext.Anchor} (message
 * causality); an occurrence a message did not start and a thread key does
 * not place is CONCURRENT with everything, which is the honest answer.
 * When the thread-start edge comes back it comes back with a producer.</p>
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
