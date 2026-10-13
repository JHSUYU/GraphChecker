package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: one activation a replay session entered, with its address.
 * {@code focused}: ran symbolically as the task's region (others run
 * concretely).  {@code instrumented=false}: entry hook only, so "no decisions"
 * is a hole, not evidence.  {@code threadKey}: same key means program order
 * -- the claimed start the activation runs inside (a queue item or a task a
 * consumer thread claimed), else its thread: two items one consumer thread
 * claims run in the order their starters queued them, which is no program
 * order of theirs.
 *
 * <p>No thread-start edge: happens-before is {@code threadKey} plus the
 * {@link CausalContext.Anchor}; anything else is concurrent.  Re-add the edge
 * only with a producer that publishes it.</p>
 */
public final class ActivationRow extends Value {
    /** The {@link #threadKey} prefix of an activation that runs as claimed
     *  work: a queue item or task a consumer thread claimed. */
    public static final String CLAIMED = "start:";

    /**
     * What the claim an activation runs in is ({@link #claimKind}): a task
     * an executor handed to a worker of its own, which holds nothing queued
     * behind it; a task a worker took off its executor's queue; an item a
     * consumer took off a queue; or no claim (its thread orders it).
     */
    public enum ClaimKind {
        NONE("no claimed work"),
        HANDOFF_TASK("a task its executor handed to a worker of its own"),
        QUEUED_TASK("a task its worker took off its executor's queue"),
        ITEM("a queue item a consumer thread took");

        private final String description;

        ClaimKind(String description) {
            this.description = description;
        }

        public String description() {
            return description;
        }
    }

    private final String sessionId;
    private final OccurrenceAddress occurrence;
    private final String taskId;
    private final boolean focused;
    private final boolean instrumented;
    private final String threadKey;
    private final ClaimKind claimKind;
    private final Endpoint anchorProducer;

    private ActivationRow(String sessionId, OccurrenceAddress occurrence,
                          String taskId, boolean focused, boolean instrumented,
                          String threadKey, ClaimKind claimKind,
                          Endpoint anchorProducer) {
        this.sessionId = sessionId;
        this.occurrence = occurrence;
        this.taskId = taskId;
        this.focused = focused;
        this.instrumented = instrumented;
        this.threadKey = threadKey;
        this.claimKind = claimKind;
        this.anchorProducer = anchorProducer;
    }

    public static ActivationRow of(String sessionId,
                                   OccurrenceAddress occurrence, String taskId,
                                   boolean focused, boolean instrumented,
                                   String threadKey) {
        return of(sessionId, occurrence, taskId, focused, instrumented,
                threadKey, ClaimKind.NONE, null);
    }

    /** The same, stating the kind of the claim it runs in and the endpoint
     *  that sent the message whose receipt the occurrence's anchor names,
     *  when this run sent it. */
    public static ActivationRow of(String sessionId,
                                   OccurrenceAddress occurrence, String taskId,
                                   boolean focused, boolean instrumented,
                                   String threadKey, ClaimKind claimKind,
                                   Endpoint anchorProducer) {
        return new ActivationRow(Fields.text(sessionId, "sessionId"),
                Fields.required(occurrence, "occurrence"),
                Fields.required(taskId, "taskId"), focused, instrumented,
                Fields.text(threadKey, "threadKey"),
                Fields.required(claimKind, "claimKind"), anchorProducer);
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

    /** The session's stable key for the claimed start, else the thread,
     *  this activation ran on. */
    public String threadKey() {
        return threadKey;
    }

    /** Whether it ran as claimed work on a consumer thread ({@link
     *  #CLAIMED}): what holds it holds the items queued behind it. */
    public boolean claimed() {
        return threadKey.startsWith(CLAIMED);
    }

    /** What the claim it runs in is ({@link ClaimKind}). */
    public ClaimKind claimKind() {
        return claimKind;
    }

    /**
     * Whether holding it where it runs holds nothing else: it is no claimed
     * work, or a task its executor handed to a worker of its own.  A
     * queued task or a queue item is held where it was sent
     * ({@code runtime.Confirmation#submitter}).
     */
    public boolean heldWhereItRuns() {
        return !claimed() || claimKind == ClaimKind.HANDOFF_TASK;
    }

    /**
     * The endpoint that sent the message this occurrence's anchor names, or
     * {@code null} (no anchor, or a sender outside this run): what lets a
     * reader follow the causal chain past the anchor to its root.
     */
    public Endpoint anchorProducer() {
        return anchorProducer;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, occurrence, taskId, focused,
                instrumented, threadKey, claimKind, anchorProducer};
    }

    @Override
    public String toString() {
        return "ActivationRow{" + sessionId + " " + occurrence
                + " task=" + taskId + " thread=" + threadKey
                + (claimKind == ClaimKind.NONE ? "" : " " + claimKind)
                + (focused ? " focused" : "")
                + (instrumented ? "" : " uninstrumented") + "}";
    }
}
