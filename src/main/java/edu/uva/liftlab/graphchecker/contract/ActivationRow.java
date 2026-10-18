package edu.uva.liftlab.graphchecker.contract;

import java.util.Set;

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
     * an executor handed to a worker of its own, which holds nothing of its
     * executor's queue behind it; a task a worker took off its executor's
     * queue; an item a consumer took off a queue; or no claim (its thread
     * orders it).  A row from before this field states NONE under a {@link
     * #CLAIMED} key: claimed work of no stated kind, held at its send.
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

    /** The same, stating the kind of the claim it runs in and the endpoint
     *  that sent the message whose receipt the occurrence's anchor names,
     *  when this run sent it. */
    public static ActivationRow of(String sessionId,
                                   OccurrenceAddress occurrence, String taskId,
                                   boolean focused, boolean instrumented,
                                   String threadKey, ClaimKind claimKind,
                                   Endpoint anchorProducer) {
        String key = Fields.text(threadKey, "threadKey");
        if (Fields.required(claimKind, "claimKind") != ClaimKind.NONE
                && !key.startsWith(CLAIMED)) {
            throw new IllegalArgumentException("an activation of claimed work"
                    + " (" + claimKind + ") is keyed by its claimed start, not"
                    + " by thread " + key);
        }
        return new ActivationRow(Fields.text(sessionId, "sessionId"),
                Fields.required(occurrence, "occurrence"),
                Fields.required(taskId, "taskId"), focused, instrumented, key,
                claimKind, anchorProducer);
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

    /** Whether it ran as claimed work ({@link #CLAIMED}): a task or a queue
     *  item, ordered by its claimed start, not by the thread it ran on. */
    public boolean claimed() {
        return threadKey.startsWith(CLAIMED);
    }

    /** What the claim it runs in is ({@link ClaimKind}). */
    public ClaimKind claimKind() {
        return claimKind;
    }

    /**
     * Whether holding it where it runs holds nothing else: it is no claimed
     * work, or a task its executor handed to a worker of its own that served
     * no queue ({@code servingTasks}, its session's {@link
     * SessionManifest#servingTasks}).  A queued task, a queue item, a
     * hand-off task that took other work on its thread (a ConcurrentUpdate
     * client's Runner), and claimed work of no stated kind are held where
     * they were sent ({@code runtime.Confirmation#submitter}).
     */
    public boolean heldWhereItRuns(Set<String> servingTasks) {
        return !claimed() || claimKind == ClaimKind.HANDOFF_TASK
                && !servingTasks.contains(threadKey);
    }

    /** Why claimed work is not held where it runs ({@link
     *  #heldWhereItRuns}), in words. */
    public String claimedAs(Set<String> servingTasks) {
        if (claimKind == ClaimKind.NONE) {
            return "claimed work its row states no kind of, a row from before"
                    + " claimKind";
        }
        return claimKind.description()
                + (claimKind == ClaimKind.HANDOFF_TASK
                        && servingTasks.contains(threadKey)
                        ? ", which took other work on its thread: it serves a"
                                + " queue" : "");
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
