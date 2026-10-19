package edu.uva.liftlab.graphchecker.contract;

import java.util.Set;

public final class ActivationRow extends Value {
    public static final String CLAIMED = "start:";

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

    public boolean instrumented() {
        return instrumented;
    }

    public String threadKey() {
        return threadKey;
    }

    public boolean claimed() {
        return threadKey.startsWith(CLAIMED);
    }

    public ClaimKind claimKind() {
        return claimKind;
    }

    public boolean heldWhereItRuns(Set<String> servingTasks) {
        return !claimed() || claimKind == ClaimKind.HANDOFF_TASK
                && !servingTasks.contains(threadKey);
    }

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
