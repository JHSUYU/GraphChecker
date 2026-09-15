package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 1: the scope KIND a lineage hop ran under.
 *
 * <p>IDENTITY-V2: roles are scope kinds -- a client action, an IPC handler, a
 * DataXceiver op, a daemon tick -- and never thread ids, which are a timing
 * fact no replay can be held to.  {@link #REQUEST} is the depth-1 v1 hop kept
 * so that a case declaration written against v1 keeps naming its occurrence;
 * {@link #UNKNOWN} is what a hop degrades to when the runtime could not
 * attribute it, published with {@code lineageLost} rather than guessed.</p>
 */
public enum Role {
    CLIENT,
    IPC_HANDLER,
    DATA_XCEIVER,
    HEARTBEAT_TICK,
    KEY_MANAGER_TICK,
    BP_SERVICE_ACTOR,
    SPS,
    BALANCER,
    EXECUTOR_TASK,
    /** The v1 depth-1 hop: one request of one api from one source node. */
    REQUEST,
    UNKNOWN
}
