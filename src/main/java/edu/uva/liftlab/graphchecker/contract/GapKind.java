package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 2: the closed set of things a stage may refuse on.
 *
 * <p>Closed on purpose: a kind without a consumer is a report nobody reads, and
 * the deletion pass removed several.  Every kind here is either BLOCKING for
 * some stage or a DIAGNOSTIC that a report prints.</p>
 */
public enum GapKind {
    /** A selected path's replay was not admitted on its focused region. */
    ADMISSION_GAP,
    /** A replay paired an endpoint the epoch catalog does not have. */
    TOPOLOGY_DIVERGENCE,
    /** An arm from a run whose producer never stated a path condition. */
    UNATTESTED_ARM,
    /** A projection joined to no write version and pinned to no value. */
    UNSTATED_VALUE,
    /** An attach answered with a value no producer arm can produce. */
    UNPRODUCIBLE_ANSWER,
    /** The composed formula is satisfied at the recorded valuation. */
    FORMULA_SAT_AT_RECORDED_VALUATION,
    /** A root or a port the case never declared. */
    DECLARATION_MISSING,
    /** An address degraded because a lineage hop was unattributable. */
    LINEAGE_LOST,
    /** A planned task no activation of this replay answered. */
    TASK_UNANSWERED,
    /** The solver gave no answer in the time it was given. */
    SOLVER_TIMEOUT,
    /**
     * An activation closed at a different execution-index depth than it
     * opened at.
     *
     * <p>BLOCKING, and it has to be: the frames an occurrence stands on ARE
     * its identity (IDENTITY-V3 §1), so a frame pushed at an entry and not
     * popped at its exit moves the address of everything that runs after
     * it -- on hdfs-17960 it moved four frames onto the replay's index and
     * 34 of 81 planned tasks were refused on an address nobody could see
     * was wrong.  A leak cannot be reported as a diagnostic, because every
     * row published after it is addressed by the wrong occurrence.</p>
     */
    FRAME_UNBALANCED
}
