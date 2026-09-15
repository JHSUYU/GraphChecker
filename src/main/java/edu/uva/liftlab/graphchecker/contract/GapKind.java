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
    /** The solver gave no answer in the time it was given. */
    SOLVER_TIMEOUT,
    /** A retained condition loop ran under an inherited K_L, not a declared
     *  one, so the model it produces is a prefix nobody stated. */
    BOUNDED_LOOP_BODY_BOUND_UNDECLARED,
    /** A retained array-indexed loop declared no K_L: its trip count is the
     *  array length the replay observes, which the replay states exactly. */
    BOUNDED_LOOP_FIXED_COUNT_BOUND_UNDECLARED,
    /** One loop nest's control sites do not all classify alike, so the nest
     *  is published as the weaker CONDITION_BOUNDED and named here. */
    BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT,
    /** A declared wire flow no region of the slice holds the capture of. */
    COMMUNICATION_REQUEST_PORT_UNRESOLVED,
    /** A port truncated its recorded accesses, so the accesses above the
     *  retained ones are invisible to every later stage. */
    BOUND_INSUFFICIENT
}
