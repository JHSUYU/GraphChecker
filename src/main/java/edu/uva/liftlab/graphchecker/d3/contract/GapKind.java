package edu.uva.liftlab.graphchecker.d3.contract;

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
    SOLVER_TIMEOUT
}
