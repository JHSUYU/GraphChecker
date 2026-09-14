package edu.uva.liftlab.graphchecker.d3.contract;

/**
 * CONTRACT-SPEC 3: how an obligation ended.
 */
public enum Verdict {
    /** The solver produced a model; the replay may be driven from it. */
    SAT_MODEL_READY,
    /** No valuation of the declared roots satisfies the obligation. */
    UNSAT,
    /** A replay took the flipped arm under the obligation's valuation. */
    VALIDATED,
    /** The replay did not reproduce the focused region's own prefix. */
    NOT_ADMITTED,
    /** The replay's closure differs from the plan's: a new epoch. */
    DIVERGED
}
