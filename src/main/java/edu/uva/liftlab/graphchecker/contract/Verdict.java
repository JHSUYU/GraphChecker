package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §3: how an obligation ended.
 */
public enum Verdict {
    /** The solver produced a model; the replay may be driven from it. */
    SAT_MODEL_READY,
    /** No valuation of the declared roots satisfies the obligation. */
    UNSAT,
    /**
     * A focused replay took the flipped arm and published its rows.  Never
     * "validated": replays collect arms; only z3 on the composed query
     * decides a witness.
     */
    ADMITTED,
    /** The replay did not reproduce the focused region's own prefix. */
    NOT_ADMITTED
}
