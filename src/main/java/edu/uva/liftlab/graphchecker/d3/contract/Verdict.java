package edu.uva.liftlab.graphchecker.d3.contract;

/**
 * CONTRACT-SPEC 3: how an obligation ended.
 */
public enum Verdict {
    /** The solver produced a model; the replay may be driven from it. */
    SAT_MODEL_READY,
    /** No valuation of the declared roots satisfies the obligation. */
    UNSAT,
    /**
     * A focused replay took the flipped arm and published its rows.
     *
     * <p>ADMITTED, never "validated": a focused replay exists to COLLECT the
     * arms the seed does not contain, and confirms nothing.  What a flip,
     * a witness or a bug rests on is the composed query and z3's verdict on
     * it, and no replay is evidence for or against one.</p>
     */
    ADMITTED,
    /** The replay did not reproduce the focused region's own prefix. */
    NOT_ADMITTED,
    /** The replay's closure differs from the plan's: a new epoch. */
    DIVERGED
}
