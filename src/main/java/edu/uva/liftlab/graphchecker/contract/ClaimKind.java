package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §4: what a composition may conclude.
 */
public enum ClaimKind {
    /** A declared marker root at its other value reaches the fatal read. */
    MARKER_FLIPPED,
    /** A clock the case declared has to skew for the fatal read. */
    CLOCK_SKEW,
    /** The recorded roots suffice once the wire pairing changes. */
    MESSAGE_PAIRING_FLIPPED,
    /**
     * The recorded roots suffice once a shared-field read takes a different
     * attested writer.  Same polarity rule as {@link #MESSAGE_PAIRING_FLIPPED}:
     * the seed disjunct must be unsat at the recorded valuation.
     */
    STATE_PAIRING_FLIPPED,
    /**
     * The formula is satisfiable and no mechanism the recording decides
     * names why (a polarity the recording does not decide, a root moved
     * inside an unattested arm, a model of the formula that is the run as
     * recorded on its healthy run, which CONFIRM refuses by name):
     * composer imprecision until CONFIRM says otherwise,
     * so it is confirmed like any claim, its model's arms and valuation
     * planted, and a refutation excluded before the claim is decided again.
     */
    FORMULA_SAT,
    /** Nothing in the corpus supports a witness: the honest answer. */
    NO_SUPPORTED_WITNESS
}
