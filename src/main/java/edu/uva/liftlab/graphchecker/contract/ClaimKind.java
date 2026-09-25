package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 4: what a composition may conclude.
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
    /** The seed run itself observed the fatal arm. */
    RECORDED_FAILURE_EXPLAINED,
    /** Nothing in the corpus supports a witness: the honest answer. */
    NO_SUPPORTED_WITNESS
}
