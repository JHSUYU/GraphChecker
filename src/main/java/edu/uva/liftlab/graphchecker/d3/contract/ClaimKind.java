package edu.uva.liftlab.graphchecker.d3.contract;

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
     * The recorded roots suffice once the STATE pairing changes.
     *
     * <p>The state-edge counterpart of {@link #MESSAGE_PAIRING_FLIPPED}: every
     * declared root stays at its recorded value and the fatal arm is still
     * reached, because the shared-field read is delivered by a different
     * eligible, attested writer than the one the reader happened to observe.
     * Same polarity rule -- the seed disjunct must be unsat at the recorded
     * valuation, or the formula was satisfiable all along and explains
     * nothing.</p>
     */
    STATE_PAIRING_FLIPPED,
    /** The seed run itself observed the fatal arm. */
    RECORDED_FAILURE_EXPLAINED,
    /** Nothing in the corpus supports a witness: the honest answer. */
    NO_SUPPORTED_WITNESS
}
