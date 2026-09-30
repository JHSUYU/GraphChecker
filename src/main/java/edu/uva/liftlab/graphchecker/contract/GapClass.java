package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.5: whether a gap stops a claim or only describes one.
 */
public enum GapClass {
    /** The stage refuses: no claim may be made over this gap. */
    BLOCKING,
    /** Recorded for the report; the claim stands. */
    DIAGNOSTIC
}
