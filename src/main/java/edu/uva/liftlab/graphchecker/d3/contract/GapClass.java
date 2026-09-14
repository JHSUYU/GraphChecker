package edu.uva.liftlab.graphchecker.d3.contract;

/**
 * CONTRACT-SPEC 2: whether a gap stops a claim or only describes one.
 */
public enum GapClass {
    /** The stage refuses: no claim may be made over this gap. */
    BLOCKING,
    /** Recorded for the report; the claim stands. */
    DIAGNOSTIC
}
