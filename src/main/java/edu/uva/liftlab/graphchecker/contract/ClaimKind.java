package edu.uva.liftlab.graphchecker.contract;

public enum ClaimKind {
    MARKER_FLIPPED,
    CLOCK_SKEW,
    MESSAGE_PAIRING_FLIPPED,
    STATE_PAIRING_FLIPPED,
    FORMULA_SAT,
    NO_SUPPORTED_WITNESS
}
