package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §1: what kind of location a state edge is about.
 */
public enum LocationKind {
    STATIC,
    INSTANCE,
    ARRAY,
    MAP
}
