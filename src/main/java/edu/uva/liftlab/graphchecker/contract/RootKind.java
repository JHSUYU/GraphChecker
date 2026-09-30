package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §5: how a witness may move a root: MARKER over both values,
 * INTEGRAL over its declared domain, CLOCK unbounded with a {@code >= 0}
 * floor, per path.
 */
public enum RootKind {
    MARKER,
    INTEGRAL,
    CLOCK
}
