package edu.uva.liftlab.graphchecker.d3.contract;

/**
 * CONTRACT-SPEC 2: what a root is, which decides how a witness may move it.
 *
 * <p>A {@link #MARKER} is enumerated over both of its values, an
 * {@link #INTEGRAL} over its declared domain relative to the recorded value,
 * and a {@link #CLOCK} is unbounded with a {@code >= 0} floor, per path.</p>
 */
public enum RootKind {
    MARKER,
    INTEGRAL,
    CLOCK
}
