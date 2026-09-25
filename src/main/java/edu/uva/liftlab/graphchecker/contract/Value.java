package edu.uva.liftlab.graphchecker.contract;

import java.util.Arrays;

/**
 * A contract value: equal to another of its own class iff their
 * {@link #parts()} are equal, hashed as {@code Objects.hash(parts())}.  A part
 * left out (a cached id) is derived, never state.
 */
abstract class Value {
    /** The state that decides equality, in a fixed order. */
    abstract Object[] parts();

    @Override
    public final boolean equals(Object value) {
        return this == value || value != null && value.getClass() == getClass()
                && Arrays.equals(parts(), ((Value) value).parts());
    }

    @Override
    public final int hashCode() {
        return Arrays.hashCode(parts());
    }
}
