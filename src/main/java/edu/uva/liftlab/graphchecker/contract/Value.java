package edu.uva.liftlab.graphchecker.contract;

import java.util.Arrays;

abstract class Value {
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
