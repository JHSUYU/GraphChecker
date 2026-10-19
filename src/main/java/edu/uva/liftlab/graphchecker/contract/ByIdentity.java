package edu.uva.liftlab.graphchecker.contract;

public final class ByIdentity<T> {
    private final T value;

    public ByIdentity(T value) {
        this.value = value;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof ByIdentity
                && ((ByIdentity<?>) other).value == value;
    }

    @Override
    public int hashCode() {
        return System.identityHashCode(value);
    }
}
