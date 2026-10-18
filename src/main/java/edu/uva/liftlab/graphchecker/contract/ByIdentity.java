package edu.uva.liftlab.graphchecker.contract;

/**
 * An object as a key by its identity, for a concurrent map: a task's
 * equality hashes every part of it, and the memo keyed by it ({@code
 * explore.Corpus#ofTask}) is asked from every core ({@link Parallel}).
 */
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
