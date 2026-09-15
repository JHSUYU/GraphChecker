package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 4: one consumer path in the composition, with its selector.
 *
 * <p>The selector is the Boolean the composed formula implies from:
 * {@code selector_p => pi_p and phi_fatal and reads_p}.  Arrivals, clock
 * readings and valuations are stated inside that implication, never as a global
 * assertion about one session's facts.</p>
 */
public final class PathEntry {
    private final String pathId;
    private final String sessionId;
    private final String selector;
    private final boolean fatalObserved;

    private PathEntry(String pathId, String sessionId, String selector,
                      boolean fatalObserved) {
        this.pathId = pathId;
        this.sessionId = sessionId;
        this.selector = selector;
        this.fatalObserved = fatalObserved;
    }

    public static PathEntry of(String pathId, String sessionId, String selector,
                               boolean fatalObserved) {
        return new PathEntry(Fields.text(pathId, "pathId"),
                Fields.text(sessionId, "sessionId"),
                Fields.text(selector, "selector"), fatalObserved);
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof PathEntry)) return false;
        PathEntry other = (PathEntry) value;
        return fatalObserved == other.fatalObserved
                && pathId.equals(other.pathId)
                && sessionId.equals(other.sessionId)
                && selector.equals(other.selector);
    }

    @Override
    public int hashCode() {
        return Objects.hash(pathId, sessionId, selector, fatalObserved);
    }

    @Override
    public String toString() {
        return "PathEntry{" + pathId + " " + selector
                + (fatalObserved ? " fatal}" : "}");
    }
}
