package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 4: how far a root may move, absolutely.
 *
 * <p>Declared relative to the recorded value and resolved to absolute bounds by
 * the runtime ({@link RootMintRow}); a root with neither bound is pinned
 * everywhere -- in the composer and in the flip solver, which is the same rule
 * stated once.</p>
 */
public final class RootDomain {
    private final String rootId;
    private final RootKind kind;
    private final String recordedValue;
    private final String min;
    private final String max;

    private RootDomain(String rootId, RootKind kind, String recordedValue,
                       String min, String max) {
        this.rootId = rootId;
        this.kind = kind;
        this.recordedValue = recordedValue;
        this.min = min;
        this.max = max;
    }

    public static RootDomain of(String rootId, RootKind kind,
                                String recordedValue, String min, String max) {
        return new RootDomain(Fields.text(rootId, "rootId"),
                Fields.required(kind, "kind"),
                Fields.stated(recordedValue, "recordedValue"),
                Fields.optional(min), Fields.optional(max));
    }

    public String rootId() {
        return rootId;
    }

    public RootKind kind() {
        return kind;
    }

    public String recordedValue() {
        return recordedValue;
    }

    /** The absolute lower bound, or {@code null}. */
    public String min() {
        return min;
    }

    /** The absolute upper bound, or {@code null}. */
    public String max() {
        return max;
    }

    /** A root with no declared domain does not move. */
    public boolean pinned() {
        return min == null && max == null;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof RootDomain)) return false;
        RootDomain other = (RootDomain) value;
        return kind == other.kind && rootId.equals(other.rootId)
                && recordedValue.equals(other.recordedValue)
                && Objects.equals(min, other.min)
                && Objects.equals(max, other.max);
    }

    @Override
    public int hashCode() {
        return Objects.hash(rootId, kind, recordedValue, min, max);
    }

    @Override
    public String toString() {
        return "RootDomain{" + rootId + " " + kind + " [" + min + ", " + max
                + "] recorded " + recordedValue + "}";
    }
}
