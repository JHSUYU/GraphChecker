package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 1: a replay-stable name for the storage a state edge joins on.
 *
 * <p>{@code owner} is the class name for a static field and
 * {@code <allocating Endpoint id>#<m>} for a heap object -- the m-th allocation
 * at that site inside that occurrence (IDENTITY-V2 sec 4), which is what makes
 * "the same BlockKey" mean the same thing in two replays without any
 * concrete-identity heuristic.  {@code slot} is the field name or offset, the
 * index, or the map key hash.</p>
 */
public final class LocationId {
    private final LocationKind kind;
    private final String owner;
    private final String slot;

    private LocationId(LocationKind kind, String owner, String slot) {
        this.kind = kind;
        this.owner = owner;
        this.slot = slot;
    }

    public static LocationId of(LocationKind kind, String owner, String slot) {
        return new LocationId(Fields.required(kind, "kind"),
                Fields.text(owner, "owner"), Fields.text(slot, "slot"));
    }

    /**
     * The owner of a heap object: its allocating endpoint and allocation
     * ordinal.
     *
     * <p>One spelling of the rule, so the runtime that writes a location and
     * the composer that joins on it cannot mint two different owners for one
     * object.</p>
     */
    public static String heapOwner(Endpoint allocation, int allocationOrdinal) {
        return Fields.required(allocation, "allocation").id() + "#"
                + Fields.ordinal(allocationOrdinal, "allocationOrdinal");
    }

    public LocationKind kind() {
        return kind;
    }

    public String owner() {
        return owner;
    }

    public String slot() {
        return slot;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof LocationId)) return false;
        LocationId other = (LocationId) value;
        return kind == other.kind && owner.equals(other.owner)
                && slot.equals(other.slot);
    }

    @Override
    public int hashCode() {
        return Objects.hash(kind, owner, slot);
    }

    @Override
    public String toString() {
        return kind + " " + owner + "." + slot;
    }
}
