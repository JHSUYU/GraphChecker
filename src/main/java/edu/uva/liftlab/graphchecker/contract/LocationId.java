package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * The name of the storage a state edge joins on, as the runtime writes it.
 *
 * <p>ONE owner spelling, and it is the VM's: the symbolic rid of the object
 * whose state this is, from the location key the runtime publishes
 * ({@code RowPublication.locationKey}, {@code KIND/rid#slot}).  A rid is a
 * per-run counter, and a join is per SESSION -- the write log and the read
 * rows of one run, spelled the same way on both sides -- so inside that run
 * it names exactly one object.  A static field is owned by its class, which
 * owns exactly one cell.  {@code slot} is the field offset, the index, or
 * the reserved state slot of a whole container.</p>
 *
 * <p>Whether an owner names its storage well enough to offer a read
 * ALTERNATIVE writers is one question, asked in one place
 * ({@code smt.Arms.namedOwner}): a class on a heap location aliases every
 * instance of it at once.  The allocation-endpoint form this class used to
 * mint (Memory Indexing, Sumner and Zhang, FSE 2010) is deleted: no main
 * code ever produced it, and the gate that admitted only it refused every
 * row of both corpora -- 128 DECLARATION_MISSING rows on the clean
 * hdfs-17960 run.  When cross-replay object identity is needed, it comes
 * back with a producer.</p>
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
