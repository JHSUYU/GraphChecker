package edu.uva.liftlab.graphchecker.contract;

/**
 * The storage a state edge joins on, spelled as the VM's location key
 * ({@code RowPublication.locationKey}, {@code KIND/rid#slot}).  A rid is a
 * per-run counter, so it names one object only within a session; a static
 * field's owner is its class.  {@code slot}: field offset, index, or a
 * container's state slot.
 *
 * <p>Trap: a class owner on a heap location aliases every instance;
 * {@code smt.Arms.namedOwner} is the one place that decides.  No
 * cross-replay object identity exists.</p>
 */
public final class LocationId extends Value {
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
    Object[] parts() {
        return new Object[] {kind, owner, slot};
    }

    @Override
    public String toString() {
        return kind + " " + owner + "." + slot;
    }
}
