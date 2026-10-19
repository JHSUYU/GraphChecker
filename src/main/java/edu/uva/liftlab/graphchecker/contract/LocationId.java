package edu.uva.liftlab.graphchecker.contract;

import com.google.common.collect.Interner;
import com.google.common.collect.Interners;

public final class LocationId extends Value {
    private final LocationKind kind;
    private final String owner;
    private final String slot;
    private String key;

    private static final class Keys {
        static final Interner<String> HELD = Interners.newWeakInterner();
    }

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

    public String key() {
        String spelled = key;
        if (spelled == null) {
            spelled = Keys.HELD.intern(kind + "/" + owner + "#" + slot);
            key = spelled;
        }
        return spelled;
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
