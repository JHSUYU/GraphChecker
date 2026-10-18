package edu.uva.liftlab.graphchecker.contract;

import com.google.common.collect.Interner;
import com.google.common.collect.Interners;

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
    /** {@link #key()}, spelled once: a corpus asks every row's location
     *  for it, and holds it in every index by location. */
    private String key;

    /** The location keys a JVM holds, one string a key while any index
     *  holds it: rows' locations and expressions' location nodes spell the
     *  same keys (SGF8-adhoc-05 round 5's planner: 1.6 M key strings, 294
     *  MB, for about half as many keys).  Loaded only where a key is asked
     *  for, never by a replay's runtime. */
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

    /** The VM's location key, {@code KIND/owner#slot}: the one spelling
     *  every join and index of rows keys a location by. */
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
