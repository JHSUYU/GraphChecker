package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * IDENTITY-V3 sec 5: a replay-stable name for the storage a state edge joins on.
 *
 * <p>Memory Indexing (Sumner and Zhang, FSE 2010): an object's canonical name is
 * the execution index of its ALLOCATION, so the same semantic object gets the
 * same name in every replay whatever its address.  Here that is literally the
 * allocating {@link Endpoint}'s id -- the allocating occurrence, the allocation
 * site ({@code class#method#bci:NEW} or {@code :NEWARRAY}) and the site-local
 * execution index.  Never a session rid, never a machine address: those are the
 * two things that differ between two runs of the same program.</p>
 *
 * <p>The three owner forms, and no fourth: a static field is owned by its class;
 * a heap object by {@link #allocated}; an object that already existed when the
 * recording window opened by {@link #preWindowOwner}, which is a named degraded
 * form -- the case must declare a root at its source if the anchor reads it.
 * {@code slot} is the field name or offset, the index, or the map key.</p>
 */
public final class LocationId {
    /** The prefix of an owner that predates the recording window. */
    public static final String PRE_WINDOW = "preWindow:";

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
     * A heap location, owned by the endpoint that allocated the object.
     *
     * <p>Refuses {@link LocationKind#STATIC}: a static field is not allocated,
     * and an owner that says otherwise would join two locations that are not
     * the same storage.</p>
     */
    public static LocationId allocated(Endpoint allocation, LocationKind kind,
                                       String slot) {
        if (Fields.required(kind, "kind") == LocationKind.STATIC) {
            throw new IllegalArgumentException(
                    "a STATIC location is owned by its class, not by an "
                            + "allocation");
        }
        return of(kind, Fields.required(allocation, "allocation").id(), slot);
    }

    /**
     * The owner of an object that already existed when the window opened.
     *
     * <p>{@code m} is the m-th such pre-window object of that class seen -- an
     * ordinal, because there is no allocation to index; the form is named so a
     * reader can tell a degraded owner from an allocated one at a glance.</p>
     */
    public static String preWindowOwner(String className, int m) {
        return PRE_WINDOW + Fields.text(className, "className") + "#"
                + Fields.ordinal(m, "m");
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

    /** Whether this location's owner predates the recording window. */
    public boolean preWindow() {
        return owner.startsWith(PRE_WINDOW);
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
