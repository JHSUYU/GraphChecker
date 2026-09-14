package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * OCC-2: the one address of a region occurrence.
 *
 * <p>An occurrence is
 * {@code (node, epoch, region, k-th activation)} together with root-source
 * inheritance, and nothing else.  Everything an activation was <em>reached
 * under</em> -- the RPC exchange, the request api, the thread it ran on, the
 * receiver's runtime class, whether the source was registered on the receiver
 * or inherited from the thread -- is information about the activation, never a
 * condition on recognising it.  Those circumstances belong in
 * {@link ReachedUnder}, which matching never consults.</p>
 *
 * <p>This type exists because four places each held their own second version
 * of "are these two activations the same", and they disagreed.  Two of the
 * expensive 17960 failures were that disagreement: the request veto refused
 * every flip replay whose workload reached the planned activation by another
 * path, and the inherited-source veto read an absence as a contradiction.
 * A third was the activation counter, keyed on the planned request -- a
 * constant per task -- so every candidate fell into one bucket whatever it
 * actually entered under.  One address, one comparison, one counting rule.</p>
 *
 * <p>The rendered form is {@link OccurrenceId}'s: {@code
 * <node>#<epoch>/region/<regionId>#<k>}, optionally with {@code #a<n>} for the
 * activation that ran it.  Parsing is total: a string that does not spell an
 * address yields {@link #isNamed()} {@code false} and refuses to match
 * anything, rather than half-matching on the parts it could read.</p>
 */
public final class OccurrenceAddress {
    private static final String REGION_MARKER = "/region/";
    private static final String EPOCH_MARKER = "#epoch";

    /** The address no occurrence has: it matches nothing, including itself. */
    public static final OccurrenceAddress NONE =
            new OccurrenceAddress("", "", "", 0);

    private final String node;
    private final String epoch;
    private final String regionId;
    private final int ordinal;

    private OccurrenceAddress(String node, String epoch, String regionId,
                              int ordinal) {
        this.node = node;
        this.epoch = epoch;
        this.regionId = regionId;
        this.ordinal = ordinal;
    }

    /**
     * Reads an address out of an occurrence id, activation suffix or not.
     *
     * <p>The activation suffix is deliberately dropped: {@code #a2} says
     * which run of this address published a row, and every activation of one
     * address is the same occurrence.</p>
     */
    public static OccurrenceAddress parse(String occurrenceId) {
        String planned = OccurrenceId.parse(occurrenceId).planned();
        int region = planned.indexOf(REGION_MARKER);
        if (region <= 0) return NONE;
        String source = planned.substring(0, region);
        String rest = planned.substring(region + REGION_MARKER.length());
        int hash = rest.lastIndexOf('#');
        if (hash <= 0 || hash + 1 >= rest.length()) return NONE;
        final int ordinal;
        try {
            ordinal = Integer.parseInt(rest.substring(hash + 1));
        } catch (NumberFormatException notAnOrdinal) {
            return NONE;
        }
        if (ordinal < 1) return NONE;
        return of(source, rest.substring(0, hash), ordinal);
    }

    /** The address of the {@code ordinal}-th activation of one region. */
    public static OccurrenceAddress of(String sourceKey, String regionId,
                                       int ordinal) {
        String source = sourceKey == null ? "" : sourceKey.trim();
        String region = regionId == null ? "" : regionId.trim();
        if (source.isEmpty() || region.isEmpty() || ordinal < 1) {
            return NONE;
        }
        int epoch = source.lastIndexOf(EPOCH_MARKER);
        if (epoch <= 0 || epoch + EPOCH_MARKER.length() >= source.length()) {
            // A source that names no epoch is still a node; the epoch is then
            // the empty one, which only matches another empty one.
            return new OccurrenceAddress(source, "", region, ordinal);
        }
        return new OccurrenceAddress(source.substring(0, epoch),
                source.substring(epoch + EPOCH_MARKER.length()), region,
                ordinal);
    }

    /** Whether this address names an occurrence at all. */
    public boolean isNamed() {
        return !node.isEmpty() && !regionId.isEmpty() && ordinal >= 1;
    }

    /** The node this occurrence ran on, without its epoch. */
    public String node() {
        return node;
    }

    /**
     * The lifecycle of that node, as the workload labelled it.
     *
     * <p>A workload declares its epochs literally -- {@code
     * registerSource(..., 0)} at start, {@code restartSource(..., 1)} across a
     * restart -- so the label means the same lifecycle in every run of it and
     * is comparable between a recording and a replay.</p>
     */
    public String epoch() {
        return epoch;
    }

    /** Node and epoch together, as a source key. */
    public String sourceKey() {
        return epoch.isEmpty() ? node : node + EPOCH_MARKER + epoch;
    }

    public String regionId() {
        return regionId;
    }

    /** The k in "k-th activation of this region on this node and epoch". */
    public int ordinal() {
        return ordinal;
    }

    /**
     * Whether {@code observed} is this occurrence.
     *
     * <p>All four parts, and only those four.  An unnamed address on either
     * side is not a match: an address nobody could read is not evidence that
     * the activation is the planned one.</p>
     */
    public boolean matches(OccurrenceAddress observed) {
        return isNamed() && observed != null && observed.isNamed()
                && ordinal == observed.ordinal
                && node.equals(observed.node)
                && epoch.equals(observed.epoch)
                && regionId.equals(observed.regionId);
    }

    /** Whether {@code observed} is this occurrence's node and epoch. */
    public boolean sameLifecycle(OccurrenceAddress observed) {
        return isNamed() && observed != null && observed.isNamed()
                && node.equals(observed.node)
                && epoch.equals(observed.epoch);
    }

    /** Why {@code observed} is not this occurrence, or {@code ""}. */
    public String describe(OccurrenceAddress observed) {
        if (matches(observed)) return "";
        if (!isNamed()) return "the planned address names no occurrence";
        if (observed == null || !observed.isNamed()) {
            return "the activation names no occurrence";
        }
        if (!node.equals(observed.node)) {
            return "occurrence ran on " + observed.node + ", not " + node;
        }
        if (!epoch.equals(observed.epoch)) {
            return "occurrence ran in epoch " + observed.epoch + " of "
                    + node + ", not epoch " + epoch;
        }
        if (!regionId.equals(observed.regionId)) {
            return "occurrence is region " + observed.regionId + ", not "
                    + regionId;
        }
        return "occurrence is activation " + observed.ordinal + ", not "
                + ordinal;
    }

    /**
     * The bucket activations of this region are counted in.
     *
     * <p>Node, epoch, region and the root the activations enter through --
     * the address without its ordinal, which is what the ordinal counts
     * within.  The planner and the replay both use this, so the two ends
     * count one population.  The request is deliberately absent: it is a
     * circumstance, and a circumstance does not partition a count.</p>
     */
    public String counterScope(String rootMethod) {
        return sourceKey() + "\n" + regionId + "\n"
                + (rootMethod == null ? "" : rootMethod);
    }

    /** This address as {@link OccurrenceId} spells it, without activation. */
    public String render() {
        return isNamed()
                ? sourceKey() + REGION_MARKER + regionId + "#" + ordinal : "";
    }

    /** This address as the given activation of it. */
    public String render(int activationOrdinal) {
        return isNamed() && activationOrdinal >= 1
                ? render() + "#a" + activationOrdinal : render();
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof OccurrenceAddress)) return false;
        OccurrenceAddress other = (OccurrenceAddress) value;
        return ordinal == other.ordinal && node.equals(other.node)
                && epoch.equals(other.epoch)
                && regionId.equals(other.regionId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node, epoch, regionId, ordinal);
    }

    @Override
    public String toString() {
        return isNamed() ? render() : "<unnamed occurrence>";
    }
}
