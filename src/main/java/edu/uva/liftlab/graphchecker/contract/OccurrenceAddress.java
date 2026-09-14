package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * OCC-2: the one address of a region occurrence.
 *
 * <p>An occurrence is
 * {@code (node, epoch, region, request family, k-th activation within that
 * family)} together with root-source inheritance, and nothing else.  Every
 * component is a boundary the execution itself declares: the epoch by a
 * restart, the recording window by {@code startRecording}, the request family
 * by {@code beginRequest} or the RPC header the transport carries.  The
 * family is {@code (source, api)} of the innermost request in force -- and
 * deliberately NOT that request's own ordinal, which is a timing fact: a
 * replay whose DataNode heartbeats a few rounds further than the recording's
 * still reaches the same occurrence, and on hdfs-17899 bug1 eighteen
 * activations were reported diverged for exactly that.</p>
 *
 * <p>What remains a circumstance, never a component: the RPC exchange, the
 * thread it ran on, the receiver's runtime class, whether the source was
 * registered on the receiver or inherited from the thread.  Those belong in
 * {@link ReachedUnder}, which matching never consults.</p>
 *
 * <p>Why the family and not the whole request: two requests running
 * concurrently against one node are two populations, and numbering their
 * activations together makes k depend on which arrived first.  On
 * hdfs-17899 bug2 that is observable -- {@code nn0 REGION.2392e4b7#1} and
 * {@code #2}, recorded under {@code target-dn/heartbeat} and {@code
 * sps/refresh-block-keys}, were answered by each other's activations in the
 * replay.  Under the family each is the first activation of its own family
 * and neither can take the other's address.</p>
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
 * <node>#<epoch>/region/<regionId>[@<family>]#<k>}, optionally with {@code
 * #a<n>} for the activation that ran it.  The family segment is written only
 * when there is one, so every address of an activation under no request --
 * and every id minted before the family existed -- is byte-identical to what
 * it was.  Parsing is total: a string that does not spell an
 * address yields {@link #isNamed()} {@code false} and refuses to match
 * anything, rather than half-matching on the parts it could read.</p>
 */
public final class OccurrenceAddress {
    private static final String REGION_MARKER = "/region/";
    private static final String EPOCH_MARKER = "#epoch";
    /** Separates the request family from the region in the rendered form. */
    private static final char FAMILY_MARKER = '@';
    private static final String REQUEST_MARKER = "/request/";

    /** The address no occurrence has: it matches nothing, including itself. */
    public static final OccurrenceAddress NONE =
            new OccurrenceAddress("", "", "", "", 0);

    private final String node;
    private final String epoch;
    private final String regionId;
    /** {@code <requestSource>/<api>}, or {@code ""} under no request. */
    private final String family;
    private final int ordinal;

    private OccurrenceAddress(String node, String epoch, String regionId,
                              String family, int ordinal) {
        this.node = node;
        this.epoch = epoch;
        this.regionId = regionId;
        this.family = family;
        this.ordinal = ordinal;
    }

    /**
     * The request family a request key belongs to, or {@code ""}.
     *
     * <p>{@code hdfs-11741/balancer#epoch0/request/balance-block#1} is the
     * first occurrence of the family {@code
     * hdfs-11741/balancer#epoch0/balance-block}.  The trailing ordinal is
     * dropped on purpose: it counts requests in the recording window, which
     * is the one part of a request key a replay cannot be held to.</p>
     */
    public static String familyOf(String requestKey) {
        String key = requestKey == null ? "" : requestKey.trim();
        int marker = key.lastIndexOf(REQUEST_MARKER);
        if (marker <= 0) return "";
        String source = key.substring(0, marker);
        String api = key.substring(marker + REQUEST_MARKER.length());
        int hash = api.lastIndexOf('#');
        if (hash > 0) api = api.substring(0, hash);
        return source.isEmpty() || api.isEmpty() ? "" : source + "/" + api;
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
        // The region never contains '@' -- it is REGION.<uuid> -- and a
        // family-less address carries none, so an id written before the
        // family existed reads back exactly as it did.
        String head = rest.substring(0, hash);
        int at = head.indexOf(FAMILY_MARKER);
        return at < 0 ? of(source, head, "", ordinal)
                : of(source, head.substring(0, at), head.substring(at + 1),
                ordinal);
    }

    /** The address of the {@code ordinal}-th activation under no request. */
    public static OccurrenceAddress of(String sourceKey, String regionId,
                                       int ordinal) {
        return of(sourceKey, regionId, "", ordinal);
    }

    /**
     * The address of the {@code ordinal}-th activation of one region on one
     * node and epoch, within one request family.
     */
    public static OccurrenceAddress of(String sourceKey, String regionId,
                                       String requestFamily, int ordinal) {
        String source = sourceKey == null ? "" : sourceKey.trim();
        String region = regionId == null ? "" : regionId.trim();
        String scope = requestFamily == null ? "" : requestFamily.trim();
        if (source.isEmpty() || region.isEmpty() || ordinal < 1) {
            return NONE;
        }
        int epoch = source.lastIndexOf(EPOCH_MARKER);
        if (epoch <= 0 || epoch + EPOCH_MARKER.length() >= source.length()) {
            // A source that names no epoch is still a node; the epoch is then
            // the empty one, which only matches another empty one.
            return new OccurrenceAddress(source, "", region, scope, ordinal);
        }
        return new OccurrenceAddress(source.substring(0, epoch),
                source.substring(epoch + EPOCH_MARKER.length()), region,
                scope, ordinal);
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

    /**
     * The request family this occurrence ran inside, or {@code ""}.
     *
     * <p>{@code (source, api)} of the innermost request in force -- the
     * population k counts within.</p>
     */
    public String family() {
        return family;
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
                && regionId.equals(observed.regionId)
                && family.equals(observed.family);
    }

    /** Whether {@code observed} is this occurrence's node and epoch. */
    public boolean sameLifecycle(OccurrenceAddress observed) {
        return isNamed() && observed != null && observed.isNamed()
                && node.equals(observed.node)
                && epoch.equals(observed.epoch);
    }

    /** Why {@code observed} is not this occurrence, or {@code ""}. */
    /**
     * The same difference, never empty.
     *
     * <p>A refusal has to name what differed.  {@link #describe} answers
     * {@code ""} when the address matches, which is the right answer to
     * "how do these differ" and the wrong thing to put in a refusal: a
     * candidate refused for something other than its address was reported
     * as "matching root:  (attributed to X)", a sentence with a hole where
     * the reason should be.</p>
     */
    public String difference(OccurrenceAddress observed) {
        String stated = describe(observed);
        return stated.isEmpty()
                ? "the address matches; it was refused on something else"
                : stated;
    }

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
        if (!family.equals(observed.family)) {
            return "occurrence ran in request family "
                    + (observed.family.isEmpty() ? "(none)" : observed.family)
                    + ", not " + (family.isEmpty() ? "(none)" : family);
        }
        return "occurrence is activation " + observed.ordinal + ", not "
                + ordinal;
    }

    /**
     * The bucket activations of this region are counted in.
     *
     * <p>Node, epoch, region, request family and the root the activations
     * enter through -- the address without its ordinal, which is what the
     * ordinal counts within.  The planner and the replay both use this, so
     * the two ends count one population.</p>
     *
     * <p>The whole request used to be here and then was removed, because a
     * count partitioned by request while matching ignored it handed out
     * ordinal 1 in several buckets and any of them satisfied a planned
     * ordinal of 1.  The family is back in both at once: it partitions the
     * count AND it is part of the address the count is checked against, so
     * the two spellings cannot drift.</p>
     */
    public String counterScope(String rootMethod) {
        return sourceKey() + "\n" + regionId + "\n" + family + "\n"
                + (rootMethod == null ? "" : rootMethod);
    }

    /** This address as {@link OccurrenceId} spells it, without activation. */
    public String render() {
        if (!isNamed()) return "";
        return sourceKey() + REGION_MARKER + regionId
                + (family.isEmpty() ? "" : FAMILY_MARKER + family)
                + "#" + ordinal;
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
                && regionId.equals(other.regionId)
                && family.equals(other.family);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node, epoch, regionId, family, ordinal);
    }

    @Override
    public String toString() {
        return isNamed() ? render() : "<unnamed occurrence>";
    }
}
