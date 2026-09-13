import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Contract smoke for what a whole-state carrier's INITIAL version says about
 * the contents the container held before it was selected.
 *
 * <p>Selecting roots the container's state, and that root is opaque: the VM
 * did not watch the members that were already there, so the INITIAL value
 * alone leaves a reader free to solve with an empty container.  When the
 * recorder has been told the contents, the INITIAL value is instead the
 * snapshot chain - a SNAPSHOT_BASE with one PUT (map) or APPEND (list) per
 * member, in iteration order, in exactly the node shapes the later
 * STATE_PUT/STATE_APPEND versions use - and the version record says how many
 * members it states.</p>
 *
 * <p>Past the bound the chain is refused and the opaque root is kept, and the
 * record says so: {@code truncated} distinguishes "held nothing" from "held
 * something this engine declined to state".</p>
 *
 * <p>A container the recorder has already watched change is the case that
 * used to fall silently between the two.  The offer was dropped so that the
 * history - the one thing relating the container to this activation's inputs
 * - survived, the same {@code true} was answered as for an installed chain,
 * and the INITIAL version went out with an opaque root described as a
 * complete snapshot.  The base is recoverable instead: the history says which
 * mutations produced the observed content, and an APPEND or a positional
 * INSERT each carries its own inverse, so undoing them yields the content the
 * root denotes and the history is rebuilt on top of it.  A record that
 * carries no inverse leaves the base honestly unknown.</p>
 */
public final class RegionInitialSnapshotCarrierSmoke {
    /** ConcolicMngr::InitialSnapshotAnswer. */
    private static final int INSTALLED = 1;
    private static final int KEPT_EXISTING_HISTORY = 2;
    private static final int REFUSED_OVER_BOUND = 3;
    private static final int REBASED_UNDER_HISTORY = 4;

    /** A field owner, so the list can be given a shadow by name. */
    private static final class Holder {
        private final List<Object> rows = new ArrayList<Object>();
    }

    public static void main(String[] args) {
        twoEntryMapSnapshot();
        twoElementListSnapshot();
        anEmptyContainerStatesThatItHeldNothing();
        aListMutatedBeforeSelectionPublishesItsBase();
        anUnrecoverableBaseIsPublishedAsUnknown();
        boundedSnapshotKeepsTheOpaqueRoot();
        System.out.println(
                "CAUSYNTH_REGION_INITIAL_SNAPSHOT_CARRIER_SMOKE_OK");
    }

    private static void twoEntryMapSnapshot() {
        Map<Object, Object> map = new HashMap<Object, Object>();
        map.put("k0", "v0");
        map.put("k1", "v1");

        require(System.startConcolicRegion(
                "REGION.initial-snapshot-map",
                "TASK.initial-snapshot-map") == 0L, "region start rejected");
        // The Java side inspects the live container and hands over its
        // members; the VM never iterates a Java collection itself.
        require(System.snapshotContainerExpression(map,
                new Object[]{"k0", "k1"}, new Object[]{"v0", "v1"}, 1)
                == INSTALLED, "map snapshot rejected");
        require(System.selectSharedMapCarrier(map) > 0L,
                "map carrier selection rejected");

        String evidence = System.getSharedMapVersions(map);
        System.endConcolic();

        require(evidence.contains("\"versionKind\":\"INITIAL\""), evidence);
        require(evidence.contains("\"initialSnapshot\""), evidence);
        require(evidence.contains("\"entries\":2"), evidence);
        require(evidence.contains("\"truncated\":false"), evidence);
        // One PUT per entry, from the explicit empty base.
        require(evidence.contains("\"operation\":\"SNAPSHOT_BASE\""),
                evidence);
        require(count(evidence, "\"operation\":\"PUT\"") == 2, evidence);
        require(evidence.contains("\"shape\":\"ASSOCIATIVE\""), evidence);
        // The members are named by content, not by an opaque identity.
        require(evidence.contains("k0") && evidence.contains("v1"), evidence);
    }

    private static void twoElementListSnapshot() {
        List<Object> rows = new ArrayList<Object>();
        rows.add("e0");
        rows.add("e1");

        require(System.startConcolicRegion(
                "REGION.initial-snapshot-list",
                "TASK.initial-snapshot-list") == 0L, "region start rejected");
        require(System.snapshotContainerExpression(rows, null,
                new Object[]{"e0", "e1"}, 0) == INSTALLED,
                "list snapshot rejected");
        require(System.selectSharedMapCarrier(rows) > 0L,
                "list carrier selection rejected");

        String evidence = System.getSharedMapVersions(rows);
        System.endConcolic();

        require(evidence.contains("\"entries\":2"), evidence);
        require(evidence.contains("\"truncated\":false"), evidence);
        require(evidence.contains("\"operation\":\"SNAPSHOT_BASE\""),
                evidence);
        require(count(evidence, "\"operation\":\"APPEND\"") == 2, evidence);
        require(evidence.contains("\"shape\":\"INDEXED\""), evidence);
    }

    private static void boundedSnapshotKeepsTheOpaqueRoot() {
        // The run lowers the bound, so three members exceed it.
        List<Object> rows = new ArrayList<Object>();
        Object[] members = new Object[3];
        for (int index = 0; index < members.length; index++) {
            members[index] = "e" + index;
            rows.add(members[index]);
        }

        require(System.startConcolicRegion(
                "REGION.initial-snapshot-bound",
                "TASK.initial-snapshot-bound") == 0L,
                "region start rejected");
        require(System.snapshotContainerExpression(rows, null, members, 0)
                == REFUSED_OVER_BOUND,
                "the bound must say it refused, not that it installed");
        require(System.selectSharedMapCarrier(rows) > 0L,
                "list carrier selection rejected");

        String evidence = System.getSharedMapVersions(rows);
        System.endConcolic();

        require(evidence.contains("\"entries\":3"), evidence);
        require(evidence.contains("\"truncated\":true"), evidence);
        // The opaque root is kept: nothing states the members.
        require(!evidence.contains("\"operation\":\"SNAPSHOT_BASE\""),
                evidence);
        require(count(evidence, "\"operation\":\"APPEND\"") == 0, evidence);
    }

    /**
     * A container that held nothing states that it held nothing.
     *
     * <p>Its complete snapshot is the bare SNAPSHOT_BASE, which is the exact
     * empty collection - the most constrained initial state there is.  The
     * record used to be derived from "more than zero members were stated or
     * the bound refused them", so this carrier published no snapshot block at
     * all and read back as content-unknown: the one container nobody has to
     * reconstruct was the one left free.</p>
     */
    private static void anEmptyContainerStatesThatItHeldNothing() {
        List<Object> rows = new ArrayList<Object>();

        require(System.startConcolicRegion(
                "REGION.initial-snapshot-empty",
                "TASK.initial-snapshot-empty") == 0L, "region start rejected");
        require(System.snapshotContainerExpression(rows, null,
                new Object[0], 0) == INSTALLED, "empty snapshot rejected");
        require(System.selectSharedMapCarrier(rows) > 0L,
                "list carrier selection rejected");

        String evidence = System.getSharedMapVersions(rows);
        System.endConcolic();

        require(evidence.contains("\"initialSnapshot\""), evidence);
        require(evidence.contains("\"entries\":0"), evidence);
        require(evidence.contains("\"truncated\":false"), evidence);
        require(evidence.contains("\"operation\":\"SNAPSHOT_BASE\""),
                evidence);
        require(count(evidence, "\"operation\":\"APPEND\"") == 0, evidence);
    }

    /**
     * A list the recorder watched change before the selection still publishes
     * the content it started with.
     *
     * <p>The list holds "e0" before the region.  Inside it, watched, "e1" is
     * inserted at index 0, so the observed content is ["e1", "e0"] over an
     * opaque root.  Undoing the recorded INSERT at its recorded position
     * recovers the base ["e0"], and the INSERT is rebuilt on top of it: the
     * INITIAL value denotes the same two members it always did, states the
     * one the container already held, and keeps the recorded mutation.</p>
     */
    private static void aListMutatedBeforeSelectionPublishesItsBase() {
        Holder holder = new Holder();
        holder.rows.add("e0");

        require(System.startConcolicRegion(
                "REGION.initial-snapshot-rebase",
                "TASK.initial-snapshot-rebase") == 0L,
                "region start rejected");
        System.symbolizeField(holder, "rows", "rebased_input_rows");
        // Watched: the list now carries a mutation history over an opaque
        // root, which is exactly what used to make the offer a no-op.
        holder.rows.add(0, "e1");
        require(holder.rows.size() == 2,
                "concrete list diverged: " + holder.rows.size());

        require(System.snapshotContainerExpression(holder.rows, null,
                new Object[]{"e1", "e0"}, 0) == REBASED_UNDER_HISTORY,
                "a recoverable base must be recovered, not dropped");
        require(System.selectSharedMapCarrier(holder.rows) > 0L,
                "list carrier selection rejected");

        String evidence = System.getSharedMapVersions(holder.rows);
        System.endConcolic();

        require(evidence.contains("\"versionKind\":\"INITIAL\""), evidence);
        require(evidence.contains("\"initialSnapshot\""), evidence);
        // What the INITIAL value denotes is the content at selection.
        require(evidence.contains("\"entries\":2"), evidence);
        require(evidence.contains("\"truncated\":false"), evidence);
        // The base is published: one APPEND for the member already there,
        // standing on the explicit empty base.
        require(evidence.contains("\"operation\":\"SNAPSHOT_BASE\""),
                evidence);
        require(count(evidence, "\"operation\":\"APPEND\"") == 1, evidence);
        require(evidence.contains("e0"), evidence);
        // And the watched mutation is still the watched mutation.
        require(evidence.contains("\"operation\":\"INSERT\""), evidence);
    }

    /**
     * A history that carries no inverse leaves the base unknown, and says so.
     *
     * <p>REMOVE took a member the record does not carry, so nothing here can
     * reconstruct what the list held.  Reporting that as a complete snapshot
     * would state a content the run never had; reporting it as an ordinary
     * opaque root would hide that an offer was made and declined.  The
     * version says truncated with no member count.</p>
     */
    private static void anUnrecoverableBaseIsPublishedAsUnknown() {
        Holder holder = new Holder();
        holder.rows.add("e0");
        holder.rows.add("e1");

        require(System.startConcolicRegion(
                "REGION.initial-snapshot-unrecoverable",
                "TASK.initial-snapshot-unrecoverable") == 0L,
                "region start rejected");
        System.symbolizeField(holder, "rows", "unrecoverable_input_rows");
        holder.rows.remove(0);
        require(holder.rows.size() == 1,
                "concrete list diverged: " + holder.rows.size());

        require(System.snapshotContainerExpression(holder.rows, null,
                new Object[]{"e1"}, 0) == KEPT_EXISTING_HISTORY,
                "an unrecoverable base must be reported, not installed");
        require(System.selectSharedMapCarrier(holder.rows) > 0L,
                "list carrier selection rejected");

        String evidence = System.getSharedMapVersions(holder.rows);
        System.endConcolic();

        require(evidence.contains("\"initialSnapshot\""), evidence);
        require(evidence.contains("\"truncated\":true"), evidence);
        require(evidence.contains("\"entries\":-1"), evidence);
        require(!evidence.contains("\"operation\":\"SNAPSHOT_BASE\""),
                evidence);
    }

    private static int count(String value, String needle) {
        int result = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            result++;
            offset += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
