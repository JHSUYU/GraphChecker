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
 */
public final class RegionInitialSnapshotCarrierSmoke {
    public static void main(String[] args) {
        twoEntryMapSnapshot();
        twoElementListSnapshot();
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
                new Object[]{"k0", "k1"}, new Object[]{"v0", "v1"}, 1),
                "map snapshot rejected");
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
                new Object[]{"e0", "e1"}, 0), "list snapshot rejected");
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
        require(System.snapshotContainerExpression(rows, null, members, 0),
                "bounded snapshot must still answer");
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
