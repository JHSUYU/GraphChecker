package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The one address: node, epoch, region, k-th activation, and nothing else.
 *
 * <p>Each case here is a job one of the replay's five separate predicates
 * used to do, so that deleting them is a removal of duplication rather than
 * a removal of checks.</p>
 */
public class OccurrenceAddressTest {
    private static final String PLANNED =
            "hdfs-17960/nn0#epoch1/region/"
                    + "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d#1";

    private static OccurrenceAddress address(String occurrenceId) {
        return OccurrenceAddress.parse(occurrenceId);
    }

    /** The rendered form is the bytes the corpus already carries. */
    @Test
    public void anAddressRoundTripsItsOccurrenceId() {
        assertEquals(PLANNED, address(PLANNED).render());
        assertEquals("the activation suffix is not part of the address",
                PLANNED, address(PLANNED + "#a2").render());
        assertEquals(PLANNED + "#a2", address(PLANNED).render(2));
        assertEquals("an address under no request writes no family, so every"
                        + " id minted before the family existed is its own",
                PLANNED, OccurrenceAddress.of("hdfs-17960/nn0#epoch1",
                        "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d", "", 1)
                        .render());
        assertEquals("", address(PLANNED).family());

        String withFamily = PLANNED.substring(0, PLANNED.length() - 2)
                + "@hdfs-17960/client#epoch0/checkpoint-namespace#1";
        assertEquals(withFamily, address(withFamily).render());
        assertEquals("hdfs-17960/client#epoch0/checkpoint-namespace",
                address(withFamily).family());
        assertEquals("and the region is still read whole",
                "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d",
                address(withFamily).regionId());
        assertEquals(withFamily + "#a2", address(withFamily).render(2));
    }

    /** Node, epoch, region and ordinal are read out structurally. */
    @Test
    public void theAddressIsItsFourParts() {
        OccurrenceAddress planned = address(PLANNED);

        assertEquals("hdfs-17960/nn0", planned.node());
        assertEquals("1", planned.epoch());
        assertEquals("hdfs-17960/nn0#epoch1", planned.sourceKey());
        assertEquals("REGION.9492ec77-0f65-34ba-a3af-14753ac7347d",
                planned.regionId());
        assertEquals(1, planned.ordinal());
    }

    /** The same four parts match; any one of them different does not. */
    @Test
    public void allFourPartsDecideTheMatch() {
        OccurrenceAddress planned = address(PLANNED);

        assertTrue(planned.matches(address(PLANNED)));
        assertTrue("a different activation of it is the same occurrence",
                planned.matches(address(PLANNED + "#a3")));
        assertFalse(planned.matches(address(
                "hdfs-17960/dn0#epoch1/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#1")));
        assertFalse("epoch 0 is not epoch 1", planned.matches(address(
                "hdfs-17960/nn0#epoch0/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#1")));
        assertFalse(planned.matches(address(
                "hdfs-17960/nn0#epoch1/region/REGION.other#1")));
        assertFalse("the second activation is not the first",
                planned.matches(address(
                        "hdfs-17960/nn0#epoch1/region/REGION.9492ec77-0f65-"
                                + "34ba-a3af-14753ac7347d#2")));
    }

    /**
     * An epoch of one node is a different occurrence, and says so.
     *
     * <p>The 17960 flip replay threw inside the workload before it restarted
     * the NameNode, so every activation it offered was epoch 0 while the plan
     * addressed epoch 1.  Nothing compared the epochs, and the flip's model
     * was applied at the epoch-0 mint.</p>
     */
    @Test
    public void anotherEpochOfOneNodeIsAnotherOccurrence() {
        OccurrenceAddress planned = address(PLANNED);
        OccurrenceAddress epoch0 = address(
                "hdfs-17960/nn0#epoch0/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#1");

        assertFalse(planned.matches(epoch0));
        assertFalse(planned.sameLifecycle(epoch0));
        assertEquals("occurrence ran in epoch 0 of hdfs-17960/nn0, not "
                + "epoch 1", planned.describe(epoch0));
    }

    /** An unreadable address matches nothing rather than half-matching. */
    @Test
    public void anUnnamedAddressMatchesNothing() {
        assertFalse(address("").isNamed());
        assertFalse(address("nn0#epoch1/region/REGION.1").isNamed());
        assertFalse(address("nn0#epoch1/region/REGION.1#0").isNamed());
        assertFalse(address("nn0#epoch1/region/REGION.1#x").isNamed());
        assertFalse(address(PLANNED).matches(OccurrenceAddress.NONE));
        assertFalse(OccurrenceAddress.NONE.matches(address(PLANNED)));
    }

    /**
     * The counting bucket is the address without its ordinal.
     *
     * <p>Including the request family, and excluding that request's own
     * ordinal.  Two requests running concurrently against one node are two
     * populations -- numbering them together makes k depend on which
     * arrived first, which is how hdfs-17899 bug2's two {@code
     * nn0 REGION.2392e4b7} activations answered each other's addresses --
     * while two rounds of ONE family are one population, because a replay
     * whose heartbeat counter ran further than the recording's is still at
     * the same occurrence.</p>
     */
    @Test
    public void theCounterScopeIsTheAddressWithoutItsOrdinal() {
        String root = "<a.B: void run()>";
        String first = address(PLANNED).counterScope(root);
        String second = address(
                "hdfs-17960/nn0#epoch1/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#7").counterScope(root);

        assertEquals("two activations of one region are one bucket",
                first, second);
        assertEquals("node, region, family, root -- four parts", 4,
                first.split("\n", -1).length);
        assertFalse("the request key is not in the bucket",
                first.contains("/request/"));
        assertFalse("two epochs are two buckets", first.equals(address(
                "hdfs-17960/nn0#epoch0/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#1").counterScope(root)));

        // The family partitions the count, and the request ordinal does not.
        String region = "hdfs-17899/nn0#epoch0/region/REGION.2392e4b7";
        String heartbeat = region
                + "@hdfs-17899/target-dn#epoch0/heartbeat#1";
        String refresh = region + "@hdfs-17899/sps#epoch0/refresh#1";
        assertFalse("two families are two buckets",
                address(heartbeat).counterScope(root)
                        .equals(address(refresh).counterScope(root)));
        assertEquals("a second round of one family is one bucket",
                address(heartbeat).counterScope(root),
                address(region + "@hdfs-17899/target-dn#epoch0/heartbeat#2")
                        .counterScope(root));
        assertEquals("and the family survives the address round-trip",
                heartbeat, address(heartbeat).render());
        assertEquals("which the request key it came from spells",
                "hdfs-17899/target-dn#epoch0/heartbeat",
                OccurrenceAddress.familyOf(
                        "hdfs-17899/target-dn#epoch0/request/heartbeat#4"));
        assertFalse("an activation under a family is not one under none",
                address(heartbeat).matches(address(region + "#1")));
    }

    /** A source that names no epoch is still a node. */
    @Test
    public void anEpochlessSourceIsStillAnAddress() {
        OccurrenceAddress plain = OccurrenceAddress.of("dn0", "REGION.1", 1);

        assertTrue(plain.isNamed());
        assertEquals("dn0", plain.node());
        assertEquals("", plain.epoch());
        assertEquals("dn0/region/REGION.1#1", plain.render());
    }
}
