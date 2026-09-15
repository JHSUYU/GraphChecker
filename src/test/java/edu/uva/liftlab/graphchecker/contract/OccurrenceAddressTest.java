package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The one address: node, epoch, region, k-th activation, and nothing else.
 *
 */
public class OccurrenceAddressTest {
    private static final String PLANNED =
            "hdfs-17960/nn0#epoch1/region/"
                    + "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d#1";

    private static OccurrenceAddress address(String occurrenceId) {
        return OccurrenceAddress.parse(occurrenceId);
    }

    /**
     * OCC-1 grammar: the address is the identity and the activation that ran
     * it is provenance rendered beside it, so an address renders back to the
     * bytes the corpus already carries.
     */
    @Test
    public void theActivationSuffixIsNotPartOfTheAddress() {
        assertEquals(PLANNED, address(PLANNED).render());
        assertEquals("the activation suffix is not part of the address",
                PLANNED, address(PLANNED + "#a2").render());
        assertEquals(PLANNED + "#a2", address(PLANNED).render(2));
        assertEquals(PLANNED, OccurrenceAddress.of("hdfs-17960/nn0#epoch1",
                        "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d", 1)
                        .render());

        // A corpus written while the request family was a component of the
        // address still names the occurrence it always named: the suffix
        // parses and is discarded, because which request an activation was
        // reached under names neither endpoint of any interaction.
        String withFamily = PLANNED.substring(0, PLANNED.length() - 2)
                + "@hdfs-17960/client#epoch0/checkpoint-namespace#1";
        assertEquals(PLANNED, address(withFamily).render());
        assertEquals("and the region is still read whole",
                "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d",
                address(withFamily).regionId());
        assertTrue("so the two spellings are one occurrence",
                address(withFamily).matches(address(PLANNED)));

        // An id carrying the suffix still reads back as the address it
        // names: nothing mints one any more -- identity v3 tells two runs of
        // an address apart by the execution index they entered under -- and
        // a corpus written while something did is read, not refused.
        String occurrence = "hdfs-17960/nn0#epoch1/region/REGION.3cdc7049#1";
        assertEquals(occurrence, address(occurrence + "#a7").render());

        // A source that names no epoch is still a node.
        OccurrenceAddress plain = OccurrenceAddress.of("dn0", "REGION.1", 1);
        assertTrue(plain.isNamed());
        assertEquals("dn0", plain.node());
        assertEquals("", plain.epoch());
        assertEquals("dn0/region/REGION.1#1", plain.render());
    }

    /**
     * The same four parts match; any one of them different does not, and an
     * address nothing can read matches nothing rather than half-matching.
     */
    @Test
    public void allFourPartsDecideTheMatch() {
        OccurrenceAddress planned = address(PLANNED);

        assertTrue(planned.matches(address(PLANNED)));
        assertTrue("a different activation of it is the same occurrence",
                planned.matches(address(PLANNED + "#a3")));

        // One part changed per row: node, epoch, region, k.
        String[] elsewhere = {
                "hdfs-17960/dn0#epoch1/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#1",
                "hdfs-17960/nn0#epoch0/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#1",
                "hdfs-17960/nn0#epoch1/region/REGION.other#1",
                "hdfs-17960/nn0#epoch1/region/REGION.9492ec77-0f65-"
                        + "34ba-a3af-14753ac7347d#2",
        };
        for (String other : elsewhere) {
            assertFalse(other, planned.matches(address(other)));
        }

        // An epoch of one node is a different occurrence, and says so: the
        // 17960 flip replay threw inside the workload before it restarted the
        // NameNode, so every activation it offered was epoch 0 while the plan
        // addressed epoch 1.
        OccurrenceAddress epoch0 = address(elsewhere[1]);
        assertFalse(planned.sameLifecycle(epoch0));
        assertEquals("occurrence ran in epoch 0 of hdfs-17960/nn0, not "
                + "epoch 1", planned.describe(epoch0));

        String[] unreadable = {"", "nn0#epoch1/region/REGION.1",
                "nn0#epoch1/region/REGION.1#0", "nn0#epoch1/region/REGION.1#x"};
        for (String half : unreadable) {
            assertFalse(half, address(half).isNamed());
        }
        assertFalse(address(PLANNED).matches(OccurrenceAddress.NONE));
        assertFalse(OccurrenceAddress.NONE.matches(address(PLANNED)));
    }

    /**
     * The counting bucket is the address without its ordinal.
     *
     * <p>Including the request family, and excluding that request's own
     * ordinal: two concurrent requests are two populations, while two
     * rounds of ONE family are one, because a replay whose counter ran
     * further than the recording's is still at the same occurrence.</p>
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
        assertEquals("node, region, root -- three parts", 3,
                first.split("\n", -1).length);
        assertFalse("the request key is not in the bucket",
                first.contains("/request/"));
        assertFalse("two epochs are two buckets", first.equals(address(
                "hdfs-17960/nn0#epoch0/region/REGION.9492ec77-0f65-34ba-"
                        + "a3af-14753ac7347d#1").counterScope(root)));

        // The request an activation was reached under partitions nothing:
        // two activations of one region on one node and epoch are one
        // population however each arrived, and the k inside it is what the
        // control lineage will refine (IDENTITY-V2), never a header.
        String region = "hdfs-17899/nn0#epoch0/region/REGION.2392e4b7";
        String heartbeat = region
                + "@hdfs-17899/target-dn#epoch0/heartbeat#1";
        String refresh = region + "@hdfs-17899/sps#epoch0/refresh#1";
        assertEquals("two requests are one bucket",
                address(heartbeat).counterScope(root),
                address(refresh).counterScope(root));
        assertEquals("and the retired family spelling names the occurrence"
                        + " it always named",
                region + "#1", address(heartbeat).render());
        assertTrue(address(heartbeat).matches(address(region + "#1")));
    }
}
