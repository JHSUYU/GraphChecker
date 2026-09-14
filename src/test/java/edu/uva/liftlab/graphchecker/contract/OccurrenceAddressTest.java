package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import java.util.ArrayList;
import java.util.List;
import static org.junit.Assert.fail;

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
    public void occurrenceAddressRules() throws Exception {
        anAddressRoundTripsItsOccurrenceId();
        theAddressIsItsFourParts();
        allFourPartsDecideTheMatch();
        anotherEpochOfOneNodeIsAnotherOccurrence();
        anUnnamedAddressMatchesNothing();
        theCounterScopeIsTheAddressWithoutItsOrdinal();
        anEpochlessSourceIsStillAnAddress();
        OccurrenceIdTest t0 =
                new OccurrenceIdTest();
        t0.occurrenceIdRules();
        SiteIdTest t1 =
                new SiteIdTest();
        t1.aSiteIsItsMethodAndUnitIndex();
        HandoffSideIsTheFrontierTest t2 =
                new HandoffSideIsTheFrontierTest();
        t2.handoffSideIsTheFrontierRules();
    }

    private void anAddressRoundTripsItsOccurrenceId() {
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
    private void theAddressIsItsFourParts() {
        OccurrenceAddress planned = address(PLANNED);

        assertEquals("hdfs-17960/nn0", planned.node());
        assertEquals("1", planned.epoch());
        assertEquals("hdfs-17960/nn0#epoch1", planned.sourceKey());
        assertEquals("REGION.9492ec77-0f65-34ba-a3af-14753ac7347d",
                planned.regionId());
        assertEquals(1, planned.ordinal());
    }

    /** The same four parts match; any one of them different does not. */
    private void allFourPartsDecideTheMatch() {
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
    private void anotherEpochOfOneNodeIsAnotherOccurrence() {
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
    private void anUnnamedAddressMatchesNothing() {
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
    private void theCounterScopeIsTheAddressWithoutItsOrdinal() {
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
    private void anEpochlessSourceIsStillAnAddress() {
        OccurrenceAddress plain = OccurrenceAddress.of("dn0", "REGION.1", 1);

        assertTrue(plain.isNamed());
        assertEquals("dn0", plain.node());
        assertEquals("", plain.epoch());
        assertEquals("dn0/region/REGION.1#1", plain.render());
    }

    /** OCC-1 grammar: one address, optionally the activation that ran it. */
    static final class OccurrenceIdTest {
        private static final String ADDRESS =
                "hdfs-17960/nn0#epoch1/region/REGION.3cdc7049#1";

        public void occurrenceIdRules() throws Exception {
            activationSuffixSplitsOffTheAddressAndRendersBack();
            plannedDropsTheActivationAndWithActivationRestoresOne();
        }

        private void activationSuffixSplitsOffTheAddressAndRendersBack() {
            OccurrenceId parsed = OccurrenceId.parse(ADDRESS + "#a7");

            assertEquals(ADDRESS, parsed.planned());
            assertEquals(ADDRESS + "#a7", parsed.render());
        }

        private void plannedDropsTheActivationAndWithActivationRestoresOne() {
            OccurrenceId parsed = OccurrenceId.parse(ADDRESS + "#a3");

            assertEquals(ADDRESS + "#a1",
                    parsed.withActivation(1).render());
            assertEquals(ADDRESS + "#a12",
                    OccurrenceId.parse(ADDRESS).withActivation(12).render());
        }
    }


    /** {@code <method>#u<unitIndex>}: one spelling of one bytecode site. */
    static final class SiteIdTest {
        private static final String METHOD =
                "<org.apache.hadoop.hdfs.server.namenode.FSNamesystem:"
                        + " void startFile()>";

        public void aSiteIsItsMethodAndUnitIndex() {
            assertEquals(METHOD + "#u0", SiteId.of(METHOD, 0));
            assertEquals(METHOD + "#u137", SiteId.of(METHOD, 137));
        }
    }


    /**
     * A consumer keeps the ports it attaches.
     *
     * <p>Lane VM13's shape. {@code XCH....resp.block-key-id} is declared IN on
     * the DataNode region that decodes it ({@code REGION.16ba41cf}, captureKind
     * CALL_RETURN) and OUT on the NameNode region that encodes it
     * ({@code REGION.2392e4b7}, CALL_ARGUMENT) -- so the plan is right about who
     * the consumer is. What dropped it from the consumer's execution task was a
     * filter that kept only ports named by the task's edgeBindings, whose
     * {@code fromOutputPort} / {@code toInputPort} are field-flow ports, never
     * XCH ports. The attach then had no declaration to match and was read as an
     * UNPLANNED_HANDOFF fifteen times, while the exporter was told twenty-nine
     * times that it had not reproduced a handoff an exporter never publishes.</p>
     */
    static final class HandoffSideIsTheFrontierTest {
        private static final String PORT =
                "XCH.1174244c-0000-0000-0000-6cc5895259bf.resp.block-key-id";

        /** An IN site survives a filter no field-flow edge names. */
        public void handoffSideIsTheFrontierRules() throws Exception {
            aConsumerKeepsThePortItAttaches();
            anExportIsStillSelectedByItsEdges();
        }

        private void aConsumerKeepsThePortItAttaches() {
            List<String> ports = retained(handoff(PORT, "IN"));

            assertEquals(1, ports.size());
            assertEquals(PORT, ports.get(0));
        }

        /** An OUT site is still filtered by the selected edges. */
        private void anExportIsStillSelectedByItsEdges() {
            assertTrue("no edge names it, so it is not this task's frontier",
                    retained(handoff(PORT, "OUT")).isEmpty());
        }

        /** One task row, with one declared handoff and one field-flow edge. */
        private static List<String> retained(JsonObject declared) {
            JsonObject task = new JsonObject();
            task.addProperty("taskId", "TASK.SEED.4dd307c1");
            task.addProperty("goalId", "GOAL.1");
            task.addProperty("goalKind", "REGION_PATH_CLOSURE");
            task.addProperty("regionId", "REGION.16ba41cf");
            task.addProperty("relationKey", "REL.1");
            task.addProperty("sourceKey", "hdfs-17899/target-dn#epoch0");
            task.addProperty("occurrenceId",
                    "hdfs-17899/target-dn#epoch0/region/REGION.16ba41cf#1");
            task.addProperty("rootMethod", "<a.B: void run()>");
            task.addProperty("instrumentationSelector", "sel");
            JsonObject admission = new JsonObject();
            admission.addProperty("state", "EXECUTABLE");
            task.add("admission", admission);
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "GLOBAL_INVOCATION");
            selector.addProperty("invocationOrdinal", 1);
            selector.addProperty("method", "<a.B: void run()>");
            JsonObject anchor = new JsonObject();
            anchor.addProperty("sourceKey", "hdfs-17899/target-dn#epoch0");
            anchor.addProperty("kind", "INHERITED_CONTEXT");
            selector.add("causalAnchor", anchor);
            task.add("rootSelector", selector);
            task.add("branches", new JsonArray());
            task.add("inputActions", new JsonArray());
            JsonObject loopBound = new JsonObject();
            loopBound.addProperty("schemaVersion", 1);
            task.add("loopBound", loopBound);

            JsonArray handoffs = new JsonArray();
            handoffs.add(declared);
            task.add("communicationHandoffs", handoffs);

            // One field-flow edge, as a region task carries: its ports are
            // region output/input ports, not the XCH port.
            JsonArray edges = new JsonArray();
            JsonObject edge = new JsonObject();
            edge.addProperty("schemaVersion", 3);
            edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
            edge.addProperty("fromOutputPort", "REGION.16ba41cf.out.ea1e850d");
            edge.addProperty("toInputPort", "REGION.53092d3e.in.43545de8");
            edges.add(edge);
            task.add("edgeBindings", edges);

            // The filter the task builder applies, on the row it applies it to.
            ExecutionTask.retainSelectedCommunicationHandoffs(task, edges);

            List<String> ports = new ArrayList<>();
            for (CommunicationHandoffSpec site
                    : ExecutionTask.decode(task).communicationHandoffs()) {
                ports.add(site.portId());
            }
            return ports;
        }

        private static JsonObject handoff(String portId, String side) {
            JsonObject row = new JsonObject();
            row.addProperty("portId", portId);
            row.addProperty("side", side);
            row.addProperty("direction", "RESPONSE");
            row.addProperty("captureKind",
                    "IN".equals(side) ? "CALL_RETURN" : "CALL_ARGUMENT");
            row.addProperty("definitionMethod",
                    "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                            + "org.apache.hadoop.hdfs.security.token.block."
                            + "BlockKey convert(org.apache.hadoop.hdfs.protocol."
                            + "proto.HdfsServerProtos$BlockKeyProto)>");
            row.addProperty("definitionUnitIndex", 2);
            if ("OUT".equals(side)) {
                row.addProperty("argumentIndex", 0);
                row.addProperty("declaredCallee",
                        "<org.apache.hadoop.hdfs.protocol.proto."
                                + "HdfsServerProtos$BlockKeyProto$Builder: "
                                + "Builder setKeyId(int)>");
            } else {
                row.addProperty("declaredCallee",
                        "<org.apache.hadoop.hdfs.protocol.proto."
                                + "HdfsServerProtos$BlockKeyProto: "
                                + "int getKeyId()>");
            }
            row.addProperty("javaType", "int");
            row.addProperty("handoffLeafPath", portId);
            return row;
        }
    }

}
