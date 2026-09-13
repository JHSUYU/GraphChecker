package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * One fault over one request is one control fact, however many wire flows
 * the response it idles happens to carry.
 *
 * <p>A confirmed request-fault control edge names the fault that decides a
 * controlled occurrence and the request transaction that proves membership.
 * It also names {@code controlledResponseEdgeId}: the retained response
 * value edge it was minted from.  A single heartbeat response carries every
 * declared wire flow at once -- in hdfs-17899 both {@code block-key-id} and
 * {@code block-key-expiry-date} -- and the finalizer mints one control edge
 * per retained response edge.  So one fault reached one
 * {@code PBHelper.convert(BlockKeyProto)} occurrence twice, in two rows that
 * agree on the fault, the node, the request and all five ordering event
 * sequences, and differ only in which response leg they were minted from.</p>
 *
 * <p>The composer compared {@code edgeId}, which is hashed over
 * {@code controlledResponseEdgeId}, so it read those two rows as two faults
 * contending for one occurrence and refused the composition once per
 * occurrence.  On the hdfs-17899-bug3 corpus that was six refusals with one
 * declared fault root and eleven once the target-side heartbeat fault was
 * admitted as a second root -- all of them spurious, since the emitter
 * asserts the partition once from the row it holds either way and the
 * emitted SMT is byte-identical with and without the refusals.</p>
 */
public class RequestFaultControlIdentityTest {
    private static final String SOURCE_FAULT_PORT =
            "REGION.763d087e-89f1-3a45-a53b-21f4012a2fe8"
                    + ".in.6654de32-72a6-34b3-bde9-76e670f754fd";
    private static final String TARGET_FAULT_PORT =
            "REGION.763d087e-89f1-3a45-a53b-21f4012a2fe8"
                    + ".in.b2cf05e4-3c15-3fd0-b597-f2f912bb72c4";

    /**
     * The two legs of one response state one control fact.
     *
     * <p>Both rows are taken from the hdfs-17899-bug3 corpus: the
     * {@code block-key-id} leg and the {@code block-key-expiry-date} leg of
     * the same target-dn heartbeat response, both delivered into
     * {@code REGION.1f6914ec...#2}.</p>
     */
    @Test
    public void twoResponseLegsOfOneRequestAreOneFault() {
        JsonObject keyIdLeg = controlEdge(
                "CTRL.08bf68aa-a023-3ab1-ad4a-9a352d23cd63",
                "hdfs-17899/target-dn#epoch0",
                TARGET_FAULT_PORT,
                "hdfs-17899/target-dn#epoch0/request/heartbeat#1",
                "RPC.82d162d6-a4cd-3708-80f1-805d9239ae12");
        JsonObject expiryDateLeg = controlEdge(
                "CTRL.26e69352-1c1d-346b-aec4-b44b01498fb2",
                "hdfs-17899/target-dn#epoch0",
                TARGET_FAULT_PORT,
                "hdfs-17899/target-dn#epoch0/request/heartbeat#1",
                "RPC.da2b6d2a-d4bb-34d7-a8d4-134abbdffa20");

        assertNotEquals(keyIdLeg.get("edgeId"), expiryDateLeg.get("edgeId"));
        assertNotEquals(keyIdLeg.get("controlledResponseEdgeId"),
                expiryDateLeg.get("controlledResponseEdgeId"));
        assertEquals(ConcolicSmtComposer.requestFaultIdentity(keyIdLeg),
                ConcolicSmtComposer.requestFaultIdentity(expiryDateLeg));
    }

    /** Two faults on two nodes stay two faults, so the refusal survives. */
    @Test
    public void twoDistinctFaultsRemainAmbiguous() {
        JsonObject sourceSide = controlEdge("CTRL.source",
                "hdfs-17899/source-dn#epoch0", SOURCE_FAULT_PORT,
                "hdfs-17899/source-dn#epoch0/request/heartbeat#1",
                "RPC.source-response");
        JsonObject targetSide = controlEdge("CTRL.target",
                "hdfs-17899/target-dn#epoch0", TARGET_FAULT_PORT,
                "hdfs-17899/target-dn#epoch0/request/heartbeat#1",
                "RPC.target-response");

        assertNotEquals(ConcolicSmtComposer.requestFaultIdentity(sourceSide),
                ConcolicSmtComposer.requestFaultIdentity(targetSide));
    }

    /** One fault raised twice in one node is two faults, not one. */
    @Test
    public void twoRequestsOfOneNodeRemainAmbiguous() {
        JsonObject first = controlEdge("CTRL.first",
                "hdfs-17899/source-dn#epoch0", SOURCE_FAULT_PORT,
                "hdfs-17899/source-dn#epoch0/request/heartbeat#1",
                "RPC.first-response");
        JsonObject second = controlEdge("CTRL.second",
                "hdfs-17899/source-dn#epoch0", SOURCE_FAULT_PORT,
                "hdfs-17899/source-dn#epoch0/request/heartbeat#2",
                "RPC.second-response");

        assertNotEquals(ConcolicSmtComposer.requestFaultIdentity(first),
                ConcolicSmtComposer.requestFaultIdentity(second));
    }

    /**
     * The activation an occurrence ran under does not split the fault.
     *
     * <p>The controlled side is keyed on the planned address, so the
     * deciding side has to be too, or one fault replayed under two
     * activations would read as two faults.</p>
     */
    @Test
    public void theFaultActivationDoesNotSplitTheIdentity() {
        JsonObject first = controlEdge("CTRL.a1",
                "hdfs-17899/source-dn#epoch0", SOURCE_FAULT_PORT,
                "hdfs-17899/source-dn#epoch0/request/heartbeat#1",
                "RPC.a1-response");
        JsonObject second = controlEdge("CTRL.a2",
                "hdfs-17899/source-dn#epoch0", SOURCE_FAULT_PORT,
                "hdfs-17899/source-dn#epoch0/request/heartbeat#1",
                "RPC.a2-response");
        second.addProperty("fromOccurrenceId",
                second.get("fromOccurrenceId").getAsString() + "#a2");

        assertEquals(ConcolicSmtComposer.requestFaultIdentity(first),
                ConcolicSmtComposer.requestFaultIdentity(second));
    }

    /** A refused guarded read says where it happened. */
    @Test
    public void anUnnamedGuardedReadStillCarriesItsVmAddress() {
        JsonObject read = new JsonObject();
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "INSTANCE_FIELD");
        location.addProperty("ownerSymRid", 32);
        location.addProperty("slot", 32);
        read.add("location", location);
        read.addProperty("readEventId", 247);

        assertEquals("INSTANCE_FIELD/32#32#event247",
                ConcolicSmtComposer.vmReadAddress(read));
    }

    /**
     * A read that carries no address at all is still reported, as before.
     *
     * <p>Naming the site must not turn a gap into an exception: a node the
     * VM published without a location is exactly the one a reader most
     * needs to see in the ledger.</p>
     */
    @Test
    public void areadWithNoAddressIsStillNamed() {
        assertEquals("unnamed",
                ConcolicSmtComposer.vmReadAddress(new JsonObject()));
        assertEquals("unnamed", ConcolicSmtComposer.vmReadAddress(null));
    }

    /** One row exactly as the finalizer publishes the fields compared. */
    private static JsonObject controlEdge(String edgeId, String sourceKey,
                                          String faultPortId,
                                          String requestKey,
                                          String controlledResponseEdgeId) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_REQUEST_CONTROL");
        edge.addProperty("state", "CONFIRMED_REQUEST_CONTROL");
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("sourceKey", sourceKey);
        edge.addProperty("consumerSourceKey", sourceKey);
        edge.addProperty("fromOccurrenceId", sourceKey
                + "/region/REGION.763d087e-89f1-3a45-a53b-21f4012a2fe8#1");
        edge.addProperty("toOccurrenceId", sourceKey
                + "/region/REGION.1f6914ec-f8dc-3369-8f6a-dbfcccdb2762#2");
        edge.addProperty("faultPortId", faultPortId);
        edge.addProperty("symbolicName", "hadoopIpcRequestFails");
        edge.addProperty("requestKey", requestKey);
        edge.addProperty("exchangeTransaction",
                "hadoop-ipc-d0878ab5ff154a27bafaeca3c2014b3e-20");
        edge.addProperty("controlledResponseEdgeId", controlledResponseEdgeId);
        edge.addProperty("dependencyRole", "CONCRETE_STRUCTURE_CARRIER");
        return edge;
    }
}
