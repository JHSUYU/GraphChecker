package edu.uva.liftlab.graphchecker.d3.contract;

import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The Design 3 contract, checked where two modules would otherwise disagree:
 * the spelling of an address, the identity of an interaction, the shape of a
 * row on disk, and the owner of a heap location.
 */
public class D3ContractTest {
    /** A case declaration written against v1: a region under one request. */
    private static final String V1_WITH_REQUEST =
            "hdfs-17897/dn0#epoch0/region/"
                    + "REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de"
                    + "@hdfs-17897/client#epoch0/striped-file-checksum#1";
    /** A case declaration written against v1 under no request at all. */
    private static final String V1_BARE =
            "hdfs-17899/dn0#epoch0/region/"
                    + "REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de#1";

    /** The descriptor of the value the target region stores and reads. */
    private static final String BLOCK_KEY =
            "Lorg/apache/hadoop/hdfs/security/token/block/BlockKey;";

    @Rule
    public TemporaryFolder iteration = new TemporaryFolder();

    @Test
    public void readsBothV1SpellingsAndRendersEveryAddressBack() {
        OccurrenceAddress request = OccurrenceAddress.parse(V1_WITH_REQUEST);
        assertEquals(NodeId.of("hdfs-17897/dn0", 0), request.node());
        assertEquals(Collections.singletonList(LineageHop.of(Role.REQUEST,
                "hdfs-17897/client#epoch0/striped-file-checksum", 1)),
                request.lineage());
        assertEquals("REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de",
                request.regionId());
        assertEquals(1, request.k());
        assertFalse(request.lineageLost());
        // The v1 request segment becomes one REQUEST hop, and the v2 render of
        // it reads back as the same address: one address, two spellings.
        assertEquals("hdfs-17897/dn0#epoch0"
                        + "/REQUEST@hdfs-17897/client#epoch0"
                        + "/striped-file-checksum#1"
                        + "/region/REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de#1",
                request.render());
        assertEquals(request, OccurrenceAddress.parse(request.render()));

        // The bare v1 spelling IS the v2 render of an address with no lineage.
        OccurrenceAddress bare = OccurrenceAddress.parse(V1_BARE);
        assertTrue(bare.lineage().isEmpty());
        assertEquals(V1_BARE, bare.render());
        assertEquals(bare, OccurrenceAddress.parse(bare.render()));
        assertNotEquals(request.id(), bare.id());
        assertEquals(16, bare.id().length());

        // A v2 lineage of several hops, including one whose api carries the
        // slashes and hashes that make hop boundaries ambiguous.
        OccurrenceAddress deep = OccurrenceAddress.of(
                NodeId.of("hdfs-11741/dn1", 2),
                Arrays.asList(LineageHop.of(Role.BP_SERVICE_ACTOR, null, 3),
                        LineageHop.of(Role.IPC_HANDLER,
                                "hdfs-11741/nn0#epoch0/getBlockKeys", 1),
                        LineageHop.of(Role.DATA_XCEIVER, "readBlock", 7)),
                "REGION.9f2c", 4, false);
        assertEquals("hdfs-11741/dn1#epoch2/BP_SERVICE_ACTOR#3"
                        + "/IPC_HANDLER@hdfs-11741/nn0#epoch0/getBlockKeys#1"
                        + "/DATA_XCEIVER@readBlock#7/region/REGION.9f2c#4",
                deep.render());
        assertEquals(deep, OccurrenceAddress.parse(deep.render()));
    }

    @Test
    public void endpointsSeparateProducersAttemptsAndTheirInteractions() {
        OccurrenceAddress consumer = OccurrenceAddress.parse(V1_BARE);
        OccurrenceAddress heartbeatOne = occurrence("hdfs-11741/nn0", 0,
                Role.HEARTBEAT_TICK, 1);
        OccurrenceAddress heartbeatTwo = occurrence("hdfs-11741/nn0", 0,
                Role.HEARTBEAT_TICK, 2);
        String port = "XCH.53092d3e.resp.block-key-id";

        Endpoint attach = Endpoint.of(consumer, port, 1, 0);
        Endpoint fromFirst = Endpoint.of(heartbeatOne, port, 1, 0);
        Endpoint fromSecond = Endpoint.of(heartbeatTwo, port, 1, 0);
        Endpoint retried = Endpoint.of(heartbeatOne, port, 1, 1);

        // Same port, same consumer k: only the producer endpoint tells the two
        // deliveries apart, so only the interaction is a usable family key.
        assertNotEquals(fromFirst.id(), fromSecond.id());
        assertNotEquals(fromFirst.id(), retried.id());
        Interaction first = Interaction.of(InteractionKind.WIRE, fromFirst,
                attach);
        Interaction second = Interaction.of(InteractionKind.WIRE, fromSecond,
                attach);
        Interaction afterRetry = Interaction.of(InteractionKind.WIRE, retried,
                attach);
        assertNotEquals(first.id(), second.id());
        assertNotEquals(first.id(), afterRetry.id());
        assertEquals(first.id(), Interaction.of(InteractionKind.WIRE,
                Endpoint.of(heartbeatOne, port, 1, 0), attach).id());
        // A STATE edge over the same two endpoints is a different edge.
        assertNotEquals(first.id(), Interaction.of(InteractionKind.STATE,
                fromFirst, attach).id());
        assertFalse(first.producerDegraded());

        // A producer the runtime could not name still names an interaction.
        OccurrenceAddress degraded = OccurrenceAddress.of(
                heartbeatOne.node(), heartbeatOne.lineage(),
                heartbeatOne.regionId(), heartbeatOne.k(), true);
        Interaction unnamed = Interaction.of(InteractionKind.WIRE,
                Endpoint.of(degraded, port, 1, 0), attach);
        assertTrue(unnamed.producerDegraded());
        assertEquals(first.id(), unnamed.id());
    }

    @Test
    public void everyRowKindSurvivesItsFileInTheSessionLayout()
            throws IOException {
        Path root = iteration.getRoot().toPath();
        SessionDir session = SessionDir.of(root, "s-17897-1").create();
        assertEquals(root.resolve("sessions").resolve("s-17897-1")
                .resolve(SessionDir.ACTIVATIONS), session.activations());

        OccurrenceAddress anchor = OccurrenceAddress.parse(V1_WITH_REQUEST);
        OccurrenceAddress producer = OccurrenceAddress.of(
                occurrence("hdfs-17897/nn0", 0, Role.KEY_MANAGER_TICK, 2)
                        .node(),
                Collections.singletonList(
                        LineageHop.of(Role.KEY_MANAGER_TICK, null, 2)),
                "REGION.a1b2", 1, true);
        Endpoint attach = Endpoint.of(anchor, "XCH.53092d3e.resp.key-id", 2, 1);
        Endpoint export = Endpoint.of(producer, "XCH.53092d3e.resp.key-id", 1,
                0);
        LocationId keys = LocationId.of(LocationKind.MAP,
                "org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager",
                "allKeys");
        Map<String, Long> clocks = new LinkedHashMap<>();
        clocks.put("clock_dn0", 1757700000000L);

        ActivationRow activation = ActivationRow.of("s-17897-1", anchor,
                "task-1", true);
        // The session's own event order: export, attach, write, decision,
        // read, anchor -- the numbers a producer's condition is cut at.
        DecisionRow decision = DecisionRow.of("s-17897-1", 12L, anchor,
                "BlockTokenSecretManager#retrieve#61", 1, false,
                "(= v_H_key_id 3)", clocks);
        ExportRow exported = ExportRow.of("s-17897-1", 4L, export,
                "EXPR.v1.9f2c", "I", 41L, "3");
        AttachRow attached = AttachRow.of("s-17897-1", 9L, attach,
                "v_H_key_id", "I", "3", true, "4", export, "xch-53092d3e");
        WriteRow written = WriteRow.of("s-17897-1", 10L,
                Endpoint.of(anchor, Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true), 1, 0),
                keys, 7L, "EXPR.v1.7ab1", BLOCK_KEY);
        ReadRow read = ReadRow.of("s-17897-1", 14L,
                Endpoint.of(anchor, Endpoint.stateSite(
                        "BlockTokenSecretManager", "retrieve", 61, false), 1,
                        0), keys, 7L, "state_allKeys_7", BLOCK_KEY, null);
        RootMintRow minted = RootMintRow.of("s-17897-1", producer, "SERIAL_NO",
                "root_serial_no", RootKind.INTEGRAL, "3", "3", "6", true);
        TargetRow target = TargetRow.of("s-17897-1", 15L, anchor,
                "BlockTokenSecretManager#retrieve#61", "(= key nil)", true,
                true);
        GapRow gap = GapRow.of("s-17897-1", GapKind.LINEAGE_LOST,
                GapClass.DIAGNOSTIC, export.id(),
                "the exporter ran outside any attributable scope");

        assertEquals(activation, RowCodec.readActivation(
                reline(RowCodec.writeActivation(activation))));
        assertEquals(decision, RowCodec.readDecision(
                reline(RowCodec.writeDecision(decision))));
        assertEquals(exported, RowCodec.readExport(
                reline(RowCodec.writeExport(exported))));
        assertEquals(attached, RowCodec.readAttach(
                reline(RowCodec.writeAttach(attached))));
        assertEquals(written, RowCodec.readWrite(
                reline(RowCodec.writeWrite(written))));
        assertEquals(read, RowCodec.readRead(
                reline(RowCodec.writeRead(read))));
        assertEquals(minted, RowCodec.readRootMint(
                reline(RowCodec.writeRootMint(minted))));
        assertEquals(target, RowCodec.readTarget(
                reline(RowCodec.writeTarget(target))));
        assertEquals(gap, RowCodec.readGap(reline(RowCodec.writeGap(gap))));
        // v1.1: the session's event order and the declared sorts survive the
        // line form -- a solver reads the sort, it does not infer one.
        assertEquals(4L,
                RowCodec.readExport(reline(RowCodec.writeExport(exported)))
                        .seq());
        assertEquals("I",
                RowCodec.readAttach(reline(RowCodec.writeAttach(attached)))
                        .javaType());
        assertEquals(BLOCK_KEY,
                RowCodec.readWrite(reline(RowCodec.writeWrite(written)))
                        .javaType());
        assertEquals(15L,
                RowCodec.readTarget(reline(RowCodec.writeTarget(target)))
                        .seq());
        assertEquals(GapKind.SOLVER_TIMEOUT, RowCodec.readGap(reline(
                RowCodec.writeGap(GapRow.of("s-17897-1",
                        GapKind.SOLVER_TIMEOUT, GapClass.BLOCKING,
                        anchor.id(), "z3 gave no answer in 900s")))).kind());
        // A nullable field that was null comes back null, not "" or "null".
        assertNull(RowCodec.readRead(reline(RowCodec.writeRead(read)))
                .concreteValue());
        // The degraded flag is evidence about the row and travels with it,
        // while the id it joins on stays the address's.
        assertTrue(RowCodec.readRootMint(reline(RowCodec.writeRootMint(minted)))
                .occurrence().lineageLost());

        RowCodec.writeAll(session.attaches(), Arrays.asList(attached,
                AttachRow.of("s-17897-1", 11L, Endpoint.of(anchor,
                        "XCH.53092d3e.resp.key-id", 3, 0), "v_H_key_id_2", "I",
                        "5", false, null, null, "xch-53092d3e")),
                RowCodec::writeAttach);
        List<AttachRow> back = RowCodec.readAll(session.attaches(),
                RowCodec::readAttach);
        assertEquals(2, back.size());
        assertEquals(attached, back.get(0));
        assertNull(back.get(1).producer());
        assertEquals(2, RowCodec.readJsonl(session.attaches()).size());
        // Reading one kind never touches another kind's file.
        assertTrue(RowCodec.readAll(session.reads(), RowCodec::readRead)
                .isEmpty());

        JsonObject expression = new JsonObject();
        expression.addProperty("op", "SYMBOL");
        expression.addProperty("name", "root_serial_no");
        Map<String, JsonObject> expressions = new LinkedHashMap<>();
        expressions.put("EXPR.v1.9f2c", expression);
        RowCodec.writeExpressions(session.expressions(),
                ExpressionTable.of(expressions));
        assertEquals(ExpressionTable.of(expressions),
                RowCodec.readExpressions(session.expressions()));
        assertEquals(Collections.singletonList(session),
                SessionDir.sessionsIn(root));
    }

    @Test
    public void aHeapLocationIsOwnedByTheEndpointThatAllocatedIt() {
        OccurrenceAddress tick = occurrence("hdfs-11741/nn0", 0,
                Role.KEY_MANAGER_TICK, 5);
        Endpoint allocation = Endpoint.of(tick, Endpoint.stateSite(
                "BlockKeyGenerator", "generateKey", 18, true), 2, 0);
        LocationId expiry = LocationId.of(LocationKind.INSTANCE,
                LocationId.heapOwner(allocation, 3), "expiryDate");

        assertEquals(allocation.id() + "#3", expiry.owner());
        assertEquals(LocationKind.INSTANCE, expiry.kind());
        // Another allocation at the same site is another object, and a static
        // field is owned by its class, not by any allocation.
        assertNotEquals(expiry, LocationId.of(LocationKind.INSTANCE,
                LocationId.heapOwner(allocation, 4), "expiryDate"));
        assertNotEquals(expiry.owner(), LocationId.of(LocationKind.STATIC,
                "BlockKeyGenerator", "expiryDate").owner());
        // The owner is an identity, so two runs of the same allocation site in
        // the same occurrence name the same object.
        assertEquals(expiry, LocationId.of(LocationKind.INSTANCE,
                LocationId.heapOwner(Endpoint.of(
                        OccurrenceAddress.parse(tick.render()),
                        allocation.site(), 2, 0), 3), "expiryDate"));
    }

    private static OccurrenceAddress occurrence(String node, int epoch,
                                                Role role, int k) {
        List<LineageHop> lineage = new ArrayList<>();
        lineage.add(LineageHop.of(role, null, k));
        return OccurrenceAddress.of(NodeId.of(node, epoch), lineage,
                "REGION.a1b2", 1, false);
    }

    /** One row through the line form it is stored in and back. */
    private static JsonObject reline(JsonObject row) {
        return RowCodec.fromLine(RowCodec.toLine(row));
    }
}
