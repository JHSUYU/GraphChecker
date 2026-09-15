package edu.uva.liftlab.graphchecker.d3.contract;

import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.file.Path;
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
 * what an occurrence is called, what makes two occurrences the same one across
 * replays, what a case declaration selects, and what a row looks like on disk.
 */
public class D3ContractTest {
    private static final NodeId DN0 = NodeId.of("hdfs-17897/dn0", 0);
    private static final NodeId NN0 = NodeId.of("hdfs-17897/nn0", 0);
    private static final String REGION =
            "REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de";
    private static final String RPC =
            "ClientNamenodeProtocol#getBlockKeys";
    private static final String PRODUCER_ID = "9f2c1a3b4c5d6e7f";
    private static final String PORT = "XCH.53092d3e.resp.block-key-id";
    private static final String BLOCK_KEY =
            "Lorg/apache/hadoop/hdfs/security/token/block/BlockKey;";

    /** The three frames from the scope root to the region entry. */
    private static final String RUN = "o.a.h.h.s.d.DataXceiver#run#12";
    private static final String CHECKSUM =
            "o.a.h.h.s.d.DataXceiver#blockChecksum#48";
    private static final String COMPUTE =
            "o.a.h.h.s.d.BlockChecksumHelper#compute#7";

    /** A case declaration naming the request that reached the region. */
    private static final String V1_WITH_API =
            "hdfs-17897/dn0#epoch0/region/" + REGION
                    + "@hdfs-17897/client#epoch0/striped-file-checksum#1";
    /** A case declaration under no request at all. */
    private static final String V1_BARE =
            "hdfs-17899/dn0#epoch0/region/" + REGION + "#2";
    private static final String DECLARED_API =
            "hdfs-17897/client#epoch0/striped-file-checksum";

    @Rule
    public TemporaryFolder iteration = new TemporaryFolder();

    @Test
    public void rendersAndParsesEveryCausalContextAndIndex() {
        OccurrenceAddress anchored = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC),
                index(frame(RUN, 0), frame(CHECKSUM, 2), frame(COMPUTE, 0)));
        assertEquals(DN0.render() + "/region/" + REGION
                        + "/ctx:Anchor:" + PRODUCER_ID + "@" + RPC
                        + "/idx:" + RUN + "@0/" + CHECKSUM + "@2/"
                        + COMPUTE + "@0",
                anchored.render());
        assertEquals(anchored, OccurrenceAddress.parse(anchored.render()));
        assertEquals(anchored.id(),
                OccurrenceAddress.parse(anchored.render()).id());
        assertEquals(16, anchored.id().length());
        assertFalse(anchored.lineageLost());
        assertEquals(3, anchored.index().depth());

        // A daemon tick has no incoming message, only its role and the k-th
        // tick of that role inside the window.
        OccurrenceAddress tick = OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.KEY_MANAGER_TICK, 3),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
        assertEquals(NN0.render() + "/region/REGION.a1b2"
                        + "/ctx:Root:KEY_MANAGER_TICK#3"
                        + "/idx:o.a.h.h.s.b.KeyManager#run#9@0",
                tick.render());
        assertEquals(tick, OccurrenceAddress.parse(tick.render()));

        // A scope nobody could attribute degrades to its role and says so in
        // the id itself, rather than in a flag beside it.
        OccurrenceAddress lost = OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.UNKNOWN), ExecutionIndex.empty());
        assertEquals(NN0.render()
                + "/region/REGION.a1b2/ctx:Lost:UNKNOWN/idx:", lost.render());
        assertEquals(lost, OccurrenceAddress.parse(lost.render()));
        assertTrue(lost.lineageLost());
        assertEquals(16, ExecutionIndex.empty().hash().length());
        assertEquals(anchored.index(),
                ExecutionIndex.parse(anchored.index().render()));
    }

    @Test
    public void theSameControlPathIsTheSameOccurrence() {
        List<Frame> path = Arrays.asList(frame(RUN, 0), frame(CHECKSUM, 2),
                frame(COMPUTE, 0));
        CausalContext started = CausalContext.of(PRODUCER_ID, RPC);
        OccurrenceAddress recorded =
                OccurrenceAddress.of(DN0, REGION, started,
                        ExecutionIndex.of(path));
        // The replay ran an unrelated extra invocation elsewhere: nothing on
        // the path to the region moved, so it is the same occurrence -- which
        // is the whole reason the index replaced the k-th-activation ordinal.
        OccurrenceAddress replayed =
                OccurrenceAddress.of(DN0, REGION, started,
                        ExecutionIndex.of(Arrays.asList(frame(RUN, 0),
                                frame(CHECKSUM, 2), frame(COMPUTE, 0))));
        assertEquals(recorded, replayed);
        assertEquals(recorded.id(), replayed.id());
        // One more turn of a loop ON the path is a different occurrence, and
        // so is the same path reached for another reason.
        assertNotEquals(recorded.id(), OccurrenceAddress.of(DN0, REGION,
                started, index(frame(RUN, 0), frame(CHECKSUM, 3),
                        frame(COMPUTE, 0))).id());
        assertNotEquals(recorded.id(), OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.CLIENT, 1),
                ExecutionIndex.of(path)).id());

        // Same port, same consumer: only the producer endpoint tells two
        // deliveries apart, so only the interaction is a usable family key.
        ExecutionIndex site = index(frame("o.a.h.h.p.PBHelper#convert#31", 0));
        Endpoint attach = Endpoint.of(recorded, PORT, site, 0);
        Endpoint first = Endpoint.of(tick(1), PORT, site, 0);
        Endpoint second = Endpoint.of(tick(2), PORT, site, 0);
        Endpoint retried = Endpoint.of(tick(1), PORT, site, 1);
        assertNotEquals(first.id(), second.id());
        assertNotEquals(first.id(), retried.id());
        assertNotEquals(first.id(), Endpoint.of(tick(1), PORT,
                index(frame("o.a.h.h.p.PBHelper#convert#31", 1)), 0).id());
        Interaction delivered = Interaction.of(InteractionKind.WIRE, first,
                attach);
        assertNotEquals(delivered.id(), Interaction.of(InteractionKind.WIRE,
                second, attach).id());
        assertNotEquals(delivered.id(), Interaction.of(InteractionKind.STATE,
                first, attach).id());
        assertFalse(delivered.producerDegraded());
        assertTrue(Interaction.of(InteractionKind.WIRE,
                Endpoint.of(OccurrenceAddress.of(NN0, "REGION.a1b2",
                        CausalContext.of(Role.UNKNOWN), site), PORT, site, 0),
                attach).producerDegraded());

        // Memory indexing: an object is named by the endpoint that allocated
        // it, so two turns of the allocating loop are two objects.
        String allocates = Endpoint.allocationSite("o.a.h.h.s.t.b.BlockKey",
                "generate", 18, false);
        Endpoint allocation = Endpoint.of(tick(1), allocates,
                index(frame("o.a.h.h.s.b.KeyManager#updateKeys#22", 1)), 0);
        LocationId expiry = LocationId.allocated(allocation,
                LocationKind.INSTANCE, "expiryDate");
        assertEquals(allocation.id(), expiry.owner());
        assertFalse(expiry.preWindow());
        assertNotEquals(expiry, LocationId.allocated(Endpoint.of(tick(1),
                allocates,
                index(frame("o.a.h.h.s.b.KeyManager#updateKeys#22", 2)), 0),
                LocationKind.INSTANCE, "expiryDate"));
        assertTrue(LocationId.of(LocationKind.INSTANCE,
                LocationId.preWindowOwner("o.a.h.h.s.t.b.BlockKey", 2),
                "expiryDate").preWindow());
    }

    @Test
    public void selectorsReadTheV1CaseDeclarations() {
        Selector declared = OccurrenceAddress.parseSelector(V1_WITH_API);
        assertEquals(DN0, declared.node());
        assertEquals(REGION, declared.regionId());
        assertEquals(DECLARED_API, declared.api());
        assertEquals(1, declared.k());
        assertEquals(V1_WITH_API, declared.render());
        Selector elsewhere = OccurrenceAddress.parseSelector(V1_BARE);
        assertEquals(NodeId.of("hdfs-17899/dn0", 0), elsewhere.node());
        assertEquals(REGION, elsewhere.regionId());
        assertNull(elsewhere.api());
        assertEquals(2, elsewhere.k());

        OccurrenceAddress anchored = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC), index(frame(RUN, 0)));
        // The same region on another component is another case: the node the
        // declaration names is part of what selects.
        assertFalse(elsewhere.matches(anchored, null));
        // Region only, on this component: every occurrence of that region is a
        // candidate, and k among them is the scheduler's business.
        Selector here = OccurrenceAddress.parseSelector(
                DN0.render() + "/region/" + REGION + "#2");
        assertTrue(here.matches(anchored, null));
        assertTrue(declared.matches(anchored, DECLARED_API));
        assertFalse(declared.matches(anchored, "hdfs-17897/client#epoch0/x"));
        assertFalse(here.matches(OccurrenceAddress.of(DN0, "REGION.other",
                CausalContext.of(PRODUCER_ID, RPC), index(frame(RUN, 0))),
                null));
        // A selector that names an api matches nothing no message started.
        assertFalse(declared.matches(tick(1), DECLARED_API));
        // A declaration with no component selects on every component, and
        // round-trips through its own rendering.
        Selector anywhere = Selector.of(REGION, null, 1, null);
        assertTrue(anywhere.matches(anchored, null));
        assertEquals(anywhere, OccurrenceAddress.parseSelector(
                anywhere.render()));
    }

    @Test
    public void everyRowKindSurvivesItsFileInTheSessionLayout()
            throws IOException {
        Path root = iteration.getRoot().toPath();
        SessionDir session = SessionDir.of(root, "s-17897-1").create();
        assertEquals(root.resolve("sessions").resolve("s-17897-1")
                .resolve(SessionDir.ACTIVATIONS), session.activations());

        OccurrenceAddress anchor = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC),
                index(frame(RUN, 0), frame(CHECKSUM, 2), frame(COMPUTE, 0)));
        OccurrenceAddress producer = OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.UNKNOWN),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
        ExecutionIndex site = index(frame("o.a.h.h.p.PBHelper#convert#31", 0));
        Endpoint attach = Endpoint.of(anchor, PORT, site, 1);
        Endpoint export = Endpoint.of(producer, PORT, site, 0);
        LocationId keys = LocationId.of(LocationKind.MAP,
                "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys");
        Map<String, Long> clocks = new LinkedHashMap<>();
        clocks.put("clock_dn0", 1757700000000L);

        ActivationRow activation = ActivationRow.of("s-17897-1", anchor,
                "task-1", true, true, "DataXceiver-7#41", export);
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
                        "BlockTokenSecretManager", "addKeys", 12, true), site,
                        0), keys, 7L, "EXPR.v1.7ab1", BLOCK_KEY);
        ReadRow read = ReadRow.of("s-17897-1", 14L,
                Endpoint.of(anchor, Endpoint.stateSite(
                        "BlockTokenSecretManager", "retrieve", 61, false),
                        site, 0), keys, 7L, "state_allKeys_7", BLOCK_KEY,
                null);
        RootMintRow minted = RootMintRow.of("s-17897-1", 2L, producer,
                "SERIAL_NO", "root_serial_no", RootKind.INTEGRAL, "3", "3",
                "6", true);
        TargetRow target = TargetRow.of("s-17897-1", 15L, anchor,
                "BlockTokenSecretManager#retrieve#61", "(= key nil)", true,
                true);
        GapRow gap = GapRow.of("s-17897-1", GapKind.LINEAGE_LOST,
                GapClass.DIAGNOSTIC, export.id(),
                "the exporter ran outside any attributable scope");

        assertEquals(activation, RowCodec.readActivation(
                reline(RowCodec.writeActivation(activation))));
        // An activation a lightweight entry hook published carries no thread
        // starter, and says the region was never instrumented -- so a reader
        // that finds no decisions for it knows why.
        ActivationRow ambient = ActivationRow.of("s-17897-1", producer, "",
                false, false, "KeyManager-1#13", null);
        ActivationRow ambientBack = RowCodec.readActivation(
                reline(RowCodec.writeActivation(ambient)));
        assertEquals(ambient, ambientBack);
        assertFalse(ambientBack.instrumented());
        assertNull(ambientBack.startedBy());
        assertEquals("KeyManager-1#13", ambientBack.threadKey());
        assertEquals(export.id(), RowCodec.readActivation(
                reline(RowCodec.writeActivation(activation)))
                .startedBy().id());
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
        // The parts a reader joins on survive the line form: the context, the
        // index, the site index, the session order and the declared sorts.
        AttachRow back = RowCodec.readAttach(
                reline(RowCodec.writeAttach(attached)));
        assertEquals(attach.id(), back.endpoint().id());
        assertEquals(site, back.endpoint().siteIndex());
        assertEquals(9L, back.seq());
        assertEquals("I", back.javaType());
        assertEquals(3, back.endpoint().occurrence().index().depth());
        assertTrue(RowCodec.readRootMint(reline(RowCodec.writeRootMint(minted)))
                .occurrence().lineageLost());
        assertEquals(2L, RowCodec.readRootMint(
                reline(RowCodec.writeRootMint(minted))).seq());
        assertEquals(GapKind.SOLVER_TIMEOUT, RowCodec.readGap(reline(
                RowCodec.writeGap(GapRow.of("s-17897-1",
                        GapKind.SOLVER_TIMEOUT, GapClass.BLOCKING,
                        anchor.id(), "z3 gave no answer in 900s")))).kind());
        // A nullable field that was null comes back null, not "" or "null".
        assertNull(RowCodec.readRead(reline(RowCodec.writeRead(read)))
                .concreteValue());

        RowCodec.writeAll(session.attaches(), Arrays.asList(attached,
                AttachRow.of("s-17897-1", 11L, Endpoint.of(anchor, PORT,
                        index(frame("o.a.h.h.p.PBHelper#convert#31", 1)), 0),
                        "v_H_key_id_2", "I", "5", false, null, null,
                        "xch-53092d3e")), RowCodec::writeAttach);
        List<AttachRow> rows = RowCodec.readAll(session.attaches(),
                RowCodec::readAttach);
        assertEquals(2, rows.size());
        assertEquals(attached, rows.get(0));
        assertNull(rows.get(1).producer());
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

    private static Frame frame(String callSite, int iteration) {
        return Frame.of(callSite, iteration);
    }

    private static ExecutionIndex index(Frame... frames) {
        return ExecutionIndex.of(Arrays.asList(frames));
    }

    /** The w-th key-manager tick of the name node. */
    private static OccurrenceAddress tick(int windowIndex) {
        return OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.KEY_MANAGER_TICK, windowIndex),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
    }

    /** One row through the line form it is stored in and back. */
    private static JsonObject reline(JsonObject row) {
        return RowCodec.fromLine(RowCodec.toLine(row));
    }
}
