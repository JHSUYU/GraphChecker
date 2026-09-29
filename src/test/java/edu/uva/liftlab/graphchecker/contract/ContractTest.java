package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.Arms;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * The contract, checked where two modules would otherwise disagree:
 * what an occurrence is called, what makes two occurrences the same one across
 * replays, what a case declaration selects, and what a row looks like on disk.
 */
public class ContractTest {
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

    /** A session's expressions are logged as the DAG they are: a chain
     *  whose every node names the one below twice is 2^64 nodes as a tree (a
     *  File.getParent chain left finalize-gs a8's table unwritable).  A ref
     *  is the content's, whatever the objects and their member order. */
    @Test
    public void aSessionLogHoldsTheDagAndRefsNameContent()
            throws IOException {
        Path file = iteration.getRoot().toPath().resolve(
                SessionDir.EXPRESSIONS);
        JsonObject chain = new JsonObject();
        chain.addProperty("_type", "ConstExpr");
        chain.addProperty("_exp", "C_I_1");
        chain.addProperty("_java_type", "I");
        for (int depth = 0; depth < 64; depth++) {
            JsonObject sum = new JsonObject();
            sum.addProperty("_type", "BinaryExpression");
            sum.addProperty("_op", "+");
            sum.add("_left", chain);
            sum.add("_right", chain);
            chain = sum;
        }
        Map<String, JsonObject> expressions =
                new LinkedHashMap<String, JsonObject>();
        expressions.put("EXPR.0000000000000001", chain);
        RowCodec.writeExpressions(file, ExpressionTable.of(expressions));
        assertTrue(Files.size(file) < 64 * 1024);
        JsonObject read = RowCodec.readExpressions(file)
                .expression("EXPR.0000000000000001");
        assertSame(read.get("_left"), read.get("_right"));
        assertEquals(new ExpressionRefs().ref(chain),
                new ExpressionRefs().ref(read));

        JsonObject reordered = new JsonObject();
        reordered.addProperty("_java_type", "I");
        reordered.addProperty("_exp", "C_I_1");
        reordered.addProperty("_type", "ConstExpr");
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_exp", "C_I_1");
        constant.addProperty("_java_type", "I");
        assertEquals(new ExpressionRefs().ref(constant),
                new ExpressionRefs().ref(reordered));
        constant.addProperty("_exp", "C_I_2");
        assertNotEquals(new ExpressionRefs().ref(constant),
                new ExpressionRefs().ref(reordered));
    }

    /**
     * A VM chain is imported and judged once per node and to its end: one
     * whose nodes name the one below twice is 2^64 paths as a tree, and one
     * 100000 deep overflowed the import's recursion (the publication thread
     * was given a 512 MB stack for it) and passed the gate's depth-64 cap
     * unjudged.
     */
    @Test(timeout = 120_000L)
    public void aDeepSharedChainIsImportedAndJudgedToItsEnd()
            throws IOException {
        for (int depth : new int[]{64, 100_000}) {
            boolean doubled = depth == 64;
            // The VM's own encoding: node k names node k-1 by its id.
            JsonArray definitions = new JsonArray();
            definitions.add(vmDefinition(1, binary("!=",
                    symbol("M_Z_marker"), literal("Y_Z_0"))));
            for (int id = 2; id <= depth; id++) {
                definitions.add(vmDefinition(id, binary("==",
                        vmReference(id - 1), doubled ? vmReference(id - 1)
                                : literal("Y_Z_1"))));
            }
            JsonObject table = new JsonObject();
            table.addProperty("schemaVersion", 1);
            table.addProperty("kind", VmExpressionTable.KIND);
            table.addProperty("authority", VmExpressionTable.AUTHORITY);
            table.addProperty("sessionId", 1L);
            table.addProperty("definitionCount", depth);
            table.add("definitions", definitions);
            JsonObject envelope = new JsonObject();
            envelope.add(VmExpressionTable.FIELD, table);
            envelope.add("expression", vmReference(depth));
            JsonObject chain = new VmExpressionTable.Store()
                    .importEnvelope(envelope).getAsJsonObject("expression");
            if (doubled) assertSame(chain.get("_left"), chain.get("_right"));
            Set<String> symbols = new LinkedHashSet<>();
            Arms.symbolsIn(chain, symbols);
            assertTrue(depth + ": " + symbols, symbols.contains("M_Z_marker"));

            // True at the marker the session minted, so outcome=false is
            // the complement of what the term held.
            Rows flipped = clean();
            flipped.expressions.put("EXPR.0000000000000001", chain);
            flipped.decisions.set(0, DecisionRow.of("s-gate", 12L,
                    flipped.anchor, "Guard#u8", 1, false,
                    "EXPR.0000000000000001",
                    Collections.<String, Long>emptyMap()));
            assertInvariant(6, GapClass.BLOCKING, "field=outcome", flipped);
        }
    }

    private static JsonObject vmReference(long id) {
        JsonObject reference = new JsonObject();
        reference.addProperty("_type", VmExpressionTable.REFERENCE_TYPE);
        reference.addProperty("sessionId", 1L);
        reference.addProperty("expressionId", id);
        return reference;
    }

    private static JsonObject vmDefinition(long id, JsonObject expression) {
        JsonObject definition = vmReference(id);
        definition.addProperty("_type", VmExpressionTable.DEFINITION_TYPE);
        definition.add("expression", expression);
        return definition;
    }

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
        assertEquals(3, anchored.index().frames().size());

        // A daemon tick has no incoming message, only its role and the k-th
        // tick of that role inside the window.
        OccurrenceAddress tick = OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", 3),
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
                CausalContext.of(Role.CLIENT, "", 1),
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
        assertFalse(delivered.producer().occurrence().lineageLost());
        assertTrue(Interaction.of(InteractionKind.WIRE,
                Endpoint.of(OccurrenceAddress.of(NN0, "REGION.a1b2",
                        CausalContext.of(Role.UNKNOWN), site), PORT, site, 0),
                attach).producer().occurrence().lineageLost());

        // ONE owner spelling, the one the runtime writes: the VM's
        // symbolic rid of the object whose state this is.  A join is per
        // session, and inside one run two rids are two objects.  The
        // allocation-endpoint owner this asked for is deleted -- no main
        // code produced it, and the gate that admitted only it refused
        // every row of both corpora.
        LocationId expiry = LocationId.of(LocationKind.INSTANCE, "12",
                "expiryDate");
        assertEquals("12", expiry.owner());
        assertNotEquals(expiry, LocationId.of(LocationKind.INSTANCE, "13",
                "expiryDate"));
        assertEquals("INSTANCE 12.expiryDate", expiry.toString());
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

        // The sender its anchor names rides along, so a reader follows the
        // causal chain past the anchor.
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
                "v_H_key_id", "I", "3", true, "4", export, "xch-53092d3e",
                "HANDLE");
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
                "6", true, 0L);
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
                false, false, "KeyManager-1#13");
        ActivationRow ambientBack = RowCodec.readActivation(
                reline(RowCodec.writeActivation(ambient)));
        assertEquals(ambient, ambientBack);
        assertFalse(ambientBack.instrumented());
        assertEquals("KeyManager-1#13", ambientBack.threadKey());
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
        // A placeholder's mint version is part of the row it round-trips as.
        ReadRow placeholder = ReadRow.of("s-17897-1", 14L, read.endpoint(),
                keys, 7L, "state_allKeys_7", BLOCK_KEY, null, 9L);
        assertEquals(placeholder, RowCodec.readRead(
                reline(RowCodec.writeRead(placeholder))));
        assertFalse("a stated mint version is not the unknown one",
                placeholder.equals(read));
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
        assertEquals(3, back.endpoint().occurrence().index().frames().size());
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
                        "xch-53092d3e", "")), RowCodec::writeAttach);
        List<AttachRow> rows = RowCodec.readAll(session.attaches(),
                RowCodec::readAttach);
        assertEquals(2, rows.size());
        assertEquals(attached, rows.get(0));
        // WHICH key paired it survives the round trip, and a blank one is
        // UNSTATED rather than a third spelling: the unpaired row already
        // says so with a null producer.
        assertEquals("HANDLE", rows.get(0).pairedBy());
        assertNull(rows.get(1).pairedBy());
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

        // ---- the row contract as a GATE (RowInvariants) ----------------
        //
        // One table, one row per rule: what a recording has to state, and
        // what it is told when it does not.  This is the shape of the fix
        // 17960 needed twice -- a decision whose outcome was the complement
        // of its term's truth value, and a focused session whose expression
        // table was empty -- so each rule is checked where every row passes
        // through rather than in the stage that happened to trip over it.
        assertTrue("a recording that states everything states no violation: "
                        + names(gate(clean())),
                gate(clean()).isEmpty());
        // 1: exactly one seed session per epoch, and every row's occurrence
        // ran in its own session.
        Rows second = clean();
        second.id = "s-two";
        assertInvariant(1, GapClass.BLOCKING, "epoch/sessions",
                clean(), second);
        Rows unactivated = clean();
        unactivated.activations.clear();
        assertInvariant(1, GapClass.BLOCKING, "field=occurrence",
                unactivated);
        // 2: never neither -- a read states a version or a value.
        Rows neither = clean();
        neither.reads.set(0, ReadRow.of("s-gate", 14L, neither.readAt, keys,
                -1L, "state_allKeys_7", BLOCK_KEY, null));
        assertInvariant(2, GapClass.BLOCKING, "field=observedVersion",
                neither);
        // 3: a reference a row cites exists in its OWN session's table, and
        // no other reference spelling appears.
        Rows empty = clean();
        empty.expressions.clear();
        assertInvariant(3, GapClass.BLOCKING, "field=term", empty);
        Rows spelled = clean();
        spelled.decisions.set(0, DecisionRow.of("s-gate", 12L,
                spelled.anchor, "Guard#u8", 1, true, "EXPR.v1.9f2c", clocks));
        assertInvariant(3, GapClass.BLOCKING, "EXPR.v1.9f2c", spelled);
        // 4: one row per event; an endpoint two events share is the site
        // index's failure and is recorded, not refused.
        Rows twice = clean();
        twice.reads.add(twice.reads.get(0));
        assertInvariant(4, GapClass.BLOCKING, "field=seq/location", twice);
        Rows collided = clean();
        collided.reads.add(ReadRow.of("s-gate", 20L, collided.readAt, keys,
                7L, "state_allKeys_7", BLOCK_KEY, null));
        assertInvariant(4, GapClass.DIAGNOSTIC, "site index missing",
                collided);
        // A target row that did not reach its anchor states no event, so
        // two occurrences that both ran without reaching it are two rows;
        // two rows at one reached event are still one event twice.
        Rows unreached = clean();
        OccurrenceAddress other = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 2),
                index(frame(RUN, 0)));
        unreached.activations.add(ActivationRow.of("s-gate", other, "t",
                false, true, "DataXceiver-8#42"));
        unreached.targets.add(TargetRow.of("s-gate", 0L, unreached.anchor,
                "Guard#u8", "", false, false));
        unreached.targets.add(TargetRow.of("s-gate", 0L, other, "Guard#u8",
                "", false, false));
        assertTrue("an unreached anchor is one row per occurrence: "
                + names(gate(unreached)), noViolation(gate(unreached), 4));
        // Nor does a concrete decision: it stands after the last VM event,
        // which two occurrences can share.
        Rows decided = clean();
        decided.activations.add(ActivationRow.of("s-gate", other, "t",
                false, true, "DataXceiver-8#42"));
        decided.targets.add(TargetRow.of("s-gate",
                decided.targets.get(0).seq(), other, "Guard#u8", "", false,
                true));
        assertTrue("two occurrences deciding concretely after one event: "
                + names(gate(decided)), noViolation(gate(decided), 4));
        Rows reachedTwice = clean();
        reachedTwice.targets.add(reachedTwice.targets.get(0));
        assertInvariant(4, GapClass.BLOCKING,
                "field=occurrence/seq/anchorSiteId", reachedTwice);
        // 5: one name, one spelled sort, and a placeholder read's sort is the
        // one its own row declares.
        Rows mixed = clean();
        mixed.reads.add(ReadRow.of("s-gate", 21L, mixed.placeholderAt, keys,
                7L, "M_Z_field_" + REGION + ".in.a1", "I", "2"));
        assertInvariant(5, GapClass.BLOCKING, "field=symbol/javaType", mixed);
        // 6: outcome says whether the published term HELD.
        Rows flipped = clean();
        flipped.decisions.set(0, DecisionRow.of("s-gate", 12L,
                flipped.anchor, "Guard#u8", 1, false, "EXPR.0000000000000001",
                clocks));
        assertInvariant(6, GapClass.BLOCKING, "field=outcome", flipped);
        // 7: a version some row of the session states, and never a write
        // whose whole expression is a placeholder's own symbol.
        Rows unstated = clean();
        unstated.writes.clear();
        // and the mint states a different version, so nothing states v7
        unstated.reads.set(1, ReadRow.of("s-gate", 16L,
                unstated.placeholderAt, keys, 7L,
                "M_I_field_" + REGION + ".in.a1", "I", "2", 99L));
        assertInvariant(7, GapClass.DIAGNOSTIC, "field=observedVersion",
                unstated);
        // The mint's own store published as a write: the version the
        // placeholder minted, whatever expression the row carries.
        Rows fabricated = clean();
        fabricated.writes.add(WriteRow.of("s-gate", 11L,
                fabricated.writeAt, keys, 8L, "EXPR.0000000000000002",
                BLOCK_KEY));
        assertInvariant(7, GapClass.BLOCKING, "field=version", fabricated);
        // A legitimate copy: a later version of the cell assigned the minted
        // symbol is a write of its own, whole expression that symbol or not.
        Rows copied = clean();
        copied.writes.add(WriteRow.of("s-gate", 11L, copied.writeAt, keys,
                9L, "EXPR.0000000000000002", BLOCK_KEY));
        assertTrue("a write of another version that carries the minted "
                        + "symbol is no fabricated write: "
                        + names(gate(copied)),
                noViolation(gate(copied), 7));
        // Contract v2.4: a placeholder read states the version it mints, so
        // a version no write carries is stated all the same -- and a
        // placeholder that states none is refused, once the recording
        // publishes the field at all.
        // The mint's own version is NOT the version it observed: laneA5's
        // placeholder observed 77 and minted 177, and keying the mint by the
        // observed version refused a row whose field was right there in it.
        Rows mintStated = clean();
        mintStated.reads.set(1, ReadRow.of("s-gate", 16L,
                mintStated.placeholderAt, keys, 7L,
                "M_I_field_" + REGION + ".in.a1", "I", "2", 177L));
        mintStated.reads.add(ReadRow.of("s-gate", 17L, mintStated.readAt,
                keys, 177L, "state_allKeys_177", BLOCK_KEY, null));
        assertTrue("the mint states 177 and a later read observes it, so "
                        + "neither is unstated: " + names(gate(mintStated)),
                noViolation(gate(mintStated), 7));
        Rows unminted = clean();
        unminted.reads.set(1, ReadRow.of("s-gate", 16L,
                unminted.placeholderAt, keys, 7L,
                "M_I_field_" + REGION + ".in.a1", "I", "2"));
        assertInvariant(7, GapClass.BLOCKING, "field=mintVersion", unminted);
        // 8: a RootMintRow is published for a declared root, and its reading
        // is spelled the way its kind is read back.
        Rows undeclared = clean();
        undeclared.roots.set(0, RootMintRow.of("s-gate", 2L,
                undeclared.anchor, "CASE.MARKER", "M_Z_marker",
                RootKind.MARKER, "true", null, null, false, 0L));
        assertInvariant(8, GapClass.BLOCKING, "field=declared", undeclared);
        Rows unspelled = clean();
        unspelled.roots.set(0, RootMintRow.of("s-gate", 2L, unspelled.anchor,
                "CASE.MARKER", "M_Z_marker", RootKind.MARKER, "1", null,
                null, true, 0L));
        assertInvariant(8, GapClass.BLOCKING, "field=recordedValue",
                unspelled);
        // 9: phi is published in the FATAL polarity, so an observed fatal
        // states one and it holds at the recording's own root values.
        Rows silent = clean();
        silent.targets.set(0, TargetRow.of("s-gate", 15L, silent.anchor,
                "Guard#u8", "", true, true));
        assertInvariant(9, GapClass.BLOCKING, "field=phiTerm", silent);
        Rows concrete = clean();
        concrete.targets.set(0, TargetRow.of("s-gate", 15L, concrete.anchor,
                "Guard#u8", "", false, true));
        assertInvariant(9, GapClass.DIAGNOSTIC, "field=phiTerm", concrete);
        // 11 (R4): a root symbol without its RootMintRow.  WHICH quantities
        // are roots is a fact about the SET -- CASE.MARKER is a root because
        // some session of the epoch minted a row naming it -- and a session
        // that NAMES that root's symbol while publishing no mint row of its
        // own carries a quantity nothing of it attributes.  That is 11741
        // campaign #4: the symbol reached the expressions out of an
        // activation the run abandoned, and the composer met it as an arm it
        // could not guard.
        Rows unattributed = clean();
        unattributed.id = "s-abandoned";
        unattributed.roots.clear();
        assertInvariant(11, GapClass.BLOCKING, "CASE.MARKER",
                clean(), unattributed);
        assertEquals("one row per (session, root), naming both: "
                        + names(gate(clean(), unattributed)),
                1, stating(gate(clean(), unattributed),
                        GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING));
        // And the same corpus with the mint row present states none.
        Rows attributed = clean();
        attributed.id = "s-abandoned";
        assertEquals("a session that states the mint row is not refused: "
                        + names(gate(clean(), attributed)),
                0, stating(gate(clean(), attributed),
                        GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING));
    }

    /** How many rows of one kind and class a gate stated. */
    private static int stating(List<GapRow> gaps, GapKind kind,
                               GapClass cls) {
        int count = 0;
        for (GapRow gap : gaps) {
            if (gap.kind() == kind && gap.cls() == cls) count++;
        }
        return count;
    }

    /** No violation of that rule at all, whatever its class. */
    private static boolean noViolation(List<GapRow> gaps, int rule) {
        for (GapRow gap : gaps) {
            if (gap.detail().contains("invariant " + rule)) return false;
        }
        return true;
    }

    /** One session's rows, as a recording a table row can bend. */
    private final class Rows {
        private String id = "s-gate";

        private OccurrenceAddress anchor;
        private Endpoint readAt;
        private Endpoint writeAt;
        private Endpoint placeholderAt;
        private final List<ActivationRow> activations =
                new java.util.ArrayList<>();
        private final List<DecisionRow> decisions = new java.util.ArrayList<>();
        private final List<ReadRow> reads = new java.util.ArrayList<>();
        private final List<WriteRow> writes = new java.util.ArrayList<>();
        private final List<RootMintRow> roots = new java.util.ArrayList<>();
        private final List<TargetRow> targets = new java.util.ArrayList<>();
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<>();

        private SessionReader read(Path root) throws IOException {
            SessionDir dir = SessionDir.of(root, id).create();
            RowCodec.writeAll(dir.activations(), activations,
                    RowCodec::writeActivation);
            RowCodec.writeAll(dir.decisions(), decisions,
                    RowCodec::writeDecision);
            RowCodec.writeAll(dir.reads(), reads, RowCodec::writeRead);
            RowCodec.writeAll(dir.writes(), writes, RowCodec::writeWrite);
            RowCodec.writeAll(dir.roots(), roots, RowCodec::writeRootMint);
            RowCodec.writeAll(dir.targets(), targets, RowCodec::writeTarget);
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
            // The fixture STATES the role, as a campaign's own session
            // manifest does.
            boolean focused = false;
            for (ActivationRow activation : activations) {
                if (activation.focused()) focused = true;
            }
            RowCodec.writeManifest(dir.manifest(),
                    SessionManifest.of(id,
                            focused ? SessionManifest.Role.FOCUSED
                                    : SessionManifest.Role.SEED,
                            focused ? java.util.Collections.singletonList(
                                    "OBL." + id)
                                    : java.util.Collections
                                            .<String>emptyList()));
            return SessionReader.read(dir);
        }
    }

    /** A recording that states everything the contract asks of one. */
    private Rows clean() {
        Rows rows = new Rows();
        rows.anchor = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 1),
                index(frame(RUN, 0)));
        ExecutionIndex site = index(frame(COMPUTE, 0));
        rows.readAt = Endpoint.of(rows.anchor, Endpoint.stateSite(
                "BlockTokenSecretManager", "retrieve", 61, false), site, 0);
        rows.writeAt = Endpoint.of(rows.anchor, Endpoint.stateSite(
                "BlockTokenSecretManager", "addKeys", 12, true), site, 0);
        rows.placeholderAt = Endpoint.of(rows.anchor,
                "INSTANCE_FIELD/2#24" + RowInvariants.PLACEHOLDER + "0:READ",
                site, 0);
        rows.activations.add(ActivationRow.of("s-gate", rows.anchor, "t", false,
                true, "DataXceiver-7#41"));
        // A marker the session minted true, and a term that is true at it.
        rows.roots.add(RootMintRow.of("s-gate", 2L, rows.anchor,
                "CASE.MARKER", "M_Z_marker", RootKind.MARKER, "true", null,
                null, true, 0L));
        rows.expressions.put("EXPR.0000000000000001",
                binary("!=", symbol("M_Z_marker"), literal("Y_Z_0")));
        rows.expressions.put("EXPR.0000000000000002",
                symbol("M_I_field_" + REGION + ".in.a1"));
        rows.decisions.add(DecisionRow.of("s-gate", 12L, rows.anchor,
                "Guard#u8", 1, true, "EXPR.0000000000000001",
                Collections.<String, Long>emptyMap()));
        rows.writes.add(WriteRow.of("s-gate", 10L, rows.writeAt,
                LocationId.of(LocationKind.MAP,
                        "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys"),
                7L, "EXPR.0000000000000001", BLOCK_KEY));
        rows.reads.add(ReadRow.of("s-gate", 14L, rows.readAt,
                LocationId.of(LocationKind.MAP,
                        "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys"),
                7L, "state_allKeys_7", BLOCK_KEY, null));
        // The declared region input, as a placeholder read: the only row
        // that mints it, so a write whose whole expression IS its symbol
        // would be a value the two of them fabricated between them.
        rows.reads.add(ReadRow.of("s-gate", 16L, rows.placeholderAt,
                LocationId.of(LocationKind.MAP,
                        "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys"),
                7L, "M_I_field_" + REGION + ".in.a1", "I", "2", 8L));
        rows.targets.add(TargetRow.of("s-gate", 15L, rows.anchor, "Guard#u8",
                "EXPR.0000000000000001", true, true));
        return rows;
    }

    /** The violations one set of sessions states. */
    private List<GapRow> gate(Rows... sessions) throws IOException {
        Path root = iteration.newFolder().toPath();
        for (Rows rows : sessions) rows.read(root);
        return RowInvariants.check(SessionDir.sessionsIn(root),
                java.util.Collections.<String, List<JsonObject>>emptyMap());
    }

    /** That rule, that class, that subject -- and nothing silent. */
    private void assertInvariant(int rule, GapClass cls, String subject,
                                 Rows... sessions) throws IOException {
        List<GapRow> gaps = gate(sessions);
        for (GapRow gap : gaps) {
            if (gap.cls() != cls) continue;
            if (!gap.detail().contains("invariant " + rule)) continue;
            if (gap.subject().contains(subject)
                    || gap.detail().contains(subject)) {
                return;
            }
        }
        throw new AssertionError("invariant " + rule + " did not state " + cls
                + " over " + subject + "; it stated " + names(gaps));
    }

    private static List<String> names(List<GapRow> gaps) {
        List<String> named = new java.util.ArrayList<>();
        for (GapRow gap : gaps) {
            named.add(gap.cls() + " " + gap.subject());
        }
        return named;
    }

    private static JsonObject symbol(String name) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", name);
        return node;
    }

    private static JsonObject literal(String value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_exp", value);
        return node;
    }

    private static JsonObject binary(String op, JsonObject left,
                                     JsonObject right) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", op);
        node.add("_left", left);
        node.add("_right", right);
        return node;
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
                CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", windowIndex),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
    }

    /** One row through the line form it is stored in and back. */
    private static JsonObject reline(JsonObject row) {
        return RowCodec.fromLine(RowCodec.toLine(row));
    }
}
