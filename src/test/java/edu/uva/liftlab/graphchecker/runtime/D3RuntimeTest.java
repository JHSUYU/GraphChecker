package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;
import edu.uva.liftlab.graphchecker.runtime.d3.D3Runtime;
import edu.uva.liftlab.graphchecker.runtime.d3.Identity;
import edu.uva.liftlab.graphchecker.runtime.d3.Interactions;
import edu.uva.liftlab.graphchecker.runtime.d3.Lineage;
import edu.uva.liftlab.graphchecker.runtime.d3.OccurrenceMinterV2;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The runtime half of Design 3: the lineage an activation is addressed by,
 * and the rows one session publishes.
 */
public class D3RuntimeTest {
    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs-17899/nn0", 0);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        D3Runtime.resetForTests();
    }

    @After
    public void clear() {
        RuntimeTraceContext.resetForTests();
        D3Runtime.resetForTests();
    }

    /**
     * A scope reaches the work, not the thread: a thread started inside a
     * request and a task submitted to a pool created before it both carry
     * the lineage they were made in.
     */
    @Test
    public void aCarriedScopeReachesTheThreadThatRunsTheWork()
            throws Exception {
        Object anchor = new Object();
        RuntimeTraceContext.registerSource(anchor, NN);
        long request = RuntimeTraceContext.beginRequest(NN, "balance-block");
        assertEquals("CLIENT@balance-block#1", Lineage.path());

        // The IPC Server.Call queue: captured at enqueue on this thread,
        // restored at dequeue on a handler that never saw the request.
        final Object carried = RuntimeTraceContext.captureScope();
        final AtomicReference<String> onHandler = new AtomicReference<>("");
        Thread handler = poolThreadCreatedOutsideAnyScope(new Runnable() {
            @Override
            public void run() {
                long scope = RuntimeTraceContext.enterCarriedScope(carried,
                        "IPC_HANDLER", "balance-block");
                onHandler.set(Lineage.path());
                RuntimeTraceContext.exitCarriedScope(scope);
            }
        });
        handler.start();
        handler.join();
        assertEquals("CLIENT@balance-block#1/IPC_HANDLER@balance-block#1",
                onHandler.get());

        // An executor submission: the same carry, through the seed the
        // recorder captures at Thread.start and at submit(task).
        final Object task = new Object();
        RuntimeTraceContext.captureAsync(task);
        final AtomicReference<String> onWorker = new AtomicReference<>("");
        Thread worker = poolThreadCreatedOutsideAnyScope(new Runnable() {
            @Override
            public void run() {
                RuntimeTraceContext.View entered =
                        RuntimeTraceContext.enterRoot(task);
                onWorker.set(Lineage.path());
                RuntimeTraceContext.exitRoot(entered.spanId);
            }
        });
        worker.start();
        worker.join();
        assertEquals("CLIENT@balance-block#1/EXECUTOR_TASK#1",
                onWorker.get());
        RuntimeTraceContext.endRequest(request);
        assertEquals("", Lineage.path());
    }

    /**
     * A daemon tick is a root of its own: the NameNode's key rotation is
     * addressed by its role and the k-th tick of the window, where before
     * it was addressed by nothing at all.
     */
    @Test
    public void aDaemonTickIsAddressedByItsRoleAndItsWindowLocalK() {
        Object anchor = new Object();
        RuntimeTraceContext.registerSource(anchor, NN);
        List<OccurrenceAddress> addresses = new ArrayList<>();
        for (int tick = 0; tick < 2; tick++) {
            long token = CausynthTraceRecorder.beginDaemonTick(anchor,
                    "HEARTBEAT_TICK");
            addresses.add(OccurrenceMinterV2.mint("hdfs-17899/nn0#epoch0",
                    "REGION.aaa1cfd7",
                    CausalContext.of(Role.HEARTBEAT_TICK,
                            Lineage.rootWindowIndex()),
                    ExecutionIndex.empty()));
            CausynthTraceRecorder.endDaemonTick(token);
        }
        assertEquals("Root:HEARTBEAT_TICK#1",
                addresses.get(0).context().render());
        assertEquals("Root:HEARTBEAT_TICK#2",
                addresses.get(1).context().render());
        // Two ticks, two identities: the window index is the tick's own
        // ordinal, which is inherent to the role.
        assertFalse(addresses.get(0).id().equals(addresses.get(1).id()));

        // An unattributable scope degrades rather than disappearing.
        OccurrenceAddress lost = OccurrenceMinterV2.degraded(
                "hdfs-17899/nn0#epoch0", Role.KEY_MANAGER_TICK, "XCH.port");
        assertTrue(lost.lineageLost());
        assertEquals("ROLE.KEY_MANAGER_TICK", lost.regionId());
        assertNull(OccurrenceMinterV2.mint("", "REGION.aaa1cfd7",
                CausalContext.of(Role.UNKNOWN), ExecutionIndex.empty()));
        executionIndexIsStableUnderUnrelatedCalls();
    }

    /**
     * The entry rule: a delivery with no selected region still mints, and
     * the row pairs it to the producer the run staged the value from.
     */
    @Test
    public void anUnselectedAttachMintsAndPairsToItsExportByHandle()
            throws Exception {
        D3Runtime.configure(sessionFile());
        OccurrenceAddress producer = OccurrenceMinterV2.mint(
                "hdfs-17899/nn0#epoch0", "REGION.2392e4b7",
                CausalContext.of(Role.HEARTBEAT_TICK, 3),
                ExecutionIndex.parse("PBHelper.convert()#u2@0"));
        Endpoint exported = D3Runtime.exported(producer, 61L,
                "XCH.resp.block-key-id", 4242L, "hadoop-ipc-7", 0, null, "J",
                "119981");
        assertNotNull(exported);

        OccurrenceAddress consumer = D3Runtime.degraded(
                "hdfs-17899/target-dn#epoch0", "XCH.resp.block-key-id");
        assertTrue(consumer.lineageLost());
        Endpoint attached = D3Runtime.attached(consumer, 62L,
                "XCH.resp.block-key-id", 4242L, "hadoop-ipc-7", 0,
                "HOFF.5e10236f", "J", "119981", false, "");
        D3Runtime.closeSession();

        List<AttachRow> rows = RowCodec.readAll(
                session().attaches(), RowCodec::readAttach);
        assertEquals(1, rows.size());
        AttachRow row = rows.get(0);
        assertEquals(attached, row.endpoint());
        assertEquals(exported, row.producer());
        assertTrue(row.interaction().producerDegraded() == false);
        assertTrue(row.endpoint().occurrence().lineageLost());
        // Pairing is the run's own evidence: another port's delivery on the
        // same correlation takes no producer from this one.
        assertNull(Interactions.producer("XCH.resp.other", 0L, ""));
    }

    /** Every row kind round-trips through the codec it is written with. */
    @Test
    public void theSessionRoundTripsEveryRowKind() throws Exception {
        D3Runtime.configure(sessionFile());
        OccurrenceAddress occurrence = OccurrenceMinterV2.mint(
                "hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
        Endpoint endpoint = D3Runtime.nextEndpoint(occurrence, "XCH.port", 0);
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_exp", "M_J_serial");

        D3Runtime.decision(occurrence, 12L, "Klass.m()#u8", 1, true,
                expression);
        D3Runtime.exported(occurrence, 4L, "XCH.port", 7L, "c1", 0,
                expression, "J", "1");
        D3Runtime.attachedAt(endpoint, 9L, "XCH.port", 7L, "c1", "v_H", "J",
                "1", true, "2");
        LocationId location = LocationId.of(LocationKind.INSTANCE, "22", "24");
        D3Runtime.write(occurrence, 10L, "L#w#0:WRITE", location, 125L,
                expression, "J");
        D3Runtime.read(occurrence, 14L, "L#r#0:READ", location, 125L, "s",
                "J", "9");
        D3Runtime.rootMint(occurrence, 11L, "HDFS.BLOCK_KEY.SERIAL_NO",
                "M_I_1", RootKind.INTEGRAL, "3", "3", "6", true);
        D3Runtime.target(occurrence, 15L, "Klass.m()#u8", expression, true,
                true, true);
        D3Runtime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, "s", "d");
        // A declared region input is a READ of the location it stands for,
        // spelled the way the write log spells it, so the placeholder joins
        // the write above rather than naming a second location nobody wrote.
        placeholder(occurrence, placeholderRow("a", vmRead(125L)), "M_I_placeholder",
                Collections.<String, String[]>emptyMap());
        placeholder(occurrence, placeholderRow("b", null), "M_I_unversioned",
                Collections.<String, String[]>emptyMap());
        // The mint's own shadow store is not a write, and the row still
        // states the location and version the VM observed for the read.
        placeholder(occurrence, placeholderRow("c", null), "M_I_installed",
                Collections.singletonMap("M_I_installed",
                        new String[]{"INSTANCE_FIELD/22#24", "125"}));
        D3Runtime.closeSession();

        SessionDir dir = session();
        List<DecisionRow> decisions = RowCodec.readAll(dir.decisions(),
                RowCodec::readDecision);
        assertEquals(1, decisions.size());
        assertEquals(occurrence, decisions.get(0).occurrence());
        assertTrue(decisions.get(0).term().startsWith("EXPR."));
        List<ExportRow> exports = RowCodec.readAll(dir.exports(),
                RowCodec::readExport);
        assertEquals(1, exports.size());
        assertEquals(7L, exports.get(0).handle());
        assertEquals(4L, exports.get(0).seq());
        assertEquals("J", exports.get(0).javaType());
        List<AttachRow> attaches = RowCodec.readAll(dir.attaches(),
                RowCodec::readAttach);
        assertTrue(attaches.get(0).answered());
        assertEquals("2", attaches.get(0).answeredValue());
        List<WriteRow> writes = RowCodec.readAll(dir.writes(),
                RowCodec::readWrite);
        assertEquals(125L, writes.get(0).version());
        assertEquals(10L, writes.get(0).seq());
        List<ReadRow> reads = RowCodec.readAll(dir.reads(),
                RowCodec::readRead);
        assertEquals(125L, reads.get(0).observedVersion());
        assertEquals(14L, reads.get(0).seq());
        assertEquals("the placeholder reads the location the write wrote",
                writes.get(0).location(), reads.get(1).location());
        assertEquals("at the version the write states",
                writes.get(0).version(), reads.get(1).observedVersion());
        assertEquals("M_I_placeholder", reads.get(1).symbol());
        // No version from the VM: the row pins the plain decimal it read,
        // and never states neither.
        assertEquals(ReadRow.UNKNOWN_VERSION, reads.get(2).observedVersion());
        assertEquals("2", reads.get(2).concreteValue());
        assertEquals(LocationId.of(LocationKind.INSTANCE,
                        "java.util.concurrent.atomic.AtomicInteger", "value"),
                reads.get(2).location());
        // The mint is not a write -- no WriteRow states its version -- but
        // the row names the VM's location and the version the read saw, so
        // a term that spells that read finds this symbol there.
        assertEquals(writes.get(0).location(), reads.get(3).location());
        assertEquals(125L, reads.get(3).observedVersion());
        assertEquals("2", reads.get(3).concreteValue());
        List<RootMintRow> roots = RowCodec.readAll(dir.roots(),
                RowCodec::readRootMint);
        assertEquals(RootKind.INTEGRAL, roots.get(0).kind());
        assertEquals(11L, roots.get(0).seq());
        assertFalse(roots.get(0).pinned());
        // The kind is read off the declaration: a configured source states
        // no javaType of its own and carries it on the symbol it minted, so
        // a declared boolean root is a MARKER and not an INTEGRAL with a
        // range of two.
        assertEquals(RootKind.MARKER, kindOf(booleanConfiguredSourceRow()));
        assertEquals(RootKind.INTEGRAL, kindOf(placeholderRow("d", null)));
        List<TargetRow> targets = RowCodec.readAll(dir.targets(),
                RowCodec::readTarget);
        assertTrue(targets.get(0).observedFatal());
        List<GapRow> gaps = RowCodec.readAll(dir.gaps(), RowCodec::readGap);
        assertTrue(gaps.get(0).blocking());
        // The expressions the refs name are in the session's own table.
        assertTrue(Files.exists(dir.expressions()));
        assertTrue(RowCodec.readExpressions(dir.expressions())
                .refs().contains(exports.get(0).expressionRef()));
    }

    /** One manual mint row, as {@code recordManualSymbolization} writes it. */
    private static JsonObject placeholderRow(String port, JsonObject read) {
        JsonObject row = new JsonObject();
        row.addProperty("portId", "REGION.f0132fca.in." + port);
        row.addProperty("occurrenceId", "hdfs-17960/nn0#epoch1/region/"
                + "REGION.f0132fca#1");
        row.addProperty("rawSymbol", read == null
                ? "M_I_unversioned" : "M_I_placeholder");
        row.addProperty("javaType", "int");
        row.addProperty("fieldSignature",
                "<java.util.concurrent.atomic.AtomicInteger: int value>");
        row.addProperty("observedValue", "2");
        row.addProperty("recordedValue", "2");
        row.addProperty("eventSeq", 16L);
        if (read != null) row.add("expression", read);
        return row;
    }

    /** The VM's read of a tracked location, as it spells one. */
    private static JsonObject vmRead(long version) {
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "INSTANCE_FIELD");
        location.addProperty("ownerSymRid", 22);
        location.addProperty("slot", 24);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty("_exp", "M_I_placeholder");
        read.addProperty("_java_type", "I");
        read.add("location", location);
        read.addProperty("observedVersion", version);
        return read;
    }

    /** A configured source mints through the VM's label and states no type. */
    private static JsonObject booleanConfiguredSourceRow() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "Z");
        symbol.addProperty("_exp", "M_Z_field_SRC.50c885b3_a/Manager");
        JsonObject row = new JsonObject();
        row.addProperty("sourceId", "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED");
        row.addProperty("recordedValue", "true");
        row.add("expression", symbol);
        return row;
    }

    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    java.util.Map<String, String[]> installed)
            throws Exception {
        java.lang.reflect.Method publish = D3RowPublication.class
                .getDeclaredMethod("placeholder", OccurrenceAddress.class,
                        JsonObject.class, String.class, java.util.Map.class);
        publish.setAccessible(true);
        publish.invoke(null, occurrence, row, symbol, installed);
    }

    private static RootKind kindOf(JsonObject row) throws Exception {
        java.lang.reflect.Method kind = D3RowPublication.class
                .getDeclaredMethod("kindOf", JsonObject.class);
        kind.setAccessible(true);
        return (RootKind) kind.invoke(null, row);
    }

    /**
     * The anchor's phi is published in the FATAL polarity whichever arm the
     * run took, so no reader downstream negates it a second time.
     */
    @Test
    public void phiIsPublishedInTheFatalPolarityForBothObservedArms()
            throws Exception {
        D3Runtime.configure(sessionFile());
        OccurrenceAddress occurrence = OccurrenceMinterV2.mint(
                "hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.addProperty("_exp", "allKeys.get(id) == null");

        // The run that took the fatal arm, and the run that took the
        // healthy one, state the same predicate about the same anchor.
        D3Runtime.target(occurrence, 8L, "retrieveDataEncryptionKey#u8",
                condition, true, true, true);
        D3Runtime.target(occurrence, 9L, "retrieveDataEncryptionKey#u8",
                condition, false, false, true);
        D3Runtime.closeSession();

        List<TargetRow> rows = RowCodec.readAll(session().targets(),
                RowCodec::readTarget);
        assertEquals(2, rows.size());
        String ref = rows.get(0).phiTerm();
        assertTrue(ref.startsWith("EXPR."));
        assertTrue(rows.get(0).observedFatal());
        assertEquals("(not " + ref + ")", rows.get(1).phiTerm());
        assertFalse(rows.get(1).observedFatal());
    }

    /**
     * The execution index, and why it is not an ordinal.
     *
     * <p>Folded into the daemon-tick case because it is the same question:
     * an identity that moves when an unrelated call is inserted elsewhere
     * is not an identity.</p>
     */
    private void executionIndexIsStableUnderUnrelatedCalls() {
        Identity.resetForTests();
        Identity.scopeStart();
        Identity.enterCall("Caller.run()#u3");
        Identity.enterCall("Caller.step()#u7");
        ExecutionIndex inner = Identity.atScope();
        assertEquals("Caller.run()#u3@0/Caller.step()#u7@0", inner.render());

        // An unrelated call, entered and left, moves nothing.
        Identity.enterCall("Other.helper()#u1");
        Identity.exitCall();
        assertEquals(inner, Identity.atScope());

        // Re-entering one site under one frame IS the next iteration --
        // the rule that makes a loop body's turns distinct, computed the
        // same way in the recording and in the replay.
        Identity.enterCall("Caller.body()#u9");
        Identity.exitCall();
        Identity.enterCall("Caller.body()#u9");
        assertEquals("Caller.run()#u3@0/Caller.step()#u7@0"
                + "/Caller.body()#u9@1", Identity.atScope().render());

        // A region entry re-bases the index: an endpoint inside it is
        // addressed from the region, not from the thread's whole stack.
        ExecutionIndex atEntry = Identity.regionEnter();
        assertEquals(3, atEntry.frames().size());
        assertTrue(Identity.siteIndex().isEmpty());
        Identity.enterCall("Region.port()#u2");
        assertEquals("Region.port()#u2@0", Identity.siteIndex().render());

        // The three causal contexts, and the one that is not an ordinal.
        assertEquals("Root:HEARTBEAT_TICK#4", Identity.context("", "",
                Role.HEARTBEAT_TICK, 4).render());
        assertEquals("Anchor:abc123@HADOOP_IPC#heartbeat",
                Identity.context("abc123", "HADOOP_IPC#heartbeat",
                        Role.IPC_HANDLER, 2).render());
        assertEquals("Lost:DATA_XCEIVER",
                Identity.context("", "", Role.DATA_XCEIVER, 0).render());
    }

    /** A thread a pool created before any scope existed. */
    private static Thread poolThreadCreatedOutsideAnyScope(Runnable work) {
        final AtomicReference<Thread> created = new AtomicReference<>();
        Thread factory = new Thread(new Runnable() {
            @Override
            public void run() {
                created.set(new Thread(work));
            }
        });
        factory.start();
        try {
            factory.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        return created.get();
    }

    private Path sessionFile() throws Exception {
        Path results = iteration.getRoot().toPath()
                .resolve("iteration-0000").resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        System.setProperty(D3Runtime.SESSION_PROPERTY, "seed");
        return results;
    }

    private SessionDir session() {
        return SessionDir.of(iteration.getRoot().toPath()
                .resolve("iteration-0000"), D3Runtime.sessionId());
    }

}
