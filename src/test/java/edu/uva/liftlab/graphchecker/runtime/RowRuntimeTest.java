package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.runtime.FrameJournal;
import edu.uva.liftlab.graphchecker.runtime.RowRuntime;
import edu.uva.liftlab.graphchecker.runtime.Identity;
import edu.uva.liftlab.graphchecker.runtime.Interactions;
import edu.uva.liftlab.graphchecker.runtime.Lineage;
import edu.uva.liftlab.graphchecker.runtime.Identity;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
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
 * The runtime half of the contract: the lineage an activation is addressed by,
 * and the rows one session publishes.
 */
public class RowRuntimeTest {
    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs-17899/nn0", 0);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void clear() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
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

    /** One address, by the contract constructor the runtime calls. */
    private static OccurrenceAddress address(String nodeKey, String regionId,
                                             CausalContext context,
                                             ExecutionIndex index) {
        return OccurrenceAddress.of(NodeId.parse(nodeKey), regionId, context,
                index);
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
            addresses.add(address("hdfs-17899/nn0#epoch0",
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
        OccurrenceAddress lost = Identity.roleOccurrence(
                "hdfs-17899/nn0#epoch0", Role.KEY_MANAGER_TICK);
        assertTrue(lost.lineageLost());
        assertEquals("ROLE.KEY_MANAGER_TICK", lost.regionId());
        // A node this run cannot name addresses nothing: a guessed node is
        // a wrong causal chain.
        assertNull(Identity.occurrence("", "REGION.aaa1cfd7", false));
        executionIndexIsStableUnderUnrelatedCalls();
    }

    /**
     * The entry rule: a delivery with no selected region still mints, and
     * the row pairs it to the producer the run staged the value from.
     */
    @Test
    public void anUnselectedAttachMintsAndPairsToItsExportByHandle()
            throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress producer = address(
                "hdfs-17899/nn0#epoch0", "REGION.2392e4b7",
                CausalContext.of(Role.HEARTBEAT_TICK, 3),
                ExecutionIndex.parse("PBHelper.convert()#u2@0"));
        Endpoint exported = RowRuntime.exported(producer, 61L,
                "XCH.resp.block-key-id", 4242L, "hadoop-ipc-7", 0, null, "J",
                "119981");
        assertNotNull(exported);

        OccurrenceAddress consumer = RowRuntime.degraded(
                "hdfs-17899/target-dn#epoch0", "XCH.resp.block-key-id");
        assertTrue(consumer.lineageLost());
        Endpoint attached = RowRuntime.attached(consumer, 62L,
                "XCH.resp.block-key-id", 4242L, "hadoop-ipc-7", 0,
                "HOFF.5e10236f", "J", "119981", false, "");
        RowRuntime.closeSession();

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
        RowRuntime.configure(sessionFile());
        OccurrenceAddress occurrence = address(
                "hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
        Endpoint endpoint = RowRuntime.nextEndpoint(occurrence, "XCH.port", 0);
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_exp", "M_J_serial");

        RowRuntime.decision(occurrence, 12L, "Klass.m()#u8", 1, true,
                expression);
        // hdfs-17960's marker decision: the source reads
        // `if marker == 0 goto`, the run had marker true so the jump fell
        // through, and the VM published the constraint it SATISFIED,
        // `marker != false`.  The row states the JUMP's predicate --
        // `marker == false`, the one spelling of this site that does not
        // move between arms or replays -- and outcome=false, the arm.  The
        // conjunct a consumer forms, `(not term)`, is the satisfied
        // constraint back again; the flipped replay states the same term
        // with outcome=true, which is what lets a flip be seen at all.
        RowRuntime.decision(occurrence, 13L, "SnapshotManager.delete()#u7", 1,
                false, markerJumpCondition("M_Z_marker"));
        RowRuntime.exported(occurrence, 4L, "XCH.port", 7L, "c1", 0,
                expression, "J", "1");
        RowRuntime.attachedAt(endpoint, 9L, "XCH.port", 7L, "c1", "v_H", "J",
                "1", true, "2");
        LocationId location = LocationId.of(LocationKind.INSTANCE, "22", "24");
        // The site is spelled once, by the contract's renderer, from what the
        // VM's log states about the event -- including the descriptor, so two
        // overloads of one name are two sites.
        RowRuntime.write(occurrence, 10L,
                Endpoint.stateSite("java.util.concurrent.atomic.AtomicInteger",
                        "getAndIncrement", "()I", 12, true),
                location, 125L, rmwExpression(), "",
                "Caller.body()#u9@1");
        RowRuntime.read(occurrence, 14L,
                Endpoint.stateSite("java.util.concurrent.atomic.AtomicInteger",
                        "get", "()I", 2, false),
                location, 125L, "s", "J", "9", "");
        RowRuntime.rootMint(occurrence, 11L, "HDFS.BLOCK_KEY.SERIAL_NO",
                "M_I_1", RootKind.INTEGRAL, "3", "3", "6", true);
        RowRuntime.rootMint(occurrence, 13L,
                "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED", "M_Z_marker",
                RootKind.MARKER, "true", "", "", true);
        RowRuntime.target(occurrence, 15L, "Klass.m()#u8", expression, true,
                true, true);
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, "s", "d");
        // A declared region input is a READ of the location it stands for,
        // spelled the way the write log spells it, so the placeholder joins
        // the write above rather than naming a second location nobody wrote.
        placeholder(occurrence, placeholderRow("a", vmRead(125L)), "M_I_placeholder",
                Collections.<String, String[]>emptyMap());
        placeholder(occurrence, placeholderRow("b", null), "M_I_unversioned",
                Collections.<String, String[]>emptyMap());
        // The mint symbolized the object, not the int cell: the sorts
        // disagree (L against I), so the row states neither.  A reference
        // mint for a reference cell agrees and does publish (P2l).
        placeholder(occurrence, placeholderRow("f", null),
                "P_L'org/apache/hadoop/hdfs/server/namenode/snapshot/"
                        + "Snapshot'_",
                Collections.<String, String[]>emptyMap());
        // The mint's own shadow store is not a write, so the version this
        // read OBSERVED is the last real write before it -- version 125,
        // which the WriteRow above states -- and the row is the anchor's
        // join to that writer.
        placeholder(occurrence, placeholderRow("c", null), "M_I_installed",
                Collections.singletonMap("M_I_installed",
                        new String[]{"INSTANCE_FIELD/22#28", "126", "125"}));
        // A second declared port of the SAME cell is a second read event
        // and states its own row: two calls of a declared accessor in one
        // occurrence are two values.
        placeholder(occurrence, secondPortRow(), "M_I_second",
                Collections.singletonMap("M_I_second",
                        new String[]{"INSTANCE_FIELD/22#28", "127", "125"}));
        // The SAME read event reached again -- the same mint row, from an
        // activation the read also ran inside -- states no second row.
        placeholder(occurrence, placeholderRow("c", null), "M_I_installed",
                Collections.singletonMap("M_I_installed",
                        new String[]{"INSTANCE_FIELD/22#28", "126", "125"}));
        // A mint with no write before it states -1 and pins the decimal.
        placeholder(occurrence, placeholderRow("e", null), "M_I_unwritten",
                Collections.singletonMap("M_I_unwritten",
                        new String[]{"INSTANCE_FIELD/22#32", "126", "-1"}));
        RowRuntime.closeSession();

        SessionDir dir = session();
        List<DecisionRow> decisions = RowCodec.readAll(dir.decisions(),
                RowCodec::readDecision);
        assertEquals(2, decisions.size());
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
        assertEquals("java.util.concurrent.atomic.AtomicInteger"
                        + "#getAndIncrement()I#12:WRITE",
                writes.get(0).endpoint().site());
        assertEquals("Caller.body()#u9@1",
                writes.get(0).endpoint().siteIndex().render());
        // An operator node states no type of its own; the run states the
        // operands', so an int RMW is not published as an Object.
        assertEquals("I", writes.get(0).javaType());
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
        // The mint is not a write -- no WriteRow states its version -- so
        // the row names the VM's location and the LAST REAL WRITE before
        // the mint: the placeholder read is the anchor's JOIN to the
        // occurrence that wrote the cell.
        assertEquals(LocationKind.INSTANCE, reads.get(3).location().kind());
        assertEquals(125L, reads.get(3).observedVersion());
        assertEquals("2", reads.get(3).concreteValue());
        ReadRow unwritten = null;
        for (ReadRow read : reads) {
            if ("M_I_unwritten".equals(read.symbol())) unwritten = read;
        }
        assertNotNull("the unwritten mint states a row", unwritten);
        // CONTRACT v2.4: the placeholder states the version its own mint
        // published, which is what a term's ReadFrom names, beside the last
        // real write it observed, which is the join to the writer.
        assertEquals(126L, unwritten.mintVersion());
        assertEquals(ReadRow.UNKNOWN_VERSION,
                reads.get(0).mintVersion());
        assertEquals("no write precedes the mint: -1 and the decimal",
                ReadRow.UNKNOWN_VERSION, unwritten.observedVersion());
        assertEquals("2", unwritten.concreteValue());
        assertEquals("a reference-sorted mint states no row; a second mint"
                        + " of one cell (version 127) is a second mint and"
                        + " states one; the SAME mint reached twice states"
                        + " one row, whatever occurrence or read event"
                        + " reached it",
                6, reads.size());
        List<RootMintRow> roots = RowCodec.readAll(dir.roots(),
                RowCodec::readRootMint);
        // The corpus invariant: a decision whose term is over declared root
        // symbols only holds exactly when the row says its outcome does.
        // This is what tells "the term held" apart from "the jump was
        // taken", and the two differ at every fall-through branch.
        Map<String, String> recorded = new java.util.HashMap<>();
        for (RootMintRow root : roots) {
            recorded.put(root.symbol(), root.recordedValue());
        }
        Map<String, JsonObject> table =
                RowCodec.readExpressions(dir.expressions()).expressions();
        int checked = 0;
        for (DecisionRow row : decisions) {
            Boolean held = holdsAtRoots(table.get(row.term()), recorded,
                    table);
            if (held == null) continue;
            // `outcome ? term : (not term)` is the constraint the run
            // satisfied, so a term over declared roots alone holds exactly
            // when the row's arm says it does.
            assertEquals("the conjunct of " + row.siteId() + " is satisfied",
                    held, Boolean.valueOf(row.outcome()));
            checked++;
        }
        assertEquals("one decision is over declared roots only", 1, checked);
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
        // What the read-out keeps of the VM's envelope is what a write or
        // read endpoint can be built from: the bytecode site the event stood
        // at and the activation that ran it.  The reduction used to drop
        // both and the whole read log, which is why every write endpoint
        // carried its location as a site and the empty index.
        JsonObject reduced = SharedStateCapture.reduceWriteLogForTest(
                vmEnvelopeRecord());
        JsonObject envelope = reduced.getAsJsonObject("envelope");
        JsonObject version = envelope.getAsJsonArray("versions").get(0)
                .getAsJsonObject();
        assertEquals(41L, version.get("regionEnterEventId").getAsLong());
        assertEquals("getAndIncrement", version.getAsJsonObject("site")
                .get("methodName").getAsString());
        JsonObject read = envelope.getAsJsonArray("reads").get(0)
                .getAsJsonObject();
        assertEquals(76L, read.get("readEventId").getAsLong());
        assertEquals(41L, read.get("regionEnterEventId").getAsLong());
        assertEquals("()I", read.getAsJsonObject("site")
                .get("methodDescriptor").getAsString());
        // The expressions the refs name are in the session's own table.
        assertTrue(Files.exists(dir.expressions()));
        assertTrue(RowCodec.readExpressions(dir.expressions())
                .refs().contains(exports.get(0).expressionRef()));
    }

    /** One tracked location, as the VM's read-out states it. */
    private static JsonObject vmEnvelopeRecord() {
        JsonObject site = new JsonObject();
        site.addProperty("className",
                "java/util/concurrent/atomic/AtomicInteger");
        site.addProperty("methodName", "getAndIncrement");
        site.addProperty("methodDescriptor", "()I");
        site.addProperty("bci", 12);
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 50L);
        version.addProperty("versionKind", "RMW");
        version.addProperty("regionEnterEventId", 41L);
        version.addProperty("writerContextId", 7L);
        version.add("site", site);
        version.add("expression", rmwExpression());
        JsonObject read = new JsonObject();
        read.addProperty("readEventId", 76L);
        read.addProperty("regionEnterEventId", 41L);
        read.addProperty("readerContextId", 7L);
        read.add("site", site);
        JsonArray versions = new JsonArray();
        versions.add(version);
        JsonArray reads = new JsonArray();
        reads.add(read);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind", "SHARED_FIELD_VERSIONS");
        envelope.addProperty("schemaVersion", 1);
        envelope.add("versions", versions);
        envelope.add("reads", reads);
        envelope.addProperty("readLogTruncated", false);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", "INSTANCE_FIELD/2#24");
        record.add("envelope", envelope);
        return record;
    }

    /** {@code marker == false}, the predicate the jump is taken under. */
    private static JsonObject markerJumpCondition(String symbol) {
        JsonObject marker = new JsonObject();
        marker.addProperty("_type", "SymbolExpression");
        marker.addProperty("_java_type", "Z");
        marker.addProperty("_exp", symbol);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ConsumerBoundaryExpression");
        read.addProperty("boundaryKind", "FIELD_READ");
        read.addProperty("_java_type", "Z");
        read.add("expression", marker);
        JsonObject literal = new JsonObject();
        literal.addProperty("_type", "ConstExpr");
        literal.addProperty("_java_type", "Z");
        literal.addProperty("_exp", "Y_Z_0");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.add("_left", read);
        predicate.addProperty("_op", "==");
        predicate.add("_right", literal);
        return predicate;
    }

    /**
     * Whether one term holds at the roots the session recorded, or null when
     * it is not a comparison over declared roots and literals alone.
     *
     * <p>Deliberately small: {@code Y_<sort>_<value>} is the VM's spelling
     * of a literal and a root's {@code recordedValue} is what the run read,
     * so an equality over the two is decidable from the rows without a
     * solver.  Anything else is not this invariant's business.</p>
     */
    private static Boolean holdsAtRoots(JsonObject term,
                                        Map<String, String> roots,
                                        Map<String, JsonObject> table) {
        if (term == null
                || !"BinaryExpression".equals(text(term, "_type"))) {
            return null;
        }
        String operator = text(term, "_op");
        if (!"==".equals(operator) && !"!=".equals(operator)) return null;
        String left = valueAtRoots(term.get("_left"), roots, table);
        String right = valueAtRoots(term.get("_right"), roots, table);
        if (left == null || right == null) return null;
        return Boolean.valueOf("==".equals(operator)
                ? left.equals(right) : !left.equals(right));
    }

    private static String valueAtRoots(com.google.gson.JsonElement node,
                                       Map<String, String> roots,
                                       Map<String, JsonObject> table) {
        if (node == null || !node.isJsonObject()) return null;
        JsonObject object = node.getAsJsonObject();
        String symbol = text(object, "_exp");
        if (roots.containsKey(symbol)) return normalized(roots.get(symbol));
        if (symbol.startsWith("Y_")) {
            int mark = symbol.lastIndexOf('_');
            return mark < 0 ? null : normalized(symbol.substring(mark + 1));
        }
        com.google.gson.JsonElement nested = object.get("expression");
        return nested == null ? null : valueAtRoots(nested, roots, table);
    }

    /** {@code true}/{@code 1} and {@code false}/{@code 0} are one value. */
    private static String normalized(String value) {
        String stated = value == null ? "" : value.trim();
        if ("true".equals(stated)) return "1";
        if ("false".equals(stated)) return "0";
        return stated;
    }

    private static String text(JsonObject object, String field) {
        com.google.gson.JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                ? value.getAsString() : "";
    }

    /** {@code Y_I_0 + Y_I_1}, as the VM publishes a linearized RMW. */
    private static JsonObject rmwExpression() {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "ConstExpr");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "Y_I_0");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_1");
        JsonObject binary = new JsonObject();
        binary.addProperty("_type", "BinaryExpression");
        binary.add("_left", left);
        binary.addProperty("_op", "+");
        binary.add("_right", right);
        return binary;
    }

    /** A second declared port of one cell: another read, another event. */
    private static JsonObject secondPortRow() {
        JsonObject row = placeholderRow("g", null);
        row.addProperty("eventSeq", 19L);
        return row;
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
        java.lang.reflect.Method publish = RowPublication.class
                .getDeclaredMethod("placeholder", OccurrenceAddress.class,
                        JsonObject.class, String.class, java.util.Map.class);
        publish.setAccessible(true);
        publish.invoke(null, occurrence, row, symbol, installed);
    }

    private static RootKind kindOf(JsonObject row) throws Exception {
        java.lang.reflect.Method kind = RowPublication.class
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
        RowRuntime.configure(sessionFile());
        OccurrenceAddress occurrence = address(
                "hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.addProperty("_exp", "allKeys.get(id) == null");

        // The run that took the fatal arm, and the run that took the
        // healthy one, state the same predicate about the same anchor.
        RowRuntime.target(occurrence, 8L, "retrieveDataEncryptionKey#u8",
                condition, true, true, true);
        RowRuntime.target(occurrence, 9L, "retrieveDataEncryptionKey#u8",
                condition, false, false, true);
        RowRuntime.closeSession();

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

        // The frame journal: a VM-logged event takes the frames the thread
        // stood on when the VM's event clock was below its id.  The clock is
        // the VM's; the frames are this stack's; nothing is an ordinal.
        Identity.resetForTests();
        // The region-enter event is the newest when the region opens.
        final long[] clock = {41L};
        Identity.clock(new FrameJournal.Clock() {
            @Override
            public long now() {
                return clock[0];
            }
        });
        Identity.scopeStart();
        Identity.regionEnter();
        Identity.regionKey(41L);
        // No event between the region entry and this call, so the entry the
        // clock stood at is replaced rather than duplicated.
        Identity.enterCall("Saver.save()#u1");
        clock[0] = 44L;
        Identity.enterCall("Manager.count()#u2");
        clock[0] = 48L;
        // Event 45..48 happened inside count(): the last entry below it is
        // the one the clock read when count() was entered.
        assertEquals("Saver.save()#u1@0/Manager.count()#u2@0",
                FrameJournal.framesAt(41L, 45L).render());
        assertEquals("Saver.save()#u1@0/Manager.count()#u2@0",
                FrameJournal.framesAt(41L, 48L).render());
        // Event 42..44 happened after save() was entered and before count()
        // was, so it stands one frame shallower.
        assertEquals("Saver.save()#u1@0",
                FrameJournal.framesAt(41L, 43L).render());
        // Entered and left with no event in between: the interval holds
        // nothing, so the collapsed entry is the one that stood at 48.
        Identity.exitCall();
        Identity.enterCall("Manager.count()#u2");
        assertEquals("Saver.save()#u1@0/Manager.count()#u2@1",
                FrameJournal.framesAt(41L, 49L).render());
        // Not this activation's journal, and below the region entry: unplaced
        // rather than answered with someone else's frames.
        assertNull(FrameJournal.framesAt(99L, 49L));
        assertNull(FrameJournal.framesAt(41L, 41L));
        // One key, two answers of the same activation: the frames a logged
        // event stood on, and the occurrence that performed it.  A row of a
        // read belongs to the activation the VM names on the record, not to
        // whichever activation's read-out found the location's log first.
        OccurrenceAddress performer = address(
                "hdfs-17960/nn0#epoch1", "REGION.9492ec77",
                CausalContext.of(Role.CLIENT, 1),
                ExecutionIndex.parse("Manager.delete()#u3@0"));
        RowRuntime.journalRegion(41L, performer);
        assertEquals(performer, RowRuntime.occurrenceAt(41L));
        assertNull("an event of no activation of this session names none",
                RowRuntime.occurrenceAt(99L));
        Identity.resetForTests();
        Identity.scopeStart();
        Identity.enterCall("Caller.run()#u3");
        Identity.enterCall("Caller.step()#u7");
        Identity.enterCall("Caller.body()#u9");

        // The thread-start handover (P2h): the child's inherited stack
        // GAINS the frame of the start that created it, and two siblings
        // started from one site inside one starter frame -- hdfs-17960's two
        // FSImageSaver threads -- differ by that start's iteration and by
        // nothing else.  No thread id, no address, no session counter.
        Identity.resetForTests();
        Identity.scopeStart();
        Identity.enterCall("FSImage.saveFSImageInAllDirs()#u12");
        String first = startedWorkIndex("FSImage.saveFSImageInAllDirs()#u40");
        String second = startedWorkIndex("FSImage.saveFSImageInAllDirs()#u40");
        assertEquals("FSImage.saveFSImageInAllDirs()#u12@0"
                + "/FSImage.saveFSImageInAllDirs()#u40@0"
                + "/FSImageSaver.run()#u1@0", first);
        assertEquals("FSImage.saveFSImageInAllDirs()#u12@0"
                + "/FSImage.saveFSImageInAllDirs()#u40@1"
                + "/FSImageSaver.run()#u1@0", second);
        // The count lives in the starter FRAME and is gone with it: the next
        // activation of the starter starts its starts again at 0, exactly as
        // a loop iteration count does.
        Identity.exitCall();
        Identity.enterCall("FSImage.saveFSImageInAllDirs()#u12");
        assertEquals("FSImage.saveFSImageInAllDirs()#u12@1"
                + "/FSImage.saveFSImageInAllDirs()#u40@0"
                + "/FSImageSaver.run()#u1@0",
                startedWorkIndex("FSImage.saveFSImageInAllDirs()#u40"));

        // A pool thread was created before the work it runs, so it inherits
        // nothing from the submission: the start filed for the TASK is
        // claimed on the object the region is entered on, and the next task
        // replaces that frame instead of nesting under it.
        Identity.resetForTests();
        final List<String> ran =
                Collections.synchronizedList(new ArrayList<String>());
        final Object[] tasks = {new Object(), new Object()};
        Thread worker = poolThreadCreatedOutsideAnyScope(new Runnable() {
            @Override
            public void run() {
                for (Object task : tasks) {
                    Identity.claimStart(task);
                    Identity.enterCall("Task.run()#u1");
                    ran.add(Identity.atScope().render());
                    Identity.exitCall();
                }
            }
        });
        Identity.scopeStart();
        Identity.enterCall("Pool.submitAll()#u5");
        Identity.startWork("Pool.submitAll()#u9", tasks[0], NN.key());
        Identity.startWork("Pool.submitAll()#u9", tasks[1], NN.key());
        worker.start();
        try {
            worker.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        assertEquals("Pool.submitAll()#u9@0/Task.run()#u1@0", ran.get(0));
        assertEquals("Pool.submitAll()#u9@1/Task.run()#u1@0", ran.get(1));

        // An activation's push and its pop are paired, recursion included:
        // the frames an occurrence stands on ARE its identity, so a frame
        // left standing moves the address of everything after it.  Every
        // entry of one method has its own depth, and an unbalanced one is
        // visible as a depth that did not come back.
        int depthAtOpen = Identity.depth();
        Identity.enterCall("Recursive.m()#u1");
        Identity.enterCall("Recursive.m()#u1");
        assertEquals(depthAtOpen + 2, Identity.depth());
        assertEquals("Recursive.m()#u1", Identity.innermostFrame());
        Identity.exitCall();
        Identity.exitCall();
        assertEquals(depthAtOpen, Identity.depth());

        Identity.resetForTests();
        Identity.scopeStart();
        Identity.enterCall("Caller.run()#u3");

        // The three causal contexts, and the one that is not an ordinal.
        assertEquals("Root:HEARTBEAT_TICK#4", Identity.context("", "",
                Role.HEARTBEAT_TICK, 4).render());
        assertEquals("Anchor:abc123@HADOOP_IPC#heartbeat",
                Identity.context("abc123", "HADOOP_IPC#heartbeat",
                        Role.IPC_HANDLER, 2).render());
        assertEquals("Lost:DATA_XCEIVER",
                Identity.context("", "", Role.DATA_XCEIVER, 0).render());
    }

    /**
     * The index of the work one start site started, on its own thread.
     *
     * <p>The child is CONSTRUCTED before the start is filed, which is the
     * real order -- {@code new Thread(saver)} then {@code start()} -- and the
     * reason the frame cannot travel by inheritance.</p>
     */
    private static String startedWorkIndex(String startSite) {
        final AtomicReference<String> onChild = new AtomicReference<>("");
        Thread child = new Thread(new Runnable() {
            @Override
            public void run() {
                Identity.enterCall("FSImageSaver.run()#u1");
                onChild.set(Identity.atScope().render());
            }
        });
        Identity.startWork(startSite, child, NN.key());
        child.start();
        try {
            child.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        return onChild.get();
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
        System.setProperty(RowRuntime.SESSION_PROPERTY, "seed");
        return results;
    }

    private SessionDir session() {
        return SessionDir.of(iteration.getRoot().toPath()
                .resolve("iteration-0000"), RowRuntime.sessionId());
    }

}
