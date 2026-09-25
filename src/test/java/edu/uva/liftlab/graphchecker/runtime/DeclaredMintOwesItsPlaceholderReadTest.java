package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.RowInvariants;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * EVERY MINT OWES THE PLACEHOLDER READ THAT STATES IT, and a mint store is
 * no write in any activation.
 *
 * <p>A mint installs its symbol into a field the VM versions, and that
 * version is suppressed: nobody stored it, the mint made it.  The row that
 * says what the suppressed version is worth is the placeholder ReadRow, and
 * it used to be published only for an UNATTRIBUTED region input -- a
 * declared CLOCK or configured source got a RootMintRow and nothing else, so
 * every read of its own store was bound by nothing.</p>
 *
 * <p>On hdfs-11741 that is the whole ADMISSION_GAP.  The woven clock mint
 * symbolizes the {@code value} of a freshly allocated {@code java.lang.Long}
 * and the code unboxes it at once, so the anchor's terms read
 * {@code INSTANCE/217#24@v1155} -- the mint's own store.  In campaign #5b,
 * 284 of those 877 reads had no row to resolve them, in 64 of 64 sessions,
 * and all 17 paths that reached the anchor were refused on one.  The other
 * 593 bound only by accident, off a WriteRow a SECOND activation published
 * for the very store the minting activation suppresses -- which is the other
 * half of this test.</p>
 */
public class DeclaredMintOwesItsPlaceholderReadTest {
    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    private static final String METHOD = "<a.B: void run()>";
    private static final String REGION = "REGION.ba3902cd";
    private static final String NODE = "hdfs-11741/dn1#epoch0";
    private static final String OCCURRENCE =
            NODE + "/region/" + REGION + "#1";
    /** The cell the woven clock mint allocates and symbolizes. */
    private static final String CLOCK_CELL = "INSTANCE_FIELD/217#24";
    /** The version that mint installed: the one the unbox read observes. */
    private static final long MINT_VERSION = 1155L;
    /** The VM's own name for what it installed there. */
    private static final String CLOCK_LABEL =
            "REGION.ba3902cd.in.559a1724.occ.e36a3c48";
    private static final String CLOCK_SYMBOL =
            "M_J_field_" + CLOCK_LABEL + "_java/lang/Long";
    private static final String INSTANT = "1789965233929";

    /** The configured source the second half of the fixture declares. */
    private static final String SOURCE_ID = "CFG.ORDERED";
    private static final String SOURCE_FIELD =
            "<a.Manager: boolean snapshotDeletionOrdered>";
    private static final String SOURCE_METHOD =
            "<a.Manager: boolean isSnapshotDeletionOrdered()>";
    private static final int UNIT = 1;
    private static final String SOURCE_CELL = "INSTANCE_FIELD/64#8";
    private static final long SOURCE_MINT_VERSION = 311L;

    /** And the unattributed region input, which this changes nothing for. */
    private static final String COUNTER_SYMBOL = "M_I_field_PORT.count";
    private static final String COUNTER_CELL = "INSTANCE_FIELD/19#24";
    private static final long COUNTER_WRITE = 171L;
    private static final long COUNTER_MINT = 172L;

    private final List<Long> opened = new ArrayList<Long>();

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void clear() {
        for (Long token : opened) {
            ConcolicRegionRuntime.ACTIVE.remove(token);
        }
        opened.clear();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    /**
     * A CLOCK mint publishes BOTH rows, and they say different things.
     *
     * <p>The root row states the kind, the domain and the instant this
     * execution read; the read row states the VERSION the mint installed and
     * states no value at all.  A value here would be a PIN, and the composer
     * pins no declared root -- {@code Composer#valuationOf} and {@code
     * #domains} both skip a CLOCK -- so a clock pinned by its own read row
     * would make {@code clockNecessary} answer "decoration" for every witness
     * and leave CLOCK_SKEW exactly as unreachable as it was.</p>
     */
    @Test
    public void aClockMintStatesItsRootAndTheVersionItInstalled()
            throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress at = address();
        ActiveRegion active = region(at);
        clockMint(active);
        // The VM's write log, as the activation read it out: one version of
        // the fresh box's `value`, and its whole expression is the symbol.
        active.sharedStateRecords.put(CLOCK_CELL,
                record(CLOCK_CELL, version(MINT_VERSION,
                        symbolExpression(CLOCK_SYMBOL, "J"))));

        RowPlaceholderMint.roots(active, at);
        RowRuntime.closeSession();

        List<RootMintRow> roots = roots();
        assertEquals("the declared clock still states its root row",
                1, roots.size());
        assertEquals(RootKind.CLOCK, roots.get(0).kind());
        assertEquals(CLOCK_SYMBOL, roots.get(0).symbol());
        assertEquals("and the instant this execution read", INSTANT,
                roots.get(0).recordedValue());

        List<ReadRow> reads = reads();
        assertEquals("and the read that states the version it minted",
                1, reads.size());
        ReadRow placeholder = reads.get(0);
        assertEquals(CLOCK_SYMBOL, placeholder.symbol());
        assertEquals("the version the mint installed", MINT_VERSION,
                placeholder.mintVersion());
        assertEquals("which is the only version this cell ever had",
                MINT_VERSION, placeholder.observedVersion());
        assertTrue("published as a placeholder of that location",
                placeholder.endpoint().site().startsWith(CLOCK_CELL)
                        && placeholder.endpoint().site()
                        .contains(RowInvariants.PLACEHOLDER));
        assertEquals("on the location the VM numbered", "217",
                placeholder.location().owner());
        assertNull("and it states no value: the root row states that, and a"
                        + " second statement of it is a pin",
                placeholder.concreteValue());
    }

    /**
     * A configured-source mint likewise: the root row and the version row.
     *
     * <p>Driven through the runtime's own recorder -- {@code
     * observeConfiguredSourceEntry} then {@code recordConfiguredSourceMint}
     * -- so the symbol this asserts on is the one the VM label produces and
     * not a spelling the test chose.</p>
     */
    @Test
    public void aConfiguredSourceMintStatesItsRootAndItsVersion()
            throws Exception {
        RowRuntime.configure(sessionFile());
        RecordingWindow.open();
        long invocation = CausynthTraceRecorder.beginCall(0L, SOURCE_METHOD,
                UNIT, SOURCE_METHOD, new Object());
        try {
            OccurrenceAddress at = address();
            ActiveRegion active = region(sourceTask(), at);
            RootMint.SourceSiteEntry entry =
                    active.observeConfiguredSourceEntry(SOURCE_ID,
                            SOURCE_FIELD);
            assertNotNull("the fixture declares this source's site", entry);
            String label = ConfiguredSourcePhaseContract
                    .engineLabelForPhase(phaseId(), SOURCE_ID);
            // The VM's spelling of the field it mints under that label
            // (FieldSymbolExp: M_<sort>_field_<label>_<owner class>), with
            // the label filed before the store, as RootMint files it.
            String symbol = "M_Z_field_" + label + "_a/Manager";
            RowRuntime.declaredMintLabel(label);
            active.recordConfiguredSourceMint(entry, SOURCE_ID, SOURCE_FIELD,
                    label, symbolExpression(symbol, "Z"), false, "true");
            active.sharedStateRecords.put(SOURCE_CELL,
                    record(SOURCE_CELL, version(SOURCE_MINT_VERSION,
                            symbolExpression(symbol, "Z"))));

            RowPlaceholderMint.roots(active, at);
            RowRuntime.closeSession();

            List<RootMintRow> roots = roots();
            assertEquals(1, roots.size());
            assertEquals(SOURCE_ID, roots.get(0).rootId());
            assertEquals("a configured boolean source is a MARKER",
                    RootKind.MARKER, roots.get(0).kind());
            List<ReadRow> reads = reads();
            assertEquals("and it owes the same version row a clock does",
                    1, reads.size());
            assertEquals(symbol, reads.get(0).symbol());
            assertEquals(SOURCE_MINT_VERSION, reads.get(0).mintVersion());
            assertEquals(SOURCE_MINT_VERSION, reads.get(0).observedVersion());
            assertNull(reads.get(0).concreteValue());
        } finally {
            CausynthTraceRecorder.endCall(invocation, null, "");
        }
    }

    /**
     * And the UNATTRIBUTED region input is exactly what it was.
     *
     * <p>No root row, one placeholder read, and that read keeps both things
     * a declared root's does not: the LAST REAL WRITE before the mint, which
     * is the join to the occurrence that wrote the cell, and the value it
     * read.  Nothing moves such a symbol, so nothing is pinned by saying so
     * -- it is hdfs-17960's counter, and the join is the point of it.</p>
     */
    @Test
    public void anUnattributedRegionInputIsUnchanged() throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress at = address();
        ActiveRegion active = region(at);
        RowRuntime.declaredMintLabel("PORT.count");
        active.recordManualSymbolization(
                new SymbolizeAction(counterAction()), "PORT.count",
                Collections.<String>emptyList(),
                "<java.util.concurrent.atomic.AtomicInteger: int value>",
                symbolExpression(COUNTER_SYMBOL, "I"), true, false, "2");
        JsonObject record = record(COUNTER_CELL,
                version(COUNTER_MINT, symbolExpression(COUNTER_SYMBOL, "I")));
        array(record, "versions").add(version(COUNTER_WRITE,
                integerExpression(2L)));
        active.sharedStateRecords.put(COUNTER_CELL, record);

        RowPlaceholderMint.roots(active, at);
        RowRuntime.closeSession();

        assertTrue("an unattributed region input is no root",
                roots().isEmpty());
        List<ReadRow> reads = reads();
        assertEquals(1, reads.size());
        assertEquals(COUNTER_SYMBOL, reads.get(0).symbol());
        assertEquals("it states the version it minted", COUNTER_MINT,
                reads.get(0).mintVersion());
        assertEquals("and joins the last real write before it",
                COUNTER_WRITE, reads.get(0).observedVersion());
        assertEquals("and what it read", "2", reads.get(0).concreteValue());
    }

    /**
     * A MINT STORE IS NEVER A WRITE, WHICHEVER ACTIVATION GETS THERE FIRST.
     *
     * <p>The suppression used to be a question about one activation's own
     * mint rows, and {@code RowPublication#writes} skips the version BEFORE
     * it claims the write event -- so a second activation that merely read
     * the same VM record out published the mint's store as a WriteRow and
     * won the claim.  Here that second activation publishes FIRST and knows
     * nothing about the mint -- and it publishes BETWEEN the VM's store and
     * the mint row, the window bug2 v20 lost a session to (INSTANCE
     * 204.24@855, published at {@code GeneratedMethodAccessor#invoke#40}):
     * it is the label the mint filed BEFORE the store that answers for
     * it.</p>
     *
     * <p>Which is also what keeps invariant 7 from firing.  Now that a clock
     * publishes a placeholder, any surviving mint-store WriteRow is
     * "a fabricated write: this write's whole expression is the symbol a
     * placeholder read of this session minted" -- BLOCKING, and correctly
     * so.  The control write of the same location proves the suppression is
     * the mint's and not the location's.</p>
     */
    @Test
    public void noActivationPublishesAMintStoreAsAWrite() throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress at = address();
        ActiveRegion minting = region(at);
        // RootMint files the label, then the VM makes the store; the mint
        // row comes later, after the bystander below has published.
        RowRuntime.declaredMintLabel(CLOCK_LABEL);

        // The VM record as EVERY activation reads it out: the mint's store,
        // and one real write of the same cell by the same performer.
        RowRuntime.journalRegion(900L, at);
        JsonObject shared = record(CLOCK_CELL,
                loggedAt(version(MINT_VERSION,
                        symbolExpression(CLOCK_SYMBOL, "J"))));
        array(shared, "versions").add(loggedAt(version(MINT_VERSION + 1L,
                symbolExpression("M_J_field_HOFF.9f1c_a/Carrier", "J"))));

        // The OTHER activation, which never minted anything, publishing
        // before the one that did.
        ActiveRegion bystander = region(address(
                NODE + "/region/REGION.16ba41cf#1"));
        bystander.sharedStateRecords.put(CLOCK_CELL, shared);
        writes(bystander);
        clockMint(minting);
        minting.sharedStateRecords.put(CLOCK_CELL, shared);
        writes(minting);
        RowPlaceholderMint.roots(minting, at);
        RowRuntime.closeSession();

        List<WriteRow> writes = writes();
        assertEquals("the cell's one real write is published", 1,
                writes.size());
        assertEquals(MINT_VERSION + 1L, writes.get(0).version());
        for (WriteRow write : writes) {
            assertFalse("and no activation states the mint's own store as a"
                            + " write of it",
                    write.version() == MINT_VERSION);
        }
        List<ReadRow> reads = reads();
        assertEquals(1, reads.size());
        assertEquals("so the one row that states that version is the"
                        + " placeholder", MINT_VERSION,
                reads.get(0).mintVersion());
        assertEquals(CLOCK_SYMBOL, reads.get(0).symbol());
    }

    // ------------------------------------------------------------------
    // The fixture.
    // ------------------------------------------------------------------

    /** One declared CLOCK mint, through the runtime's own recorder. */
    private void clockMint(ActiveRegion active) {
        // Filed before the store, as RootMint files every declared mint.
        RowRuntime.declaredMintLabel(CLOCK_LABEL);
        active.recordManualSymbolization(
                new SymbolizeAction(clockAction()), "PORT.now",
                Collections.<String>emptyList(),
                "<org.apache.hadoop.util.Timer: long now()>.return",
                symbolExpression(CLOCK_SYMBOL, "J"), true, false, INSTANT);
    }

    /** {@code RowPublication#writes}, the one publisher of WriteRows. */
    private static void writes(ActiveRegion active) throws Exception {
        java.lang.reflect.Method publish = RowPublication.class
                .getDeclaredMethod("writes", ActiveRegion.class);
        publish.setAccessible(true);
        publish.invoke(null, active);
    }

    private ActiveRegion region(OccurrenceAddress at) throws Exception {
        return region(task(), at);
    }

    private ActiveRegion region(JsonObject encoded, OccurrenceAddress at)
            throws Exception {
        long token = 880001L + opened.size();
        ActiveRegion active = new ActiveRegion(token,
                new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded)),
                null, Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        opened.add(Long.valueOf(token));
        active.d3Address = at;
        return active;
    }

    private static OccurrenceAddress address() {
        return address(OCCURRENCE);
    }

    private static OccurrenceAddress address(String occurrence) {
        return OccurrenceAddress.of(NodeId.parse(NODE),
                occurrence.substring(occurrence.indexOf("/region/") + 8,
                        occurrence.lastIndexOf('#')),
                CausalContext.of("5c6bd4ac", "HADOOP_IPC/refresh-block-keys"),
                ExecutionIndex.parse("a.B.run()#u1@0"));
    }

    /** One VM write-log record, as an activation reads one out. */
    private static JsonObject record(String locationKey, JsonObject first) {
        JsonObject envelope = new JsonObject();
        JsonArray versions = new JsonArray();
        versions.add(first);
        envelope.add("versions", versions);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", locationKey);
        record.add("envelope", envelope);
        return record;
    }

    private static JsonArray array(JsonObject record, String member) {
        return record.getAsJsonObject("envelope").getAsJsonArray(member);
    }

    private static JsonObject version(long id, JsonObject expression) {
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", id);
        version.add("expression", expression);
        return version;
    }

    /** The same version, with the site and activation the VM logs on it. */
    private static JsonObject loggedAt(JsonObject version) {
        JsonObject site = new JsonObject();
        site.addProperty("className", "sun/reflect/NativeMethodAccessorImpl");
        site.addProperty("methodName", "invoke");
        site.addProperty("methodDescriptor",
                "(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;");
        site.addProperty("bci", 100);
        version.add("site", site);
        version.addProperty("regionEnterEventId", 900L);
        return version;
    }

    private static JsonObject symbolExpression(String symbol, String type) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", type);
        expression.addProperty("_exp", symbol);
        return expression;
    }

    private static JsonObject integerExpression(long value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConstantExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_value", value);
        return expression;
    }

    /** One frozen SYMBOLIC action declaring a wall-clock read. */
    private static JsonObject clockAction() {
        JsonObject encoded = action("PORT.now", "J");
        encoded.addProperty("cell",
                "<org.apache.hadoop.util.Timer: long now()>.return");
        encoded.addProperty("rootKind", "CALL_RETURN");
        encoded.addProperty("clock", true);
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", INSTANT);
        encoded.addProperty("eventSeq", 7L);
        return encoded;
    }

    /** And one that declares no root at all: a region input. */
    private static JsonObject counterAction() {
        JsonObject encoded = action("PORT.count", "I");
        encoded.addProperty("cell",
                "<java.util.concurrent.atomic.AtomicInteger: int value>");
        return encoded;
    }

    private static JsonObject action(String symbol, String javaType) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", symbol);
        encoded.addProperty("actionDigest", "DIGEST.1");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", javaType);
        return encoded;
    }

    private static String phaseId() {
        return ConfiguredSourcePhaseContract.phaseId(SOURCE_ID,
                SiteId.of(SOURCE_METHOD, UNIT));
    }

    /** One executable task row, as the plan carries it. */
    private static JsonObject task() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", REGION);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", NODE);
        encoded.addProperty("occurrenceId", OCCURRENCE);
        encoded.addProperty("rootMethod", METHOD);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", METHOD);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", NODE);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branchMethods", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        loopBound.addProperty("defaultBackedgeTraversals", 8);
        encoded.add("loopBound", loopBound);
        return encoded;
    }

    /** The same row, declaring one configured-source phase. */
    private static JsonObject sourceTask() {
        JsonObject encoded = task();
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                SOURCE_ID, SOURCE_FIELD, SOURCE_METHOD, UNIT));
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(declarations)
                        .get(0),
                OCCURRENCE, 11L, 3L, SOURCE_METHOD,
                Arrays.asList(Long.valueOf(7L), Long.valueOf(5L))));
        encoded.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        return encoded;
    }

    private List<RootMintRow> roots() throws Exception {
        return RowCodec.readAll(session().roots(), RowCodec::readRootMint);
    }

    private List<ReadRow> reads() throws Exception {
        return RowCodec.readAll(session().reads(), RowCodec::readRead);
    }

    private List<WriteRow> writes() throws Exception {
        return RowCodec.readAll(session().writes(), RowCodec::readWrite);
    }

    private Path sessionFile() throws Exception {
        Path results = iteration.getRoot().toPath()
                .resolve("iteration-0000").resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        return results;
    }

    private SessionDir session() {
        return SessionDir.of(iteration.getRoot().toPath()
                .resolve("iteration-0000"), RowRuntime.sessionId());
    }
}
