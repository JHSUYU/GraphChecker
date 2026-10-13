package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.RowInvariants;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
    /** The node's clock ran an hour ahead of the host at that mint. */
    private static final long SKEW = 3_600_000L;

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
     *
     * <p>A configured-source mint likewise: the root row and the version
     * row.  Driven through the runtime's own recorder -- {@code
     * observeConfiguredSourceEntry} then {@code recordConfiguredSourceMint}
     * -- so the symbol this asserts on is the one the VM label produces and
     * not a spelling the test chose.</p>
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
                filed(record(CLOCK_CELL,
                        version(MINT_VERSION,
                                symbolExpression(CLOCK_SYMBOL, "J")))));

        RowPlaceholderMint.roots(active, at);
        RowRuntime.closeSession();

        List<RootMintRow> roots = roots();
        assertEquals("the declared clock still states its root row",
                1, roots.size());
        assertEquals(RootKind.CLOCK, roots.get(0).kind());
        assertEquals(CLOCK_SYMBOL, roots.get(0).symbol());
        assertEquals("and the instant this execution ran it at", INSTANT,
                roots.get(0).recordedValue());
        assertEquals("how far its node's clock ran off the host there",
                SKEW, roots.get(0).clockSkew());
        assertEquals("so the host read the instant less that skew",
                Long.toString(Long.parseLong(INSTANT) - SKEW),
                roots.get(0).hostReading());
        assertEquals("and the clock it is: the JVM clock it wraps, its tick",
                Clock.of(1_000_000L, Clock.WALL), roots.get(0).clock());

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

        // A configured-source mint likewise, in a session of its own.
        clear();
        RowRuntime.configure(sessionFile());
        RecordingWindow.open();
        long invocation = CausynthTraceRecorder.beginCall(0L, SOURCE_METHOD,
                UNIT, SOURCE_METHOD, new Object(), true);
        try {
            OccurrenceAddress source = address();
            ActiveRegion configured = region(sourceTask(), source);
            RootMint.SourceSiteEntry entry =
                    configured.observeConfiguredSourceEntry(SOURCE_ID,
                            SOURCE_FIELD);
            assertNotNull("the fixture declares this source's site", entry);
            String label =
                    ConfiguredSourcePhaseContract.engineLabel(SOURCE_ID);
            // The VM's spelling of the field it mints under that label
            // (FieldSymbolExp: M_<sort>_field_<label>_<owner class>), with
            // the label filed before the store, as RootMint files it.
            String symbol = "M_Z_field_" + label + "_a/Manager";
            RowRuntime.declaredMintLabel(label);
            configured.recordConfiguredSourceMint(entry, SOURCE_ID,
                    SOURCE_FIELD, label, symbolExpression(symbol, "Z"), false,
                    "true");
            configured.sharedStateRecords.put(SOURCE_CELL,
                    filed(record(SOURCE_CELL,
                            version(SOURCE_MINT_VERSION,
                                    symbolExpression(symbol, "Z")))));

            RowPlaceholderMint.roots(configured, source);
            RowRuntime.closeSession();

            roots = roots();
            assertEquals(1, roots.size());
            assertEquals(SOURCE_ID, roots.get(0).rootId());
            assertEquals("a configured boolean source is a MARKER",
                    RootKind.MARKER, roots.get(0).kind());
            reads = reads();
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
                symbolExpression(COUNTER_SYMBOL, "I"), true, false, "2", 0L);
        JsonObject record = record(COUNTER_CELL,
                version(COUNTER_MINT, symbolExpression(COUNTER_SYMBOL, "I")));
        array(record, "versions").add(version(COUNTER_WRITE,
                integerExpression(2L)));
        active.sharedStateRecords.put(COUNTER_CELL,
                filed(record));

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
        // One record both read out alike: the minting one's walk of it is
        // skipped, and its placeholder still finds the store there.
        SharedStateCapture.Filed once = filed(shared);
        bystander.sharedStateRecords.put(CLOCK_CELL, once);
        writes(bystander);
        assertTrue("walked whole: no later publication walks it",
                once.walked);
        clockMint(minting);
        minting.sharedStateRecords.put(CLOCK_CELL, once);
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

    /**
     * A version stored outside every region (VM 22f2707a1) has no write row
     * to join, so the read of it states what it returned (VM f11) or the
     * composer has nothing to pin it to (commit-gs v74: the GS an IPC
     * handler's updatePipeline stored, read at the third target).
     */
    @Test
    public void aReadOfAStoreOutsideEveryRegionStatesWhatItReturned()
            throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress at = address();
        ActiveRegion active = region(at);
        RowRuntime.journalRegion(900L, at);
        JsonObject stored = new JsonObject();
        stored.addProperty("_type", "ConstExpr");
        stored.addProperty("_java_type", "J");
        stored.addProperty("_exp", "Y_J_1003");
        // The stamp's log: one store no region made, and the read of it.
        JsonObject stamp = record("INSTANCE_FIELD/10#40",
                version(456L, stored));
        JsonObject read = new JsonObject();
        read.addProperty("readEventId", 510L);
        read.addProperty("regionEnterEventId", 900L);
        JsonObject envelope = stamp.getAsJsonObject("envelope");
        envelope.add("reads", new JsonArray());
        array(stamp, "reads").add(loggedAt(read));
        // A write of this region whose value is that read.
        JsonObject observed = new JsonObject();
        observed.addProperty("fieldVersionId", 456L);
        observed.addProperty("versionKind", "WRITE");
        observed.add("expression", stored);
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", 10);
        location.addProperty("slot", 40);
        location.addProperty("locationKind", "INSTANCE_FIELD");
        JsonObject readFrom = new JsonObject();
        readFrom.addProperty("_type", "ReadFromExpression");
        readFrom.addProperty("_java_type", "J");
        readFrom.addProperty("readEventId", 510L);
        readFrom.add("location", location);
        readFrom.add("observedVersion", observed);
        readFrom.add("concreteValue", stored);
        JsonObject copy = record("INSTANCE_FIELD/77#24",
                loggedAt(version(900L + 1L, readFrom)));
        active.sharedStateRecords.put("INSTANCE_FIELD/10#40",
                filed(stamp));
        active.sharedStateRecords.put("INSTANCE_FIELD/77#24",
                filed(copy));
        writes(active);
        RowRuntime.closeSession();

        ReadRow stated = null;
        for (ReadRow row : reads()) {
            if (row.observedVersion() == 456L) stated = row;
        }
        assertNotNull("the read of the outside store is a row", stated);
        assertEquals("and states what the read returned", "1003",
                stated.concreteValue());
    }

    /**
     * EVERY OBSERVED READ_SITE ACCESS IS A ROW (SYMBOL-SCOPE §5.2), whether
     * or not a published expression holds its value: hdfs-adhoc-45 tests
     * {@code state == State.IN_SEGMENT}, a reference compared with a
     * constant, which records no condition, so the read of {@code state}
     * reached no expression and the closure never saw it.  The read log
     * states what each read's plan chose; a read in a READ_SITE's method is
     * a row of that version, one stated by an expression too is one row, a
     * read in any other method is left to the expressions as before.
     */
    @Test
    public void anObservedReadSiteAccessIsARowThoughNoExpressionHoldsIt()
            throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress at = address();
        ActiveRegion active = region(at);
        RowRuntime.journalRegion(900L, at);
        JsonObject state = symbolExpression("M_L'a/B$State'_5", "a/B$State");
        JsonObject log = record("INSTANCE_FIELD/10#80",
                loggedAt(version(456L, state)));
        JsonObject envelope = log.getAsJsonObject("envelope");
        envelope.add("reads", new JsonArray());
        envelope.addProperty("readLogTruncated", false);
        // 457 in the READ_SITE's method, 458 in another, 459 in the
        // READ_SITE's method and in a write's expression too.
        for (Object[] each : new Object[][]{
                {457L, "isSegmentOpen"}, {458L, "other"},
                {459L, "isSegmentOpen"}}) {
            JsonObject site = new JsonObject();
            site.addProperty("className", "a/B");
            site.addProperty("methodName", (String) each[1]);
            site.addProperty("methodDescriptor", "()Z");
            site.addProperty("bci", 1);
            JsonObject read = new JsonObject();
            read.addProperty("readEventId", (Long) each[0]);
            read.addProperty("regionEnterEventId", 900L);
            read.add("site", site);
            JsonObject chosen = new JsonObject();
            chosen.addProperty("fieldVersionId", 456L);
            chosen.addProperty("versionKind", "WRITE");
            read.add("observedVersion", chosen);
            read.addProperty("observedExact", true);
            read.addProperty("writerSetComplete", true);
            read.addProperty("_java_type", "L");
            array(log, "reads").add(read);
        }
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", 10);
        location.addProperty("slot", 80);
        location.addProperty("locationKind", "INSTANCE_FIELD");
        JsonObject observed = new JsonObject();
        observed.addProperty("fieldVersionId", 456L);
        observed.add("expression", state);
        JsonObject readFrom = new JsonObject();
        readFrom.addProperty("_type", "ReadFromExpression");
        readFrom.addProperty("_java_type", "L");
        readFrom.addProperty("readEventId", 459L);
        readFrom.addProperty("observedExact", true);
        readFrom.add("location", location);
        readFrom.add("observedVersion", observed);
        readFrom.add("concreteValue", state);
        JsonObject copy = record("INSTANCE_FIELD/77#24",
                loggedAt(version(901L, readFrom)));
        active.sharedStateRecords.put("INSTANCE_FIELD/10#80",
                filed(log));
        active.sharedStateRecords.put("INSTANCE_FIELD/77#24",
                filed(copy));
        JsonObject readSite = new JsonObject();
        readSite.addProperty("kind", "STATIC_SCOPE_SITE");
        readSite.addProperty("role", "READ_SITE");
        readSite.addProperty("vmSite", "a.B#isSegmentOpen()Z");
        RowPublication.installReadSites(Collections.singletonList(readSite));
        try {
            writes(active);
        } finally {
            RowPublication.installReadSites(
                    Collections.<JsonObject>emptyList());
        }
        RowRuntime.closeSession();

        Map<Long, ReadRow> rows = new LinkedHashMap<Long, ReadRow>();
        for (ReadRow row : reads()) {
            assertNull("one row per read event", rows.put(row.seq(), row));
        }
        assertEquals(Arrays.asList(457L, 459L),
                new ArrayList<Long>(new java.util.TreeSet<Long>(
                        rows.keySet())));
        ReadRow tested = rows.get(457L);
        assertEquals("the version its plan chose", 456L,
                tested.observedVersion());
        assertEquals("L", tested.javaType());
        assertEquals("an exact read returned its version's identity",
                "M_L'a/B$State'_5", tested.concreteValue());
        assertTrue(tested.endpoint().site(), tested.endpoint().site()
                .startsWith("a.B#isSegmentOpen()Z#"));
    }

    /**
     * A location's INITIAL is a write row, flagged: Writers_W(l)'s writer at
     * version 0, placed at the access that started the log and spelled as
     * its own kind there -- a log a store starts states the INITIAL and the
     * store at one event, and they are two endpoints.
     */
    @Test
    public void aLocationsInitialIsAFlaggedRowOfItsOwnSite()
            throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress at = address();
        ActiveRegion active = region(at);
        RowRuntime.journalRegion(900L, at);
        Map<Long, String> kinds = new LinkedHashMap<Long, String>();
        kinds.put(455L, "INITIAL");
        kinds.put(456L, "WRITE");
        JsonObject log = null;
        for (Map.Entry<Long, String> kind : kinds.entrySet()) {
            JsonObject value = new JsonObject();
            value.addProperty("_type", "ConstExpr");
            value.addProperty("_java_type", "J");
            value.addProperty("_exp", "Y_J_" + kind.getKey());
            JsonObject logged = loggedAt(version(kind.getKey(), value));
            logged.addProperty("versionKind", kind.getValue());
            if (log == null) {
                log = record("INSTANCE_FIELD/10#40", logged);
            } else {
                array(log, "versions").add(logged);
            }
        }
        active.sharedStateRecords.put("INSTANCE_FIELD/10#40",
                filed(log));
        writes(active);
        RowRuntime.closeSession();

        Map<Long, WriteRow> rows = new LinkedHashMap<Long, WriteRow>();
        for (WriteRow row : writes()) rows.put(row.version(), row);
        assertTrue("the INITIAL is a row, flagged", rows.get(455L).initial());
        assertFalse("the store is a write", rows.get(456L).initial());
        assertEquals("at the store's site, as its own kind",
                Endpoint.initialSite(rows.get(456L).endpoint().site()),
                rows.get(455L).endpoint().site());
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
                symbolExpression(CLOCK_SYMBOL, "J"), true, false, INSTANT,
                SKEW);
    }

    /** {@code RowPublication#writes}, the one publisher of WriteRows. */
    private static void writes(ActiveRegion active) throws Exception {
        java.lang.reflect.Method publish = RowPublication.class
                .getDeclaredMethod("writes", ActiveRegion.class);
        publish.setAccessible(true);
        publish.invoke(null, active);
    }

    /**
     * A refused envelope read out again unchanged is held as its refusal,
     * decoded once: every activation whose read-out states it still files
     * the location as refused and defers the gap with its own read-out
     * ({@code SharedStateCapture#file}), so neither depends on which
     * activation read it first.
     */
    @Test
    public void aHeldRefusalIsFiledWithEveryActivation() throws Exception {
        VmExpressionTable.Store store =
                ConcolicRegionRuntime.workloadExpressionStore;
        // Before the activations, which take the session's store.
        ConcolicRegionRuntime.workloadExpressionStore =
                new VmExpressionTable.Store(owner -> false);
        SharedStateCapture.resetForTests();
        try {
            String refused = "{\"schemaVersion\":2,\"kind\":"
                    + "\"SHARED_FIELD_VERSIONS\",\"sessionId\":1,\"selected\":"
                    + "false,\"location\":{\"ownerSymRid\":10,\"slot\":40,"
                    + "\"locationKind\":\"INSTANCE_FIELD\"},"
                    + "\"writerSetComplete\":true,\"versions\":[],"
                    + "\"readLogTruncated\":false,\"reads\":[],"
                    + "\"serializationTruncated\":false}";
            String page = "{\"schemaVersion\":1,\"kind\":"
                    + "\"SHARED_TRACKED_LOCATIONS\",\"sessionId\":1,"
                    + "\"locations\":[" + refused + "],\"locationCount\":1,"
                    + "\"complete\":true,\"nextAfterEventId\":0,"
                    + "\"vmExpressionTable\":{\"schemaVersion\":1,\"kind\":\""
                    + VmExpressionTable.KIND + "\",\"authority\":\""
                    + VmExpressionTable.AUTHORITY + "\",\"sessionId\":1,"
                    + "\"definitionCount\":0,\"definitions\":[]}}";
            java.lang.reflect.Field decoding = SharedStateCapture.class
                    .getDeclaredField("DECODING");
            decoding.setAccessible(true);
            java.lang.reflect.Method decode = SharedStateCapture.class
                    .getDeclaredMethod("decodeTrackedLocations",
                            String.class, ActiveRegion.class);
            decode.setAccessible(true);
            for (ActiveRegion active : new ActiveRegion[] {
                    region(address()),
                    region(address(NODE + "/region/REGION.16ba41cf#1"))}) {
                List<Runnable> deferred = new ArrayList<Runnable>();
                @SuppressWarnings("unchecked")
                ThreadLocal<List<Runnable>> filing =
                        (ThreadLocal<List<Runnable>>) decoding.get(null);
                filing.set(deferred);
                try {
                    decode.invoke(null, page, active);
                } finally {
                    filing.remove();
                }
                assertEquals("its gap, with this read-out", 1,
                        deferred.size());
                assertEquals("location was never selected as a carrier",
                        active.sharedStateRefusals.get(
                                "INSTANCE_FIELD/10#40"));
                assertTrue(active.sharedStateRecords.isEmpty());
            }
            String summary = SharedStateCapture.readOutSummary();
            assertTrue(summary, summary.contains(
                    "2 location envelope(s) filed, 1 of them decoded"));
            assertTrue(summary, summary.contains("1 record(s) held"));
        } finally {
            ConcolicRegionRuntime.workloadExpressionStore = store;
            SharedStateCapture.resetForTests();
        }
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
        encoded.addProperty("clock", 1_000_000L);
        encoded.addProperty(InputActionCatalog.DECLARED_CLOCK_SOURCE,
                Clock.WALL);
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
        return SessionReader.read(session()).reads();
    }

    private List<WriteRow> writes() throws Exception {
        return SessionReader.read(session()).writes();
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

    /** A write log record as a read-out files it. */
    private static SharedStateCapture.Filed filed(JsonObject record) {
        return new SharedStateCapture.Filed("", record, "", 0);
    }
}
