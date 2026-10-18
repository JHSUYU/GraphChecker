package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.call;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.live;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.region;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.symbol;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.taskRow;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.tokens;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * The mint is the unit: what it publishes and what it owes.  Every mint
 * states the value it read (a manual mint once stated none: VM12's {@code
 * DelegationKey.expiryDate} RECORDED_ROOT_VALUE_UNSTATED) and owes the
 * placeholder read that states the version it installed; a model is applied
 * only where this run can place the mint; a clock reading runs on from its
 * node's jumps.
 */
public class MintTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String METHOD = "<a.B: void run()>";
    private static final String MANUAL_REGION = "REGION.aaa1cfd7";
    private static final String MANUAL_SOURCE = "hdfs-17899/nn0#epoch0";
    private static final String NODE = "hdfs/nn0";
    private static final String SOURCE_ID = "CFG.ORDERED";
    private static final String FIELD =
            "<a.Manager: boolean snapshotDeletionOrdered>";
    private static final String PHASE_METHOD =
            "<a.Manager: boolean isSnapshotDeletionOrdered()>";
    private static final int UNIT = 1;
    private static final String REGION = "REGION.9492ec77";
    private static final String TICK = "<a.Manager: void tick()>@0";
    private static final String FOCUSED_ADDRESS = NODE + "#epoch1/region/"
            + REGION + "/ctx:Root:CLIENT#1/idx:" + TICK;
    private static final String CONCRETE_ADDRESS = NODE + "#epoch1/region/"
            + REGION + "/ctx:Root:CLIENT#2/idx:" + TICK;
    /** The address the focus row names and the region carries. */
    private static final String PLANNED_ADDRESS =
            "hdfs/nn0#epoch1/region/" + MANUAL_REGION
                    + "/ctx:Root:CLIENT#1/idx:";
    /** Where the recording mints the root the flip depends on (11741: the
     *  SERIAL_NO minted in nn0's rotation, read by the balancer). */
    private static final String MINT_ADDRESS =
            "hdfs/dn1#epoch0/region/REGION.53092d3e/ctx:Root:CLIENT#1/idx:";
    /** One the wave named nowhere, which merely runs alongside. */
    private static final String ALONGSIDE_ADDRESS =
            "hdfs/dn0#epoch0/region/REGION.094a8e3d/ctx:Root:CLIENT#1/idx:";
    private static final String KEY_MANAGER =
            "<" + KeyManager.class.getName() + ": ";

    /** The placeholder fixture's woven clock mint: the cell, the version it
     *  installed, the VM's name for it, the instant, its node's skew. */
    private static final String DN1 = "hdfs-11741/dn1#epoch0";

    private int opened;
    private ActiveRegion lastManualRegion;

    @Before
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        NodeClocks.reset();
    }

    @After
    public void releaseRegions() {
        Fixtures.release();
        RuntimeTraceContext.resetForTests();
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        RowRuntime.resetForTests();
    }

    private Path root() {
        return folder.getRoot().toPath();
    }

    private ActiveRegion open(JsonObject row) {
        return live(region(970001L + opened++, row));
    }

    private static JsonObject task(String region, String source,
                                   String occurrence) {
        return taskRow(source, occurrence, METHOD, true, "'regionId':'"
                + region + "'");
    }

    /** {@code row} declaring the configured source's one phase at {@code
     *  occurrence}, and (with {@code model}) the wave's value of it. */
    private static JsonObject phased(JsonObject row, String occurrence,
                                     boolean model) {
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                SOURCE_ID, FIELD, PHASE_METHOD, UNIT));
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(declarations)
                        .get(0), occurrence, 11L, 3L, PHASE_METHOD,
                Arrays.asList(7L, 5L)));
        row.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        if (!model) return row;
        String phase = ConfiguredSourcePhaseContract.phaseId(SOURCE_ID,
                SiteId.of(PHASE_METHOD, UNIT));
        row.add("modelAssignments", Fixtures.with(new JsonObject(),
                "'s':[{'modelAssignmentKey':'MODEL.1','inputSymbol':"
                        + "'SOURCE_PHASE:" + phase + "','valueType':'BOOLEAN',"
                        + "'value':'false','configuredSourcePhaseId':'"
                        + phase + "','configuredSourceId':'" + SOURCE_ID
                        + "','configuredSourceFieldSignature':'" + FIELD
                        + "'}]").get("s"));
        return row;
    }

    private static JsonObject taskAt(String taskId, String occurrence) {
        JsonObject row = phased(task(REGION, NODE + "#epoch1", occurrence),
                occurrence, true);
        row.addProperty("taskId", taskId);
        return row;
    }

    private ActiveRegion manualRegion() {
        return open(task(MANUAL_REGION, MANUAL_SOURCE, MANUAL_SOURCE
                + "/region/" + MANUAL_REGION + "#1"));
    }

    private static OccurrenceAddress address(String rendered) {
        return OccurrenceAddress.parse(rendered);
    }

    private static ActiveRegion at(ActiveRegion active, String rendered) {
        active.d3Address = address(rendered);
        return active;
    }

    /** Hands this replay {@code rows} as its focus rows, afresh. */
    private void focus(String... rows) throws Exception {
        Fixtures.focus(folder.newFolder().toPath(), rows);
        FocusedReplay.resetForTests();
    }

    /** One focus row flipping {@code site}#1 at {@code at}. */
    private static String flipAt(String at, String site, boolean outcome,
                                 String members) {
        return Fixtures.focusRow(at, "'taskId':'TASK.1','obligationId':"
                + "'OBL.1','pathId':'PATH.1','seedSessionId':'s-seed',"
                + "'flip':{'siteId':'" + site + "','ordinal':1,'outcome':"
                + outcome + "},'unproducible':[]" + members);
    }

    private static ObligationResult result(String session) {
        return FocusedReplay.results(session).get(0);
    }

    private static String rootValue(ActiveRegion active, String rootId,
                                    Object observed) throws Exception {
        return (String) call(RootMint.class, "focusedRootValue",
                new Class<?>[] {ActiveRegion.class, String.class,
                        Object.class}, active, rootId, observed);
    }

    /** One frozen SYMBOLIC action, as the plan carries it. */
    private static JsonObject action(String symbol) {
        return json("{'symbol':'" + symbol + "','actionDigest':'DIGEST.1',"
                + "'cell':'<org.apache.hadoop.util.Timer: long now()>.return',"
                + "'mode':'SYMBOLIC','javaType':'J'}");
    }

    /** The same action, as the plan carries a declared clock read (of
     *  the wall clock, where {@code wall}). */
    private static JsonObject clockAction(String symbol, String value,
                                          boolean wall) {
        return Fixtures.with(action(symbol), "'rootKind':'CALL_RETURN',"
                + "'clock':1000000," + (wall ? "'"
                + InputActionCatalog.DECLARED_CLOCK_SOURCE + "':'" + Clock.WALL
                + "'," : "") + "'observed':true,'primitiveValue':'" + value
                + "','eventSeq':7");
    }

    /** The row the runtime publishes for one manual mint. */
    private JsonObject manualRow(JsonObject encoded, String recordedValue) {
        ActiveRegion active = manualRegion();
        lastManualRegion = active;
        active.recordManualSymbolization(new SymbolizeAction(encoded),
                "PORT.now", Collections.<String>emptyList(),
                "<org.apache.hadoop.security.token.delegation.DelegationKey:"
                        + " long expiryDate>", symbol(
                        "M_J_field_REGION.aaa1cfd7.in.f30dbb22_java/lang/Long",
                        "J"), true, false, recordedValue, 0L);
        List<JsonObject> published = symbolizedRows(active);
        assertEquals(1, published.size());
        return published.get(0);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> symbolizedRows(ActiveRegion active) {
        return (List<JsonObject>) Fixtures.get(active, "symbolizedRows");
    }

    private GapRow gap() throws Exception {
        return Fixtures.lastGap(root());
    }

    private List<GapRow> gaps() throws Exception {
        return Fixtures.gaps(root());
    }

    private List<RootMintRow> roots() throws Exception {
        return RowCodec.readAll(Fixtures.session(root()).roots(),
                RowCodec::readRootMint);
    }

    private List<WriteRow> writes() throws Exception {
        return SessionReader.read(Fixtures.session(root())).writes();
    }

    /** One declared cell of each kind a case declares a root at. */
    private static final class KeyManager {
        private int serialNo;
        private boolean ordered;
        private long now;
    }

    /**
     * A mint publishes the value it read -- every mint, a clock and a
     * focused one included (INVARIANT 8): the seed replay IS the reference
     * execution the deltas are relative to, and the value a mint states is
     * the one it read BEFORE the plant (hdfs-17960's two focused sessions
     * and 11741's six once stated an empty {@code recordedValue}, BLOCKING
     * at IMPORT).  A flip is addressed at ONE occurrence (R4a: 6 of 11
     * campaign-#3 flips landed on the wrong node), never abandons the mint
     * of an assigned root (17960 lost 42 decision rows and its roots.jsonl
     * that way), and admits only over a session that states every mint it
     * moved and whose prefix was not abandoned.  A clock is asked for as a
     * skew of this run's own reading; a field mint asks the same one
     * decision (11741 stated SERIAL_NO 182907 under an obligation assigning
     * 182910); a blank is named; the flips a replay inherited hold too.
     */
    @Test
    public void aMintStatesTheValueItRead() throws Exception {
        JsonObject recorded = manualRow(action("PORT.now"), "1789358343989");
        assertEquals("MANUAL_SYMBOLIC_INPUT_OBSERVATION",
                recorded.get("kind").getAsString());
        assertEquals("1789358343989",
                recorded.get("recordedValue").getAsString());
        assertEquals("J", recorded.get("javaType").getAsString());
        assertTrue(recorded.get("minted").getAsBoolean());
        JsonObject clock = manualRow(clockAction("PORT.now", "1789358343989",
                false), "1789358344655");
        assertEquals("the clock the case declared, and its tick", 1_000_000L,
                clock.get("clock").getAsLong());
        assertEquals("this execution's own instant", "1789358344655",
                clock.get("observedValue").getAsString());
        assertEquals("the seed replay is the reference execution",
                clock.get("observedValue").getAsString(),
                clock.get("recordedValue").getAsString());
        assertEquals(7L, clock.get("eventSeq").getAsLong());
        // I4: the mint files its clock cell where it runs, so a nested
        // activation's decision (published first) resolves its symbol.
        assertEquals(Collections.singletonMap("PORT.now", 1789358344655L),
                RowRuntime.clockReadings(term(clock.get("rawSymbol")
                        .getAsString())));
        assertEquals(Collections.emptyMap(),
                RowRuntime.clockReadings(term("M_I_serial")));

        focus(flipAt(PLANNED_ADDRESS, "Arrival#u8", true,
                ",'rootAssignments':{'CASE.SERIAL':'12','CASE.ORDERED':"
                        + "'false'},'clockDeltas':{'CASE.NOW':'-4200'},"
                        + "'rootMints':{'CASE.SERIAL':'" + MINT_ADDRESS
                        + "'}"));
        FocusedReplay.observeDecision(address(MINT_ADDRESS), "Arrival#u8", 1,
                true);
        FocusedReplay.observeDecision(address(ALONGSIDE_ADDRESS),
                "Arrival#u8", 1, true);
        assertEquals("another occurrence settles nothing", 1,
                FocusedReplay.results("s-flip").size());
        assertEquals(Verdict.NOT_ADMITTED, result("s-flip").verdict());
        assertTrue("named by the occurrence that never reached it: "
                + result("s-flip").detail(), result("s-flip").detail()
                .contains(address(PLANNED_ADDRESS).id()));
        assertTrue("an assigned root's mint is focused",
                FocusedReplay.focused(address(MINT_ADDRESS)));
        assertTrue("and owes no flip, so is never abandoned for one",
                FocusedReplay.complete(address(MINT_ADDRESS)));
        assertFalse(FocusedReplay.complete(address(PLANNED_ADDRESS)));
        assertTrue("an occurrence outside the focused set owes nothing",
                FocusedReplay.complete(address(ALONGSIDE_ADDRESS)));
        FocusedReplay.observeDecision(address(PLANNED_ADDRESS), "Arrival#u8",
                1, true);
        assertTrue(FocusedReplay.complete(address(PLANNED_ADDRESS)));
        assertEquals("roots it states no mint for: not admitted",
                Verdict.NOT_ADMITTED, result("s-flip").verdict());
        assertTrue("named, the clock's skew among them: "
                + result("s-flip").detail(), result("s-flip").detail()
                .contains("CASE.NOW"));
        FocusedReplay.mintPublished("CASE.SERIAL");
        FocusedReplay.mintPublished("CASE.ORDERED");
        assertEquals("one root still unstated", Verdict.NOT_ADMITTED,
                result("s-flip").verdict());
        FocusedReplay.mintPublished("CASE.NOW");
        assertEquals(Verdict.ADMITTED, result("s-flip").verdict());
        FocusedReplay.noteUnansweredTask("ROOT_NEVER_EXECUTED: another "
                + "task of this replay, which settles nothing here");
        assertEquals("an unanswered task that abandoned no prefix",
                Verdict.ADMITTED, result("s-flip").verdict());
        FocusedReplay.noteUnansweredTask("REPLAY_PREFIX_UNMATCHED: the "
                + "focused occurrence did not take the decision its "
                + "obligation flips: ");
        assertEquals("an abandoned prefix takes its rows with it",
                Verdict.NOT_ADMITTED, result("s-flip").verdict());
        assertTrue(result("s-flip").detail().startsWith(
                "REPLAY_PREFIX_UNMATCHED"));
        Fixtures.set(FocusedReplay.class, "unmatchedPrefix", "");
        Fixtures.set(FocusedReplay.class, "refusedAt", "");

        ActiveRegion focused = at(manualRegion(), PLANNED_ADDRESS);
        assertEquals("the skew moves this replay's own reading",
                "1789358340455", rootValue(focused, "CASE.NOW",
                        1789358344655L));
        assertEquals("12", rootValue(focused, "CASE.SERIAL", 7L));
        assertEquals("nothing was asked of this root", "",
                rootValue(focused, "CASE.OTHER", 7L));
        assertEquals("planted at the mint the row names", "12", rootValue(
                at(manualRegion(), MINT_ADDRESS), "CASE.SERIAL", 7L));
        assertEquals("and nowhere else", "", rootValue(at(manualRegion(),
                ALONGSIDE_ADDRESS), "CASE.SERIAL", 7L));

        KeyManager keys = new KeyManager();
        keys.serialNo = 182907;
        keys.ordered = true;
        keys.now = 1789358344655L;
        RuntimeTraceContext.registerSource(keys, new SourceRef("CLUSTER_NODE",
                "NAMENODE", "hdfs-17899/nn0", 0L));
        // R3: one rule over both spellings of what a wave asks of a root
        // (11741 campaign #3: six deltas no mint planted, silently).
        Map<String, String> owed = new LinkedHashMap<String, String>();
        owed.put("CASE.SERIAL", "12");
        owed.put("CASE.ORDERED", "false");
        owed.put("CASE.NOW", "-4200");
        assertEquals("unplanted until a mint plants it", owed,
                FocusedReplay.unplantedAssignments());
        Object[][] mints = {
            // root, action, cell, type, read, stated, the region reads back
            {"CASE.SERIAL", action("CASE.SERIAL"), "int serialNo>", "I",
                182907, "182907"},
            {"CASE.ORDERED", action("CASE.ORDERED"), "boolean ordered>", "Z",
                Boolean.TRUE, "true"},
            {"CASE.NOW", clockAction("CASE.NOW", "1789358343989", false),
                "long now>", "J", 1789358344655L, "1789358344655"}};
        for (Object[] mint : mints) {
            assertEquals("a focused mint states the value it read: "
                    + mint[0], mint[5], RootMint.fieldMintRecordedValue(
                    focused, new SymbolizeAction((JsonObject) mint[1]), keys,
                    KEY_MANAGER + mint[2], (String) mint[3], mint[4]));
        }
        assertEquals("and the region reads the wave's values back",
                Arrays.asList(12, false, 1789358340455L),
                Arrays.asList(keys.serialNo, keys.ordered, keys.now));
        assertEquals(Collections.emptyMap(),
                FocusedReplay.unplantedAssignments());
        keys.serialNo = 182907;
        assertEquals("a mint that planted nothing states what it read",
                "182907", RootMint.fieldMintRecordedValue(focused,
                        new SymbolizeAction(action("CASE.OTHER")), keys,
                        KEY_MANAGER + "int serialNo>", "I", 182907));
        assertEquals(182907, keys.serialNo);

        Fixtures.openSession(root());
        assertFalse("the row writer states no blank", manualRow(clockAction(
                "PORT.unspellable", "1789358343989", false), "")
                .has("recordedValue"));
        RowPlaceholderMint.roots(lastManualRegion, address(PLANNED_ADDRESS));
        assertEquals(GapKind.UNSTATED_VALUE, gap().kind());
        assertTrue("a root with no centre for its domain blocks",
                gap().blocking());
        assertEquals("PORT.unspellable", gap().subject());
        assertTrue(gap().detail().contains("states no value it observed"));

        // The flips this replay inherited are part of its world: the one
        // result row is the primary obligation's, held to each of them.
        String inherited = ",'inheritedFlips':[{'focusedOccurrenceId':'"
                + address(ALONGSIDE_ADDRESS).id() + "','siteId':'Rotate#u5',"
                + "'ordinal':1,'outcome':true,'obligationId':'OBL.parent'}]";
        for (boolean taken : new boolean[] {true, false}) {
            focus(flipAt(PLANNED_ADDRESS, "Arrival#u8", true, inherited));
            assertEquals(1, FocusedReplay.obligationIds().size());
            assertTrue(FocusedReplay.focused(address(ALONGSIDE_ADDRESS)));
            assertTrue("never abandoned for the primary flip",
                    FocusedReplay.complete(address(ALONGSIDE_ADDRESS)));
            FocusedReplay.observeDecision(address(PLANNED_ADDRESS),
                    "Arrival#u8", 1, true);
            if (taken) {
                assertEquals("the primary flip alone does not admit",
                        Verdict.NOT_ADMITTED, result("s-nested").verdict());
                assertTrue(result("s-nested").detail(), result("s-nested")
                        .detail().contains("Rotate#u5#1") && result(
                        "s-nested").detail().contains("OBL.parent"));
            }
            FocusedReplay.observeDecision(address(ALONGSIDE_ADDRESS),
                    "Rotate#u5", 1, taken);
            assertEquals(taken ? Verdict.ADMITTED : Verdict.NOT_ADMITTED,
                    result("s-nested").verdict());
        }
        assertTrue("it was the INHERITED flip: " + result("s-nested")
                .detail(), result("s-nested").detail().contains("INHERITED")
                && result("s-nested").detail().contains("Rotate#u5#1"));
    }

    /** One decision term that reads {@code symbol}, as the VM spells it. */
    private static JsonObject term(String symbol) {
        JsonObject predicate = json("{'_type':'BinaryExpression','_op':'<',"
                + "'_right':{'_type':'ConstExpr','_java_type':'J','_exp':"
                + "'Y_J_0'}}");
        predicate.add("_left", symbol(symbol, "J"));
        return predicate;
    }

    /**
     * I2: a refusal abandons only its own occurrence.  {@code contradicted}
     * once asked {@link FocusedReplay#focused}, true of every member of the
     * focused set, so one obligation's refusal abandoned the next focused
     * activation at its first decision (10 of hdfs-11741's 40 nn0 sessions).
     */
    @Test
    public void aRefusalAbandonsOnlyItsOwnOccurrence() throws Exception {
        String mint = ",'rootMints':{'CASE.SERIAL':'" + MINT_ADDRESS + "'}";
        focus(flipAt(PLANNED_ADDRESS, "Arrival#u8", true, ",'taskId':"
                + "'TASK.OBL.A','obligationId':'OBL.A'" + mint),
                flipAt(ALONGSIDE_ADDRESS, "Departure#u3", true, ",'taskId':"
                        + "'TASK.OBL.B','obligationId':'OBL.B'" + mint));
        assertTrue(FocusedReplay.focused("TASK.OBL.A",
                address(PLANNED_ADDRESS)));
        assertTrue(FocusedReplay.focused("TASK.OBL.B",
                address(ALONGSIDE_ADDRESS)));
        FocusedReplay.observeDecision(address(PLANNED_ADDRESS), "Arrival#u8",
                1, false);
        assertTrue(FocusedReplay.contradicted(address(PLANNED_ADDRESS)));
        assertTrue(FocusedReplay.refusal(address(PLANNED_ADDRESS))
                .startsWith("wrong decision at Arrival#u8"));
        assertFalse("another obligation's occurrence is not",
                FocusedReplay.contradicted(address(ALONGSIDE_ADDRESS)));
        assertEquals("", FocusedReplay.refusal(address(ALONGSIDE_ADDRESS)));
        assertFalse("nor the mint the wave plants at",
                FocusedReplay.contradicted(address(MINT_ADDRESS)));
        assertTrue(FocusedReplay.complete(address(MINT_ADDRESS)));
        assertFalse("OBL.B is still owed at its own occurrence",
                FocusedReplay.complete(address(ALONGSIDE_ADDRESS)));
        FocusedReplay.observeDecision(address(ALONGSIDE_ADDRESS),
                "Departure#u3", 1, true);
        assertTrue(FocusedReplay.complete(address(ALONGSIDE_ADDRESS)));
        assertFalse(FocusedReplay.contradicted(address(ALONGSIDE_ADDRESS)));
    }

    /**
     * A configured source mints where its occurrence runs SYMBOLIC
     * (SYMBOL-SCOPE §1): a concretely run region contributes literals,
     * never freedom.  On hdfs-11741 a concrete {@code updateKeys} minted
     * three fresh INTEGRAL roots beside a literal expiry, decoupling it
     * from its clock.  The seed focuses nothing, so it mints everywhere.
     */
    @Test
    public void aHookMintsOnlyWhereItsOccurrenceRunsSymbolic()
            throws Exception {
        Fixtures.openSession(root());
        RecordingWindow.open();
        ActiveRegion concrete = at(open(taskAt("TASK.CONCRETE",
                CONCRETE_ADDRESS)), CONCRETE_ADDRESS);
        ActiveRegion focused = at(open(taskAt("TASK.FOCUSED",
                FOCUSED_ADDRESS)), FOCUSED_ADDRESS);
        FocusedReplay.resetForTests();
        assertTrue("no focus row: every planned occurrence mints",
                ActiveRegion.mintsUnderSymbolicOccurrence(concrete, SOURCE_ID,
                        FIELD));
        assertTrue(gaps().isEmpty());
        focus(Fixtures.focusRow(FOCUSED_ADDRESS, "'taskId':'TASK.FOCUSED',"
                + "'obligationId':'OBL.9','pathId':'PATH.9','seedSessionId':"
                + "'s-seed','flip':{'siteId':'Arrival#u8','ordinal':1,"
                + "'outcome':true},'unproducible':[]"));
        long invocation = CausynthTraceRecorder.beginCall(0L, PHASE_METHOD,
                UNIT, PHASE_METHOD, new Object(), true);
        try {
            assertFalse("a hook outside every occurrence mints nothing",
                    ConcolicRegionRuntime.symbolizeConfiguredSourceField(
                            SOURCE_ID, new Object(), FIELD));
            assertEquals(GapKind.DECLARATION_MISSING, gap().kind());
            assertFalse("nothing was rewritten", gap().blocking());
            assertEquals(SOURCE_ID, gap().subject());
            assertTrue(gap().detail(), gap().detail().contains("none"));
            tokens().push(concrete.token);
            assertFalse("a concretely run occurrence mints no root",
                    ConcolicRegionRuntime.symbolizeConfiguredSourceField(
                            SOURCE_ID, new Object(), FIELD));
            tokens().remove(concrete.token);
            assertTrue(symbolizedRows(concrete).isEmpty());
            assertTrue(gap().detail().contains(CONCRETE_ADDRESS));
            assertEquals("one row per occurrence", 2, gaps().size());

            // The focused occurrence mints: a concrete value this site's
            // symbol, and an arrival carrying an expression of its own none.
            assertTrue(ActiveRegion.mintsUnderSymbolicOccurrence(focused,
                    SOURCE_ID, FIELD));
            RootMint.SourceSiteEntry entry =
                    focused.observeConfiguredSourceEntry(SOURCE_ID, FIELD);
            assertNotNull(entry);
            assertEquals(2, gaps().size());
            String label = ConfiguredSourcePhaseContract.engineLabel(SOURCE_ID);
            focused.recordConfiguredSourceMint(entry, SOURCE_ID, FIELD, label,
                    symbol(label, "Z"), false, "true");
            RowPlaceholderMint.roots(focused, address(FOCUSED_ADDRESS));
            List<RootMintRow> minted = roots();
            assertEquals(1, minted.size());
            assertEquals(SOURCE_ID, minted.get(0).rootId());
            assertEquals(label, minted.get(0).symbol());
            assertEquals("true", minted.get(0).recordedValue());
            ActiveRegion again = at(open(taskAt("TASK.FOCUSED",
                    FOCUSED_ADDRESS)), FOCUSED_ADDRESS);
            RootMint.SourceSiteEntry reused =
                    again.observeConfiguredSourceEntry(SOURCE_ID, FIELD);
            assertNotNull(reused);
            again.recordConfiguredSourceMint(reused, SOURCE_ID, FIELD, label,
                    symbol(label, "Z"), true, "true");
            assertTrue(symbolizedRows(again).get(0).get("reused")
                    .getAsBoolean());
            RowPlaceholderMint.roots(again, address(FOCUSED_ADDRESS));
            assertEquals("a reused read mints none", 1, roots().size());
        } finally {
            CausynthTraceRecorder.endCall(invocation, null, "");
        }
    }

    /** A declared clock read of the plan's, read at this recorded event. */
    private static SymbolizeAction clock(long place, String source) {
        return new SymbolizeAction(json("{'symbol':'PORT.now." + place + "',"
                + "'actionDigest':'DIGEST.1','cell':'<org.apache.hadoop.util."
                + "Time: long now()>.return','mode':'SYMBOLIC','javaType':'J',"
                + "'" + InputActionCatalog.DECLARED_WALL_CLOCK + "':1000000,'"
                + InputActionCatalog.DECLARED_CLOCK_SOURCE + "':'" + source
                + "','observed':true,'primitiveValue':'1000','eventSeq':"
                + place + "}"));
    }

    // ---- every mint owes the placeholder read that states it ----------

    private ActiveRegion placeholderRegion(String occurrence) {
        return placeholderRegion(task("REGION.ba3902cd", DN1, DN1
                + "/region/REGION.ba3902cd#1"), occurrence);
    }

    private ActiveRegion placeholderRegion(JsonObject row, String occurrence) {
        ActiveRegion active = open(row);
        active.d3Address = OccurrenceAddress.of(NodeId.parse(DN1),
                occurrence.substring(occurrence.indexOf("/region/") + 8,
                        occurrence.lastIndexOf('#')),
                CausalContext.of("5c6bd4ac", "HADOOP_IPC/refresh-block-keys"),
                ExecutionIndex.parse("a.B.run()#u1@0"));
        return active;
    }

    private static final String OCCURRENCE = DN1 + "/region/REGION.ba3902cd#1";

    /** One VM write-log record, as an activation reads one out. */
    private static JsonObject record(String locationKey,
                                     JsonObject... versions) {
        JsonObject record = json("{'locationKey':'" + locationKey + "',"
                + "'envelope':{'versions':[]}}");
        for (JsonObject version : versions) array(record, "versions")
                .add(version);
        return record;
    }

    private static JsonArray array(JsonObject record, String member) {
        JsonObject envelope = record.getAsJsonObject("envelope");
        if (!envelope.has(member)) envelope.add(member, new JsonArray());
        return envelope.getAsJsonArray(member);
    }

    private static JsonObject version(long id, JsonElement expression) {
        JsonObject version = json("{'fieldVersionId':" + id + "}");
        version.add("expression", expression);
        return version;
    }

    /** The version with the site and activation the VM logs on it. */
    private static JsonObject loggedAt(JsonObject version) {
        version.add("site", json("{'className':'sun/reflect/"
                + "NativeMethodAccessorImpl','methodName':'invoke',"
                + "'methodDescriptor':'(Ljava/lang/Object;[Ljava/lang/Object;)"
                + "Ljava/lang/Object;','bci':100}"));
        version.addProperty("regionEnterEventId", 900L);
        return version;
    }

    private static JsonObject constant(String sort, long value) {
        return json("{'_type':'ConstExpr','_java_type':'" + sort + "',"
                + "'_exp':'Y_" + sort + "_" + value + "'}");
    }

    private static SharedStateCapture.Filed filed(JsonObject record) {
        return new SharedStateCapture.Filed("", record, "", 0);
    }

    private static void publishWrites(ActiveRegion active) throws Exception {
        call(RowPublication.class, "writes",
                new Class<?>[] {ActiveRegion.class}, active);
    }

    /** Publishes {@code records} of one activation's read-out, with
     *  {@code readSites} installed. */
    private void published(Map<String, JsonObject> records,
                           JsonObject... readSites) throws Exception {
        Fixtures.openSession(root());
        ActiveRegion active = placeholderRegion(OCCURRENCE);
        RowRuntime.journalRegion(900L, active.d3Address);
        records.forEach((key, record) -> active.sharedStateRecords.put(key,
                filed(record)));
        RowPublication.installReadSites(Arrays.asList(readSites));
        try {
            publishWrites(active);
        } finally {
            RowPublication.installReadSites(
                    Collections.<JsonObject>emptyList());
        }
        RowRuntime.closeSession();
    }

    /**
     * A location's INITIAL is a write row, flagged: Writers_W(l)'s writer at
     * version 0, at the access that started the log and spelled as its own
     * kind there -- a log a store starts states both at one event.
     */
    @Test
    public void aLocationsInitialIsAFlaggedRowOfItsOwnSite()
            throws Exception {
        Fixtures.openSession(root());
        ActiveRegion active = placeholderRegion(OCCURRENCE);
        RowRuntime.journalRegion(900L, active.d3Address);
        JsonObject initial = loggedAt(version(455L, constant("J", 455L)));
        initial.addProperty("versionKind", "INITIAL");
        JsonObject store = loggedAt(version(456L, constant("J", 456L)));
        store.addProperty("versionKind", "WRITE");
        active.sharedStateRecords.put("INSTANCE_FIELD/10#40", filed(record(
                "INSTANCE_FIELD/10#40", initial, store)));
        publishWrites(active);
        RowRuntime.closeSession();
        Map<Long, WriteRow> rows = new LinkedHashMap<Long, WriteRow>();
        for (WriteRow row : writes()) rows.put(row.version(), row);
        assertTrue("the INITIAL is a row, flagged", rows.get(455L).initial());
        assertFalse("the store is a write", rows.get(456L).initial());
        assertEquals("at the store's site, as its own kind",
                Endpoint.initialSite(rows.get(456L).endpoint().site()),
                rows.get(455L).endpoint().site());
    }

    /**
     * A refused envelope read out again unchanged is held as its refusal,
     * decoded once: every activation whose read-out states it still files
     * the location as refused and defers the gap with its own read-out
     * ({@code SharedStateCapture#file}).
     */
    @Test
    public void aHeldRefusalIsFiledWithEveryActivation() throws Exception {
        VmExpressionTable.Store store =
                ConcolicRegionRuntime.workloadExpressionStore;
        ConcolicRegionRuntime.workloadExpressionStore =
                new VmExpressionTable.Store(owner -> false);
        SharedStateCapture.resetForTests();
        try {
            String page = ("{'schemaVersion':2,'kind':"
                    + "'SHARED_TRACKED_LOCATIONS','sessionId':1,'locations':["
                    + "{'schemaVersion':2,'kind':'SHARED_FIELD_VERSIONS',"
                    + "'sessionId':1,'selected':false,'location':{"
                    + "'ownerSymRid':10,'slot':40,'locationKind':"
                    + "'INSTANCE_FIELD'},'writerSetComplete':true,'versions':"
                    + "[],'readLogTruncated':false,'reads':[],"
                    + "'serializationTruncated':false}],'locationCount':1,"
                    + "'complete':true,'nextAfterEventId':0,"
                    + "'vmExpressionTable':{'schemaVersion':1,'kind':'"
                    + VmExpressionTable.KIND + "','authority':'"
                    + VmExpressionTable.READ_OUT_AUTHORITY + "','sessionId':1,"
                    + "'sequence':SEQUENCE,'definitionCount':0,"
                    + "'definitions':[]}}").replace('\'', '"');
            @SuppressWarnings("unchecked")
            ThreadLocal<List<Runnable>> filing = (ThreadLocal<List<Runnable>>)
                    Fixtures.get(SharedStateCapture.class, "DECODING");
            int sequence = 0;
            for (String occurrence : new String[] {OCCURRENCE,
                    DN1 + "/region/REGION.16ba41cf#1"}) {
                sequence++;
                ActiveRegion active = placeholderRegion(occurrence);
                List<Runnable> deferred = new ArrayList<Runnable>();
                filing.set(deferred);
                try {
                    call(SharedStateCapture.class, "decodeTrackedLocations",
                            new Class<?>[] {String.class, ActiveRegion.class,
                                    SharedStateCapture.SharedStateReadOut.class},
                            page.replace("SEQUENCE",
                                    String.valueOf(sequence)), active, null);
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
}
