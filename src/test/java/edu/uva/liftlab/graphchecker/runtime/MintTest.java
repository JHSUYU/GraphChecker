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
import static org.junit.Assert.assertNull;
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
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.RowInvariants;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Validity;
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
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
    private static final String PLANNED =
            NODE + "#epoch1/region/" + REGION + "#1";
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
    private static final String CLOCK_CELL = "INSTANCE_FIELD/217#24";
    private static final long MINT_VERSION = 1155L;
    private static final String CLOCK_LABEL =
            "REGION.ba3902cd.in.559a1724.occ.e36a3c48";
    private static final String CLOCK_SYMBOL =
            "M_J_field_" + CLOCK_LABEL + "_java/lang/Long";
    private static final String INSTANT = "1789965233929";
    private static final long SKEW = 3_600_000L;

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

    private ActiveRegion phaseRegion(String source, String occurrence) {
        return open(phased(task(REGION, source, occurrence), occurrence,
                true));
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

    private List<ReadRow> reads() throws Exception {
        return SessionReader.read(Fixtures.session(root())).reads();
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
     * An assignment is UNPLANTED only where its mint ran: a root whose mint
     * never came was read by nothing (hdfs-17967 path B reported five
     * blockers under obligations NOT_ADMITTED for exactly that reason); a
     * mint running where the row does not name it is owed.
     */
    @Test
    public void anAssignmentWhoseMintNeverRanIsNotUnplanted()
            throws Exception {
        focus(flipAt(PLANNED_ADDRESS, "Arrival#u8", true,
                ",'rootAssignments':{'CASE.SERIAL':'12'},'clockDeltas':"
                        + "{'CASE.NOW':'-4200'},'rootMints':{'CASE.SERIAL':'"
                        + MINT_ADDRESS + "'}"));
        assertEquals(Collections.emptyMap(),
                FocusedReplay.unplantedAssignments());
        assertEquals(Verdict.NOT_ADMITTED, result("s-unreached").verdict());
        assertEquals("", rootValue(at(manualRegion(), ALONGSIDE_ADDRESS),
                "CASE.SERIAL", 7L));
        assertEquals(Collections.singletonMap("CASE.SERIAL", "12"),
                FocusedReplay.unplantedAssignments());
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
     * The wave's value is written only at a mint this run can place: a
     * configured source names one site reached once per node lifecycle, so
     * the epoch tells two mints apart and an unattributed mint keeps the
     * recorded value, named.  One site is one variable whatever reaches it,
     * and the catalog is no budget: the published row states no ordinal
     * (17960's re-read of the marker was once refused as read n+1).
     */
    @Test
    public void aModelIsAppliedOnlyAtAMintThisRunCanPlace() throws Exception {
        Fixtures.openSession(root());
        ActiveRegion active = phaseRegion(NODE + "#epoch1", PLANNED);
        Object manager = new Object();
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));
        assertFalse("a mint of another epoch is not written",
                placeable(active, manager));
        assertEquals(GapKind.EPOCH_UNMATCHED, gap().kind());
        assertTrue(gap().blocking());
        RuntimeTraceContext.restartSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));
        assertTrue(placeable(active, manager));
        assertTrue("a second occurrence of its site, one valuation",
                placeable(phaseRegion(NODE + "#epoch1", NODE + "#epoch1"
                        + "/region/" + REGION + "#2"), manager));
        JsonObject row = phased(task(REGION, NODE + "#epoch1", PLANNED),
                PLANNED, true).getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD).get(0)
                .getAsJsonObject();
        assertFalse(row.has("baselineOrdinal"));
        JsonArray catalog = new JsonArray();
        catalog.add(row.deepCopy());
        JsonObject later = row.deepCopy();
        later.addProperty("eventSeq", row.get("eventSeq").getAsLong() + 1L);
        later.addProperty("invocationId",
                row.get("invocationId").getAsLong() + 1L);
        catalog.add(later);
        Set<String> labels = new LinkedHashSet<String>();
        for (ConfiguredSourcePhaseContract.Occurrence phase
                : ConfiguredSourcePhaseContract.occurrencesOf(catalog)) {
            labels.add(ConfiguredSourcePhaseContract.engineLabel(
                    phase.sourceId()));
        }
        assertEquals("the symbol is the site's", 1, labels.size());
        assertFalse("nothing places this mint",
                placeable(phaseRegion(NODE + "#epoch1", PLANNED),
                        new Object()));
        assertEquals(GapKind.MINT_UNATTRIBUTED, gap().kind());
        assertTrue(gap().detail().contains("attributes this mint to no node"));
        assertTrue(gap().detail().contains("recorded value stands"));
        assertTrue("nothing to place, nothing to refuse", placeable(
                phaseRegion("workload/unregistered", "workload/unregistered"
                        + "/region/" + REGION + "#1"), new Object()));
        assertEquals("and files nothing", GapKind.MINT_UNATTRIBUTED,
                gap().kind());
    }

    private static boolean placeable(ActiveRegion active, Object owner)
            throws Exception {
        return (Boolean) call(active, "mintIsPlaceable",
                new Class<?>[] {Object.class}, owner);
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

    /**
     * A read at a site its occurrence's catalog lacks: a configuration's
     * field already holds the world's value, so it mints nothing, named
     * DIAGNOSTIC; a tree hook's plant is per site, so its site blocks.
     */
    @Test
    public void aReadOutsideItsOccurrencesCatalogBlocksOnlyForAHook()
            throws Exception {
        Fixtures.openSession(root());
        String seventh = NODE + "#epoch1/region/" + REGION + "#7";
        JsonObject configTask = task(REGION, NODE + "#epoch1", seventh);
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.configDeclaration(
                "CONFIG:k", FIELD, PHASE_METHOD, UNIT, "0", "4",
                Validity.ANY));
        JsonArray reads = new JsonArray();
        reads.add(ConfiguredSourcePhaseContract.configOccurrence(
                ConfiguredSourcePhaseContract.declarationsOf(declarations)
                        .get(0), seventh, 11L, FIELD, Arrays.asList(7L)));
        configTask.add(ConfiguredSourcePhaseContract.PLAN_FIELD, reads);
        configTask.addProperty("taskId", "TASK.CONFIG");
        Object before = Fixtures.get(ConcolicTaskPlan.class, "plan");
        Fixtures.set(ConcolicTaskPlan.class, "plan", new ConcolicTaskPlan(
                null, Arrays.asList(Fixtures.runtimeTask(configTask),
                Fixtures.runtimeTask(phased(task(REGION, NODE + "#epoch1",
                        PLANNED), PLANNED, true)))));
        ActiveRegion elsewhere = open(task(REGION, NODE + "#epoch1",
                NODE + "#epoch1/region/" + REGION + "#9"));
        long invocation = CausynthTraceRecorder.beginCall(0L, PHASE_METHOD,
                UNIT + 5, PHASE_METHOD, new Object(), true);
        try {
            Object[][] rows = {
                {"CONFIG:k", false, "world's value"},
                {SOURCE_ID, true, "outside the frozen phase catalog"}};
            for (Object[] row : rows) {
                assertNull(row[0] + " mints nothing",
                        elsewhere.observeConfiguredSourceEntry(
                                (String) row[0], FIELD));
                assertEquals(GapKind.DECLARATION_MISSING, gap().kind());
                assertEquals((String) row[0], row[1], gap().blocking());
                assertTrue(gap().detail().contains((String) row[2]));
            }
        } finally {
            CausynthTraceRecorder.endCall(invocation, null, "");
            Fixtures.set(ConcolicTaskPlan.class, "plan", before);
        }
    }

    /**
     * A configuration's one symbol per key per JVM holds ONE value: a read
     * at another is read concretely and named.  Its domain is stated whole
     * or not at all; its validation clips the static hull while the value
     * read passes it, and is dropped, named, where it fails.
     */
    @Test
    public void aConfigurationSymbolHoldsOneValue() throws Exception {
        Fixtures.openSession(root());
        Object[][] reads = {
            {"the first mint fixes the value", "CONFIG:k", "5", true, 0},
            {"a second read shares the symbol", "CONFIG:k", "5", true, 0},
            {"another value is pinned, named", "CONFIG:k", "7", false, 1},
            {"once", "CONFIG:k", "7", false, 1},
            {"another key is another symbol", "CONFIG:j", "7", true, 1}};
        for (Object[] read : reads) {
            assertEquals((String) read[0], read[3],
                    RootMint.configurationAgrees((String) read[1],
                            (String) read[2], "a.B#u1"));
            assertEquals((String) read[0], read[4], gaps().size());
        }
        assertEquals(GapKind.UNSTATED_VALUE, gap().kind());
        assertFalse(gap().blocking());
        assertEquals("CONFIG:k", gap().subject());
        assertTrue(gap().detail(), gap().detail().contains("ran at 7")
                && gap().detail().contains("stands for 5"));
        Validity atLeastSix = Validity.of(java.math.BigInteger.valueOf(6),
                null, "a.B#u3");
        Object[][] domains = {
            // why, min, max, validity, value read, domain, its validation
            // stated, gaps
            {"a boolean or no anchor states none", "", "", Validity.ANY, "5",
                "-", false, 1},
            {"the static hull", "0", "10", Validity.ANY, "5", "0..10", false,
                1},
            {"widened to the value read", "0", "10", Validity.ANY, "12",
                "0..12", false, 1},
            {"half a domain states none, named", "0", "", Validity.ANY, "5",
                "-", false, 2},
            {"no integer read states none, named", "0", "10", Validity.ANY,
                "", "-", false, 3},
            {"a passed validation clips the hull", "4", "10", atLeastSix,
                "7", "6..10", true, 3},
            {"a failed one clips nothing, named", "4", "10", atLeastSix, "5",
                "4..10", false, 4}};
        for (Object[] domain : domains) {
            JsonObject row = json("{'sourceId':'CONFIG:k'}");
            ActiveRegion.configDomain(row, (String) domain[1],
                    (String) domain[2], (Validity) domain[3],
                    (String) domain[4]);
            assertEquals((String) domain[0], domain[5], row.has("domainMin")
                    ? row.get("domainMin").getAsString() + ".."
                    + row.get("domainMax").getAsString() : "-");
            assertEquals((String) domain[0], domain[6],
                    row.has(Validity.MIN));
            assertEquals((String) domain[0], domain[7], gaps().size());
        }
        assertTrue(gap().detail(), gap().detail().contains("(5) lies outside"
                + " what its validation admits [6, ] by a.B#u3"));
    }

    /**
     * A demanded door's marker called at an invocation its task plans no
     * input for -- a call only a flipped world made -- runs concretely and is
     * named, so GROW can plan it (PIPELINE §7.8); another input's later call
     * keeps its rule, unnamed.
     */
    @Test
    public void anUnplannedMarkerInvocationIsNamed() throws Exception {
        Object[][] rows = {
            // the action's marker, the row its call #1 names
            {"FAULT:TIMED_WAIT:AWAIT", "TASK.1 SYM.marker#1"},
            {"", ""},
            {"FAULT:ZOOKEEPER:WRITE", ""}};
        for (Object[] row : rows) {
            RowRuntime.resetForTests();
            Fixtures.openSession(root());
            JsonObject action = Fixtures.with(action("SYM.marker"),
                    "'bindingMode':'LOCAL_DEFINITION','method':'" + METHOD
                            + "','unitIndex':" + UNIT + ",'local':'$z0',"
                            + "'javaType':'Z','marker':'" + row[0] + "',"
                            + "'replayOccurrence':2");
            JsonObject task = task(MANUAL_REGION, MANUAL_SOURCE,
                    MANUAL_SOURCE + "/region/" + MANUAL_REGION + "#1");
            task.getAsJsonArray("inputActions").add(action);
            ActiveRegion active = open(task);
            tokens().push(active.token);
            try {
                assertEquals(Boolean.FALSE, RootMint.materializePrimitive(
                        METHOD, UNIT, "$z0", Boolean.FALSE));
                if (row[1].equals("")) {
                    assertNull("named only for a demanded door's marker: "
                            + row[0], gap());
                } else {
                    assertEquals(GapKind.UNPLANNED_INPUT, gap().kind());
                    assertFalse(gap().blocking());
                    assertEquals(row[1], gap().subject());
                }
            } finally {
                tokens().remove(active.token);
            }
        }
    }

    /**
     * A replay's clock readings, as {@link RootMint} runs them: a node's
     * clock runs on from its jumps in the RECORDING's order, one clock at a
     * time ({@link NodeClocks}), and a mint states how far its clock ran off
     * the host.
     */
    @Test
    public void aReadingRunsOnFromTheJumpBeforeItInTheRecordingsOrder() {
        long hour = 3_600_000L;
        // Planted in this order, the later place first, as two threads may:
        // an hour at the reading of event 200, a minute at event 100.
        assertEquals("a plant states its skew off the host", hour,
                RootMint.clockSkew("nn0", clock(200L, Clock.WALL), 10L,
                        10L + hour, true));
        assertEquals(60_000L, RootMint.clockSkew("nn0",
                clock(100L, Clock.WALL), 5L, 5L + 60_000L, true));
        assertEquals("a plant at no recorded event moves its reading alone",
                60_000L, RootMint.clockSkew("dn1", clock(0L, Clock.WALL), 5L,
                        5L + 60_000L, true));
        assertEquals("and one whose clock states no JVM clock", 60_000L,
                RootMint.clockSkew("dn1", clock(400L, ""), 5L, 5L + 60_000L,
                        true));
        Object[][] readings = {
            // node, place, source, host reading, instant it runs at, why
            {"nn0", 50L, Clock.WALL, 1000L, 1000L, "before every jump"},
            {"nn0", 150L, Clock.WALL, 1000L, 61_000L,
                "between: the earlier jump, planted last"},
            {"nn0", 300L, Clock.WALL, 1000L, 1000L + hour,
                "after both: the later jump"},
            {"nn0", 300L, Clock.MONOTONIC, 1000L, 1000L,
                "the node's monotonic clock is another"},
            {"dn1", 300L, Clock.WALL, 1000L, 1000L, "another node's clock"},
            {"dn1", 500L, "", 1000L, 1000L, "a clock stating no source"},
            {"nn0", 0L, Clock.WALL, 1000L, 1000L, "no recorded event"}};
        for (Object[] reading : readings) {
            assertEquals((String) reading[5], reading[4],
                    RootMint.clockReading((String) reading[0],
                            clock((Long) reading[1], (String) reading[2]),
                            reading[3]));
        }
        assertEquals("a reading nothing planted states its skew, files no "
                + "jump", hour, RootMint.clockSkew("nn0", clock(300L,
                Clock.WALL), 1000L, 1000L + hour, false));
        assertEquals(1000L + hour, RootMint.clockReading("nn0",
                clock(300L, Clock.WALL), 1000L));
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

    /** One declared CLOCK mint, its label filed before the store. */
    private static void clockMint(ActiveRegion active) {
        RowRuntime.declaredMintLabel(CLOCK_LABEL);
        active.recordManualSymbolization(new SymbolizeAction(clockAction(
                "PORT.now", INSTANT, true)), "PORT.now",
                Collections.<String>emptyList(),
                "<org.apache.hadoop.util.Timer: long now()>.return",
                symbol(CLOCK_SYMBOL, "J"), true, false, INSTANT, SKEW);
    }

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

    /** A ReadFromExpression at {@code readEventId} of the version {@code
     *  observed} states ({@code fieldVersionId} 456) of {@code slot}. */
    private static JsonObject readFrom(String sort, long readEventId,
                                       String more, long slot,
                                       JsonObject observed, JsonObject value) {
        JsonObject read = json("{'_type':'ReadFromExpression','_java_type':'"
                + sort + "','readEventId':" + readEventId + more
                + ",'location':{'ownerSymRid':10,'slot':" + slot + ","
                + "'locationKind':'INSTANCE_FIELD'}}");
        read.add("observedVersion", observed);
        read.add("concreteValue", value);
        return read;
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
     * A version stored outside every region has no write row to join, so
     * the read of it states what it returned (VM f11) or the composer has
     * nothing to pin it to (commit-gs v74: the GS an IPC handler stored,
     * read at the third target).
     */
    @Test
    public void aReadOfAStoreOutsideEveryRegionStatesWhatItReturned()
            throws Exception {
        JsonObject stored = constant("J", 1003L);
        JsonObject stamp = record("INSTANCE_FIELD/10#40", version(456L,
                stored));
        array(stamp, "reads").add(loggedAt(json("{'readEventId':510,"
                + "'regionEnterEventId':900}")));
        JsonObject observed = json("{'fieldVersionId':456,'versionKind':"
                + "'WRITE'}");
        observed.add("expression", stored);
        Map<String, JsonObject> records = new LinkedHashMap<>();
        records.put("INSTANCE_FIELD/10#40", stamp);
        records.put("INSTANCE_FIELD/77#24", record("INSTANCE_FIELD/77#24",
                loggedAt(version(901L, readFrom("J", 510L, "", 40L, observed,
                        stored)))));
        published(records);
        ReadRow stated = null;
        for (ReadRow row : reads()) {
            if (row.observedVersion() == 456L) stated = row;
        }
        assertNotNull("the read of the outside store is a row", stated);
        assertEquals("1003", stated.concreteValue());
    }

    /**
     * EVERY OBSERVED READ_SITE ACCESS IS A ROW (SYMBOL-SCOPE §5.2), whether
     * or not a published expression holds its value: hdfs-adhoc-45 tests
     * {@code state == State.IN_SEGMENT}, which records no condition, so the
     * closure never saw the read.  A read in a READ_SITE's method is a row
     * of the version its plan chose, one an expression states too is one
     * row, a read in any other method is left to the expressions.
     */
    @Test
    public void anObservedReadSiteAccessIsARowThoughNoExpressionHoldsIt()
            throws Exception {
        JsonObject state = symbol("M_L'a/B$State'_5", "a/B$State");
        JsonObject log = record("INSTANCE_FIELD/10#80", loggedAt(version(
                456L, state)));
        array(log, "reads");
        log.getAsJsonObject("envelope").addProperty("readLogTruncated",
                false);
        // 457 in the READ_SITE's method, 458 in another, 459 in it and in a
        // write's expression too.
        for (Object[] each : new Object[][] {{457L, "isSegmentOpen"},
                {458L, "other"}, {459L, "isSegmentOpen"}}) {
            array(log, "reads").add(json("{'readEventId':" + each[0] + ","
                    + "'regionEnterEventId':900,'site':{'className':'a/B',"
                    + "'methodName':'" + each[1] + "','methodDescriptor':"
                    + "'()Z','bci':1},'observedVersion':{'fieldVersionId':456,"
                    + "'versionKind':'WRITE'},'observedExact':true,"
                    + "'writerSetComplete':true,'_java_type':'L'}"));
        }
        JsonObject observed = json("{'fieldVersionId':456}");
        observed.add("expression", state);
        Map<String, JsonObject> records = new LinkedHashMap<>();
        records.put("INSTANCE_FIELD/10#80", log);
        records.put("INSTANCE_FIELD/77#24", record("INSTANCE_FIELD/77#24",
                loggedAt(version(901L, readFrom("L", 459L,
                        ",'observedExact':true", 80L, observed, state)))));
        published(records, json("{'kind':'STATIC_SCOPE_SITE','role':"
                + "'READ_SITE','vmSite':'a.B#isSegmentOpen()Z'}"));
        Map<Long, ReadRow> rows = new LinkedHashMap<Long, ReadRow>();
        for (ReadRow row : reads()) {
            assertNull("one row per read event", rows.put(row.seq(), row));
        }
        assertEquals(Arrays.asList(457L, 459L), new ArrayList<Long>(
                new TreeSet<Long>(rows.keySet())));
        ReadRow site = rows.get(457L);
        assertEquals("the version its plan chose", 456L,
                site.observedVersion());
        assertEquals("L", site.javaType());
        assertEquals("an exact read returned its version's identity",
                "M_L'a/B$State'_5", site.concreteValue());
        assertTrue(site.endpoint().site(), site.endpoint().site()
                .startsWith("a.B#isSegmentOpen()Z#"));
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
            String page = ("{'schemaVersion':1,'kind':"
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
                    + VmExpressionTable.AUTHORITY + "','sessionId':1,"
                    + "'definitionCount':0,'definitions':[]}}")
                    .replace('\'', '"');
            @SuppressWarnings("unchecked")
            ThreadLocal<List<Runnable>> filing = (ThreadLocal<List<Runnable>>)
                    Fixtures.get(SharedStateCapture.class, "DECODING");
            for (String occurrence : new String[] {OCCURRENCE,
                    DN1 + "/region/REGION.16ba41cf#1"}) {
                ActiveRegion active = placeholderRegion(occurrence);
                List<Runnable> deferred = new ArrayList<Runnable>();
                filing.set(deferred);
                try {
                    call(SharedStateCapture.class, "decodeTrackedLocations",
                            new Class<?>[] {String.class, ActiveRegion.class},
                            page, active);
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
