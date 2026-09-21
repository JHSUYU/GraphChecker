package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
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
 * The mint is the unit: what it publishes, and what it owes.
 *
 * <p>A manual mint published no {@code recordedValue}, so lane VM12's
 * {@code DelegationKey.expiryDate} was refused RECORDED_ROOT_VALUE_UNSTATED.
 * The other half of the unit is the occurrence a mint can be placed at: a
 * model rewrites the recorded execution, so it applies only where the
 * registry can place this mint at the address the plan named.</p>
 */
public class ManualMintStatesItsValueTest {
    @Rule
    public final TemporaryFolder session = new TemporaryFolder();

    private static final String METHOD = "<a.B: void run()>";
    private static final String MANUAL_REGION = "REGION.aaa1cfd7";
    private static final String MANUAL_SOURCE = "hdfs-17899/nn0#epoch0";
    private static final String MINT_PHASE = "SOURCE_PHASE.0b2b2a3d";
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
    /** The tick frame every occurrence of this fixture stands on. */
    private static final String TICK_FRAME = "<a.Manager: void tick()>@0";
    /** The occurrence a focused replay runs symbolic, and its task. */
    private static final String FOCUSED_TASK = "TASK.FOCUSED";
    private static final String FOCUSED_ADDRESS =
            NODE + "#epoch1/region/" + REGION + "/ctx:Root:CLIENT#1/idx:"
                    + TICK_FRAME;
    /** And one that merely runs alongside it, concretely. */
    private static final String CONCRETE_TASK = "TASK.CONCRETE";
    private static final String CONCRETE_ADDRESS =
            NODE + "#epoch1/region/" + REGION + "/ctx:Root:CLIENT#2/idx:"
                    + TICK_FRAME;

    private final List<Long> opened = new ArrayList<>();
    private String occurrenceId = PLANNED;
    /** The activation the last {@link #manualRow} published into. */
    private ActiveRegion lastManualRegion;

    @Before
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void releaseRegions() {
        opened.forEach(ConcolicRegionRuntime.ACTIVE::remove);
        opened.clear();
        RuntimeTraceContext.resetForTests();
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        RowRuntime.resetForTests();
    }

    /**
     * A mint publishes the value it read -- and every mint publishes one.
     *
     * <p>A clock is no exception.  The seed replay IS the reference
     * execution the composer's clock deltas are relative to, so the instant
     * THIS run read is what both members state; the row used to publish the
     * PLAN's instant as {@code recordedValue}, which made every delta
     * relative to an execution nobody ran.</p>
     *
     * <p>INVARIANT 8, and it holds in a FOCUSED replay too.  A mint that
     * planted the wave's value used to state nothing, on the ground that a
     * counterfactual is not a recording -- but the value a mint states is
     * the one it read BEFORE the plant, which is the recording's own, and
     * the session's valuation is stated by the focus row.  Suppressing it
     * published the one root each obligation moves with an empty {@code
     * recordedValue}: hdfs-17960's two focused sessions state {@code
     * roots.jsonl seq=121 field=recordedValue
     * HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=} and hdfs-11741's six state
     * one empty CLOCK row each, which IMPORT refuses as BLOCKING and the
     * composer cannot resolve a relative domain against.</p>
     */
    @Test
    public void aMintStatesTheValueItRead() throws Exception {
        JsonObject recorded = manualRow(action("PORT.now"), "1789358343989");
        assertEquals("MANUAL_SYMBOLIC_INPUT_OBSERVATION",
                recorded.get("kind").getAsString());
        assertTrue("the mint states what it read",
                recorded.has("recordedValue"));
        assertEquals("1789358343989",
                recorded.get("recordedValue").getAsString());
        assertEquals("J", recorded.get("javaType").getAsString());
        assertTrue(recorded.get("minted").getAsBoolean());

        JsonObject clock = manualRow(clockAction("PORT.now"), "1789358344655");
        assertTrue("the mint states the clock the case declared",
                clock.get("clock").getAsBoolean());
        assertEquals("this execution's own instant, which the window is "
                        + "centred on", "1789358344655",
                clock.get("observedValue").getAsString());
        assertEquals("and the same instant as what this run recorded: the "
                        + "seed replay is the reference execution",
                clock.get("observedValue").getAsString(),
                clock.get("recordedValue").getAsString());
        assertEquals("the plan's instant is stated by nothing here",
                7L, clock.get("eventSeq").getAsLong());

        // What the wave asks of a clock is a SKEW, and the mint applies it
        // to the instant THIS run read: a model is an instant of the
        // recording's window, and writing it absolutely would rewind the
        // clock to an epoch no replay reads.  An ordinary root keeps its
        // absolute value, and both come out of one decision.
        focusRow("{\"taskId\":\"TASK.1\",\"obligationId\":\"OBL.1\","
                + "\"pathId\":\"PATH.1\",\"seedSessionId\":\"s-seed\","
                + "\"focused\":\"" + PLANNED_ADDRESS + "\","
                + "\"focusedOccurrenceId\":\"" + address(PLANNED_ADDRESS)
                .id() + "\","
                + "\"flip\":{\"siteId\":\"Arrival#u8\",\"ordinal\":1,"
                + "\"outcome\":true},"
                + "\"rootAssignments\":{\"CASE.SERIAL\":\"12\","
                + "\"CASE.ORDERED\":\"false\"},"
                + "\"clockDeltas\":{\"CASE.NOW\":\"-4200\"},"
                + "\"rootMints\":{\"CASE.SERIAL\":\"" + MINT_ADDRESS
                + "\"},"
                + "\"answers\":{},\"unproducible\":[]}");

        // R4a: THE FLIP IS ADDRESSED AT ONE OCCURRENCE.  (siteId, ordinal)
        // alone is not an address: an ordinal restarts per activation, and
        // 11741's four nodes run one BlockTokenSecretManager, so
        // removeExpiredKeys#u15#1 happens on nn0, dn0, dn1 and the balancer
        // and whichever ran first decided the obligation (6 of 11
        // campaign-#3 flips landed on the wrong node).  The occurrence's
        // own focused gate does not narrow it either: every member of the
        // focused set answers it, the assigned root's MINT included -- and
        // MINT_ADDRESS is exactly such a member here.
        FocusedReplay.observeDecision(address(MINT_ADDRESS),
                "Arrival#u8", 1, true);
        FocusedReplay.observeDecision(address(ALONGSIDE_ADDRESS),
                "Arrival#u8", 1, true);
        assertEquals("a decision at another occurrence settles nothing, "
                        + "whatever its site and ordinal", 1,
                FocusedReplay.results("s-flip").size());
        assertEquals(edu.uva.liftlab.graphchecker.contract.Verdict
                        .NOT_ADMITTED,
                FocusedReplay.results("s-flip").get(0).verdict());
        assertTrue("and the refusal names the occurrence that never "
                        + "reached it: "
                        + FocusedReplay.results("s-flip").get(0).detail(),
                FocusedReplay.results("s-flip").get(0).detail()
                        .contains(address(PLANNED_ADDRESS).id()));
        // THE SAME JOIN, ON THE TERMINAL SIDE.  The flip's question is
        // asked of the occurrence the obligation names it at, and of no
        // other -- and the FOCUSED SET is wider than that occurrence: the
        // MINT of every assigned root is in it, and a mint usually finishes
        // before the flip has run (17960 obligation 793875fb482a10a4 flips
        // applyEditLogOp@8/deleteSnapshot and mints its root at @7).  Asked
        // occurrence-blind, "is the prefix complete" is false at the mint's
        // terminal, judgeFinishedOccurrence abandons the mint, and every
        // row that occurrence published -- the root mint row included --
        // goes with it: hdfs-17960's 793875fb482a10a4-4b39d011 lost 42
        // decision rows and its whole roots.jsonl that way.
        assertTrue("the mint of an assigned root is in the focused set",
                FocusedReplay.focused(address(MINT_ADDRESS)));
        assertTrue("and no flip is addressed at it, so its terminal answers"
                        + " no obligation and is never abandoned for one",
                FocusedReplay.complete(address(MINT_ADDRESS)));
        assertFalse("the occurrence the flip IS addressed at has not taken"
                        + " it yet",
                FocusedReplay.complete(address(PLANNED_ADDRESS)));
        assertTrue("an occurrence outside the focused set is asked nothing",
                FocusedReplay.complete(address(ALONGSIDE_ADDRESS)));

        FocusedReplay.observeDecision(address(PLANNED_ADDRESS),
                "Arrival#u8", 1, true);
        assertTrue("and once it has, its own terminal is complete",
                FocusedReplay.complete(address(PLANNED_ADDRESS)));

        // AND THE SESSION HAS TO CARRY THE EVIDENCE.  "The focused prefix
        // reproduced" is a claim about the rows a later stage reads, so the
        // flip alone does not admit: a root the wave moves whose mint row
        // this session never published leaves the valuation the replay ran
        // stated nowhere.  hdfs-17960 on 39bedd768 published exactly that
        // -- session 793875fb482a10a4-4b39d011, a 0-byte roots.jsonl, a
        // REPLAY_PREFIX_UNMATCHED gap, and obligation_result.jsonl reading
        // ADMITTED -- and the composer would have read it as a disjunct.
        assertEquals("a flip whose roots the session states no mint for is "
                        + "not admitted: "
                        + FocusedReplay.results("s-flip").get(0).detail(),
                edu.uva.liftlab.graphchecker.contract.Verdict.NOT_ADMITTED,
                FocusedReplay.results("s-flip").get(0).verdict());
        assertTrue("and the refusal names the roots whose rows are missing,"
                        + " the clock's skew among them: "
                        + FocusedReplay.results("s-flip").get(0).detail(),
                FocusedReplay.results("s-flip").get(0).detail()
                        .contains("CASE.NOW"));
        publishedMint("CASE.SERIAL");
        publishedMint("CASE.ORDERED");
        assertEquals("one root still unstated is still not admitted",
                edu.uva.liftlab.graphchecker.contract.Verdict.NOT_ADMITTED,
                FocusedReplay.results("s-flip").get(0).verdict());
        publishedMint("CASE.NOW");
        assertEquals("the obligation's own occurrence taking the flipped "
                        + "arm, over a session that states every mint it "
                        + "moved, is what admits it",
                edu.uva.liftlab.graphchecker.contract.Verdict.ADMITTED,
                FocusedReplay.results("s-flip").get(0).verdict());

        // A prefix this replay was abandoned on takes the abandoned
        // occurrence's whole row set with it, so it un-admits the same way.
        FocusedReplay.noteUnansweredTask("ROOT_NEVER_EXECUTED: another "
                + "task of this replay, which settles nothing here");
        assertEquals("an unanswered task that is not a prefix abandonment "
                        + "settles nothing",
                edu.uva.liftlab.graphchecker.contract.Verdict.ADMITTED,
                FocusedReplay.results("s-flip").get(0).verdict());
        FocusedReplay.noteUnansweredTask("REPLAY_PREFIX_UNMATCHED: the "
                + "focused occurrence did not take the decision its "
                + "obligation flips: ");
        assertEquals("a replay whose prefix was abandoned publishes no "
                        + "admission over the rows that went with it",
                edu.uva.liftlab.graphchecker.contract.Verdict.NOT_ADMITTED,
                FocusedReplay.results("s-flip").get(0).verdict());
        assertTrue("and the gap is the reason it states: "
                        + FocusedReplay.results("s-flip").get(0).detail(),
                FocusedReplay.results("s-flip").get(0).detail()
                        .startsWith("REPLAY_PREFIX_UNMATCHED"));
        unmatchedPrefixCleared();
        ActiveRegion focused = manualRegion();
        focused.d3Address = edu.uva.liftlab.graphchecker.contract
                .OccurrenceAddress.parse(PLANNED_ADDRESS);
        assertEquals("the skew moves this replay's own reading",
                "1789358340455",
                focusedRootValue(focused, "CASE.NOW",
                        Long.valueOf(1789358344655L)));
        assertEquals("a value is a value", "12",
                focusedRootValue(focused, "CASE.SERIAL", Long.valueOf(7L)));
        assertEquals("nothing was asked of this root", "",
                focusedRootValue(focused, "CASE.OTHER", Long.valueOf(7L)));

        // THE FOCUSED SET holds the MINT of every root the obligation
        // assigns, not only the occurrence the flip is about: an assignment
        // is planted where the run mints it, and 11741's SERIAL_NO is
        // minted in nn0's rotation while the flip is the balancer's.  A
        // focused replay is one run of the whole workload, so both run
        // symbolic in it.
        ActiveRegion minting = manualRegion();
        minting.d3Address = edu.uva.liftlab.graphchecker.contract
                .OccurrenceAddress.parse(MINT_ADDRESS);
        assertEquals("the value is planted at the mint the row names", "12",
                focusedRootValue(minting, "CASE.SERIAL", Long.valueOf(7L)));
        ActiveRegion alongside = manualRegion();
        alongside.d3Address = edu.uva.liftlab.graphchecker.contract
                .OccurrenceAddress.parse(ALONGSIDE_ADDRESS);
        assertEquals("and nowhere else: a region that merely runs alongside "
                        + "would make the run state what the obligation "
                        + "never asked", "",
                focusedRootValue(alongside, "CASE.SERIAL",
                        Long.valueOf(7L)));

        // A FIELD mint asks the same one decision.  It did not: a declared
        // INTEGRAL cell minted through symbolizeField/materializeField
        // published what the recording read, whatever the obligation
        // assigned, and 11741 session 869a1f0e285913ad-6f59cb84 states
        // SERIAL_NO = 182907 under an obligation assigning 182910.
        KeyManager keys = new KeyManager();
        keys.serialNo = 182907;
        keys.ordered = true;
        keys.now = 1789358344655L;
        // A model rewrites the recorded execution, so it is written only at
        // a mint this run can place at the node and epoch the plan names --
        // the same rule the configured source's assignment goes through.
        RuntimeTraceContext.registerSource(keys,
                new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs-17899/nn0",
                        0L));
        // R3: ONE RULE OVER BOTH SPELLINGS of what a wave asks of a root.
        // A clock is asked for as a DELTA and ASSIGNMENT_UNPLANTED covered
        // the absolute assignments only -- and a clock is the root eleven
        // of hdfs-11741 campaign #3's twelve obligations ask about, six of
        // them stating a delta no mint of their replay ever planted, every
        // one of them silently.
        java.util.Map<String, String> owed =
                new java.util.LinkedHashMap<String, String>();
        owed.put("CASE.SERIAL", "12");
        owed.put("CASE.ORDERED", "false");
        owed.put("CASE.NOW", "-4200");
        assertEquals("what the wave asked of a root is unplanted until a "
                        + "mint plants it, a clock's skew included", owed,
                FocusedReplay.unplantedAssignments());

        // INVARIANT 8 AT A FOCUSED MINT, for every kind the cases declare.
        // Two questions with two answers: the plant writes the session's
        // valuation into the cell, and the row states the value the region
        // OBSERVED there, which the mint read before the write.  The row
        // used to state nothing at all whenever a plant followed, so the
        // one root the obligation moves was the one root with no reading --
        // 17960's MARKER at seq=121 and one CLOCK per 11741 focused
        // session, both BLOCKING at IMPORT.
        assertEquals("a focused INTEGRAL mint states the value it read",
                "182907", RootMint.fieldMintRecordedValue(focused,
                        new SymbolizeAction(action("CASE.SERIAL")),
                        keys, SERIAL_FIELD, "I", Integer.valueOf(182907)));
        assertEquals("and the region reads the wave's value back",
                12, keys.serialNo);
        assertEquals("a focused MARKER mint states the polarity it read",
                "true", RootMint.fieldMintRecordedValue(focused,
                        new SymbolizeAction(action("CASE.ORDERED")),
                        keys, ORDERED_FIELD, "Z", Boolean.TRUE));
        assertFalse("and the region reads the moved polarity back",
                keys.ordered);
        assertEquals("a focused CLOCK mint states the instant it read, "
                        + "which is what the composer's deltas are "
                        + "relative to", "1789358344655",
                RootMint.fieldMintRecordedValue(focused,
                        new SymbolizeAction(clockAction("CASE.NOW")),
                        keys, NOW_FIELD, "J", Long.valueOf(1789358344655L)));
        assertEquals("and the region reads its own instant plus the skew",
                1789358340455L, keys.now);
        assertEquals("so the replay owes no ASSIGNMENT_UNPLANTED refusal "
                        + "for any of them", Collections.emptyMap(),
                FocusedReplay.unplantedAssignments());

        // A root the wave said nothing about keeps its reading, and states
        // it: the recording is what every delta is relative to.
        keys.serialNo = 182907;
        assertEquals("a mint that planted nothing states what it read",
                "182907", RootMint.fieldMintRecordedValue(
                        focused, new SymbolizeAction(
                                action("CASE.OTHER")),
                        keys, SERIAL_FIELD, "I", Integer.valueOf(182907)));
        assertEquals("and reads its own value back", 182907, keys.serialNo);

        // AND A BLANK IS NAMED.  No producer hands one now, so a root row
        // left without a reading carries a value the runtime has no scalar
        // spelling for -- and the session says which root, rather than
        // publishing the row IMPORT will refuse with nothing beside it.
        openSession();
        JsonObject unspellable =
                manualRow(clockAction("PORT.unspellable"), "");
        assertFalse("the row writer states no blank",
                unspellable.has("recordedValue"));
        RowPlaceholderMint.roots(lastManualRegion, address(PLANNED_ADDRESS));
        assertEquals(GapKind.UNSTATED_VALUE, gap().kind());
        assertTrue("a root with no centre for its domain blocks",
                gap().blocking());
        assertEquals("named by the root it is about", "PORT.unspellable",
                gap().subject());
        assertTrue(gap().detail(),
                gap().detail().contains("states no value it observed"));

        // THE FLIPS THIS REPLAY INHERITED.  An obligation cut from a
        // focused session's path extends that session's world, and the
        // decisions that session was held to are part of it: 11741's
        // witness is dn1's expiry compare flipped a second time on a
        // refresh path that exists only because nn0's rotation was flipped
        // first.  So the focus row carries the parent's flips, this replay
        // is held to each of them at its own occurrence, and the ONE result
        // row it publishes -- run_engine.sh reads exactly one verdict per
        // worker -- is the primary obligation's.
        inheritedFlipRow();
        assertEquals("one obligation is answered, whatever it inherited", 1,
                FocusedReplay.obligationIds().size());
        assertTrue("an inherited flip's occurrence runs symbolic, so its "
                        + "mints plant and its decisions are published",
                FocusedReplay.focused(address(ALONGSIDE_ADDRESS)));
        assertTrue("and it is never abandoned: only the primary flip's own "
                        + "occurrence can complete that flip",
                FocusedReplay.complete(address(ALONGSIDE_ADDRESS)));
        FocusedReplay.observeDecision(address(PLANNED_ADDRESS),
                "Arrival#u8", 1, true);
        assertEquals("the primary flip alone does not admit: the world it "
                        + "inherited has to hold too: "
                        + FocusedReplay.results("s-nested").get(0).detail(),
                edu.uva.liftlab.graphchecker.contract.Verdict.NOT_ADMITTED,
                FocusedReplay.results("s-nested").get(0).verdict());
        assertTrue("and the row names the flip it never reached: "
                        + FocusedReplay.results("s-nested").get(0).detail(),
                FocusedReplay.results("s-nested").get(0).detail()
                        .contains("Rotate#u5#1")
                        && FocusedReplay.results("s-nested").get(0).detail()
                        .contains("OBL.parent"));
        FocusedReplay.observeDecision(address(ALONGSIDE_ADDRESS),
                "Rotate#u5", 1, true);
        assertEquals("the inherited flip taken at its own occurrence is "
                        + "what lets the obligation be admitted: "
                        + FocusedReplay.results("s-nested").get(0).detail(),
                edu.uva.liftlab.graphchecker.contract.Verdict.ADMITTED,
                FocusedReplay.results("s-nested").get(0).verdict());

        // And the other arm of it un-admits the primary obligation, naming
        // which inherited flip was contradicted: this replay ran in a world
        // other than the one its path was cut from, so the path it recorded
        // is not the path the next wave would cut from it.
        inheritedFlipRow();
        FocusedReplay.observeDecision(address(PLANNED_ADDRESS),
                "Arrival#u8", 1, true);
        FocusedReplay.observeDecision(address(ALONGSIDE_ADDRESS),
                "Rotate#u5", 1, false);
        assertEquals(edu.uva.liftlab.graphchecker.contract.Verdict
                        .NOT_ADMITTED,
                FocusedReplay.results("s-nested").get(0).verdict());
        assertTrue("and the refusal says it was the INHERITED flip: "
                        + FocusedReplay.results("s-nested").get(0).detail(),
                FocusedReplay.results("s-nested").get(0).detail()
                        .contains("INHERITED")
                        && FocusedReplay.results("s-nested").get(0).detail()
                        .contains("Rotate#u5#1"));
    }

    /**
     * One focus row that carries a flip inherited from the session its
     * path was cut from, addressed at another occurrence entirely.
     */
    private void inheritedFlipRow() throws Exception {
        focusRow("{\"taskId\":\"TASK.2\",\"obligationId\":\"OBL.2\","
                + "\"pathId\":\"PATH.2\",\"seedSessionId\":\"s-seed\","
                + "\"focused\":\"" + PLANNED_ADDRESS + "\","
                + "\"focusedOccurrenceId\":\"" + address(PLANNED_ADDRESS)
                .id() + "\","
                + "\"flip\":{\"siteId\":\"Arrival#u8\",\"ordinal\":1,"
                + "\"outcome\":true},"
                + "\"rootAssignments\":{},\"clockDeltas\":{},"
                + "\"rootMints\":{},\"answers\":{},"
                + "\"inheritedFlips\":[{\"focusedOccurrenceId\":\""
                + address(ALONGSIDE_ADDRESS).id() + "\","
                + "\"siteId\":\"Rotate#u5\",\"ordinal\":1,"
                + "\"outcome\":true,\"obligationId\":\"OBL.parent\"}],"
                + "\"unproducible\":[]}");
    }

    /** One declared cell of each kind a case declares a root at. */
    private static final class KeyManager {
        private int serialNo;
        private boolean ordered;
        private long now;
    }

    private static final String KEY_MANAGER =
            "<edu.uva.liftlab.graphchecker.runtime.ManualMintStatesItsValue"
                    + "Test$KeyManager: ";
    private static final String SERIAL_FIELD =
            KEY_MANAGER + "int serialNo>";
    private static final String ORDERED_FIELD =
            KEY_MANAGER + "boolean ordered>";
    private static final String NOW_FIELD = KEY_MANAGER + "long now>";

    /** The rendered v3 address the focus row names and the region carries. */
    private static final String PLANNED_ADDRESS =
            "hdfs/nn0#epoch1/region/" + MANUAL_REGION
                    + "/ctx:Root:CLIENT#1/idx:";
    /**
     * Another occurrence entirely: where the recording mints the root the
     * flip depends on.
     *
     * <p>11741's shape -- {@code HDFS.BLOCK_KEY.SERIAL_NO} is minted in
     * nn0's key rotation and read by the balancer, so the occurrence the
     * flip is about mints nothing.</p>
     */
    private static final String MINT_ADDRESS =
            "hdfs/dn1#epoch0/region/REGION.53092d3e/ctx:Root:CLIENT#1/idx:";
    /** And one the wave named nowhere, which merely runs alongside. */
    private static final String ALONGSIDE_ADDRESS =
            "hdfs/dn0#epoch0/region/REGION.094a8e3d/ctx:Root:CLIENT#1/idx:";

    /** The session states one root mint row, as RowRuntime publishes one. */
    private static void publishedMint(String rootId) {
        FocusedReplay.mintPublished(rootId);
    }

    /** Puts the one account back the way the rest of this test found it. */
    private static void unmatchedPrefixCleared() throws Exception {
        Field prefix = FocusedReplay.class
                .getDeclaredField("unmatchedPrefix");
        prefix.setAccessible(true);
        prefix.set(null, "");
    }

    /** One rendered address, as the contract parses one. */
    private static edu.uva.liftlab.graphchecker.contract.OccurrenceAddress
            address(String rendered) {
        return edu.uva.liftlab.graphchecker.contract.OccurrenceAddress
                .parse(rendered);
    }

    /** Writes one focus row where this replay looks for it. */
    private void focusRow(String row) throws Exception {
        java.nio.file.Path dir = java.nio.file.Files.createTempDirectory(
                "causynth-focus");
        java.nio.file.Files.write(dir.resolve(ObligationDir.FOCUSED_TASK),
                (row + System.lineSeparator()).getBytes("UTF-8"));
        System.setProperty(FocusedReplay.PLAN_PROPERTY,
                dir.resolve("execution_task_plan.jsonl").toString());
        FocusedReplay.resetForTests();
    }

    /** The one decision every mint takes about the wave's value. */
    private static String focusedRootValue(
            ActiveRegion active, String rootId,
            Object observed) throws Exception {
        Method value = RootMint.class.getDeclaredMethod(
                "focusedRootValue",
                ActiveRegion.class, String.class,
                Object.class);
        value.setAccessible(true);
        return (String) value.invoke(null, active, rootId, observed);
    }

    /**
     * The wave's value is written only at a mint this run can place.
     *
     * <p>A configured source names one mint SITE reached once per node
     * lifecycle, so the epoch tells two mints of it apart and an assignment
     * at the wrong epoch rewrites a value the wave said nothing about.  A
     * write demands positive evidence, so an unattributed mint keeps the
     * recorded value with a named gap.</p>
     */
    @Test
    public void aModelIsAppliedOnlyAtAMintThisRunCanPlace() throws Exception {
        openSession();
        ActiveRegion active =
                phaseRegion(NODE + "#epoch1", PLANNED);
        Object manager = new Object();
        // Epoch 0 is registered and nothing restarted yet, so the registry
        // places this mint at epoch 0 -- not the epoch the plan addresses.
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));
        assertFalse("a mint of another epoch is not written",
                placeable(active, manager));
        assertEquals(GapKind.EPOCH_UNMATCHED, gap().kind());
        assertTrue("a mint the wave's value was not written at blocks",
                gap().blocking());

        // The restart advances the same logical source.
        RuntimeTraceContext.restartSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));
        assertTrue("the epoch-1 mint is placeable",
                placeable(active, manager));
        ActiveRegion orphan =
                phaseRegion(NODE + "#epoch1", PLANNED);
        assertFalse("nothing places this mint, so nothing rewrites it",
                placeable(orphan, new Object()));
        assertEquals(GapKind.MINT_UNATTRIBUTED, gap().kind());
        String detail = gap().detail();
        assertTrue(detail, detail.contains("attributes this mint to no node"));
        assertTrue(detail, detail.contains("recorded value stands"));

        ActiveRegion epochless =
                phaseRegion("workload/unregistered",
                        "workload/unregistered/region/" + REGION + "#1");
        assertTrue("nothing to place, nothing to refuse",
                placeable(epochless, new Object()));
        assertEquals("and files nothing", GapKind.MINT_UNATTRIBUTED,
                gap().kind());
    }

    /**
     * One site is one variable: every occurrence that reaches it is modelled.
     *
     * <p>A site reached by six regions twice each has twelve identities;
     * applying a flip at one of them leaves every other execution on the
     * recorded value.  A configured source is declared by site, so a flip
     * of it is a flip everywhere it is read.</p>
     *
     * <p>And the catalog is not a budget.  It used to be: the plan listed the
     * executions the RECORDING made, the runtime counted the reads a REPLAY
     * made against that size, and read n+1 was refused
     * {@code DECLARATION_MISSING ... exceeds the frozen phase catalog size n}
     * -- two of them on the hdfs-17960 flip replays, whose second read of
     * the marker was the wave's own re-read of the value it had just
     * written.  So the published occurrence row states no ordinal at all,
     * and a row set of any size names one variable.</p>
     */
    @Test
    public void everyOccurrenceOfOneSiteAnswersOneValuation()
            throws Exception {
        Object manager = new Object();
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));

        String second = NODE + "#epoch1/region/" + REGION + "#2";
        assertEquals("one site, one variable, whatever reached it",
                phaseId(PLANNED), phaseId(second));

        assertTrue("the first occurrence is placeable",
                placeable(phaseRegion(NODE + "#epoch1", PLANNED), manager));
        assertTrue("and so is the second, on the same valuation",
                placeable(phaseRegion(NODE + "#epoch1", second), manager));

        // The row says WHERE the recording observed the site, and nothing
        // about which read of it a replay is making.
        JsonObject row = phaseTask(NODE + "#epoch1", PLANNED)
                .getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .get(0).getAsJsonObject();
        assertFalse("no per-occurrence ordinal is published",
                row.has("baselineOrdinal"));
        assertEquals("and the symbol is the site's", 1,
                oneSymbolPerSite(row).size());
    }

    /**
     * A configured source mints where its occurrence runs SYMBOLIC.
     *
     * <p>README SS9 rule 1: a concretely run region contributes literals,
     * never freedom.  The hook fires wherever its site runs -- occurrences
     * do not nest, so everything executed synchronously below an
     * occurrence belongs to it -- and the mint used to be made on whatever
     * activation was on the thread.  On hdfs-11741 that is {@code
     * HDFS.BLOCK_KEY.EXPIRY_DATE{,.CURRENT,.RETIRED}} and {@code
     * SERIAL_NO}: where {@code updateKeys} ran concrete the expiry field
     * was a literal and three fresh INTEGRAL roots were minted beside it,
     * which decouples the expiry from the clock it is computed from and
     * left twelve wave-1 obligations {@code ASSIGNMENT_UNMINTABLE} on
     * roots no replay could plant.</p>
     */
    @Test
    public void aHookMintsOnlyWhereItsOccurrenceRunsSymbolic()
            throws Exception {
        openSession();
        CausynthTraceRecorder.setRecordingStartedForTests(true);
        ActiveRegion concrete = addressed(open(taskAt(CONCRETE_TASK,
                CONCRETE_ADDRESS)), CONCRETE_ADDRESS);
        ActiveRegion focused = addressed(open(taskAt(FOCUSED_TASK,
                FOCUSED_ADDRESS)), FOCUSED_ADDRESS);

        // THE SEED FOCUSES NOTHING, so every planned occurrence of it runs
        // symbolic and every mint it makes stands: this rule changes no
        // recording.
        FocusedReplay.resetForTests();
        assertTrue("a replay handed no focus row mints at every planned "
                        + "occurrence",
                ActiveRegion.mintsUnderSymbolicOccurrence(concrete,
                        SOURCE_ID, FIELD));
        assertTrue("and says nothing about it", gaps().isEmpty());

        focusRow("{\"taskId\":\"" + FOCUSED_TASK + "\",\"obligationId\":"
                + "\"OBL.9\",\"pathId\":\"PATH.9\",\"seedSessionId\":"
                + "\"s-seed\",\"focused\":\"" + FOCUSED_ADDRESS + "\","
                + "\"focusedOccurrenceId\":\"" + address(FOCUSED_ADDRESS)
                .id() + "\","
                + "\"flip\":{\"siteId\":\"Arrival#u8\",\"ordinal\":1,"
                + "\"outcome\":true},\"rootAssignments\":{},"
                + "\"clockDeltas\":{},\"rootMints\":{},"
                + "\"answers\":{},\"unproducible\":[]}");

        long invocation = CausynthTraceRecorder.beginCall(0L, PHASE_METHOD,
                UNIT, PHASE_METHOD, new Object());
        try {
            // A HOOK UNDER NO OCCURRENCE AT ALL.  Nothing to mint on and
            // nothing to attribute to, so it mints nothing and says which
            // source it left concrete.
            assertFalse("a hook outside every occurrence mints nothing",
                    ConcolicRegionRuntime.symbolizeConfiguredSourceField(
                            SOURCE_ID, new Object(), FIELD));
            assertEquals(GapKind.DECLARATION_MISSING, gap().kind());
            assertFalse("nothing was rewritten, so nothing blocks",
                    gap().blocking());
            assertEquals("named by the root it is about", SOURCE_ID,
                    gap().subject());
            assertTrue(gap().detail(), gap().detail().contains("none"));

            // AND UNDER ONE THIS REPLAY RUNS CONCRETELY.  The row names the
            // occurrence that was active; nothing is minted and nothing is
            // planted, so the region reads its own literal back.
            entered(concrete);
            assertFalse("a concretely run occurrence mints no root",
                    ConcolicRegionRuntime.symbolizeConfiguredSourceField(
                            SOURCE_ID, new Object(), FIELD));
            left(concrete);
            assertTrue("and publishes no mint row to plant into",
                    symbolizedRows(concrete).isEmpty());
            assertTrue(gap().detail(),
                    gap().detail().contains(CONCRETE_ADDRESS));
            assertEquals("one row per occurrence, however often the hook "
                    + "fires", 2, gaps().size());

            // THE FOCUSED OCCURRENCE MINTS AS BEFORE.  Both halves of the
            // hook: a concrete value mints this site's one symbol, and a
            // field that arrived carrying an expression of its own mints
            // none and says {@code reused}.
            assertTrue("the occurrence this replay runs symbolic mints",
                    ActiveRegion.mintsUnderSymbolicOccurrence(focused,
                            SOURCE_ID, FIELD));
            RootMint.SourceSiteEntry entry =
                    focused.observeConfiguredSourceEntry(SOURCE_ID, FIELD);
            assertNotNull("at its own declared site", entry);
            assertEquals("and files nothing to explain itself", 2,
                    gaps().size());
            String symbol = ConfiguredSourcePhaseContract
                    .engineLabelForPhase(phaseId(FOCUSED_ADDRESS), SOURCE_ID);
            focused.recordConfiguredSourceMint(entry, SOURCE_ID, FIELD,
                    symbol, symbolExpression(symbol), false, "true");
            RowPlaceholderMint.roots(focused, address(FOCUSED_ADDRESS));
            List<edu.uva.liftlab.graphchecker.contract.RootMintRow> minted =
                    roots();
            assertEquals("the concrete value is this site's root", 1,
                    minted.size());
            assertEquals(SOURCE_ID, minted.get(0).rootId());
            assertEquals(symbol, minted.get(0).symbol());
            assertEquals("true", minted.get(0).recordedValue());

            ActiveRegion again = addressed(open(taskAt(FOCUSED_TASK,
                    FOCUSED_ADDRESS)), FOCUSED_ADDRESS);
            RootMint.SourceSiteEntry reused =
                    again.observeConfiguredSourceEntry(SOURCE_ID, FIELD);
            assertNotNull("a symbolic arrival is the same declared site",
                    reused);
            again.recordConfiguredSourceMint(reused, SOURCE_ID, FIELD,
                    symbol, symbolExpression(symbol), true, "true");
            assertTrue("the row states what the region read back",
                    symbolizedRows(again).get(0).get("reused")
                            .getAsBoolean());
            RowPlaceholderMint.roots(again, address(FOCUSED_ADDRESS));
            assertEquals("one symbol, one root: a reused read mints none",
                    1, roots().size());
        } finally {
            CausynthTraceRecorder.endCall(invocation, null, "");
        }
    }

    /** One expression naming one VM symbol, as a mint publishes it. */
    private static JsonObject symbolExpression(String symbol) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "Z");
        expression.addProperty("_exp", symbol);
        return expression;
    }

    /** The activation, carrying the v3 address its rows are keyed by. */
    private static ActiveRegion addressed(ActiveRegion active,
                                          String rendered) {
        active.d3Address = address(rendered);
        return active;
    }

    /** Enters one activation on this thread's region stack. */
    private static void entered(ActiveRegion active) throws Exception {
        tokens().push(Long.valueOf(active.token));
    }

    /** And leaves it, the way the region hook's exit does. */
    private static void left(ActiveRegion active) throws Exception {
        tokens().remove(Long.valueOf(active.token));
    }

    @SuppressWarnings("unchecked")
    private static java.util.Deque<Long> tokens() throws Exception {
        Field stack = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        stack.setAccessible(true);
        return ((ThreadLocal<java.util.Deque<Long>>) stack.get(null)).get();
    }

    /** The root mint rows this session published. */
    private List<edu.uva.liftlab.graphchecker.contract.RootMintRow> roots()
            throws Exception {
        return RowCodec.readAll(SessionDir.of(
                        session.getRoot().toPath().resolve("iteration-0000"),
                        RowRuntime.sessionId()).roots(),
                RowCodec::readRootMint);
    }

    /** Every gap ROW this session published. */
    private List<GapRow> gaps() throws Exception {
        return RowCodec.readAll(SessionDir.of(
                        session.getRoot().toPath().resolve("iteration-0000"),
                        RowRuntime.sessionId()).gaps(),
                RowCodec::readGap);
    }

    /** Every VM label a catalog of one site asks for: exactly one. */
    private static java.util.Set<String> oneSymbolPerSite(JsonObject row) {
        JsonArray catalog = new JsonArray();
        catalog.add(row.deepCopy());
        JsonObject later = row.deepCopy();
        // A second execution of the SAME site, as the plan records it.
        later.addProperty("eventSeq", row.get("eventSeq").getAsLong() + 1L);
        later.addProperty("invocationId",
                row.get("invocationId").getAsLong() + 1L);
        catalog.add(later);
        java.util.Set<String> labels = new java.util.LinkedHashSet<String>();
        for (ConfiguredSourcePhaseContract.Occurrence phase
                : ConfiguredSourcePhaseContract.occurrencesOf(catalog)) {
            labels.add(ConfiguredSourcePhaseContract.engineLabelForPhase(
                    phase.phaseId(), phase.sourceId()));
        }
        return labels;
    }

    /** The published row, as the runtime writes it for one manual mint. */
    private JsonObject manualRow(JsonObject encoded, String recordedValue)
            throws Exception {
        ActiveRegion active = manualRegion();
        lastManualRegion = active;
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "J");
        expression.addProperty("_exp",
                "M_J_field_REGION.aaa1cfd7.in.f30dbb22_java/lang/Long");

        Method record = ActiveRegion.class
                .getDeclaredMethod("recordManualSymbolization",
                        SymbolizeAction.class,
                        String.class, List.class, String.class,
                        com.google.gson.JsonElement.class, boolean.class,
                        boolean.class, String.class);
        record.setAccessible(true);
        record.invoke(active,
                new SymbolizeAction(encoded),
                "PORT.now", Collections.emptyList(),
                "<org.apache.hadoop.security.token.delegation.DelegationKey:"
                        + " long expiryDate>", expression, true, false,
                recordedValue);

        List<JsonObject> published = symbolizedRows(active);
        assertEquals(1, published.size());
        return published.get(0);
    }

    /** Whether an activation that minted (or reused) the root owes it. */
    @SuppressWarnings("unchecked")
    private static List<JsonObject> symbolizedRows(
            ActiveRegion active) throws Exception {
        Field rows = ActiveRegion.class
                .getDeclaredField("symbolizedRows");
        rows.setAccessible(true);
        return (List<JsonObject>) rows.get(active);
    }

    /** The same action, as the plan carries a declared clock read. */
    private static JsonObject clockAction(String symbol) {
        JsonObject encoded = action(symbol);
        encoded.addProperty("rootKind", "CALL_RETURN");
        encoded.addProperty("clock", true);
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", "1789358343989");
        encoded.addProperty("eventSeq", 7L);
        return encoded;
    }

    /** One frozen SYMBOLIC action, as the plan carries it. */
    private static JsonObject action(String symbol) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", symbol);
        encoded.addProperty("actionDigest", "DIGEST.1");
        encoded.addProperty("cell", "<org.apache.hadoop.util.Timer: long "
                + "now()>.return");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        return encoded;
    }

    private ActiveRegion manualRegion() throws Exception {
        return open(task(MANUAL_REGION, MANUAL_SOURCE,
                MANUAL_SOURCE + "/region/" + MANUAL_REGION + "#1"));
    }

    private ActiveRegion phaseRegion(String sourceKey,
                                                           String occurrence)
            throws Exception {
        this.occurrenceId = occurrence;
        return open(phaseTask(sourceKey, occurrence));
    }

    private ActiveRegion open(JsonObject encoded)
            throws Exception {
        ConcolicTaskPlan.RuntimeTask runtime =
                new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded));
        long token = 970001L + opened.size();
        ActiveRegion active =
                new ActiveRegion(token, runtime, null,
                        Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        opened.add(token);
        return active;
    }

    /** Whether this run can place this mint where the plan addresses it. */
    private static boolean placeable(
            ActiveRegion active, Object mintOwner)
            throws Exception {
        Method method = active.getClass().getDeclaredMethod(
                "mintIsPlaceable", Object.class);
        method.setAccessible(true);
        return (Boolean) method.invoke(active, mintOwner);
    }

    /** The last gap ROW this session published: one gap vocabulary. */
    private GapRow gap() throws Exception {
        List<GapRow> rows = gaps();
        return rows.isEmpty() ? null : rows.get(rows.size() - 1);
    }

    /** Opens the session the refusals are published into. */
    private void openSession() throws Exception {
        java.nio.file.Path results = session.getRoot().toPath()
                .resolve("iteration-0000").resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        java.nio.file.Files.createDirectories(results.getParent());
        RowRuntime.configure(results);
    }

    private static String phaseId(String occurrenceId) {
        return ConfiguredSourcePhaseContract.phaseId(SOURCE_ID,
                SiteId.of(PHASE_METHOD, UNIT),
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
    }

    /** One executable task row, as the plan carries it. */
    private static JsonObject task(String regionId, String sourceKey,
                                   String occurrenceId) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", regionId);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", sourceKey);
        encoded.addProperty("occurrenceId", occurrenceId);
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
        anchor.addProperty("sourceKey", sourceKey);
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

    /** The same row, as a named task of one addressed occurrence. */
    private static JsonObject taskAt(String taskId, String occurrence) {
        JsonObject encoded = phaseTask(NODE + "#epoch1", occurrence);
        encoded.addProperty("taskId", taskId);
        return encoded;
    }

    /** The same row, declaring one configured-source phase and its model. */
    private static JsonObject phaseTask(String sourceKey, String occurrence) {
        JsonObject encoded = task(REGION, sourceKey, occurrence);
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH, SOURCE_ID,
                FIELD, PHASE_METHOD, UNIT));
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(declarations)
                        .get(0),
                occurrence, 11L, 7L, 3L, PHASE_METHOD,
                Arrays.asList(7L, 5L)));
        encoded.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);

        JsonObject model = new JsonObject();
        model.addProperty("modelAssignmentKey", "MODEL.1");
        model.addProperty("inputSymbol",
                "SOURCE_PHASE:" + phaseId(occurrence));
        model.addProperty("valueType", "BOOLEAN");
        model.addProperty("value", "false");
        model.addProperty("configuredSourcePhaseId", phaseId(occurrence));
        model.addProperty("configuredSourceId", SOURCE_ID);
        model.addProperty("configuredSourceFieldSignature", FIELD);
        JsonArray models = new JsonArray();
        models.add(model);
        encoded.add("modelAssignments", models);
        return encoded;
    }
}
