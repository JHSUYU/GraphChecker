package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.focus;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.focusRow;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.rules.TemporaryFolder;

/**
 * A focused replay's verdicts ({@link FocusedReplay}): when it is DECIDED
 * ({@code #refusedAt}) -- at the first refusal after which every obligation
 * it carries is NOT_ADMITTED whatever the run does next, never at a flip --
 * and the FORCE run ({@link ForcedArms}, PIPELINE §7.10): armed only in the
 * declared occurrence; a decision the VM forced off its arm opens the forced
 * world; the forced target on its fatal arm is ADMITTED, one that closed
 * first or took its healthy arm FORCE_DIVERGED.
 */
@RunWith(FreshStatics.class)
public class FocusedReplayTest {
    private static final String FOCUS =
            "hdfs/dn0#epoch0/region/REGION.7c569c3f/ctx:Root:XCEIVER#1/idx:"
                    + "<a.Handler: void handle()>@0";
    private static final String PARENT =
            "hdfs/nn0#epoch0/region/REGION.08ab84c9/ctx:Root:TICK#1/idx:"
                    + "<a.Manager: void tick()>@0";
    private static final String SITE = "<a.Handler: void handle()>#u8";
    private static final String PARENT_SITE = "<a.Manager: void tick()>#u3";
    private static final String INHERITS = "'inheritedFlips':[{"
            + "'focusedOccurrenceId':'" + OccurrenceAddress.parse(PARENT).id()
            + "','siteId':'" + PARENT_SITE + "','ordinal':1,'outcome':true,"
            + "'obligationId':'PARENT'}]";
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String GUARD = METHOD + "#u2";
    private static final String TARGET = METHOD + "#u4";
    private static final String FORCED =
            "solr/n1#epoch0/region/REGION.1/ctx:Root:OVERSEER#1/idx:"
                    + METHOD + "@0";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Before
    @After
    public void reset() {
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        FocusedReplay.resetForTests();
        RecordingWindow.reset();
    }

    /** {@code members} of a flip of {@link #SITE}#{@code ordinal} to true. */
    private static String flip(int ordinal, String members) {
        return focusRow(FOCUS, "'flip':{'siteId':'" + SITE + "','ordinal':"
                + ordinal + ",'outcome':true}" + members);
    }

    private void hand(String... rows) throws Exception {
        reset();
        focus(folder.newFolder().toPath(), rows);
    }

    /** Flip {@link #SITE}#1 at {@link #FOCUS}, holding {@link #PARENT_SITE}
     *  #1 true at {@link #PARENT}. */
    private void handed() throws Exception {
        hand(flip(1, "," + INHERITS));
    }

    private static ObligationResult only(String sessionId) {
        return FocusedReplay.results(sessionId).get(0);
    }

    private static boolean decide(String at, String site, boolean outcome) {
        return FocusedReplay.observeDecision(OccurrenceAddress.parse(at), site,
                1, outcome);
    }

    /**
     * A stall is NOT_ADMITTED for the questions still open, once, naming
     * whether a schedule hold was live: before any flip it decides the
     * replay; after one, the flips taken keep their verdicts and the session
     * stands.  Never the seed's replay, a confirmation's, or one whose
     * workload ended.
     */
    @Test
    public void aStallLeavesTheFlipsTakenAndRefusesTheQuestionsOpen()
            throws Exception {
        String still = "nothing new for 300 s";
        String held = "2 thread(s) held for a turn";
        assertFalse("the seed's replay carries no obligation",
                FocusedReplay.noProgress(still, ""));
        hand(json("{'taskId':'CONFIRM','obligationId':'C','pathId':'p',"
                + "'focused':'" + FOCUS + "','seedSessionId':'seed',"
                + "'flip':null}").toString());
        assertFalse("a confirmation's own rules stand",
                FocusedReplay.noProgress(still, ""));
        handed();
        FocusedReplay.workloadEnded(null, "");
        assertFalse("an ended workload settles",
                FocusedReplay.noProgress(still, ""));

        handed();
        assertTrue("before any flip, a stall decides the replay",
                FocusedReplay.noProgress(still, ""));
        assertFalse("once", FocusedReplay.noProgress(still, held));
        assertFalse(FocusedReplay.stalledAfterFlip());
        ObligationResult refused = only("");
        assertEquals(Verdict.NOT_ADMITTED, refused.verdict());
        String stall = FocusedReplay.REPLAY_NO_PROGRESS + ": " + still
                + "; no schedule hold was live";
        assertEquals(stall + "; the replay ended there and published no"
                + " session (until then: occurrence "
                + OccurrenceAddress.parse(FOCUS).id() + " never reached "
                + SITE + "#1 in this replay; its world did not run: " + stall
                + ")", refused.detail());
        assertFalse("a stall is no fact about the arm", refused.settlesArm());

        handed();
        decide(FOCUS, SITE, true);
        decide(PARENT, PARENT_SITE, true);
        assertTrue("after the flip, a stall ends the replay",
                FocusedReplay.noProgress(still, held));
        assertTrue(FocusedReplay.stalledAfterFlip());
        assertFalse("once", FocusedReplay.noProgress(still, held));
        assertEquals("and decides nothing", "", FocusedReplay.refusedAt());
        assertEquals(Verdict.ADMITTED, only("s").verdict());

        // Asked two flips, one taken: the stall refuses only the other.
        hand(flip(1, ",'obligationId':'OB1'"), flip(2, ",'obligationId':"
                + "'OB2'"));
        decide(FOCUS, SITE, true);
        assertTrue(FocusedReplay.noProgress("nothing new for 300 s",
                "1 thread(s) held for a turn"));
        Map<String, ObligationResult> byId = new HashMap<>();
        FocusedReplay.results("s").forEach(r -> byId.put(r.obligationId(), r));
        assertEquals(Verdict.ADMITTED, byId.get("OB1").verdict());
        ObligationResult open = byId.get("OB2");
        assertEquals(Verdict.NOT_ADMITTED, open.verdict());
        assertEquals("s", open.sessionId());
        assertTrue(open.detail(), open.detail().startsWith(
                FocusedReplay.REPLAY_NO_PROGRESS + ": nothing new for 300"
                        + " s; a schedule hold was live: 1 thread(s) held for"
                        + " a turn; the replay ended there, after another"
                        + " flip it was asked was taken"));
    }

    /** A publication the run ended without admits nothing, and decides
     *  nothing; a decided session withdraws itself, never recreated. */
    @Test
    public void aPublicationTheRunEndedWithoutAdmitsNothing() throws Exception {
        handed();
        decide(FOCUS, SITE, true);
        decide(PARENT, PARENT_SITE, true);
        assertEquals(Verdict.ADMITTED, only("s").verdict());
        FocusedReplay.noteUnsettledPublication(
                "RESULT_PUBLICATION_UNSETTLED: stuck");
        FocusedReplay.noteUnsettledPublication("a second one");
        ObligationResult result = only("s");
        assertEquals(Verdict.NOT_ADMITTED, result.verdict());
        assertEquals("RESULT_PUBLICATION_UNSETTLED: stuck", result.detail());
        assertEquals("", FocusedReplay.refusedAt());

        Path iteration = folder.newFolder().toPath();
        Path worker = folder.newFolder().toPath();
        SessionPublisher session = SessionPublisher.of(iteration, "S.cut");
        Path dir = iteration.resolve("sessions").resolve("S.cut");
        assertTrue(Files.isRegularFile(dir.resolve("manifest.json")));
        assertEquals("", session.withdrawTo(worker.resolve("refused")));
        assertFalse("out of the corpus", Files.exists(dir));
        assertTrue(Files.isRegularFile(
                worker.resolve("refused/S.cut/manifest.json")));
        session.obligationResult(ObligationResult.of("OB",
                Verdict.NOT_ADMITTED, "S.cut", "late"));
        assertFalse("a row after the close recreates nothing",
                Files.exists(dir));
    }

    /**
     * WORLD_REFUTED: an open decider arm's flip whose replay ran its world
     * faithfully and never entered the flip's occurrence refutes that world
     * -- all four conditions or a plain NOT_ADMITTED: (a) every assignment
     * minted, no prefix abandoned, every inherited flip taken, (b) no hold
     * gave way, (c) the world acted in the window before any slot was given
     * up, (d) the workload ended by itself.  Never any other flip.
     */
    @Test
    public void aFaithfulRunThatNeverEnteredAnOpenArmRefutesItsWorld()
            throws Exception {
        Throwable thrown = new java.io.IOException("Unable to close file");
        Object[][] rows = {
            // open arm, ended, entered, steps, refuted
            {true, true, false, "act", true},
            {true, true, false, "act depart", true},
            {true, true, false, "", false},
            {true, true, false, "still", false},
            {true, true, false, "early", false},
            {true, true, false, "answer", true},
            {true, true, false, "depart act", false},
            {true, true, false, "inherit act", false},
            {true, true, false, "inherit take act", true},
            {true, false, false, "act", false},
            {true, true, true, "act", false},
            {false, true, false, "act", false}};
        for (Object[] row : rows) {
            String steps = (String) row[3];
            hand(flip(1, (steps.contains("inherit") ? "," + INHERITS : "")
                    + ((Boolean) row[0] ? ",'openArm':true" : "")));
            RecordingWindow.open();
            FocusedReplay.obligationIds();
            if ((Boolean) row[2]) {
                FocusedReplay.entered(OccurrenceAddress.parse(FOCUS));
            }
            for (String step : steps.split(" ")) {
                if ("act".equals(step)) FocusedReplay.planted("r", true);
                if ("still".equals(step)) FocusedReplay.planted("r", false);
                if ("answer".equals(step)) FocusedReplay.answered(true);
                if ("depart".equals(step)) FocusedReplay.departed("7 (x)");
                if ("take".equals(step)) decide(PARENT, PARENT_SITE, true);
                if ("early".equals(step)) {
                    RecordingWindow.reset();
                    FocusedReplay.planted("r", true);
                    RecordingWindow.open();
                }
            }
            if ((Boolean) row[1]) {
                FocusedReplay.workloadEnded(thrown, getClass().getName());
            }
            ObligationResult result = only("s");
            String what = Arrays.toString(row) + " " + result.detail();
            assertEquals(what, Verdict.NOT_ADMITTED, result.verdict());
            assertEquals(what, row[4], result.refutation() != null);
            assertEquals(what, row[4],
                    result.detail().startsWith("WORLD_REFUTED: "));
            if (result.refutation() == null) continue;
            assertEquals(what, 4, result.refutation().conditions().size());
            assertEquals("java.io.IOException: Unable to close file",
                    result.refutation().exception());
            assertTrue(result.refutation().testFrame(), result.refutation()
                    .testFrame().contains("FocusedReplayTest"));
        }
    }

    /**
     * A TEST OVER ({@code ConcolicResultPublisher#stall}): a replay whose
     * window closed and whose teardown then stood ends as at the workload's
     * own end -- nothing decided, no stall rewriting a verdict, and a
     * faithful world never entered still refuted, its (d) naming the stand;
     * once.  Inside the window the same stand is the stall, which decides a
     * replay no flip of which was taken.
     */
    @Test
    public void aTeardownThatStandsEndsTheRunAsTheWorkloadsEnd()
            throws Exception {
        String still = "nothing new for 300 s";
        for (boolean over : new boolean[] {false, true}) {
            hand(flip(1, ",'openArm':true"));
            RecordingWindow.open();
            FocusedReplay.obligationIds();
            FocusedReplay.planted("r", true);
            if (over) RecordingWindow.close();
            assertEquals(over ? ConcolicResultPublisher.Conclusion.TEST_OVER
                    : ConcolicResultPublisher.Conclusion.AT_NO_PROGRESS,
                    ConcolicResultPublisher.stall(still));
            assertEquals("once", null, ConcolicResultPublisher.stall(still));
            ObligationResult result = only("s");
            assertEquals(Verdict.NOT_ADMITTED, result.verdict());
            assertEquals(result.detail(), over,
                    result.detail().startsWith("WORLD_REFUTED: "));
            if (!over) {
                assertTrue(result.detail(), result.detail().startsWith(
                        FocusedReplay.REPLAY_NO_PROGRESS + ": " + still));
                continue;
            }
            assertEquals("", FocusedReplay.refusedAt());
            assertFalse(FocusedReplay.stalledAfterFlip());
            assertEquals("(d) the workload's test was over: its window"
                    + " closed, and its teardown then made " + still,
                    result.refutation().conditions().get(3));
        }
    }

    /** The declared occurrence's activation, its table forcing the guard
     *  and the target to jump; {@code guards} and {@code force} more of
     *  its {@code targetBranch}. */
    private static ActiveRegion declared(long token, String at,
                                         String guards, String force) {
        ActiveRegion active = Fixtures.region(token, Fixtures.taskRow(
                "n1#epoch0", "REGION.1@n1#epoch0#1", METHOD, false,
                "'goalKind':'TARGET_REACH_CLOSURE','branchMethods':['" + METHOD
                        + "'],'targetBranch':{'siteId':'" + TARGET
                        + "','occurrence':1,'requiredOutcome':true,'guards':["
                        + guards + "],'force':[" + force + "{'siteId':'"
                        + GUARD + "','arm':true},{'siteId':'" + TARGET
                        + "','arm':true}]}"));
        active.d3Address = OccurrenceAddress.parse(at);
        return active;
    }

    private static ActiveRegion declared(long token) {
        return declared(token, FORCED, "", "");
    }
}
