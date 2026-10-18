package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.focus;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.focusRow;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
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
public class FocusedReplayTest {
    private static final String FOCUS =
            "hdfs/dn0#epoch0/region/REGION.7c569c3f/ctx:Root:XCEIVER#1/idx:"
                    + "<a.Handler: void handle()>@0";
    private static final String PARENT =
            "hdfs/nn0#epoch0/region/REGION.08ab84c9/ctx:Root:TICK#1/idx:"
                    + "<a.Manager: void tick()>@0";
    private static final String SITE = "<a.Handler: void handle()>#u8";
    private static final String PARENT_SITE = "<a.Manager: void tick()>#u3";
    private static final String UNMATCHED = "REPLAY_PREFIX_UNMATCHED: the"
            + " activation contradicts its obligation's prefix: ";
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
        RowRuntime.resetForTests();
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

    @Test
    public void theRecordedArmDecidesTheReplayOnceItsPrefixIsAbandoned()
            throws Exception {
        assertFalse("a replay handed no focus row carries no obligation",
                FocusedReplay.noteUnansweredTask(UNMATCHED + "x"));
        handed();
        OccurrenceAddress focus = OccurrenceAddress.parse(FOCUS);
        assertFalse("the wrong arm files a refusal; the occurrence it "
                + "abandons is what decides", decide(FOCUS, SITE, false));
        String refusal = FocusedReplay.refusal(focus);
        assertTrue(refusal, refusal.startsWith("wrong decision at " + SITE));
        assertEquals("", FocusedReplay.refusedAt());
        assertFalse("another reason word decides nothing",
                FocusedReplay.noteUnansweredTask("AT_WITNESS: late"));
        assertTrue(FocusedReplay.noteUnansweredTask(UNMATCHED + refusal));
        assertFalse("decided once",
                FocusedReplay.noteUnansweredTask(UNMATCHED + "again"));
        assertEquals(UNMATCHED + refusal, FocusedReplay.refusedAt());
        ObligationResult result = only("s");
        assertEquals(Verdict.NOT_ADMITTED, result.verdict());
        assertEquals("the session's own row keeps its id", "s",
                result.sessionId());
        assertEquals(refusal + "; the replay ended at this refusal and"
                + " published no session", result.detail());

        // A flip taken leaves a session later stages read whole; the world
        // a path was cut from not happening decides the replay.
        handed();
        assertFalse(decide(FOCUS, SITE, true));
        assertEquals("", FocusedReplay.refusedAt());
        assertTrue("a contradicted inherited flip decides all",
                decide(PARENT, PARENT_SITE, false));
        result = only("");
        assertEquals(Verdict.NOT_ADMITTED, result.verdict());
        assertTrue(result.detail(), result.detail().startsWith(
                "wrong decision at " + PARENT_SITE)
                && result.detail().contains("INHERITED")
                && result.detail().endsWith("published no session"));
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

    @Test
    public void aWindowsCloseEndsTheRunAsTheWorkloadsEnd() throws Exception {
        String still = "nothing new for 300 s";
        Object[][] rows = {
            // closed, concluded before, refuted, its exception
            {false, false, false, ""},
            {true, false, true, "java.io.IOException: boom"},
            {true, true, false, ""}};
        java.lang.reflect.Field concluded = ConcolicResultPublisher.class
                .getDeclaredField("concluded");
        concluded.setAccessible(true);
        for (Object[] row : rows) {
            hand(flip(1, ",'openArm':true"));
            RecordingWindow.open();
            FocusedReplay.obligationIds();
            FocusedReplay.planted("r", true);
            boolean closed = (Boolean) row[0];
            if ((Boolean) row[1]) {
                concluded.set(null,
                        ConcolicResultPublisher.Conclusion.AT_WITNESS);
            }
            try {
                if (closed) {
                    RecordingWindow.close();
                    FocusedReplay.windowClosed(new java.io.IOException(
                            "boom"), getClass().getName());
                }
                if (!(Boolean) row[1]) {
                    assertEquals(closed ? null
                            : ConcolicResultPublisher.Conclusion
                            .AT_NO_PROGRESS,
                            ConcolicResultPublisher.stall(still));
                }
                ObligationResult result = only("s");
                String what = Arrays.toString(row) + " " + result.detail();
                assertEquals(what, Verdict.NOT_ADMITTED, result.verdict());
                assertEquals(what, row[2], result.refutation() != null);
                if (result.refutation() != null) {
                    assertEquals(what, row[3],
                            result.refutation().exception());
                }
            } finally {
                concluded.set(null, null);
            }
        }
    }

    /**
     * A PAIRING FLIP's replay takes it where its read observed the version
     * it asks ({@code FocusedReplay#viewRead}); another version refuses it
     * by name, the version seen; a read of another endpoint decides nothing.
     */
    @Test
    public void aPairingFlipIsTakenWhereItsReadObservedTheVersionItAsks()
            throws Exception {
        OccurrenceAddress focus = OccurrenceAddress.parse(FOCUS);
        Endpoint read = Endpoint.of(focus, "SOLR_ZK#VIEWED:|aliases.json#VIEW",
                ExecutionIndex.empty(), 0);
        Endpoint other = Endpoint.of(focus, "SOLR_ZK#VIEWED:|other.json#VIEW",
                ExecutionIndex.empty(), 0);
        for (long seen : new long[] {1L, 2L}) {
            hand(focusRow(FOCUS, "'flip':{'siteId':'PAIRING:"
                    + Confirmation.id(read) + "','ordinal':2,'outcome':true}"));
            FocusedReplay.viewRead(other, 7L);
            assertTrue("another read decides nothing",
                    FocusedReplay.refusal(focus).isEmpty());
            FocusedReplay.viewRead(read, seen);
            // Version 1 is ordinal 2 (an ordinal is 1-based).
            if (seen == 1L) {
                assertTrue("taken", FocusedReplay.complete(focus));
            } else {
                String refusal = FocusedReplay.refusal(focus);
                assertTrue(refusal, refusal.startsWith("PAIRING_UNTAKEN:")
                        && refusal.contains("observed version 2"));
            }
        }
    }

    /** Hands the replay a FORCE focus row at {@link #FORCED}. */
    private void forcing() throws Exception {
        hand(focusRow(FORCED, "'taskId':'TASK.1','obligationId':'FORCE.1',"
                + "'declaredTarget':'" + FORCED + "','force':true"));
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

    /** One decision mapping as BranchObservation states it. */
    private static JsonObject mapping(String site, long event,
                                      boolean outcome) {
        return BranchObservation.decisionRow(METHOD,
                Integer.parseInt(site.substring(site.lastIndexOf('u') + 1)),
                1, event, outcome, 0, 0);
    }

    /** The VM event of a branch it forced, overriding {@code concrete}. */
    private static JsonObject forcedEvent(long concrete) {
        return json("{'forced':true,'concrete':" + concrete + "}");
    }

    @Test
    public void onlyTheDeclaredOccurrenceOfAForceRunIsArmed()
            throws Exception {
        ActiveRegion plain = declared(1L);
        ForcedArms.arm(plain);
        assertFalse("a run asked no FORCE arms nothing",
                plain.pathRecordingStarted);
        forcing();
        ActiveRegion other = declared(2L, FORCED.replace("@0", "@1"), "", "");
        ForcedArms.arm(other);
        assertFalse("another occurrence is never armed",
                other.pathRecordingStarted);
        ActiveRegion active = declared(3L);
        ForcedArms.arm(active);
        assertTrue("the declared one records from its entry",
                active.pathRecordingStarted);
        assertTrue(FocusedReplay.forcing());
        assertFalse("a FORCE run confirms nothing",
                FocusedReplay.confirming());
        assertEquals("FORCE_DIVERGED: the declared occurrence never closed",
                FocusedReplay.results("s").get(0).detail());
    }

    @Test
    public void theForcedWorldOpensAtTheFirstDecisionForcedOffItsArm()
            throws Exception {
        forcing();
        ActiveRegion active = declared(4L);
        ForcedArms.arm(active);
        JsonObject along = mapping(GUARD, 10L, true);
        ForcedArms.mark(active, along, forcedEvent(1L));
        JsonObject off = mapping(GUARD, 12L, true);
        ForcedArms.mark(active, off, forcedEvent(0L));
        JsonObject unforced = mapping(GUARD, 14L, false);
        ForcedArms.mark(active, unforced, new JsonObject());
        Object[][] rows = {
            {"forced along its concrete arm", along, true, true, false},
            {"forced off it", off, true, false, true},
            {"not forced", unforced, false, false, false}};
        for (Object[] row : rows) {
            JsonObject mapping = (JsonObject) row[1];
            assertEquals(row[0] + ": forced", row[2], mapping.has("forced"));
            if (mapping.has("forced")) {
                assertEquals(row[0] + ": concrete", row[3],
                        mapping.get("concreteOutcome").getAsBoolean());
            }
            assertEquals(row[0] + ": against", row[4],
                    mapping.has(ForcedArms.AGAINST));
        }
        assertEquals("no world before its target", 0L,
                ForcedArms.forcedFrom(active));
        ForcedArms.reachedTarget(active, TARGET, 1, true);
        assertEquals(12L, ForcedArms.forcedFrom(active));
        assertEquals("reached: nothing withdraws its session", "",
                ForcedArms.unreached());
        assertEquals("", ForcedArms.finished(active, "THROW",
                "java.lang.IllegalStateException"));
        ObligationResult verdict = FocusedReplay.results("s").get(0);
        assertEquals(Verdict.ADMITTED, verdict.verdict());
        assertTrue(verdict.detail(), verdict.detail().startsWith(
                "FORCED_TARGET") && verdict.detail().contains(TARGET + "#1")
                && verdict.detail().contains(
                "THROW java.lang.IllegalStateException"));
    }

    @Test
    public void anOccurrenceClosedShortOfItsTargetDiverges()
            throws Exception {
        String[][] rows = {
            // how it ended, what the verdict names
            {"closed", "before its target decision was forced"},
            {"healthy", "took its healthy arm"}};
        for (String[] row : rows) {
            forcing();
            ActiveRegion active = declared(5L);
            ForcedArms.arm(active);
            ForcedArms.mark(active, mapping(GUARD, 20L, true),
                    forcedEvent(0L));
            if ("healthy".equals(row[0])) {
                ForcedArms.reachedTarget(active, TARGET, 1, false);
            }
            Fixtures.pushed(active);
            try {
                ForcedArms.unwinding(
                        new NullPointerException("a forced arm's null"));
            } finally {
                Fixtures.release();
            }
            String reason = ForcedArms.finished(active, "THROW",
                    "java.lang.NullPointerException");
            assertTrue(row[0] + ": " + reason, reason.startsWith(
                    "FORCE_DIVERGED") && reason.contains(row[1]));
            assertEquals(row[0] + ": forced from", "closed".equals(row[0]),
                    reason.contains("the forced world first threw "
                            + "java.lang.NullPointerException: a forced"
                            + " arm's null at "));
            assertEquals(Verdict.NOT_ADMITTED,
                    FocusedReplay.results("s").get(0).verdict());
            assertEquals(row[0] + ": its session is withdrawn", reason,
                    ForcedArms.unreached());
        }
        forcing();
        ForcedArms.arm(declared(6L));
        assertTrue("one that never closed is withdrawn too",
                ForcedArms.unreached().contains("never closed"));
    }

    /**
     * {@code if (a || b) throw}: the first test is passable (its healthy arm
     * runs on to the second); on its healthy arm it decides nothing, and the
     * run reaches its target at the second, forced (solr-18406 F2V3).  A
     * test that is not passable diverges on its healthy arm.
     */
    @Test
    public void aPassableTargetTestOnItsHealthyArmDecidesNothing()
            throws Exception {
        String first = METHOD + "#u3";
        Object[][] rows = {
            // is the first test passable, the verdict's detail
            {true, "FORCED_TARGET"},
            {false, "FORCE_DIVERGED: the target decision " + first}};
        for (Object[] row : rows) {
            forcing();
            ActiveRegion active = declared(7L, FORCED, "{'siteId':'" + first
                    + "','requiredOutcome':true},{'siteId':'" + TARGET
                    + "','requiredOutcome':true}", "{'siteId':'" + first
                    + "','arm':true" + ((Boolean) row[0] ? ",'passable':true"
                    : "") + "},");
            ForcedArms.arm(active);
            assertEquals(row[0] + ": the first test's reach is the row's"
                    + " only where it decided", !(Boolean) row[0],
                    ForcedArms.reachedTarget(active, first, 1, false));
            ForcedArms.reachedTarget(active, TARGET, 1, true);
            String detail = FocusedReplay.results("s").get(0).detail();
            assertTrue(row[0] + ": " + detail, detail.startsWith(
                    (String) row[1]));
        }
    }

    /** A decider is forced only in a call of its helper from {@code via}:
     *  the frame one level out -- a lambda's run-minted class name compared
     *  by its stable spelling, javac's {@code access$NNN} and {@code
     *  lambda$} hops passed. */
    @Test
    public void aDeciderIsForcedOnlyInACallFromItsVia() {
        String caller = "<a.Caller$$Lambda$12/1830908236: void run()>";
        String helper = "<a.Helper: boolean ok()>";
        Object[][] rows = {
            // frames, outermost first; via; called from it
            {new String[] {caller, helper},
                "<a.Caller$$Lambda$40/99: void run()>", true},
            {new String[] {caller, "<a.Other: void go()>", helper}, caller,
                false},
            {new String[] {helper}, caller, false},
            {new String[] {caller, "<a.Caller: boolean access$000("
                    + "a.Caller)>", helper}, caller, true},
            {new String[] {caller, "<a.Caller: void lambda$run$0()>",
                    helper}, caller, true}};
        for (Object[] row : rows) {
            String[] frames = (String[]) row[0];
            long[] tokens = new long[frames.length];
            for (int index = 0; index < frames.length; index++) {
                tokens[index] = Identity.enterFrame(frames[index], null);
            }
            try {
                assertEquals(String.valueOf(row[1]), row[2],
                        ForcedArms.calledFrom((String) row[1]));
            } finally {
                for (int index = frames.length - 1; index >= 0; index--) {
                    Identity.exitFrame(tokens[index]);
                }
            }
        }
    }

    /** The forced path condition from the forced world's first decision
     *  through the target: each as taken, a concrete one forced off its arm
     *  false, the target's own as phi; a switch adds nothing. */
    @Test
    public void theForcedPhiIsTheWholeWayFromTheFirstForcedDecision() {
        JsonObject before = mapping(GUARD, 5L, false);
        before.add("siteCondition", Fixtures.symbol("M_BEFORE", "Z"));
        JsonObject first = mapping(GUARD, 7L, true);
        first.add("siteCondition", Fixtures.symbol("M_A", "Z"));
        JsonObject concreteOff = mapping(GUARD, 8L, true);
        concreteOff.addProperty(ForcedArms.AGAINST, true);
        JsonObject target = mapping(TARGET, 11L, true);
        target.add("siteCondition", Fixtures.symbol("M_TARGET", "Z"));
        List<JsonObject> mappings = new ArrayList<>(Arrays.asList(before,
                first, concreteOff, mapping(GUARD, 9L, false), target));
        String a = RowRuntime.expressionRef(Fixtures.symbol("M_A", "Z"));
        assertEquals("(and " + a + " false PHI)",
                RowPublication.forced(mappings, 7L, 11L, "PHI"));
        JsonObject concreteTarget = mapping(TARGET, 11L, true);
        concreteTarget.addProperty(ForcedArms.AGAINST, true);
        mappings.set(4, concreteTarget);
        assertEquals("a concrete target forced off its arm is false too",
                "(and " + a + " false false PHI)",
                RowPublication.forced(mappings, 7L, 11L, "PHI"));
        assertEquals("nothing between: phi alone", "PHI",
                RowPublication.forced(Collections.<JsonObject>emptyList(),
                        7L, 11L, "PHI"));
        // A switch states the case arm and no condition, its predicate
        // rows no arm.
        JsonObject predicate = BranchObservation.decisionRow(METHOD, 2, 1,
                9L, null, 0, 0);
        predicate.add("witness", Fixtures.symbol("M_KEY", "Z"));
        assertEquals("(and " + a + " PHI)", RowPublication.forced(
                Arrays.asList(first, mapping(GUARD, 9L, true), predicate,
                        target), 7L, 11L, "PHI"));
    }
}
