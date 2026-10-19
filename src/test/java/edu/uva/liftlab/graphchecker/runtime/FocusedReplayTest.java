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

    private static String flip(int ordinal, String members) {
        return focusRow(FOCUS, "'flip':{'siteId':'" + SITE + "','ordinal':"
                + ordinal + ",'outcome':true}" + members);
    }

    private void hand(String... rows) throws Exception {
        reset();
        focus(folder.newFolder().toPath(), rows);
    }

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

    @Test
    public void aFaithfulRunThatNeverEnteredAnOpenArmRefutesItsWorld()
            throws Exception {
        Throwable thrown = new java.io.IOException("Unable to close file");
        Object[][] rows = {
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
