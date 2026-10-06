package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * When a focused replay is DECIDED ({@code FocusedReplay#refusedAt}): at the
 * first refusal after which every obligation it carries is NOT_ADMITTED
 * whatever the run does next -- never at a flip, whose session later stages
 * read whole.
 */
public class FocusedReplayDecidedTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

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

    @Before
    @After
    public void reset() {
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        RowRuntime.resetForTests();
    }

    /** Hands the replay one focus row: flip {@link #SITE}#1 to true at
     *  {@link #FOCUS}, holding {@link #PARENT_SITE}#1 true at {@link #PARENT}. */
    private void handed() throws Exception {
        Path worker = folder.newFolder().toPath();
        Files.write(worker.resolve("focused_task.jsonl"), ("{\"taskId\":\"T\","
                + "\"obligationId\":\"OB\",\"pathId\":\"p\",\"focused\":\""
                + FOCUS + "\",\"focusedOccurrenceId\":\""
                + OccurrenceAddress.parse(FOCUS).id() + "\",\"seedSessionId\":"
                + "\"seed\",\"flip\":{\"siteId\":\"" + SITE + "\",\"ordinal\""
                + ":1,\"outcome\":true},\"inheritedFlips\":[{\"focusedOccurren"
                + "ceId\":\"" + OccurrenceAddress.parse(PARENT).id() + "\","
                + "\"siteId\":\"" + PARENT_SITE + "\",\"ordinal\":1,"
                + "\"outcome\":true,\"obligationId\":\"PARENT\"}],"
                + "\"rootAssignments\":{},\"clockDeltas\":{},\"answers\":{},"
                + "\"rootMints\":{}}\n").getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
    }

    private static ObligationResult only(String sessionId) {
        return FocusedReplay.results(sessionId).get(0);
    }

    @Test
    public void theRecordedArmDecidesTheReplayOnceItsPrefixIsAbandoned()
            throws Exception {
        assertFalse("a replay handed no focus row carries no obligation",
                FocusedReplay.noteUnansweredTask(UNMATCHED + "x"));
        reset();
        handed();
        OccurrenceAddress focus = OccurrenceAddress.parse(FOCUS);
        assertFalse("the wrong arm files a refusal, and the occurrence it"
                        + " abandons is what decides",
                FocusedReplay.observeDecision(focus, SITE, 1, false));
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
    }

    @Test
    public void aPublicationTheRunEndedWithoutAdmitsNothing() throws Exception {
        handed();
        FocusedReplay.observeDecision(OccurrenceAddress.parse(FOCUS), SITE,
                1, true);
        FocusedReplay.observeDecision(OccurrenceAddress.parse(PARENT),
                PARENT_SITE, 1, true);
        assertEquals(Verdict.ADMITTED, only("s").verdict());
        FocusedReplay.noteUnsettledPublication(
                "RESULT_PUBLICATION_UNSETTLED: stuck");
        FocusedReplay.noteUnsettledPublication("a second one");
        ObligationResult result = only("s");
        assertEquals(Verdict.NOT_ADMITTED, result.verdict());
        assertEquals("RESULT_PUBLICATION_UNSETTLED: stuck", result.detail());
        assertEquals("never decided: the replay ran to its end", "",
                FocusedReplay.refusedAt());
    }

    @Test
    public void aDecidedSessionWithdrawsItselfAndIsNeverRecreated()
            throws Exception {
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
    public void aFlipDecidesNothingAndAContradictedInheritedFlipDecidesAll()
            throws Exception {
        handed();
        assertFalse("the flip taken leaves a session later stages read whole",
                FocusedReplay.observeDecision(OccurrenceAddress.parse(FOCUS),
                        SITE, 1, true));
        assertEquals("", FocusedReplay.refusedAt());
        assertTrue("the world this path was cut from did not happen",
                FocusedReplay.observeDecision(OccurrenceAddress.parse(PARENT),
                        PARENT_SITE, 1, false));
        ObligationResult result = only("");
        assertEquals(Verdict.NOT_ADMITTED, result.verdict());
        assertTrue(result.detail(), result.detail().startsWith(
                "wrong decision at " + PARENT_SITE)
                && result.detail().contains("INHERITED")
                && result.detail().endsWith("published no session"));
    }

    /** Hands the replay an open decider arm's flip ({@code openArm}) of
     *  {@link #SITE}#1 at {@link #FOCUS}, in a world of its own. */
    private void handedAnArm(boolean openArm) throws Exception {
        Path worker = folder.newFolder().toPath();
        Files.write(worker.resolve("focused_task.jsonl"), ("{\"taskId\":\"T\","
                + "\"obligationId\":\"OB\",\"pathId\":\"p\",\"focused\":\""
                + FOCUS + "\",\"focusedOccurrenceId\":\""
                + OccurrenceAddress.parse(FOCUS).id() + "\",\"seedSessionId\":"
                + "\"seed\",\"flip\":{\"siteId\":\"" + SITE + "\",\"ordinal\""
                + ":1,\"outcome\":true},\"inheritedFlips\":[],"
                + "\"rootAssignments\":{},\"clockDeltas\":{},\"answers\":{},"
                + "\"rootMints\":{}" + (openArm ? ",\"openArm\":true" : "")
                + "}\n").getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
    }

    /**
     * WORLD_REFUTED: an open decider arm's flip whose replay ran its world
     * faithfully and never entered the flip's occurrence refutes that world
     * -- all four conditions or a plain NOT_ADMITTED: (a) every assignment
     * minted, no prefix abandoned, (b) no hold gave way, (c) no slot given up
     * before the world first acted, (d) the workload ended by itself.  Never
     * any other flip.
     */
    @Test
    public void aFaithfulRunThatNeverEnteredAnOpenArmRefutesItsWorld()
            throws Exception {
        Throwable thrown = new java.io.IOException("Unable to close file");
        Object[][] rows = {
            // open arm, ended, entered, first act/departure order, refuted
            {true, true, false, "", true},
            {true, true, false, "act depart", true},
            {true, true, false, "depart act", false},
            {true, false, false, "", false},
            {true, true, true, "", false},
            {false, true, false, "", false}};
        for (Object[] row : rows) {
            reset();
            handedAnArm((Boolean) row[0]);
            FocusedReplay.obligationIds();
            if ((Boolean) row[2]) {
                FocusedReplay.entered(OccurrenceAddress.parse(FOCUS));
            }
            for (String step : ((String) row[3]).split(" ")) {
                if ("act".equals(step)) FocusedReplay.worldActed();
                if ("depart".equals(step)) FocusedReplay.departed("7 (x)");
            }
            if ((Boolean) row[1]) {
                FocusedReplay.workloadEnded(thrown,
                        FocusedReplayDecidedTest.class.getName());
            }
            ObligationResult result = only("s");
            String what = java.util.Arrays.toString(row);
            assertEquals(what, Verdict.NOT_ADMITTED, result.verdict());
            assertEquals(what, row[4], result.refutation() != null);
            assertEquals(what, row[4],
                    result.detail().startsWith("WORLD_REFUTED: "));
            if (result.refutation() == null) continue;
            assertEquals(what, 4, result.refutation().conditions().size());
            assertEquals("java.io.IOException: Unable to close file",
                    result.refutation().exception());
            assertTrue(result.refutation().testFrame(), result.refutation()
                    .testFrame().contains("FocusedReplayDecidedTest"));
        }
    }
}
