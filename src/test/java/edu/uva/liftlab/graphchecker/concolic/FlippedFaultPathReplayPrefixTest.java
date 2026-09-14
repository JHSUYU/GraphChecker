package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A flipped fault path is admitted on the prefix up to the flip, and the
 * recorded work after the flip is not required to happen again.
 *
 * <p>The transcript is the hdfs-17899 heartbeat, reduced to its two source
 * decisions.  The recorded run answers the fault marker {@code false} at
 * {@code SITE.HEARTBEAT#1} and then, the request having succeeded, takes a
 * branch inside {@code addKeys} at {@code SITE.ADDKEYS#1}.  Flipping the
 * marker sends the request into its catch path, so {@code addKeys} never
 * runs and {@code SITE.ADDKEYS#1} never happens.  Requiring it anyway would
 * refuse exactly the replay the flip was scheduled to produce.</p>
 *
 * <p>These cases pin the boundary in both directions, because the two
 * mistakes are symmetric: demanding decisions recorded after the flip
 * refuses every fault replay, and dropping decisions recorded before it
 * would admit a replay that reached the flipped branch by a different
 * route.</p>
 */
public class FlippedFaultPathReplayPrefixTest {
    private static final String HEARTBEAT = "SITE.HEARTBEAT";
    private static final String ADD_KEYS = "SITE.ADDKEYS";
    private static final String SEND_REQUEST = "SITE.SENDREQUEST";
    private static final String LOOP_EXIT = "SITE.REMOVEEXPIREDKEYS#u7";
    private static final String EXPIRED_KEY = "SITE.REMOVEEXPIREDKEYS#u15";

    /** Recorded: heartbeat then addKeys. Flipped: heartbeat then catch. */
    @Test
    public void workRecordedAfterTheFlipIsNotRequiredOfTheFlippedReplay() {
        BranchReplayContract.RuntimeSchedule schedule = schedule(
                transcript(), HEARTBEAT, 1);

        // The contract is cut at the flipped decision, so the addKeys branch
        // is not in it at all -- not an event the replay is excused, an event
        // it was never asked for.
        assertEquals(0, contract(transcript(), HEARTBEAT, 1).toJson()
                .getAsJsonArray("runtimePrefix").size());

        BranchReplayContract.ReplayProgress replay =
                new BranchReplayContract.ReplayProgress(schedule);
        // true is the flipped outcome: the recorded run answered false.
        assertTrue(replay.observeBinary(HEARTBEAT, 1, true));
        assertTrue(replay.complete());
        assertFalse(replay.failed());
        assertEquals("", replay.failure());
    }

    /**
     * Lane VM10: the flipped decision is inside a retained loop.
     *
     * <p>{@code removeExpiredKeys()#u7} is the loop exit and
     * {@code #u15} is a decision inside its body carrying propagated
     * symbolic support.  Six obligations were refused there as "prefix not
     * yet complete: observed 2 of 3, still waiting for ...#u15#1 (the
     * flipped source decision)" while the site had executed all along: the
     * source event was addressed by the support digest the SEED recorded at
     * it, and a support digest is a hash over a fresh JVM's own symbols --
     * two flip replays of one planned occurrence published
     * BRANCH_SUPPORT.v1.ce0d0b14... and BRANCH_SUPPORT.v1.ba9e60ac... at
     * that same site.  So the prefix ends before the flip, and the flipped
     * decision is addressed by its occurrence and honoured by its
     * outcome.</p>
     */
    @Test
    public void theFlippedDecisionInALoopIsAdmittedByItsFlippedOutcome() {
        BranchReplayContract.RuntimeSchedule schedule = schedule(
                loopTranscript(), EXPIRED_KEY, 1, retainedLoop());
        BranchReplayContract.ReplayProgress replay =
                new BranchReplayContract.ReplayProgress(schedule);

        // 1..n-1 as recorded: the loop's first exit test, which is the whole
        // prefix, with this run's own support digest rather than the seed's.
        assertFalse(replay.observeBinary(LOOP_EXIT, 1, false, "SUPPORT.run"));
        assertFalse("the prefix alone does not complete the contract",
                replay.complete());

        // n flipped: the recorded run took true here.
        assertTrue("the flipped outcome consumes the source event",
                replay.observeBinary(EXPIRED_KEY, 1, false, "SUPPORT.run"));
        assertTrue(replay.complete());
        assertFalse(replay.failed());
        assertEquals("", replay.failure());
    }

    /** The recorded outcome at the flipped site is the flip not honoured. */
    @Test
    public void theRecordedOutcomeAtTheFlippedSiteIsRefusedByName() {
        BranchReplayContract.RuntimeSchedule schedule = schedule(
                loopTranscript(), EXPIRED_KEY, 1, retainedLoop());
        BranchReplayContract.ReplayProgress replay =
                new BranchReplayContract.ReplayProgress(schedule);

        assertFalse(replay.observeBinary(LOOP_EXIT, 1, false, "SUPPORT.run"));
        assertFalse("the recorded outcome does not consume the source",
                replay.observeBinary(EXPIRED_KEY, 1, true, "SUPPORT.run"));

        assertFalse(replay.complete());
        assertTrue("a flip that was not honoured is a refusal, not a wait",
                replay.failed());
        assertTrue(replay.failure(),
                replay.failure().startsWith("wrong decision at "
                        + EXPIRED_KEY + "#1"));
    }

    /** One activation of the key-expiry loop, as the summary records it. */
    private static JsonObject loopTranscript() {
        JsonObject exitTest = binary(variable("I_index"), "<",
                integer(2));
        JsonObject expired = binary(variable("J_expiryDate"), "<",
                integer(7));
        JsonArray path = new JsonArray();
        path.add(exitTest);
        path.add(expired);

        JsonObject normalization = new JsonObject();
        normalization.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(LOOP_EXIT, "removeExpiredKeys",
                        7, 1, false, exitTest, 0, normalization), 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(EXPIRED_KEY, "removeExpiredKeys",
                        15, 1, true, expired, 1, normalization), 1,
                SummaryBranchMapping.Policy.EXPLORE).toJson());

        JsonObject summary = new JsonObject();
        summary.add("pathCondition", path);
        summary.add("branchMappings", mappings);
        return summary;
    }

    /** The retained loop #u15 sits in, with #u7 as its exit decision. */
    private static JsonArray retainedLoop() {
        JsonObject loop = new JsonObject();
        loop.addProperty("kind", "RETAINED_LOOP");
        loop.addProperty("runtimeLoopId", LOOP_EXIT + "#loop:u6");
        JsonArray members = new JsonArray();
        members.add(LOOP_EXIT);
        members.add(EXPIRED_KEY);
        loop.add("loopInnermostBranchSiteIds", members);
        JsonObject exit = new JsonObject();
        exit.addProperty("siteId", LOOP_EXIT);
        exit.addProperty("decisionToken",
                "{\"branchKind\":\"BINARY\",\"sourceTakenOutcome\":true}");
        JsonArray exits = new JsonArray();
        exits.add(exit);
        loop.add("loopExitDecisions", exits);
        JsonArray loops = new JsonArray();
        loops.add(loop);
        return loops;
    }

    private static BranchReplayContract.RuntimeSchedule schedule(
            JsonObject summary, String siteId, int occurrence,
            JsonArray retainedLoops) {
        return BranchReplayContract.runtimeScheduleFromJson(
                contract(summary, siteId, occurrence).toJson(),
                retainedLoops);
    }

    /**
     * One heartbeat activation as the summary records it.
     *
     * <p>Two source-level decisions in path-condition order: the fault
     * marker, then the branch inside {@code addKeys} that only runs because
     * the marker answered false.</p>
     */
    private static JsonObject transcript() {
        JsonObject marker = binary(variable("Z_hadoopIpcRequestFails"),
                "==", integer(0));
        JsonObject keyPresent = binary(variable("I_keyId"), "==",
                integer(3));
        JsonArray path = new JsonArray();
        path.add(marker);
        path.add(keyPresent);

        JsonObject normalization = new JsonObject();
        normalization.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(HEARTBEAT, SEND_REQUEST, 11, 1,
                        false, marker, 0, normalization), 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(ADD_KEYS, "addKeys", 21, 1,
                        false, keyPresent, 1, normalization), 1,
                SummaryBranchMapping.Policy.EXPLORE).toJson());

        JsonObject summary = new JsonObject();
        summary.add("pathCondition", path);
        summary.add("branchMappings", mappings);
        return summary;
    }

    private static BranchReplayContract contract(JsonObject summary,
                                                 String siteId,
                                                 int occurrence) {
        return BranchReplayContract.fromSummary(summary, siteId, occurrence);
    }

    private static BranchReplayContract.RuntimeSchedule schedule(
            JsonObject summary, String siteId, int occurrence) {
        // Through JSON on purpose: this is the decoder the replay JVM runs.
        return BranchReplayContract.runtimeScheduleFromJson(
                contract(summary, siteId, occurrence).toJson());
    }

    private static JsonObject variable(String name) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", name);
        return result;
    }

    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject binary(JsonObject left, String operator,
                                     JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_java_type", "Z");
        result.addProperty("_op", operator);
        result.add("_left", left);
        result.add("_right", right);
        return result;
    }
}
