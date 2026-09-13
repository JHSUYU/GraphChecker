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
