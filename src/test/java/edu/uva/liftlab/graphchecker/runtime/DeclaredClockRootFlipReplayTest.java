package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A declared wall-clock root is replay-injectable, and its model is a skew.
 *
 * <p>EXPLORE could flip a clock-dependent branch on paper and never on the
 * VM.  The solver answered {@code SAT_MODEL_READY} and the plan carried a
 * model assignment for the {@code Timer.now()} root, so the value did reach
 * the replay -- but as an <em>absolute</em> millisecond stamp taken from the
 * seed recording's own constants.  A flip replay is a fresh JVM that mints
 * its expiries minutes later, so that stamp lands in the past, the compared
 * branch keeps its recorded outcome, and the linked replay is refused:
 * {@code REPLAY_PREFIX_UNMATCHED -- still waiting for
 * removeExpiredKeys()#u15#1 (the flipped source decision)}.  With no flipped
 * case recorded, the composition keeps asserting
 * the recorded polarity of that branch for every key and no clock window
 * admits the removal.</p>
 *
 * <p>The numbers below are the ones the laneU corpus actually carries.</p>
 */
public class DeclaredClockRootFlipReplayTest {

    /** hdfs-17897 nn0: what {@code Timer.now()} returned in the recording. */
    private static final long RECORDED_CLOCK = 1789284077460L;
    /** The model the flip solver published: the key's expiry, plus one. */
    private static final long MODEL_CLOCK = 1789284356381L;
    /** The same key's recorded expiry, which the model is one millisecond
     *  past. */
    private static final long RECORDED_EXPIRY = 1789284356380L;

    /** The replay JVM started 846 s after the recording. */
    private static final long LIVE_CLOCK = 1789284923800L;
    /** So it minted its own copy of that key 846 s later too. */
    private static final long LIVE_EXPIRY =
            RECORDED_EXPIRY + (LIVE_CLOCK - RECORDED_CLOCK);

    private static final String TIMER_NOW =
            "<org.apache.hadoop.util.Timer: long now()>";

    /** Every other declared root replays its model value verbatim. */
    @Test
    public void anIdentityRootReplaysTheModelValueVerbatim() {
        JsonObject row = clockRow();
        row.addProperty("declaredCallee",
                "<org.apache.hadoop.hdfs.security.token.block.BlockKey: "
                        + "int getKeyId()>");
        ConcolicRegionRuntime.SymbolizeAction action =
                new ConcolicRegionRuntime.SymbolizeAction(row);
        assertFalse(action.declaresWallClockRead());
        assertEquals(Long.toString(MODEL_CLOCK),
                ConcolicRegionRuntime.replayModelLiteral(action,
                        model(MODEL_CLOCK), LIVE_CLOCK));
    }

    /**
     * A replay that reproduces its recording reads exactly the model value,
     * so nothing changes for a same-timeline replay.
     */
    @Test
    public void aReplayThatReproducesItsRecordingReadsTheModelValue() {
        assertEquals(Long.toString(MODEL_CLOCK),
                ConcolicRegionRuntime.replayModelLiteral(clockAction(),
                        model(MODEL_CLOCK), RECORDED_CLOCK));
    }

    /**
     * The regression this fixes, stated as arithmetic: the model value the
     * solver published cannot expire this run's key, and the offset it
     * actually chose can.
     */
    @Test
    public void theFlipReplayTakesTheFlippedBranch() {
        assertFalse("the stamp lands 567 s before this run's expiry",
                RECORDED_EXPIRY + (LIVE_CLOCK - RECORDED_CLOCK)
                        < MODEL_CLOCK);

        String replayed = ConcolicRegionRuntime.replayModelLiteral(
                clockAction(), model(MODEL_CLOCK), LIVE_CLOCK);
        long injected = Long.parseLong(replayed);

        assertEquals("this run's clock, moved by the offset the model chose",
                LIVE_CLOCK + (MODEL_CLOCK - RECORDED_CLOCK), injected);
        assertTrue("expiryDate < now, which is the decision EXPLORE asked for",
                LIVE_EXPIRY < injected);
        assertTrue("and it stays ahead of this run's own clock",
                injected > LIVE_CLOCK);
    }

    private static ConcolicRegionRuntime.SymbolizeAction clockAction() {
        return new ConcolicRegionRuntime.SymbolizeAction(clockRow());
    }

    /**
     * The shape of the laneU plan row for
     * {@code REGION.aaa1cfd7...in.1cdfc335}: the {@code Timer.now()} return
     * that {@code removeExpiredKeys()} compares every key's expiry against.
     */
    private static JsonObject clockRow() {
        JsonObject row = new JsonObject();
        row.addProperty("symbol", "REGION.aaa1cfd7.in.1cdfc335");
        row.addProperty("location", "CALL_RETURN");
        row.addProperty("bindingMode", "LOCAL_DEFINITION");
        row.addProperty("cell", TIMER_NOW + ".return");
        row.addProperty("declaredCallee", TIMER_NOW);
        row.addProperty("javaType", "long");
        row.addProperty("method",
                "<org.apache.hadoop.hdfs.security.token.block."
                        + "BlockTokenSecretManager: void removeExpiredKeys()>");
        row.addProperty("local", "$l0");
        row.addProperty("unitIndex", 2);
        row.addProperty("mode", "SYMBOLIC");
        row.addProperty("declaredSymbolicRoot", true);
        row.addProperty("observed", true);
        row.addProperty("primitiveValue", Long.toString(RECORDED_CLOCK));
        row.addProperty("replayOccurrence", 1);
        return row;
    }

    private static ConcolicRegionRuntime.ModelAssignment model(long value) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("engineSymbol", "M_J_field_REGION.aaa1cfd7"
                + ".in.1cdfc335.occ.0a591271_java/lang/Long");
        encoded.addProperty("inputSymbol", "REGION.aaa1cfd7.in.1cdfc335");
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", Long.toString(value));
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }
}
