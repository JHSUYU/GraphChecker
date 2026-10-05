package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import org.junit.Before;
import org.junit.Test;

/**
 * A replay's clock readings, as {@link RootMint} runs them: a node's clock
 * runs on from its jumps in the RECORDING's order, one clock at a time
 * ({@link NodeClocks}), and a mint states how far its clock ran off the
 * base reading.
 */
public class NodeClocksTest {
    private static final long HOUR_MS = 3_600_000L;

    @Before
    public void reset() {
        NodeClocks.reset();
    }

    @Test
    public void aReadingRunsOnFromTheJumpBeforeItInTheRecordingsOrder() {
        // Planted in THIS order, the later place first, as two threads may:
        // nn0's wall clock jumps an hour at the reading the recording read
        // at event 200, and a minute at event 100.
        assertEquals("a plant states its skew off the base reading", HOUR_MS,
                RootMint.clockSkew("nn0", clock(200L, Clock.WALL), 10L,
                        10L + HOUR_MS, true));
        assertEquals(60_000L, RootMint.clockSkew("nn0",
                clock(100L, Clock.WALL), 5L, 5L + 60_000L, true));
        assertEquals("a plant the recording states no event for moves its "
                + "reading alone", 60_000L, RootMint.clockSkew("dn1",
                clock(0L, Clock.WALL), 5L, 5L + 60_000L, true));
        assertEquals("and one whose clock states no JVM clock", 60_000L,
                RootMint.clockSkew("dn1", clock(400L, ""), 5L, 5L + 60_000L,
                        true));
        Object[][] readings = {
                // node, place, source, base reading, instant it runs at, why
                {"nn0", 50L, Clock.WALL, 1000L, 1000L,
                        "before every jump: the base reading"},
                {"nn0", 150L, Clock.WALL, 1000L, 61_000L,
                        "between: the earlier jump, planted last here"},
                {"nn0", 300L, Clock.WALL, 1000L, 1000L + HOUR_MS,
                        "after both: the later jump"},
                {"nn0", 300L, Clock.MONOTONIC, 1000L, 1000L,
                        "the node's monotonic clock, in ms too, is another"},
                {"dn1", 300L, Clock.WALL, 1000L, 1000L,
                        "another node's clock"},
                {"dn1", 500L, "", 1000L, 1000L,
                        "a clock stating no source is on no order"},
                {"nn0", 0L, Clock.WALL, 1000L, 1000L,
                        "a reading the recording states no event for"},
        };
        for (Object[] reading : readings) {
            assertEquals((String) reading[5], reading[4],
                    RootMint.clockReading((String) reading[0],
                            clock((Long) reading[1], (String) reading[2]),
                            reading[3]));
        }
        assertEquals("a reading nothing planted states the skew it ran on "
                        + "at, and files no jump", HOUR_MS,
                RootMint.clockSkew("nn0", clock(300L, Clock.WALL), 1000L,
                        1000L + HOUR_MS, false));
        assertEquals(1000L + HOUR_MS, RootMint.clockReading("nn0",
                clock(300L, Clock.WALL), 1000L));
    }

    /**
     * A plant lands on the application's clock as this replay reads it
     * ({@link Clocks}: its order's timeline): the mint runs at that reading
     * plus the skew the wave asks, states the skew, and its row's base
     * reading is the model's reading again -- the reading the next
     * obligation's skew (model less base) is off.  A later reading of the
     * node's clock runs on from the jump.
     */
    @Test
    public void aPlantLandsOnTheModelsReadingAndItsRowStatesThatReading()
            throws Exception {
        Path order = Files.createTempFile("plant", ".jsonl");
        RowCodec.writeJsonl(order, Collections.singletonList(
                RowCodec.writeScheduleTime(ScheduleEvent.ORIGIN, 0L,
                        1_000L)));
        System.setProperty(ScheduleLog.PREFIX_PROPERTY, order.toString());
        try {
            ScheduleLog.resetForTests();
            long model = Clocks.millis();
            long skew = -4200L;
            long planted = model + skew;
            assertEquals(skew, RootMint.clockSkew("nn0",
                    clock(300L, Clock.WALL), model, planted, true));
            RootMintRow row = RootMintRow.of("s-flip", 300L,
                    OccurrenceAddress.parse("hdfs/nn0#epoch1/region/R.1"
                            + "/ctx:Root:CLIENT#1/idx:"), "CASE.NOW",
                    "M_J_now", RootKind.CLOCK, RootCategory.CLOCK,
                    Long.toString(planted), null, null, true,
                    Clock.of(1_000_000L, Clock.WALL), skew);
            assertEquals(Long.toString(model), row.baseReading());
            long later = Clocks.millis();
            assertEquals(later + skew, RootMint.clockReading("nn0",
                    clock(400L, Clock.WALL), later));
        } finally {
            System.clearProperty(ScheduleLog.PREFIX_PROPERTY);
            ScheduleLog.resetForTests();
            Files.delete(order);
        }
    }

    /** A declared clock read of the plan's, read at this recorded event. */
    private static SymbolizeAction clock(long place, String source) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", "PORT.now." + place);
        encoded.addProperty("actionDigest", "DIGEST.1");
        encoded.addProperty("cell",
                "<org.apache.hadoop.util.Time: long now()>.return");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        encoded.addProperty(InputActionCatalog.DECLARED_WALL_CLOCK,
                1_000_000L);
        encoded.addProperty(InputActionCatalog.DECLARED_CLOCK_SOURCE, source);
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", "1000");
        encoded.addProperty("eventSeq", place);
        return new SymbolizeAction(encoded);
    }
}
