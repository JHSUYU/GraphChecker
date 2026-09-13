package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * How many consumers one exported communication port may address.
 *
 * <p>A wire producer rooted at a loop body is entered once per <em>message</em>
 * and exports one value per iteration, so one outgoing port addresses one
 * consumer occurrence per element the delivery carries.  These transcripts pin
 * the two recorded campaigns that first hit it -- hdfs-17899 bug3, where the
 * NameNode answers one DataNode's heartbeat with four block keys, and
 * hdfs-17897, where it answers one refresh with five -- and pin the one thing
 * that is still refused: consumers on two execution sources, which no single
 * message could reach.  The refusal fires in the decode both the PLAN stage
 * and the replay JVM pass through, so a plan the runtime cannot execute never
 * reaches REPLAY.</p>
 */
public class ExportPortConsumerOccurrencesTest {
    private static final String KEY_ID_PORT =
            "XCH.1174244c-3118-3892-a173-6cc5895259bf.resp.block-key-id";
    private static final String EXPIRY_PORT =
            "XCH.cfba8c05-3dcb-3577-aec4-79db5ccfe24e.resp.block-key-expiry-date";

    @After
    public void clearEnvelope() {
        SymbolicMessageEnvelope.clear();
    }

    /** bug3: one heartbeat answer frame, four per-key consumer occurrences. */
    @Test
    public void oneHeartbeatAnswerAddressesEveryPerKeyConsumer() {
        ConcolicTaskPlan.RuntimeTask task = task(
                "plans/hdfs-17899-bug3-loop-body-producer.json");

        assertEquals("hdfs-17899/nn0#epoch0/region/"
                        + "REGION.2392e4b7-aa01-3487-85a3-ac776965f7f7#1",
                task.occurrenceId);
        assertEquals(consumers("hdfs-17899/target-dn", 2, 3, 4, 5),
                task.exportConsumerOccurrences(KEY_ID_PORT));
        assertEquals(consumers("hdfs-17899/target-dn", 2, 3, 4, 5),
                task.exportConsumerOccurrences(EXPIRY_PORT));
        // One response frame carrying four keys, not four responses.
        assertEquals(1, exchangeLegs(
                row("plans/hdfs-17899-bug3-loop-body-producer.json"),
                KEY_ID_PORT).size());
    }

    /** One staged value per iteration; the queue hands out one each. */
    @Test
    public void eachStagedValueIsTakenOnce() {
        ConcolicTaskPlan.RuntimeTask task = task(
                "plans/hdfs-17899-bug3-loop-body-producer.json");
        List<String> addressed = task.exportConsumerOccurrences(KEY_ID_PORT);
        for (int iteration = 1; iteration <= addressed.size(); iteration++) {
            assertTrue(SymbolicMessageEnvelope.stage(KEY_ID_PORT, iteration,
                    task.taskId, task.occurrenceId + "#a" + iteration,
                    addressed));
        }
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        for (int iteration = 1; iteration <= addressed.size(); iteration++) {
            SymbolicMessageEnvelope.Entry taken =
                    SymbolicMessageEnvelope.take(KEY_ID_PORT);
            assertTrue(taken.present());
            assertEquals(iteration, taken.handle());
        }
        assertFalse(SymbolicMessageEnvelope.take(KEY_ID_PORT).present());
    }

    private static List<String> consumers(String source, int... ordinals) {
        List<String> ids = new ArrayList<>();
        for (int ordinal : ordinals) {
            ids.add(source + "#epoch0/region/"
                    + "REGION.1f6914ec-f8dc-3369-8f6a-dbfcccdb2762#"
                    + ordinal);
        }
        return ids;
    }

    private static Set<String> exchangeLegs(JsonObject row, String portId) {
        Set<String> legs = new LinkedHashSet<>();
        for (com.google.gson.JsonElement element
                : row.getAsJsonArray("edgeBindings")) {
            JsonObject binding = element.getAsJsonObject();
            if (portId.equals(optional(binding, "fromOutputPort"))) {
                legs.add(optional(binding, "exchangeLeg"));
            }
        }
        return legs;
    }

    private static String optional(JsonObject row, String field) {
        return row.has(field) && row.get(field).isJsonPrimitive()
                ? row.get(field).getAsString() : "";
    }

    private static ConcolicTaskPlan.RuntimeTask task(String resource) {
        ExecutionTask task = ExecutionTask.decode(row(resource));
        List<String> outgoing = new ArrayList<>();
        for (CommunicationHandoffSpec site : task.communicationHandoffs()) {
            if (site.outgoing()) outgoing.add(site.portId());
        }
        assertEquals(Arrays.asList(KEY_ID_PORT, EXPIRY_PORT), outgoing);
        return new ConcolicTaskPlan.RuntimeTask(task);
    }

    private static JsonObject row(String resource) {
        try (InputStream bytes = ExportPortConsumerOccurrencesTest.class
                .getClassLoader().getResourceAsStream(resource)) {
            if (bytes == null) {
                throw new IllegalStateException("missing " + resource);
            }
            return new JsonParser().parse(new InputStreamReader(bytes,
                    StandardCharsets.UTF_8)).getAsJsonObject();
        } catch (Exception failure) {
            throw new IllegalStateException(failure);
        }
    }
}
