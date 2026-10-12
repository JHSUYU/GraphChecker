package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * GROW's planner (PIPELINE §7.8): an UNPLANNED_INPUT row's invocation is
 * planned in its own task's row -- the input it names, again, as a root of
 * its own -- never as a second row of the occurrence, once, and a row naming
 * no planned input is refused.
 */
public class ExposedRegionPlanMainTest {
    private static final String MARKER = "{\"symbol\":\"SYM.m\",\"portId\":"
            + "\"SYM.m\",\"mode\":\"SYMBOLIC\",\"marker\":"
            + "\"FAULT:TIMED_WAIT:AWAIT\",\"replayOccurrence\":1,"
            + "\"observed\":true,\"primitiveValue\":\"false\","
            + "\"eventSeq\":7,\"callId\":3}";

    @Test
    public void anUnplannedInvocationIsAnInputOfItsTask() throws Exception {
        List<JsonObject> plan = Arrays.asList(task("TASK.t", MARKER),
                task("TASK.u"));
        List<JsonObject> grown = ExposedRegionPlanMain.grown(plan,
                Arrays.asList(input("TASK.t", "SYM.m", 2),
                        input("TASK.t", "SYM.m", 2),
                        input("TASK.t", "SYM.m#2", 3)));
        assertEquals("the plan's rows, no second row of an occurrence", 2,
                grown.size());
        JsonArray actions = grown.get(0).getAsJsonArray("inputActions");
        List<String> planned = new ArrayList<String>();
        for (int index = 0; index < actions.size(); index++) {
            JsonObject action = actions.get(index).getAsJsonObject();
            planned.add(action.get("symbol").getAsString() + " "
                    + action.get("portId").getAsString() + " "
                    + action.get("replayOccurrence").getAsInt() + " "
                    + action.get("observed").getAsBoolean() + " "
                    + action.has("primitiveValue") + " "
                    + action.get("marker").getAsString());
        }
        assertEquals(Arrays.asList(
                "SYM.m SYM.m 1 true true FAULT:TIMED_WAIT:AWAIT",
                "SYM.m#2 SYM.m#2 2 false false FAULT:TIMED_WAIT:AWAIT",
                "SYM.m#3 SYM.m#3 3 false false FAULT:TIMED_WAIT:AWAIT"),
                planned);
        assertTrue("the plan given is not written",
                plan.get(0).getAsJsonArray("inputActions").size() == 1);
        for (JsonObject unknown : Arrays.asList(input("TASK.v", "SYM.m", 2),
                input("TASK.u", "SYM.m", 2))) {
            try {
                ExposedRegionPlanMain.grown(plan,
                        Collections.singletonList(unknown));
                fail("grew an input no task plans: " + unknown);
            } catch (IOException expected) {
                assertTrue(expected.getMessage(), expected.getMessage()
                        .startsWith("UNPLANNED_INPUT_UNKNOWN"));
            }
        }
    }

    private static JsonObject task(String taskId, String... actions) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        JsonArray inputs = new JsonArray();
        for (String action : actions) inputs.add(JsonParser.parseString(action));
        task.add("inputActions", inputs);
        return task;
    }

    private static JsonObject input(String taskId, String symbol, int k) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", ExposedRegionPlanMain.UNPLANNED_INPUT);
        row.addProperty("taskId", taskId);
        row.addProperty("symbol", symbol);
        row.addProperty("k", k);
        row.addProperty("sessionId", "s-flip");
        row.addProperty("obligationId", "OBL.s-flip");
        return row;
    }
}
