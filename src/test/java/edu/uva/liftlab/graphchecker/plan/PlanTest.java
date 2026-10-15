package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** IDENTITY §9: a case declaration is resolved against the seed session. */
public class PlanTest {
    private static final String REGION = "REGION.53092d3e";
    private static final NodeId DN0 = NodeId.parse("hdfs-17897/dn0#epoch0");
    private static final NodeId DN1 = NodeId.parse("hdfs-17897/dn1#epoch0");
    private static final NodeId DN9 = NodeId.parse("hdfs-17897/dn9#epoch0");
    private static final String CHECKSUM =
            "o.a.h.h.p.d.DataXceiver#blockChecksum#31";
    private static final String MARKER = "{\"symbol\":\"SYM.m\",\"portId\":"
            + "\"SYM.m\",\"mode\":\"SYMBOLIC\",\"marker\":"
            + "\"FAULT:TIMED_WAIT:AWAIT\",\"replayOccurrence\":1,"
            + "\"observed\":true,\"primitiveValue\":\"false\","
            + "\"eventSeq\":7,\"callId\":3}";

    /**
     * The k-th match in SEED order, on the declared component, under the
     * declared api -- and a declaration this recording cannot satisfy is a
     * refusal that says what the seed did hold.
     */
    @Test
    public void aDeclarationNamesTheKthMatchInSeedOrder() {
        List<ActivationRow> seed = new ArrayList<ActivationRow>();
        OccurrenceAddress first = anchored(DN0, 1);
        OccurrenceAddress second = anchored(DN0, 2);
        seed.add(activation(anchored(DN1, 1)));     // another component
        seed.add(activation(tick(DN0)));            // no message started it
        seed.add(activation(first));
        seed.add(activation(second));

        String declared = DN0.render() + "/region/" + REGION
                + "@hdfs-17897/client#epoch0/striped-file-checksum#2";
        assertEquals(second, SelectorResolution.resolve(declared, seed));

        // The daemon tick and the other component are not candidates: one was
        // started by no message, the other ran somewhere else.  So the FIRST
        // match under that api is the one on dn0, not the one on dn1.
        assertEquals(first, SelectorResolution.resolve(
                DN0.render() + "/region/" + REGION
                        + "@hdfs-17897/client#epoch0/striped-file-checksum#1",
                seed));

        // A declaration with no api takes every occurrence of the region on
        // that component, tick included, still in seed order.
        assertEquals(tick(DN0), SelectorResolution.resolve(
                DN0.render() + "/region/" + REGION + "#1", seed));

        // An address that is already resolved passes through untouched, which
        // is what a re-run hands back out of a previous manifest; declared,
        // it names that occurrence and no other.
        assertEquals(second,
                SelectorResolution.resolve(second.render(), seed));
        assertTrue(RuntimeWorkflowDiscovery.declares(second.render(),
                second.render()));
        assertFalse(RuntimeWorkflowDiscovery.declares(second.render(),
                first.render()));

        // k beyond what the seed holds, or a node the seed never ran the
        // region on, is a case pointed at an execution this recording does
        // not contain.  It degrades rather than throwing, so DECIDE reports
        // DECLARATION_MISSING out of the artifact.
        for (String missing : new String[] {DN0.render() + "/region/"
                + REGION + "#9", DN9.render() + "/region/" + REGION + "#1"}) {
            OccurrenceAddress absent = SelectorResolution.resolve(missing,
                    seed);
            assertTrue(missing, absent.context().isLost());
            assertEquals(REGION, absent.regionId());
        }
    }

    /**
     * The declared occurrence is one the window holds back to its root: a
     * target on a message sent before the window (round HG2's hdfs-adhoc-19,
     * a block report answered inside the recording's window and before the
     * replay's) is never the question, and none other is a named refusal.
     */
    @Test
    public void aDeclarationResolvesAmongTargetsTheWindowHoldsToTheirRoot()
            throws Exception {
        String beforeWindow = anchored(DN0, 1).render();
        String inWindow = anchored(DN1, 1).render();
        Map<String, List<String>> shapes = new HashMap<String, List<String>>();
        shapes.put(beforeWindow, Arrays.asList("HADOOP_IPC/r@nn0", "?"));
        shapes.put(inWindow, Arrays.asList("HADOOP_IPC/r@nn1",
                "Root:BP_SERVICE_ACTOR"));
        Object[][] rows = {
            {"first skips set-up history",
                Arrays.asList(beforeWindow, inWindow), inWindow},
            {"set-up history alone is refused, naming it",
                Collections.singletonList(beforeWindow),
                "DECLARED_TARGET_BEFORE_WINDOW"},
        };
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            List<String> observed = (List<String>) row[1];
            String outcome;
            try {
                outcome = RuntimeWorkflowDiscovery.declaredOccurrence(
                        observed, RuntimeWorkflowDiscovery.FIRST, shapes::get);
            } catch (IOException refused) {
                assertTrue((String) row[0],
                        refused.getMessage().contains(beforeWindow));
                outcome = refused.getMessage().split(":")[0];
            }
            assertEquals((String) row[0], row[2], outcome);
        }
    }

    private static ActivationRow activation(OccurrenceAddress occurrence) {
        return ActivationRow.of("s-seed", occurrence, "task", false, true,
                "main#1");
    }

    private static OccurrenceAddress anchored(NodeId node, int iteration) {
        return OccurrenceAddress.of(node, REGION,
                CausalContext.of("ep-" + node.render() + "-" + iteration,
                        "o.a.h.h.p.ClientProtocol/striped-file-checksum"),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of(CHECKSUM, iteration))));
    }

    private static OccurrenceAddress tick(NodeId node) {
        return OccurrenceAddress.of(node, REGION,
                CausalContext.of(Role.of("BP_SERVICE_ACTOR"), "", 1),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of(CHECKSUM, 0))));
    }
    /**
     * GROW's planner (PIPELINE §7.8): an UNPLANNED_INPUT row's invocation is
     * planned in its own task's row -- the input it names, again, as a root
     * of its own -- never as a second row of the occurrence, once, and a row
     * naming no planned input is refused.
     */
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
        for (String action : actions) {
            inputs.add(JsonParser.parseString(action));
        }
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
