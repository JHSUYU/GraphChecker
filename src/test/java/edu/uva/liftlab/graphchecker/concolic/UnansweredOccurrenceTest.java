package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * An occurrence one run declined and another answered, and one neither did.
 *
 * <p>A workload with two JVM epochs on one node offers every task addressed
 * at that node to both.  The epoch that never registered the addressed one
 * says so, and that is a statement about which JVM was asked.  Where another
 * run answered the task it is noise; where none did, the region was not
 * replayed at all -- which is how a campaign came back FINAL_READY over a
 * formula whose only root-dependent region never ran.</p>
 */
public class UnansweredOccurrenceTest {

    private static final String UNMATCHED =
            "REGION_OCCURRENCE_ANCHOR_UNMATCHED";

    /** No run answered it: the contract names the task and blocks. */
    @Test
    public void aTaskEveryRunDeclinedIsNamed() {
        List<JsonObject> rows = PublicationContract.check(
                tasks(task("TASK.a")), Collections.<JsonObject>emptyList(),
                Collections.singletonList(declined("TASK.a")));

        assertEquals(1, rows.size());
        assertEquals(PublicationContract.TASK_ANSWERED_BY_NO_RUN,
                rows.get(0).get("code").getAsString());
        assertEquals("TASK.a", rows.get(0).get("subject").getAsString());
    }

    /** Another run answered it, so the decline says nothing to block on. */
    @Test
    public void aTaskAnotherRunAnsweredIsClean() {
        assertTrue(PublicationContract.check(tasks(task("TASK.a")),
                Collections.singletonList(summary("TASK.a")),
                Collections.singletonList(declined("TASK.a"))).isEmpty());
    }

    /** A real skip is an answer about the region, and is not this. */
    @Test
    public void aRegionThatDidNotRunIsNotAnUnansweredTask() {
        JsonObject observed = new JsonObject();
        observed.addProperty("code", "REGION_ROOT_NEVER_EXECUTED");
        observed.addProperty("taskId", "TASK.a");

        assertTrue(PublicationContract.check(tasks(task("TASK.a")),
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(observed)).isEmpty());
    }

    private static JsonObject declined(String taskId) {
        JsonObject row = new JsonObject();
        row.addProperty("code", UNMATCHED);
        row.addProperty("taskId", taskId);
        row.addProperty("detail", "this run reached [wl/nn0#epoch0] and never"
                + " registered wl/nn0#epoch1");
        return row;
    }

    private static JsonObject summary(String taskId) {
        JsonObject row = new JsonObject();
        row.addProperty("taskId", taskId);
        row.addProperty("occurrenceId", "wl/nn0#epoch1/region/R#1#a1");
        row.add("branchMappings", new JsonArray());
        return row;
    }

    private static Map<String, ExecutionTask> tasks(JsonObject... rows) {
        Map<String, ExecutionTask> tasks = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            tasks.put(row.get("taskId").getAsString(),
                    ExecutionTask.decode(row));
        }
        return tasks;
    }

    private static JsonObject task(String taskId) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_EXECUTION_TASK");
        row.addProperty("taskId", taskId);
        row.addProperty("goalId", "GOAL." + taskId);
        row.addProperty("goalKind", "REGION_PATH_CLOSURE");
        row.addProperty("regionId", "REGION.fixture");
        row.addProperty("sourceKey", "wl/nn0#epoch1");
        row.addProperty("occurrenceId", "wl/nn0#epoch1/region/R#1");
        row.addProperty("relationKey", "wl/nn0/relation/R");
        row.add("branches", new JsonArray());
        row.add("inputActions", new JsonArray());
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        row.add("admission", admission);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(row);
        return row;
    }
}
