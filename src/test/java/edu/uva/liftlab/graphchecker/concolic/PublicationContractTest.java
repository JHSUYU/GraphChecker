package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.GapLedger;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * What the replay wave owes the stages after it, asked once at IMPORT, in
 * the words of the thing that is missing.
 */
public class PublicationContractTest {

    private static final String SITE =
            "<fixture.Saver: void save(java.io.OutputStream)>#u55";
    private static final String TARGET_SITE =
            "<fixture.Saver: void save(java.io.OutputStream)>#u61";

    /**
     * A kept task owes a row for itself and for every prefix site its goal
     * asked the replay to decide: silence is named, a skip the importer
     * named is itself a publication, and a region-path goal's branches are
     * sites rather than a required prefix.
     */
    @Test
    public void aKeptTaskOwesARowForItselfAndForItsPrefix() {
        List<JsonObject> silent = check(target("TASK.a"), null, null);
        assertEquals(1, silent.size());
        assertEquals("BLOCKING",
                silent.get(0).get(PublicationContract.CLASS).getAsString());
        assertEquals(1, PublicationContract.blocking(silent).size());
        assertEquals(PublicationContract.TASK_SILENT,
                silent.get(0).get("code").getAsString());
        assertEquals("TASK.a", silent.get(0).get("subject").getAsString());

        // A skip is a publication: the importer named it, and it is not this.
        assertTrue(check(target("TASK.a"), null,
                row("code", "REGION_ROOT_NEVER_EXECUTED",
                        "taskId", "TASK.a")).isEmpty());

        // The target goal's prefix is a path the replay was asked to follow.
        List<JsonObject> prefix = check(target("TASK.a"),
                summary("TASK.a", TARGET_SITE), null);
        assertEquals(1, prefix.size());
        assertEquals(PublicationContract.BRANCH_PREFIX_UNPUBLISHED,
                prefix.get(0).get("code").getAsString());
        assertTrue(prefix.get(0).get("detail").getAsString().contains(SITE));

        // A region-path goal's branches are sites, not a required prefix.
        assertTrue(check(task("TASK.a", "REGION_PATH_CLOSURE"),
                summary("TASK.a", TARGET_SITE), null).isEmpty());
    }

    /**
     * An activation that answered the address under another request is
     * named, as evidence rather than as a refusal: the address is the
     * identity and the request a circumstance, so the activation is
     * admitted, but a circumstance the recording had and the replay did not
     * is a divergence and it was silent.  It is timing about the run rather
     * than fact about the workload, so epoch re-seeding consumes the row.
     */
    @Test
    public void anActivationUnderAnotherRequestIsNamedAsDiagnostic() {
        String request = "wl/nn0#epoch0/request/refresh-block-keys#1";
        JsonObject ran = summary("TASK.a", SITE, TARGET_SITE);
        ran.addProperty("requestKey", "");
        ran.addProperty("threadName", "KeyManager$BlockKeyUpdater@1");

        List<JsonObject> rows = check(
                anchored(target("TASK.a"), request), ran, null);
        assertEquals(1, rows.size());
        assertEquals(PublicationContract.ACTIVATION_REQUEST_DIVERGED,
                rows.get(0).get("code").getAsString());
        String detail = rows.get(0).get("detail").getAsString();
        assertTrue(detail, detail.contains("no request"));
        assertTrue(detail, detail.contains("refresh-block-keys#1"));
        assertTrue(detail, detail.contains("KeyManager$BlockKeyUpdater@1"));

        // The row is evidence, not a contract failure, and it says so
        // itself: rows used to carry no class and the tally counted every
        // one as blocking, so lane17897f stopped at IMPORT on four of them.
        assertEquals(GapLedger.GapClass.DIAGNOSTIC, GapLedger.classOf(
                PublicationContract.ACTIVATION_REQUEST_DIVERGED));
        assertEquals("DIAGNOSTIC",
                rows.get(0).get(PublicationContract.CLASS).getAsString());
        assertTrue("the row carries the ledger's own reason",
                rows.get(0).get(PublicationContract.CLASS_REASON)
                        .getAsString().contains("circumstance"));
        assertTrue("and the campaign does not stop on it",
                PublicationContract.blocking(rows).isEmpty());

        // A task whose anchor names no request diverges from nothing.
        assertTrue(check(target("TASK.a"), ran, null).isEmpty());

        // And a divergence is not merely "not a stop": it is the recording
        // of the next epoch, and the row names the replay it seeds from, so
        // the harness plans epoch e+1 from that replay's own trace instead
        // of re-deriving which one diverged.
        assertTrue("a diverged request seeds the next epoch",
                ConcolicSummaryImporter.seedsAnEpoch(
                        PublicationContract.ACTIVATION_REQUEST_DIVERGED));
        assertTrue("so does an unplanned topology",
                ConcolicSummaryImporter.seedsAnEpoch(
                        ConcolicSummaryImporter.TOPOLOGY_DIVERGENCE));
        assertTrue("a contract failure does not",
                !ConcolicSummaryImporter.seedsAnEpoch(
                        PublicationContract.TASK_SILENT));

        JsonObject seedRow = new JsonObject();
        seedRow.addProperty("code",
                PublicationContract.ACTIVATION_REQUEST_DIVERGED);
        seedRow.addProperty(ConcolicSummaryImporter.SEEDS_NEXT_EPOCH, true);
        seedRow.addProperty(ConcolicSummaryImporter.SEED_REPLAY_GROUP,
                "REPLAY.GROUP.24f524c7");
        seedRow.addProperty(ConcolicSummaryImporter.SEED_REPLAY_TASK,
                "TASK.REPLAY.0bba7367");
        JsonObject quiet = new JsonObject();
        quiet.addProperty("code", "REGION_ROOT_NEVER_EXECUTED");
        assertEquals("the wave names the replay epoch e+1 is seeded from",
                Collections.singletonList("REPLAY.GROUP.24f524c7"),
                ConcolicSummaryImporter.seedingReplays(
                        java.util.Arrays.asList(seedRow, quiet, seedRow)));
    }

    /** The contract, over one kept task and the rows the wave published. */
    private static List<JsonObject> check(JsonObject task,
                                          JsonObject published,
                                          JsonObject named) {
        Map<String, ExecutionTask> tasks = new LinkedHashMap<>();
        tasks.put(task.get("taskId").getAsString(),
                ExecutionTask.decode(task));
        return PublicationContract.check(tasks, rows(published),
                rows(named));
    }

    private static List<JsonObject> rows(JsonObject row) {
        return row == null ? Collections.<JsonObject>emptyList()
                : Collections.singletonList(row);
    }

    /** The same task row, with a causal anchor naming one request. */
    private static JsonObject anchored(JsonObject task, String requestKey) {
        task.add("rootSelector", row("kind", "GLOBAL_INVOCATION",
                "causalAnchor", row("kind", "REGISTERED_SOURCE",
                        "sourceKey", "wl/nn0#epoch0",
                        "requestKey", requestKey,
                        "requestApi", "refresh-block-keys")));
        return task;
    }

    /** A target-reach task: its branch list is the prefix it must decide. */
    private static JsonObject target(String taskId) {
        return task(taskId, "TARGET_REACH_CLOSURE");
    }

    private static JsonObject task(String taskId, String goalKind) {
        JsonArray branches = new JsonArray();
        branches.add(branch(SITE));
        branches.add(branch(TARGET_SITE));
        JsonObject task = row("schemaVersion", 1,
                "kind", "CONCOLIC_EXECUTION_TASK", "taskId", taskId,
                "goalId", "GOAL." + taskId, "goalKind", goalKind,
                "regionId", "REGION.fixture", "sourceKey", "wl/nn0#epoch0",
                "occurrenceId", "wl/nn0#epoch0/region/REGION.fixture#1",
                "relationKey", "wl/nn0/relation/REGION.fixture",
                "branches", branches, "inputActions", new JsonArray(),
                "admission", row("state", "EXECUTABLE"));
        if ("TARGET_REACH_CLOSURE".equals(goalKind)) {
            task.add("targetBranch", branch(TARGET_SITE));
        }
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        return task;
    }

    private static JsonObject branch(String site) {
        return row("siteId", site, "occurrence", 1, "outcome", false);
    }

    /** One replay summary, naming the prefix sites it decided. */
    private static JsonObject summary(String taskId, String... decided) {
        JsonArray mappings = new JsonArray();
        for (String site : decided) {
            mappings.add(row("concreteObservation",
                    row("site", branch(site))));
        }
        return row("taskId", taskId,
                "occurrenceId", "wl/nn0#epoch0/region/REGION.fixture#1#a1",
                "branchMappings", mappings);
    }

    /** One JSON row: member name, value, member name, value. */
    private static JsonObject row(Object... members) {
        JsonObject row = new JsonObject();
        for (int index = 0; index < members.length; index += 2) {
            String name = (String) members[index];
            Object value = members[index + 1];
            if (value instanceof JsonElement) row.add(name,
                    (JsonElement) value);
            else if (value instanceof Number) row.addProperty(name,
                    (Number) value);
            else if (value instanceof Boolean) row.addProperty(name,
                    (Boolean) value);
            else row.addProperty(name, (String) value);
        }
        return row;
    }
}
