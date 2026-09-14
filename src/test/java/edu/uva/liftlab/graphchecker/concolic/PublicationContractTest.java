package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * What the replay wave owes the stages after it, asked once at IMPORT.
 *
 * <p>Each of these was a real regression that reached COMPOSE or EXPLORE as
 * something else, hours later.  The contract's whole job is to say it here,
 * in the words of the thing that is missing.</p>
 */
public class PublicationContractTest {

    private static final String SITE =
            "<fixture.Saver: void save(java.io.OutputStream)>#u55";
    private static final String TARGET_SITE =
            "<fixture.Saver: void save(java.io.OutputStream)>#u61";

    /** A kept task nothing published for is named, not silently dropped. */
    @Test
    public void publicationContractRules() throws Exception {
        aKeptTaskThatPublishedNothingIsNamed();
        aSkipTheImporterAlreadyNamedIsNotASilentTask();
        aTargetPrefixSiteNoActivationDecidedIsNamed();
        aTargetThatDecidedItsWholePrefixIsClean();
        aRegionPathGoalIsNotHeldToItsWholeBranchList();
        theTableCountsEachCodeOnceAndNamesItsFirstSubject();
        anActivationUnderAnotherRequestIsNamed();
        anActivationUnderTheAnchoredRequestIsNotNamed();
        aDivergedRequestIsDiagnosticNotBlocking();
        aTaskWithNoAnchoredRequestIsNotNamed();
    }

    private void aKeptTaskThatPublishedNothingIsNamed() {
        List<JsonObject> rows = PublicationContract.check(
                tasks(target("TASK.a")), Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList());

        assertEquals(1, rows.size());
        assertEquals(PublicationContract.TASK_SILENT,
                rows.get(0).get("code").getAsString());
        assertEquals("TASK.a", rows.get(0).get("subject").getAsString());
    }

    /** A skip is a publication: the importer named it, and it is not this. */
    private void aSkipTheImporterAlreadyNamedIsNotASilentTask() {
        JsonObject named = new JsonObject();
        named.addProperty("code", "REGION_ROOT_NEVER_EXECUTED");
        named.addProperty("taskId", "TASK.a");

        assertTrue(PublicationContract.check(tasks(target("TASK.a")),
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(named)).isEmpty());
    }

    /** The target goal's prefix is a path the replay was asked to follow. */
    private void aTargetPrefixSiteNoActivationDecidedIsNamed() {
        List<JsonObject> rows = PublicationContract.check(
                tasks(target("TASK.a")),
                Collections.singletonList(summary("TASK.a", TARGET_SITE)),
                Collections.<JsonObject>emptyList());

        assertEquals(1, rows.size());
        assertEquals(PublicationContract.BRANCH_PREFIX_UNPUBLISHED,
                rows.get(0).get("code").getAsString());
        assertTrue(rows.get(0).get("detail").getAsString().contains(SITE));
    }

    /** Every prefix site decided is the contract met. */
    private void aTargetThatDecidedItsWholePrefixIsClean() {
        assertTrue(PublicationContract.check(tasks(target("TASK.a")),
                Collections.singletonList(
                        summary("TASK.a", SITE, TARGET_SITE)),
                Collections.<JsonObject>emptyList()).isEmpty());
    }

    /** A region-path goal's branches are sites, not a required prefix. */
    private void aRegionPathGoalIsNotHeldToItsWholeBranchList() {
        assertTrue(PublicationContract.check(tasks(regionPath("TASK.a")),
                Collections.singletonList(summary("TASK.a", TARGET_SITE)),
                Collections.<JsonObject>emptyList()).isEmpty());
    }

    /** One table per wave: code, count, first subject. */
    private void theTableCountsEachCodeOnceAndNamesItsFirstSubject() {
        List<JsonObject> rows = PublicationContract.check(
                tasks(target("TASK.a"), target("TASK.b")),
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList());

        List<String> table = PublicationContract.table(rows);
        assertEquals(2, table.size());
        assertTrue(table.get(0), table.get(0).contains("first subject"));
        assertTrue(table.get(1), table.get(1).contains(
                PublicationContract.TASK_SILENT));
        assertTrue(table.get(1), table.get(1).contains("TASK.a"));
    }

    /**
     * An activation that answered the address under another request is named.
     *
     * <p>The address is the identity and the request is a circumstance -- so
     * the activation is admitted -- but a circumstance the recording had and
     * the replay did not is a divergence, and it was silent.  On hdfs-17899
     * bug2 the SPS's BlockKeyUpdater daemon answers the {@code addKeys}
     * occurrence the recording took on {@code main} inside
     * {@code refresh-block-keys#1} while carrying no request at all, and the
     * send it then makes has no request to name.</p>
     */
    private void anActivationUnderAnotherRequestIsNamed() {
        JsonObject task = anchored(target("TASK.a"),
                "wl/nn0#epoch0/request/refresh-block-keys#1");
        JsonObject ran = summary("TASK.a", SITE, TARGET_SITE);
        ran.addProperty("requestKey", "");
        ran.addProperty("threadName", "KeyManager$BlockKeyUpdater@1");

        List<JsonObject> rows = PublicationContract.check(tasks(task),
                Collections.singletonList(ran),
                Collections.<JsonObject>emptyList());

        assertEquals(1, rows.size());
        assertEquals(PublicationContract.ACTIVATION_REQUEST_DIVERGED,
                rows.get(0).get("code").getAsString());
        String detail = rows.get(0).get("detail").getAsString();
        assertTrue(detail, detail.contains("no request"));
        assertTrue(detail, detail.contains("refresh-block-keys#1"));
        assertTrue(detail, detail.contains("KeyManager$BlockKeyUpdater@1"));
    }

    /** Under the request the anchor names, nothing is said. */
    private void anActivationUnderTheAnchoredRequestIsNotNamed() {
        String request = "wl/nn0#epoch0/request/refresh-block-keys#1";
        JsonObject task = anchored(target("TASK.a"), request);
        JsonObject ran = summary("TASK.a", SITE, TARGET_SITE);
        ran.addProperty("requestKey", request);
        ran.addProperty("threadName", "main");

        assertTrue(PublicationContract.check(tasks(task),
                Collections.singletonList(ran),
                Collections.<JsonObject>emptyList()).isEmpty());
    }

    /**
     * The row is evidence, not a contract failure.
     *
     * <p>The k-th request of a periodic api -- bug1's heartbeat#4 where the
     * anchor names heartbeat#2 -- and the scope a background thread happens
     * to sit under are timing facts about the run, not facts about the
     * workload.  The address is the identity, so the activation is admitted
     * and the row published; epoch re-seeding is what consumes it.</p>
     */
    private void aDivergedRequestIsDiagnosticNotBlocking() {
        assertEquals(edu.uva.liftlab.graphchecker.contract.GapLedger
                        .GapClass.DIAGNOSTIC,
                edu.uva.liftlab.graphchecker.contract.GapLedger.classOf(
                        PublicationContract.ACTIVATION_REQUEST_DIVERGED));

        // And the row says so, and the campaign reads it from there.  The
        // ledger's answer was written down and never consulted: contract
        // rows carried no class and the tally counted every one of them as
        // blocking, so on hdfs-17897 lane17897f four diagnostic rows stopped
        // the campaign at IMPORT under the words "4 blocking row(s)".
        JsonObject task = anchored(target("TASK.a"),
                "wl/nn0#epoch0/request/refresh-block-keys#1");
        JsonObject ran = summary("TASK.a", SITE, TARGET_SITE);
        ran.addProperty("requestKey", "wl/dn1#epoch0/request/heartbeat#3");
        ran.addProperty("threadName", "IPC Server handler 6");
        List<JsonObject> rows = PublicationContract.check(tasks(task),
                Collections.singletonList(ran),
                Collections.<JsonObject>emptyList());

        assertEquals(1, rows.size());
        assertEquals("DIAGNOSTIC",
                rows.get(0).get(PublicationContract.CLASS).getAsString());
        assertTrue("the row carries the ledger's own reason",
                rows.get(0).get(PublicationContract.CLASS_REASON)
                        .getAsString().contains("circumstance"));
        assertTrue("and the campaign does not stop on it",
                PublicationContract.blocking(rows).isEmpty());

        // The control: a row the ledger classes BLOCKING still stops it.
        List<JsonObject> silent = PublicationContract.check(
                tasks(target("TASK.b")), Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList());
        assertEquals("BLOCKING",
                silent.get(0).get(PublicationContract.CLASS).getAsString());
        assertEquals(1, PublicationContract.blocking(silent).size());
    }

    /** A task whose anchor names no request diverges from nothing. */
    private void aTaskWithNoAnchoredRequestIsNotNamed() {
        JsonObject ran = summary("TASK.a", SITE, TARGET_SITE);
        ran.addProperty("requestKey", "");
        ran.addProperty("threadName", "KeyManager$BlockKeyUpdater@1");

        assertTrue(PublicationContract.check(tasks(target("TASK.a")),
                Collections.singletonList(ran),
                Collections.<JsonObject>emptyList()).isEmpty());
    }

    /** The same task row, with a causal anchor naming one request. */
    private static JsonObject anchored(JsonObject row, String requestKey) {
        JsonObject anchor = new JsonObject();
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        anchor.addProperty("sourceKey", "wl/nn0#epoch0");
        anchor.addProperty("requestKey", requestKey);
        anchor.addProperty("requestApi", "refresh-block-keys");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", "<fixture.Saver: void save(java.io.OutputStream)>");
        selector.add("causalAnchor", anchor);
        row.add("rootSelector", selector);
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

    private static JsonObject target(String taskId) {
        JsonObject row = task(taskId, "TARGET_REACH_CLOSURE");
        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId", TARGET_SITE);
        targetBranch.addProperty("occurrence", 1);
        targetBranch.addProperty("outcome", false);
        row.add("targetBranch", targetBranch);
        return row;
    }

    private static JsonObject regionPath(String taskId) {
        return task(taskId, "REGION_PATH_CLOSURE");
    }

    private static JsonObject task(String taskId, String goalKind) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_EXECUTION_TASK");
        row.addProperty("taskId", taskId);
        row.addProperty("goalId", "GOAL." + taskId);
        row.addProperty("goalKind", goalKind);
        row.addProperty("regionId", "REGION.fixture");
        row.addProperty("sourceKey", "wl/nn0#epoch0");
        row.addProperty("occurrenceId",
                "wl/nn0#epoch0/region/REGION.fixture#1");
        row.addProperty("relationKey", "wl/nn0/relation/REGION.fixture");
        row.add("branches", branches(SITE, TARGET_SITE));
        row.add("inputActions", new JsonArray());
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        row.add("admission", admission);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(row);
        return row;
    }

    private static JsonArray branches(String... sites) {
        JsonArray branches = new JsonArray();
        for (String site : sites) {
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", site);
            branch.addProperty("occurrence", 1);
            branch.addProperty("outcome", false);
            branches.add(branch);
        }
        return branches;
    }

    private static JsonObject summary(String taskId, String... decided) {
        JsonObject row = new JsonObject();
        row.addProperty("taskId", taskId);
        row.addProperty("occurrenceId",
                "wl/nn0#epoch0/region/REGION.fixture#1#a1");
        JsonArray mappings = new JsonArray();
        for (String site : decided) {
            JsonObject siteRow = new JsonObject();
            siteRow.addProperty("siteId", site);
            JsonObject observation = new JsonObject();
            observation.add("site", siteRow);
            JsonObject mapping = new JsonObject();
            mapping.add("concreteObservation", observation);
            mappings.add(mapping);
        }
        row.add("branchMappings", mappings);
        return row;
    }
}
