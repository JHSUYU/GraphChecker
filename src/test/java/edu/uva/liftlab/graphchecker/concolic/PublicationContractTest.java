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
    public void aKeptTaskThatPublishedNothingIsNamed() {
        List<JsonObject> rows = PublicationContract.check(
                tasks(target("TASK.a")), Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList());

        assertEquals(1, rows.size());
        assertEquals(PublicationContract.TASK_SILENT,
                rows.get(0).get("code").getAsString());
        assertEquals("TASK.a", rows.get(0).get("subject").getAsString());
    }

    /** A skip is a publication: the importer named it, and it is not this. */
    @Test
    public void aSkipTheImporterAlreadyNamedIsNotASilentTask() {
        JsonObject named = new JsonObject();
        named.addProperty("code", "REGION_CAUSAL_ANCHOR_NOT_OBSERVED");
        named.addProperty("taskId", "TASK.a");

        assertTrue(PublicationContract.check(tasks(target("TASK.a")),
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(named)).isEmpty());
    }

    /** The target goal's prefix is a path the replay was asked to follow. */
    @Test
    public void aTargetPrefixSiteNoActivationDecidedIsNamed() {
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
    @Test
    public void aTargetThatDecidedItsWholePrefixIsClean() {
        assertTrue(PublicationContract.check(tasks(target("TASK.a")),
                Collections.singletonList(
                        summary("TASK.a", SITE, TARGET_SITE)),
                Collections.<JsonObject>emptyList()).isEmpty());
    }

    /** A region-path goal's branches are sites, not a required prefix. */
    @Test
    public void aRegionPathGoalIsNotHeldToItsWholeBranchList() {
        assertTrue(PublicationContract.check(tasks(regionPath("TASK.a")),
                Collections.singletonList(summary("TASK.a", TARGET_SITE)),
                Collections.<JsonObject>emptyList()).isEmpty());
    }

    /** One table per wave: code, count, first subject. */
    @Test
    public void theTableCountsEachCodeOnceAndNamesItsFirstSubject() {
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
