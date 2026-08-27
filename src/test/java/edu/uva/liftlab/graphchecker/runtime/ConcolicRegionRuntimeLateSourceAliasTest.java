package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * What an exact {@code REGISTERED_SOURCE} address does when the receiver's
 * alias arrives after the root was first entered.
 *
 * <p>HDFS-11741's campaign-takeover-10 skipped its target task through a
 * producer whose root, {@code BPServiceActor.offerService()}, was entered
 * 14 s before {@code TestBalancer.bindClusterSources} aliased that actor to
 * {@code cluster0/dn0#epoch1}.  That looked like a missing deferral in
 * {@code Configuration.select}, and these tests exist because it is not one.
 * </p>
 *
 * <p>The address already stays open: an activation entered before its alias
 * is refused, notes its reason, and closes nothing, so the next entry of the
 * same root takes the address as soon as the alias exists.  Holding such a
 * candidate to admit it later would therefore change nothing for any root
 * entered more than once, and the one case it would change - a root entered
 * exactly once, before its alias - is not an address problem but a VM one.
 * Admission starts a region on the live Java frame, and
 * {@code ShadowStack::push} fixes {@code symbolic_tracking_enabled} when a
 * frame is pushed ({@code ShadowFrame} exposes a getter and no setter, and
 * {@code effective_tracking} is conjoined with the caller frame's flag), so
 * a frame pushed before the region started can never be made tracking
 * afterwards.  Admitting one anyway would publish a region whose root frame
 * propagates nothing and whose already-executed branches and backedges are
 * absent - an approximate result wearing an exact result's shape.</p>
 */
public class ConcolicRegionRuntimeLateSourceAliasTest {
    private static final String TASK = "TASK.late-alias";
    private static final String SOURCE_KEY =
            "test/late-source-alias/node#epoch0";
    private static final String OCCURRENCE =
            SOURCE_KEY + "/region/SERVICE#1";
    private static final String ROOT = "<example.Service: void offerService()>";
    private static final SourceRef SOURCE = new SourceRef("TEST", "CLIENT",
            "test/late-source-alias/node", 0L);

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;
    private Path results;

    @Before
    public void rememberProperties() {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    /**
     * The early unaliased activation is refused and closes nothing: the very
     * next entry of the same root on the same receiver, once the alias has
     * arrived, is admitted and addresses the planned occurrence.
     */
    @Test
    public void anAddressStaysOpenAcrossAnActivationEnteredBeforeItsAlias()
            throws Exception {
        load("stays-open");
        ServiceRoot root = new ServiceRoot();

        // Entered before bindClusterSources: no alias, so no exact address.
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                TASK, ROOT, root, new Object[0]));

        // The alias arrives, on another thread, long after that entry.
        RuntimeTraceContext.registerSource(root, SOURCE);

        // A later entry of the same root takes the address that was left open.
        assertEquals(TASK, ConcolicRegionRuntime.admitCampaignTaskForTests(
                TASK, ROOT, root, new Object[0]));
    }

    /** A root that is only ever entered unaliased is skipped, by name. */
    @Test
    public void anActivationNeverAliasedIsSkippedWithItsAnchorNamed()
            throws Exception {
        load("never-aliased");
        ServiceRoot root = new ServiceRoot();

        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                TASK, ROOT, root, new Object[0]));

        ConcolicRegionRuntime.publishRunTotals();

        List<JsonObject> rows = skippedRows();
        assertEquals(rows.toString(), 1, rows.size());
        String reason = rows.get(0).get("reason").getAsString();
        assertTrue(reason, reason.contains("had no registered source"));
        assertTrue(reason, reason.contains(SOURCE_KEY));
    }

    private List<JsonObject> skippedRows() throws Exception {
        List<JsonObject> rows = new ArrayList<>();
        if (!Files.exists(results)) return rows;
        for (String line : Files.readAllLines(results,
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject row = new JsonParser().parse(line).getAsJsonObject();
            if ("CONCOLIC_REGION_SKIPPED".equals(
                    row.get("event").getAsString())) {
                rows.add(row);
            }
        }
        return rows;
    }

    private void load(String name) throws Exception {
        Path plan = folder.newFile(name + "-plan.jsonl").toPath();
        Files.write(plan, (task() + "\n").getBytes(StandardCharsets.UTF_8));
        results = folder.getRoot().toPath().resolve(name + "-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL." + TASK);
        task.addProperty("sourceKey", SOURCE_KEY);
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "RELATION.SERVICE");
        task.addProperty("regionId", "SERVICE");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", ServiceRoot.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", SOURCE_KEY);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        task.add("edgeBindings", new JsonArray());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return task;
    }

    private static void restore(String property, String value) {
        if (value == null) System.clearProperty(property);
        else System.setProperty(property, value);
    }

    private static final class ServiceRoot {
    }
}
