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
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * README {@code OCC-1}: every occurrence is its own symbol, so an address is
 * not answered once.
 *
 * <p>A further activation the same address selects is another occurrence of
 * it, published as its own row, not an ambiguity gap.  Treating the first
 * satisfying activation as THE occurrence is what made a whole replay's
 * remaining activations invisible: the balancer's SASL target read the
 * initial {@code allKeys} version because that was the first activation the
 * address admitted, and the reads that came after the removal - the ones the
 * formula needs - were reported as ambiguity and dropped.</p>
 */
public class ConcolicRegionRuntimeOccurrenceAmbiguityTest {
    private static final String TASK = "TASK.ambiguous-address";
    // A source id of this test's own: RuntimeTraceContext canonicalizes
    // registrations process-wide, so a key another test registers under a
    // different kind/role would be refused here.
    private static final String SOURCE_KEY =
            "test/occurrence-ambiguity/node#epoch0";
    private static final String OCCURRENCE =
            SOURCE_KEY + "/region/SERVICE#1";
    private static final String ROOT = "<example.Service: void run()>";
    private static final SourceRef SOURCE = new SourceRef("TEST", "CLIENT",
            "test/occurrence-ambiguity/node", 0L);
    private static final SourceRef OTHER_SOURCE = new SourceRef("TEST",
            "CLIENT", "test/occurrence-ambiguity/other", 0L);

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
     * A further activation of an already-answered address is admitted as the
     * next occurrence of it, and the run names no ambiguity.
     */
    @Test
    public void anAnsweredAddressKeepsAdmittingItsLaterActivations()
            throws Exception {
        load("ambiguous");

        ServiceRoot answered = new ServiceRoot();
        RuntimeTraceContext.registerSource(answered, SOURCE);
        assertTrue(ConcolicRegionRuntime.claimCampaignTaskForTests(
                TASK, ROOT, answered, new Object[0]));

        // Same root, same registered source, same request scope: nothing in
        // the address separates this activation from the answered one, and
        // under OCC-1 that makes it the address's next occurrence.
        ServiceRoot later = new ServiceRoot();
        RuntimeTraceContext.registerSource(later, SOURCE);
        assertEquals(TASK, ConcolicRegionRuntime.admitCampaignTaskForTests(
                TASK, ROOT, later, new Object[0]));

        ConcolicRegionRuntime.publishRunTotals();
        assertEquals(Collections.emptyList(), skippedRows());
    }

    /**
     * Admitting later activations does not widen the address: one the address
     * rejects is still rejected, and an answered address publishes no gap.
     */
    @Test
    public void aRejectedActivationIsStillRejectedAfterAnAnswer()
            throws Exception {
        load("rejected");

        ServiceRoot answered = new ServiceRoot();
        RuntimeTraceContext.registerSource(answered, SOURCE);
        assertTrue(ConcolicRegionRuntime.claimCampaignTaskForTests(
                TASK, ROOT, answered, new Object[0]));

        ServiceRoot elsewhere = new ServiceRoot();
        RuntimeTraceContext.registerSource(elsewhere, OTHER_SOURCE);
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                TASK, ROOT, elsewhere, new Object[0]));

        ConcolicRegionRuntime.publishRunTotals();
        assertEquals(Collections.emptyList(), skippedRows());
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
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());
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
