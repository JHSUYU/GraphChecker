package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Two selected occurrences of one region on one root ride one activation.
 *
 * <p>A campaign instruments one entry hook per plan row, so HDFS-11741's
 * balancer {@code Dispatcher$1} -- which carries occurrence {@code #1} and
 * occurrence {@code #9} of region {@code 16599220} -- calls two entry hooks on
 * every activation.  campaign-takeover-22 let each hook start its own region:
 * {@code CURRENT_TOKEN} holds one token per thread, so the inner region took
 * every capture, the SASL handshake was exported under {@code #1} (which then
 * failed on its own constructor captures) and {@code #9} sat live and blind and
 * reported all three of its handshake leaves missing.</p>
 */
public class ConcolicRegionRuntimeSiblingOccurrenceTest {
    private static final String ROOT = "<example.Dispatcher$1: void run()>";
    private static final String SOURCE = "test/client#epoch0";
    private static final String FIRST = "TASK.occurrence-1";
    private static final String NINTH = "TASK.occurrence-9";
    private static final String OTHER_SOURCE = "TASK.other-source";
    private static final String SCOPED = "TASK.request-scoped";
    private static final String OTHER_API = "TASK.other-request-api";
    private static final String API = "encryptedWorkload";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;

    @Before
    public void rememberProperties() {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
        RuntimeTraceContext.resetForTests();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        RuntimeTraceContext.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    @Test
    public void oneActivationCarriesEveryOpenOccurrenceOfItsAddress()
            throws Exception {
        load();
        Object receiver = new Object();
        RuntimeTraceContext.registerSource(receiver, new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "test/client", 0L));

        // The activation is admitted under the occurrence the plan lists
        // first, exactly as before.
        assertEquals(FIRST, ConcolicRegionRuntime.admitCampaignTaskForTests(
                FIRST, ROOT, receiver, new Object[0]));

        // ... and the other occurrence of the same region on the same address
        // rides it, rather than starting a second region of its own.
        List<String> claimed =
                ConcolicRegionRuntime.claimSiblingOccurrencesForTests(
                        FIRST, ROOT, receiver, new Object[0]);
        assertEquals(claimed.toString(), 1, claimed.size());
        assertEquals(NINTH, claimed.get(0));

        // An occurrence of the same region on another source keeps its own
        // address: riding along never widens who may answer one.
        assertTrue(claimed.toString(), !claimed.contains(OTHER_SOURCE));

        // The claimed sibling is live, so its own entry hook admits nothing
        // and no second VM region context is started on this thread.
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                NINTH, ROOT, receiver, new Object[0]));
    }

    /**
     * The once-only write's activation carries the occurrence that demands
     * it, whichever of them the plan states at request scope.
     *
     * <p>A once-only heap write -- a cache-guarded lazy initializer -- runs
     * in the FIRST activation of its root and never again.  HDFS-11741 plans
     * two occurrences of the balancer's {@code Dispatcher$1} region: one
     * addressed by the request it serves, and one admitted for a shared
     * location it must produce, which is the only one carrying the
     * constructor's capture bindings.  Comparing the two selectors'
     * {@code requestApi} to each other made them permanent strangers, so the
     * activation that ran the initializer carried only the request-scoped
     * occurrence -- which declares no capture for it -- and the occurrence
     * that does was admitted on a later activation, after the guard closed.
     * The gate is the invocation's, not the other selector's.</p>
     */
    @Test
    public void aRequestScopedOccurrenceCarriesItsUnscopedSibling()
            throws Exception {
        load();
        Object receiver = new Object();
        RuntimeTraceContext.registerSource(receiver, new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "test/client", 0L));

        List<String> claimed =
                ConcolicRegionRuntime.claimSiblingOccurrencesForTests(
                        SCOPED, ROOT, receiver, new Object[0], API);
        // The occurrence that carries the once-only write's bindings states
        // no request API, so this invocation admits it.
        assertTrue(claimed.toString(), claimed.contains(FIRST));
        assertTrue(claimed.toString(), claimed.contains(NINTH));
        // An occurrence addressed by a different request API is not this
        // invocation's occurrence and never rides it.
        assertTrue(claimed.toString(), !claimed.contains(OTHER_API));
        // Nor is one on another source.
        assertTrue(claimed.toString(), !claimed.contains(OTHER_SOURCE));
    }

    /**
     * The claim applies {@code select}'s own gate, so it fails closed on an
     * invocation that entered no request scope.
     */
    @Test
    public void anInvocationOutsideARequestScopeClaimsNoScopedOccurrence()
            throws Exception {
        load();
        Object receiver = new Object();
        RuntimeTraceContext.registerSource(receiver, new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "test/client", 0L));

        List<String> claimed =
                ConcolicRegionRuntime.claimSiblingOccurrencesForTests(
                        FIRST, ROOT, receiver, new Object[0], "");
        assertEquals(claimed.toString(), 1, claimed.size());
        assertEquals(NINTH, claimed.get(0));
    }

    private void load() throws Exception {
        JsonObject first = task(FIRST, SOURCE + "/region/REGION.1#1", SOURCE);
        JsonObject ninth = task(NINTH, SOURCE + "/region/REGION.1#9", SOURCE);
        JsonObject other = task(OTHER_SOURCE,
                "test/other#epoch0/region/REGION.1#1", "test/other#epoch0");
        JsonObject scoped = requestScoped(task(SCOPED,
                SOURCE + "/region/REGION.1#3", SOURCE), API);
        JsonObject otherApi = requestScoped(task(OTHER_API,
                SOURCE + "/region/REGION.1#4", SOURCE), "otherWorkload");
        Path plan = folder.newFile("sibling-plan.jsonl").toPath();
        Files.write(plan, (first + "\n" + ninth + "\n" + other + "\n"
                        + scoped + "\n" + otherApi + "\n")
                .getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                FIRST + "," + NINTH + "," + OTHER_SOURCE + "," + SCOPED
                        + "," + OTHER_API);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("results.jsonl").toString());
    }

    /** Addresses one planned occurrence by the request API it serves. */
    private static JsonObject requestScoped(JsonObject task,
                                            String requestApi) {
        task.getAsJsonObject("rootSelector").getAsJsonObject("causalAnchor")
                .addProperty("requestApi", requestApi);
        return task;
    }

    private static JsonObject task(String taskId, String occurrenceId,
                                   String sourceKey) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("goalId", "GOAL." + taskId);
        task.addProperty("sourceKey", sourceKey);
        task.addProperty("occurrenceId", occurrenceId);
        task.addProperty("relationKey", "RELATION.REGION.1");
        task.addProperty("regionId", "REGION.1");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", Object.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", sourceKey);
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

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}
