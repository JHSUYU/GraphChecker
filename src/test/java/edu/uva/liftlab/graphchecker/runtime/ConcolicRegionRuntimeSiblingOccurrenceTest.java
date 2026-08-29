package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
    private static final String CONCURRENT = "TASK.concurrent-activation";
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

        // A concurrent invocation with the same method/region/source owns a
        // different frozen activation and must remain independently
        // admissible.
        assertTrue(claimed.toString(), !claimed.contains(CONCURRENT));

        // An occurrence of the same region on another source keeps its own
        // address: riding along never widens who may answer one.
        assertTrue(claimed.toString(), !claimed.contains(OTHER_SOURCE));

        // The claimed sibling is live, so its own entry hook admits nothing
        // and no second VM region context is started on this thread.
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                NINTH, ROOT, receiver, new Object[0]));
    }

    @Test
    public void completedHookDefersToAnUnfinishedActivationHook()
            throws Exception {
        load();
        Object receiver = new Object();
        RuntimeTraceContext.registerSource(receiver, new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "test/client", 0L));

        Method configured = ConcolicRegionRuntime.class.getDeclaredMethod(
                "configuration");
        configured.setAccessible(true);
        Object configuration = configured.invoke(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object completed = taskById.invoke(configuration, FIRST);
        Field reserved = completed.getClass().getDeclaredField(
                "completedRelationReserved");
        reserved.setAccessible(true);
        reserved.setBoolean(completed, true);

        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                FIRST, ROOT, receiver, new Object[0]));
        assertEquals(CONCURRENT,
                ConcolicRegionRuntime.admitCampaignTaskForTests(
                        CONCURRENT, ROOT, receiver, new Object[0]));
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

    /**
     * Access-owner carriers belong to every occurrence riding the activation,
     * just like their symbolic live-ins and output captures do.
     */
    @Test
    public void accessOwnerCarriersIncludeSiblingsAndDeduplicatePerOwner()
            throws Exception {
        load();
        Object active = activateWithSibling(71L);
        CarrierOwner firstOwner = new CarrierOwner();
        CarrierOwner secondOwner = new CarrierOwner();

        String activeField = fieldSignature("activeValue");
        String siblingField = fieldSignature("siblingValue");
        ConcolicRegionRuntime.selectFieldWriteCarrier(firstOwner,
                activeField);
        ConcolicRegionRuntime.selectFieldWriteCarrier(firstOwner,
                activeField);
        ConcolicRegionRuntime.selectFieldWriteCarrier(firstOwner,
                siblingField);
        ConcolicRegionRuntime.selectFieldWriteCarrier(firstOwner,
                siblingField);
        ConcolicRegionRuntime.selectFieldWriteCarrier(secondOwner,
                siblingField);

        Set<String> expected = new LinkedHashSet<>(Arrays.asList(
                selectionKey(firstOwner, "activeValue"),
                selectionKey(firstOwner, "siblingValue"),
                selectionKey(secondOwner, "siblingValue")));
        assertEquals(expected, accessOwnerSelections(active));
        // Stock JDKs expose no shared-state native.  One refusal per key proves
        // both that the sibling-only field was offered and that duplicate
        // claimant declarations and repeated accesses were selected once.
        assertEquals(3, sharedStateGaps(active).size());
    }

    private void load() throws Exception {
        JsonObject first = task(FIRST, SOURCE + "/region/REGION.1#1", SOURCE);
        JsonObject ninth = task(NINTH, SOURCE + "/region/REGION.1#9", SOURCE);
        JsonObject concurrent = task(CONCURRENT,
                SOURCE + "/region/REGION.1#10", SOURCE);
        concurrent.addProperty("activationId", "ACT.concurrent");
        first.add(ExecutionTask.SHARED_CARRIERS,
                carrierDeclarations("activeValue"));
        ninth.add(ExecutionTask.SHARED_CARRIERS,
                carrierDeclarations("activeValue", "siblingValue"));
        JsonObject other = task(OTHER_SOURCE,
                "test/other#epoch0/region/REGION.1#1", "test/other#epoch0");
        JsonObject scoped = requestScoped(task(SCOPED,
                SOURCE + "/region/REGION.1#3", SOURCE), API);
        JsonObject otherApi = requestScoped(task(OTHER_API,
                SOURCE + "/region/REGION.1#4", SOURCE), "otherWorkload");
        Path plan = folder.newFile("sibling-plan.jsonl").toPath();
        Files.write(plan, (first + "\n" + ninth + "\n" + concurrent + "\n"
                        + other + "\n"
                        + scoped + "\n" + otherApi + "\n")
                .getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                FIRST + "," + NINTH + "," + CONCURRENT + ","
                        + OTHER_SOURCE + "," + SCOPED + "," + OTHER_API);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("results.jsonl").toString());
    }

    private static JsonArray carrierDeclarations(String... fields) {
        JsonArray declarations = new JsonArray();
        for (String field : fields) {
            JsonObject declaration = new JsonObject();
            declaration.addProperty("kind", "INSTANCE_FIELD");
            declaration.addProperty("sourceKind",
                    "ACTIVATION_FIELD_RECEIVER");
            declaration.addProperty("declaringClass",
                    CarrierOwner.class.getName());
            declaration.addProperty("fieldName", field);
            declaration.addProperty("descriptor", "I");
            declarations.add(declaration);
        }
        return declarations;
    }

    private static Object activateWithSibling(long token) throws Exception {
        Method configured = ConcolicRegionRuntime.class.getDeclaredMethod(
                "configuration");
        configured.setAccessible(true);
        Object configuration = configured.invoke(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object primary = taskById.invoke(configuration, FIRST);
        Object sibling = taskById.invoke(configuration, NINTH);

        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, primary.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(token, primary, new Object(),
                Thread.currentThread());

        Field siblings = activeType.getDeclaredField("siblingClaimants");
        siblings.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Object> claimants = (List<Object>) siblings.get(active);
        claimants.add(sibling);

        Field activeRegions = ConcolicRegionRuntime.class.getDeclaredField(
                "ACTIVE");
        activeRegions.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<Long, Object> regions =
                (Map<Long, Object>) activeRegions.get(null);
        regions.put(token, active);
        currentToken().set(token);
        return active;
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Long> currentToken() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        field.setAccessible(true);
        return (ThreadLocal<Long>) field.get(null);
    }

    @SuppressWarnings("unchecked")
    private static Set<String> accessOwnerSelections(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField(
                "accessOwnerCarrierSelections");
        field.setAccessible(true);
        return new LinkedHashSet<>((Set<String>) field.get(active));
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> sharedStateGaps(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("sharedStateGaps");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    private static String fieldSignature(String fieldName) {
        return "<" + CarrierOwner.class.getName() + ": int " + fieldName
                + ">";
    }

    private static String selectionKey(Object owner, String fieldName) {
        return CarrierOwner.class.getName() + "#" + fieldName + "@"
                + System.identityHashCode(owner);
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
        task.addProperty("activationId", "ACT.shared");
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

    private static final class CarrierOwner {
        @SuppressWarnings("unused")
        private int activeValue;
        @SuppressWarnings("unused")
        private int siblingValue;
    }
}
