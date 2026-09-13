package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.lang.reflect.Field;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * Four places where the replay used to invent a chain element, and what each
 * of them answers now.
 *
 * <p>They share one shape.  A link the recording does not supply is not a
 * licence to supply one: the engine either keeps the value it actually holds
 * and flags the activation, or it refuses.  What it may never do is mint a
 * root, pin a polarity, or accept a site as the target because some site was
 * reached.  Each case below pins both halves -- that the invented answer is
 * gone, and that the honest one is a named row a claim can read.</p>
 *
 * <p>The rows land in {@code unresolvedInputs}, which {@code
 * ConcolicSummaryImporter} turns into {@code UNRESOLVED_INPUT} and refuses
 * the whole summary under, so "reported" here means "blocks" and not
 * "decorates".</p>
 */
public class NoFabricatedChainElementTest {

    private static final String METHOD = "<a.B: void run(int)>";
    private static final String SITE = METHOD + "#u4";
    private static final String OTHER = METHOD + "#u9";
    private static final String MARKER = "hadoopIpcRequestFails";

    private final Deque<Long> opened = new ArrayDeque<>();

    @After
    public void releaseRegions() throws Exception {
        while (!opened.isEmpty()) {
            ConcolicRegionRuntime.ACTIVE.remove(opened.pop());
        }
        currentTokens().clear();
    }

    // ---------- 1. the unreadable propagated expression ----------

    /** A well-formed envelope that simply carries no expression still does. */
    @Test
    public void anAbsentExpressionIsStillTheHonestNothing() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false);
        assertNull(ConcolicRegionRuntime.engineExpression("{}"));
        assertTrue("no expression is not a failure",
                unresolved(active).isEmpty());
    }

    // ---------- 2. the fault-idle defaults ----------

    /**
     * A seed replay answers a controlled marker from the recording.
     *
     * <p>A seed has no model by construction -- it reproduces the recording
     * -- so reading "no model assignment" as "unanswered" refused every seed
     * summary that touches a declared marker, and with it the DEPENDENCY
     * worklist ({@code NO_OBSERVED_PATH_SEED / REGION_PATH_SEED_REQUIRED}),
     * which is a campaign that dies before it composes anything.  The
     * recording's polarity is stated on the action as {@code primitiveValue}
     * gated on {@code observed}, i.e. a value the mint witnessed.</p>
     */
    @Test
    public void aSeedReplayAnswersAControlledMarkerFromTheRecording()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion recordedFalse = region(false,
                recordedFaultAction(MARKER, 1, "false"));
        assertFalse(ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
        assertTrue("a recorded answer is not a gap",
                unresolved(recordedFalse).isEmpty());

        // And the recorded value is read, not assumed: a marker the
        // recording saw fire comes back true from the same seed path.
        ConcolicRegionRuntime.ActiveRegion recordedTrue = region(false,
                recordedFaultAction(MARKER, 1, "true"));
        assertTrue(ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
        assertTrue(unresolved(recordedTrue).isEmpty());
    }

    /**
     * A flip replay answers from its model, and the model outranks the
     * recorded value -- moving the marker off what the recording saw is the
     * entire point of the flip.
     */
    @Test
    public void aFlipReplayAnswersAControlledMarkerFromItsModel()
            throws Exception {
        JsonObject action = recordedFaultAction(MARKER, 1, "false");
        ConcolicRegionRuntime.ActiveRegion active = region(false,
                Collections.singletonList(action),
                modelAssignment(action.get("symbol").getAsString(), "true"));

        assertTrue("the model decides a flip",
                ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
        assertTrue(unresolved(active).isEmpty());
    }

    /** Neither a model nor a recorded value is the unanswered case. */
    @Test
    public void neitherAModelNorARecordedValueStillBlocks()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false,
                faultAction(MARKER, 1));
        assertFalse(ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
        String row = only(unresolved(active));
        assertTrue(row, row.startsWith(
                ConcolicRegionRuntime.FAULT_IDLE_UNANSWERED));
        assertTrue(row, row.contains(
                "reason=NO_MODEL_ASSIGNMENT_AND_NO_RECORDED_VALUE"));
    }

    // ---------- 3. the target link ----------

    /**
     * A throw is not a target reach.
     *
     * <p>When the task declares no target occurrence there is no link to
     * check, so the exception the workload happened to exit through used to
     * stand in for one -- and {@code nameUnreachedTargetBranch} returned
     * early for that exact case, so nothing was filed either.</p>
     */
    @Test
    public void anyThrowIsNoLongerATargetReach() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false);
        active.exitKind = "THROW";
        active.exceptionType = "java.lang.IllegalStateException";
        assertFalse("an undeclared target cannot have been reached",
                ConcolicResultPublisher.targetReachedByActivation(active));
        active.nameUnreachedTargetBranch();
        String row = only(unresolved(active));
        assertTrue(row, row.startsWith(
                ConcolicRegionRuntime.TARGET_REACH_NOT_OBSERVED));
        assertTrue(row, row.contains("java.lang.IllegalStateException"));
    }

    /** The declared occurrence, decided at its required outcome, still is. */
    @Test
    public void theDeclaredTargetOccurrenceStillReaches() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(true);
        active.exitKind = "THROW";
        active.exceptionType = "java.lang.IllegalStateException";
        recordReach(active, SITE, 1, true);
        assertTrue(ConcolicResultPublisher.targetReachedByActivation(active));
        active.nameUnreachedTargetBranch();
        assertTrue("a genuine reach files nothing",
                unresolved(active).isEmpty());
    }

    // ---------- harness ----------

    private static Map<String, Object> policy(boolean required) {
        Map<String, Object> policy = new LinkedHashMap<>();
        policy.put("siteId", SITE);
        policy.put("requiredOutcome", required);
        policy.put("failureTarget", Boolean.TRUE);
        return policy;
    }

    private static RuntimeRegionPlanner.RuntimeEvent branchEvent(
            long seq, boolean outcome) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "BRANCH", METHOD,
                seq, seq, SITE, "", -1, "", 0, "", outcome, null, "", "");
    }

    /** The same action with the polarity the recording observed. */
    private static JsonObject recordedFaultAction(
            String name, int replayOccurrence, String primitiveValue) {
        JsonObject json = faultAction(name, replayOccurrence);
        json.addProperty("observed", true);
        json.addProperty("primitiveValue", primitiveValue);
        return json;
    }

    private static ConcolicRegionRuntime.SymbolizeAction action(
            JsonObject json) {
        return new ConcolicRegionRuntime.SymbolizeAction(json);
    }

    private static JsonObject modelAssignment(String inputSymbol,
                                              String value) {
        JsonObject json = new JsonObject();
        json.addProperty("inputSymbol", inputSymbol);
        json.addProperty("engineSymbol", inputSymbol);
        json.addProperty("valueType", "BOOL");
        json.addProperty("value", value);
        return json;
    }

    private static JsonObject faultAction(String name,
                                          int replayOccurrence) {
        JsonObject json = faultJson(name, replayOccurrence);
        json.addProperty("sourceKind", RuntimeSelectedRegionFinalizer
                .EXPLICIT_SYMBOLIC_FAULT);
        return json;
    }

    private static JsonObject faultJson(String name, int replayOccurrence) {
        JsonObject json = new JsonObject();
        json.addProperty("symbol", "REGION.ipc.in." + name + "."
                + replayOccurrence);
        json.addProperty("javaType", "boolean");
        json.addProperty("location", "CALL_RETURN");
        json.addProperty("rootKind", "ACTIVATION_LOCAL");
        json.addProperty("symbolicName", name);
        json.addProperty("replayOccurrence", replayOccurrence);
        json.addProperty("mode", "SYMBOLIC");
        return json;
    }

    private static ExecutionTask task(boolean addressesTarget,
                                      JsonObject... actions) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "dn0#epoch0");
        encoded.addProperty("occurrenceId", "REGION.1@dn0#epoch0#1");
        encoded.addProperty("rootMethod", METHOD);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "dn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", SITE);
        branch.addProperty("policy", "EXPLORE");
        branch.addProperty("selectedOccurrence", 1);
        branch.addProperty("requiredOutcome", true);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        encoded.add("branches", branches);
        JsonArray inputActions = new JsonArray();
        for (JsonObject action : actions) inputActions.add(action);
        encoded.add("inputActions", inputActions);
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        if (addressesTarget) {
            JsonObject target = new JsonObject();
            target.addProperty("siteId", SITE);
            target.addProperty("occurrence", 1);
            encoded.add("targetBranch", target);
        }
        return ExecutionTask.decode(encoded);
    }

    private ConcolicRegionRuntime.ActiveRegion region(
            boolean addressesTarget,
            java.util.List<JsonObject> actions, JsonObject... assignments)
            throws Exception {
        ExecutionTask encoded = task(addressesTarget,
                actions.toArray(new JsonObject[0]));
        JsonArray models = new JsonArray();
        for (JsonObject assignment : assignments) models.add(assignment);
        JsonObject json = encoded.json().deepCopy();
        json.add("modelAssignments", models);
        return open(ExecutionTask.decode(json));
    }

    private ConcolicRegionRuntime.ActiveRegion region(
            boolean addressesTarget, JsonObject... actions)
            throws Exception {
        return open(task(addressesTarget, actions));
    }

    private ConcolicRegionRuntime.ActiveRegion open(ExecutionTask encoded)
            throws Exception {
        ConcolicTaskPlan.RuntimeTask runtime =
                new ConcolicTaskPlan.RuntimeTask(encoded);
        long token = 910000L + opened.size() + 1;
        ConcolicRegionRuntime.ActiveRegion active =
                new ConcolicRegionRuntime.ActiveRegion(token, runtime, null,
                        Thread.currentThread(), false);
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        opened.push(token);
        return active;
    }

    private static void recordReach(ConcolicRegionRuntime.ActiveRegion active,
                                    String siteId, int occurrence,
                                    boolean outcome) throws Exception {
        JsonObject reach = new JsonObject();
        reach.addProperty("kind", "TARGET_REACH_EVENT");
        reach.addProperty("siteId", siteId);
        reach.addProperty("occurrence", occurrence);
        reach.addProperty("outcome", outcome);
        Field field = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("targetReach");
        field.setAccessible(true);
        field.set(active, reach);
    }

    @SuppressWarnings("unchecked")
    private static Set<String> unresolved(
            ConcolicRegionRuntime.ActiveRegion active) throws Exception {
        Field field = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("unresolved");
        field.setAccessible(true);
        return (Set<String>) field.get(active);
    }

    private static boolean anyUnresolvedStartsWith(
            ConcolicRegionRuntime.ActiveRegion active, String prefix)
            throws Exception {
        for (String row : unresolved(active)) {
            if (row.startsWith(prefix)) return true;
        }
        return false;
    }

    private static <T> T only(java.util.Collection<T> values) {
        assertEquals(String.valueOf(values), 1, values.size());
        return values.iterator().next();
    }

    @SuppressWarnings("unchecked")
    private static Deque<Long> currentTokens() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Long>>) field.get(null)).get();
    }
}
