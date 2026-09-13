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

    /**
     * A payload the expression store cannot read is not "nothing
     * propagated".
     *
     * <p>Returning {@code null} here was the whole defect: {@code
     * carriesInputAuthority} answers {@code false} for a {@code null}, every
     * caller reads {@code false} as permission to mint, and the producer's
     * expression is replaced by a free variable nothing constrains.  The
     * failure now has its own type so no caller can confuse the two.</p>
     */
    @Test
    public void anUnreadableImportRefusesRatherThanReadingAsNothing()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false);
        try {
            ConcolicRegionRuntime.engineExpression("{not json at all");
            fail("a malformed import must not answer 'nothing propagated'");
        } catch (ConcolicRegionRuntime.PropagatedExpressionImportFailure
                expected) {
            assertTrue(expected.getMessage().startsWith(
                    ConcolicRegionRuntime
                            .PROPAGATED_EXPRESSION_IMPORT_FAILED));
        }
        assertTrue("the import failure must reach the activation ledger",
                anyUnresolvedStartsWith(active, ConcolicRegionRuntime
                        .PROPAGATED_EXPRESSION_IMPORT_FAILED));
    }

    /** A well-formed envelope that simply carries no expression still does. */
    @Test
    public void anAbsentExpressionIsStillTheHonestNothing() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false);
        assertNull(ConcolicRegionRuntime.engineExpression("{}"));
        assertTrue("no expression is not a failure",
                unresolved(active).isEmpty());
    }

    /** The consumer-side row names who asked and for which field. */
    @Test
    public void theRefusalNamesTheConsumerAndTheField() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false);
        ConcolicRegionRuntime.refuseImportedExpression(active, "sym.port",
                "<a.B: int f>",
                new ConcolicRegionRuntime.PropagatedExpressionImportFailure(
                        "PROPAGATED_EXPRESSION_IMPORT_FAILED: producer=x",
                        null));
        String row = only(unresolved(active));
        assertTrue(row, row.contains("consumer=sym.port"));
        assertTrue(row, row.contains("field=<a.B: int f>"));
        assertTrue(row, row.contains("producer=x"));
    }

    // ---------- 2. the fault-idle defaults ----------

    /**
     * A marker this plan controls, asked at a firing it cannot answer.
     *
     * <p>The old code returned {@code false} and filed nothing, which pins
     * the marker to exactly the polarity the search exists to flip.  The
     * value still has to be a {@code boolean} -- the workload is about to
     * branch on it -- so the fix is that the activation is flagged and the
     * summary refuses, not that the call returns something else.</p>
     */
    @Test
    public void acontrolledMarkerWithNoAnswerBlocks() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false,
                faultAction(MARKER, 7));
        assertFalse("the workload still gets a boolean",
                ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
        String row = only(unresolved(active));
        assertTrue(row, row.startsWith(
                ConcolicRegionRuntime.FAULT_IDLE_UNANSWERED));
        assertTrue(row, row.contains("marker=" + MARKER + "#1"));
        assertTrue(row, row.contains(
                "reason=NO_ACTION_ACCEPTS_THIS_OCCURRENCE"));
    }

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

    /** A value the mint did not witness is not the recording's answer. */
    @Test
    public void anUnobservedPrimitiveValueIsNotARecordedAnswer()
            throws Exception {
        JsonObject unobserved = recordedFaultAction(MARKER, 1, "true");
        unobserved.addProperty("observed", false);
        ConcolicRegionRuntime.ActiveRegion active = region(false, unobserved);

        assertFalse(ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
        String row = only(unresolved(active));
        assertTrue(row, row.startsWith(
                ConcolicRegionRuntime.FAULT_IDLE_UNANSWERED));
        assertTrue(row, row.contains(
                "reason=NO_MODEL_ASSIGNMENT_AND_NO_RECORDED_VALUE"));
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

    /** The recorded polarity is read strictly: only a boolean literal. */
    @Test
    public void onlyABooleanLiteralIsARecordedPolarity() {
        assertEquals(Boolean.FALSE, ConcolicRegionRuntime
                .recordedFaultPolarity(action(
                        recordedFaultAction(MARKER, 1, "false"))));
        assertEquals(Boolean.TRUE, ConcolicRegionRuntime
                .recordedFaultPolarity(action(
                        recordedFaultAction(MARKER, 1, "true"))));
        assertNull("a marker is a boolean, and 1 is not one",
                ConcolicRegionRuntime.recordedFaultPolarity(action(
                        recordedFaultAction(MARKER, 1, "1"))));
        assertNull(ConcolicRegionRuntime.recordedFaultPolarity(action(
                recordedFaultAction(MARKER, 1, ""))));
        assertNull(ConcolicRegionRuntime.recordedFaultPolarity(null));
    }

    /**
     * A marker no plan row declares put no question to this replay, so
     * there is nothing to refuse and the ledger stays empty.
     */
    @Test
    public void anUncontrolledMarkerIsIdleWithoutBlocking() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(false);
        assertFalse(ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
        assertTrue("an undeclared marker refuses nothing",
                unresolved(active).isEmpty());
    }

    /** Which markers a plan controls is read off the finalizer's field. */
    @Test
    public void controlIsReadOffTheSourceKindTheFinalizerStamps() {
        ConcolicRegionRuntime.SymbolizeAction fault =
                new ConcolicRegionRuntime.SymbolizeAction(
                        faultAction(MARKER, 1));
        assertTrue(ConcolicRegionRuntime.declaresExplicitFault(
                Collections.singletonList(fault), MARKER));
        assertFalse("a different marker is a different question",
                ConcolicRegionRuntime.declaresExplicitFault(
                        Collections.singletonList(fault), "otherMarker"));
        assertFalse(ConcolicRegionRuntime.declaresExplicitFault(
                Collections.<ConcolicRegionRuntime.SymbolizeAction>
                        emptyList(), MARKER));
        // Control is the classification, not merely the name: an action of
        // another kind that happens to carry the name controls nothing.
        JsonObject other = faultJson(MARKER, 1);
        other.addProperty("sourceKind", "ACCESSOR_RETURN");
        assertFalse(ConcolicRegionRuntime.declaresExplicitFault(
                Collections.singletonList(
                        new ConcolicRegionRuntime.SymbolizeAction(other)),
                MARKER));
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

    /** A reach at some other site, or the wrong arm, is not the target. */
    @Test
    public void aReachAtAnotherSiteOrArmIsNotTheTarget() throws Exception {
        ConcolicRegionRuntime.ActiveRegion elsewhere = region(true);
        recordReach(elsewhere, OTHER, 1, true);
        assertFalse(ConcolicResultPublisher
                .targetReachedByActivation(elsewhere));

        ConcolicRegionRuntime.ActiveRegion wrongArm = region(true);
        recordReach(wrongArm, SITE, 1, false);
        assertFalse(ConcolicResultPublisher
                .targetReachedByActivation(wrongArm));

        ConcolicRegionRuntime.ActiveRegion wrongOccurrence = region(true);
        recordReach(wrongOccurrence, SITE, 2, true);
        assertFalse(ConcolicResultPublisher
                .targetReachedByActivation(wrongOccurrence));
    }

    /** A declared target the replay never decided keeps its own gap. */
    @Test
    public void aDeclaredTargetNeverDecidedStillNamesItself()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(true);
        active.exitKind = "NORMAL";
        active.nameUnreachedTargetBranch();
        assertTrue(only(unresolved(active)).startsWith(
                "TARGET_BRANCH_NOT_REACHED: " + SITE + "#1"));
    }

    // ---------- 4. the planner's required-outcome selection ----------

    /** An occurrence that took the required outcome is elected by it. */
    @Test
    public void aMatchingOccurrenceIsElectedByTheRequiredOutcome() {
        Map<String, Object> branch = only(RuntimeRegionPlanner.branches(
                Collections.singletonList(policy(true)),
                Arrays.asList(branchEvent(1L, false),
                        branchEvent(2L, true))));
        assertEquals(Boolean.TRUE, branch.get("observed"));
        assertEquals(Boolean.TRUE, branch.get("requiredOutcomeObserved"));
        assertEquals(2, branch.get("selectedOccurrence"));
        assertEquals("REQUIRED_OUTCOME",
                branch.get("selectedOccurrenceAuthority"));
        assertNull(branch.get("selectedOccurrenceGap"));
    }

    /**
     * The recording never took the required outcome and the site ran once.
     *
     * <p>Nothing is invented -- there was one occurrence and it is the one
     * named -- but the row must still say the required outcome was not
     * observed, which is the fact that used to be missing entirely.  It is a
     * flip target, so {@code observed} stays true: a guard the recording
     * never took the failing arm of is the normal case for a search that
     * exists to make it take it.</p>
     */
    @Test
    public void aSoleUnmatchedOccurrenceSaysSoWithoutLosingTheSite() {
        Map<String, Object> branch = only(RuntimeRegionPlanner.branches(
                Collections.singletonList(policy(false)),
                Collections.singletonList(branchEvent(1L, true))));
        assertEquals(Boolean.TRUE, branch.get("observed"));
        assertEquals(Boolean.TRUE, branch.get("observedOutcome"));
        assertEquals(Boolean.FALSE, branch.get("requiredOutcomeObserved"));
        assertEquals(1, branch.get("selectedOccurrence"));
        assertEquals("SOLE_RECORDED_OCCURRENCE",
                branch.get("selectedOccurrenceAuthority"));
        assertNull(branch.get("selectedOccurrenceGap"));
    }

    /**
     * Several occurrences and none of them matched: which one the policy
     * means is decided by nothing in the recording, and the silent answer
     * was occurrence #1.
     */
    @Test
    public void anUnmatchedChoiceAmongSeveralIsNamedAsAGap() {
        Map<String, Object> branch = only(RuntimeRegionPlanner.branches(
                Collections.singletonList(policy(false)),
                Arrays.asList(branchEvent(1L, true), branchEvent(2L, true),
                        branchEvent(3L, true))));
        assertEquals(Boolean.FALSE, branch.get("requiredOutcomeObserved"));
        assertEquals(ConcolicRegionRuntime.TARGET_REACH_NOT_OBSERVED,
                branch.get("selectedOccurrenceAuthority"));
        String gap = String.valueOf(branch.get("selectedOccurrenceGap"));
        assertTrue(gap, gap.startsWith(
                ConcolicRegionRuntime.TARGET_REACH_NOT_OBSERVED));
        assertTrue(gap, gap.contains("none of the 3 recorded occurrences"));
        assertTrue(gap, gap.contains(SITE));
    }

    /** A policy with no required outcome asks the question of nobody. */
    @Test
    public void aPolicyWithNoRequiredOutcomeStatesNoSelectionAuthority() {
        Map<String, Object> policy = new LinkedHashMap<>();
        policy.put("siteId", SITE);
        Map<String, Object> branch = only(RuntimeRegionPlanner.branches(
                Collections.singletonList(policy),
                Collections.singletonList(branchEvent(1L, true))));
        assertEquals(Boolean.TRUE, branch.get("observed"));
        assertNull(branch.get("requiredOutcomeObserved"));
        assertNull(branch.get("selectedOccurrenceAuthority"));
    }

    /** A site the recording never ran is not observed at all. */
    @Test
    public void anUnrunSiteIsNotObserved() {
        Map<String, Object> branch = only(RuntimeRegionPlanner.branches(
                Collections.singletonList(policy(true)),
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList()));
        assertEquals(Boolean.FALSE, branch.get("observed"));
        assertEquals(Boolean.FALSE, branch.get("requiredOutcomeObserved"));
        assertEquals(0, branch.get("selectedOccurrence"));
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
