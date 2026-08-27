package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A retained loop's undeclared bound is a coverage gap only when the loop's
 * trip count can reach something the failure reads.
 *
 * <p>Every site below has the shape of a real HDFS-11741 loop site: the
 * key-rotation walks the witness depends on, and the configuration/metrics
 * parsing the run only walked because it lies in the region's execution
 * scope.  The rule is stated over the plan's own demand evidence and names no
 * class, method or package.</p>
 */
public class FailureDemandedLoopScopeTest {

    private static final String DEMANDED =
            "<example.Keys: void addKeys(example.Exported)>";
    private static final String CONTROL =
            "<example.Queue: java.util.List poll(int)>";
    private static final String UNRELATED =
            "<example.Config: java.lang.String substituteVars"
                    + "(java.lang.String)>";
    private static final String CONSTRUCTOR =
            "<example.Builder: void <init>(java.lang.Object)>";
    private static final String ROOT = "<example.Monitor: void run()>";

    @Test
    public void aLoopInsideTheDemandedSliceIsStillRequired() {
        Map<String, Object> plan = plan(closedGoal(DEMANDED));
        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);

        assertEquals("LOOP_METHOD_IN_FAILURE_DEMANDED_SLICE",
                RuntimeRegionPlanner.demandedLoopReason(scope,
                        loop(DEMANDED, DEMANDED + "#u12")));
    }

    @Test
    public void aLoopOutsideEveryDemandedSliceIsImmaterial() {
        Map<String, Object> plan = plan(closedGoal(DEMANDED));
        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);

        assertEquals("", RuntimeRegionPlanner.demandedLoopReason(scope,
                loop(UNRELATED, UNRELATED + "#u10")));
    }

    @Test
    public void aNestIsRequiredWhenAnyControlSiteIsInTheDemandedSlice() {
        Map<String, Object> plan = plan(closedGoal(DEMANDED));
        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);
        Map<String, Object> nest = loop("",
                "L(" + UNRELATED + "#u10+" + DEMANDED + "#u23)");

        assertEquals("LOOP_METHOD_IN_FAILURE_DEMANDED_SLICE",
                RuntimeRegionPlanner.demandedLoopReason(scope, nest));
        assertEquals("", RuntimeRegionPlanner.demandedLoopReason(scope,
                loop("", "L(" + UNRELATED + "#u10+" + UNRELATED + "#u23)")));
    }

    @Test
    public void aLoopNamedOnlyByItsControlSitesIsStillRequired() {
        Map<String, Object> plan = plan(closedGoal(DEMANDED));
        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);
        Map<String, Object> loop = loop("", "OPAQUE-LOOP-ID");
        loop.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS,
                Collections.singletonList(DEMANDED + "#u4"));

        assertEquals("LOOP_METHOD_IN_FAILURE_DEMANDED_SLICE",
                RuntimeRegionPlanner.demandedLoopReason(scope, loop));
    }

    @Test
    public void theOccurrenceRootAndItsLoopBodyAreAlwaysInScope() {
        Map<String, Object> plan = plan(closedGoal(DEMANDED));
        Map<String, Object> selector = new LinkedHashMap<>();
        selector.put("method", ROOT);
        plan.put("rootSelector", selector);
        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);

        assertEquals("LOOP_METHOD_IN_FAILURE_DEMANDED_SLICE",
                RuntimeRegionPlanner.demandedLoopReason(scope,
                        loop(ROOT, ROOT + "#u30")));
    }

    // ---- fail-closed exits -------------------------------------------

    @Test
    public void anUndecidableScopeKeepsEveryLoopRequired() {
        assertEquals("FAILURE_DEMAND_SCOPE_UNDECIDED",
                RuntimeRegionPlanner.demandedLoopReason(
                        Collections.<String>emptySet(),
                        loop(UNRELATED, UNRELATED + "#u10")));
        assertEquals("FAILURE_DEMAND_SCOPE_UNDECIDED",
                RuntimeRegionPlanner.demandedLoopReason(null,
                        loop(UNRELATED, UNRELATED + "#u10")));
    }

    @Test
    public void aLoopThatNamesNoMethodKeepsItself() {
        Map<String, Object> plan = plan(closedGoal(DEMANDED));
        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);

        assertEquals("LOOP_NAMES_NO_METHOD",
                RuntimeRegionPlanner.demandedLoopReason(scope,
                        loop("", "not-a-site-id")));
    }

    @Test
    public void aBlockedTargetProjectionLeavesTheScopeUndecided() {
        Map<String, Object> goal = closedGoal(DEMANDED);
        goal.put("kind", "TARGET_REACH_CLOSURE");
        Map<String, Object> admission = new LinkedHashMap<>();
        admission.put("state", "BLOCKED");
        goal.put("admission", admission);

        assertTrue(RuntimeRegionPlanner.failureDemandedLoopScope(plan(goal))
                .isEmpty());

        admission.put("state", "READY");
        assertTrue(RuntimeRegionPlanner.failureDemandedLoopScope(plan(goal))
                .contains(DEMANDED));
    }

    @Test
    public void aClosureThatNamesNoDefinitionMethodLeavesTheScopeUndecided() {
        Map<String, Object> goal = closedGoal(DEMANDED);
        goal.put("runtimeDefinitionMethods", Collections.emptyList());

        assertTrue(RuntimeRegionPlanner.failureDemandedLoopScope(plan(goal))
                .isEmpty());
    }

    @Test
    public void aGoalWhoseOutputsTheBoundDroppedContributesNoScope() {
        // materializeProducerGoal strips a goal that loses every demanded
        // output down to no closure and no definition method, and such a
        // goal must widen nothing.
        Map<String, Object> dropped = new LinkedHashMap<>();
        dropped.put("kind", "OUTPUT_RELATION_CLOSURE");
        dropped.put("runtimeDefinitionMethods", Collections.emptyList());
        Map<String, Object> admission = new LinkedHashMap<>();
        admission.put("state", "DISCOVERED");
        dropped.put("admission", admission);
        Map<String, Object> plan = plan(dropped);
        Map<String, Object> selector = new LinkedHashMap<>();
        selector.put("method", ROOT);
        plan.put("rootSelector", selector);

        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);

        assertEquals(Collections.singleton(ROOT), scope);
        assertEquals("", RuntimeRegionPlanner.demandedLoopReason(scope,
                loop(UNRELATED, UNRELATED + "#u10")));
    }

    // ---- the wire contract -------------------------------------------

    @Test
    public void anUndecidedDeclarationIsRequired() {
        JsonObject declaration = new JsonObject();
        assertTrue(LoopBoundPolicy.failureRelevantLoop(declaration));
        assertTrue(LoopBoundPolicy.failureRelevantLoop(null));

        // Decided, but under no authority this build knows.
        declaration.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT, false);
        assertTrue(LoopBoundPolicy.failureRelevantLoop(declaration));
        declaration.addProperty(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                "SOMETHING_ELSE_V9");
        assertTrue(LoopBoundPolicy.failureRelevantLoop(declaration));

        declaration.addProperty(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                LoopBoundPolicy.FAILURE_DEMANDED_LOOP_SCOPE);
        assertFalse(LoopBoundPolicy.failureRelevantLoop(declaration));
        declaration.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT, true);
        assertTrue(LoopBoundPolicy.failureRelevantLoop(declaration));
    }

    @Test
    public void siteMethodsReadsANestAndAConstructorSite() {
        assertEquals(Collections.singleton(CONSTRUCTOR),
                LoopBoundPolicy.siteMethods(CONSTRUCTOR + "#u17"));
        assertEquals(new java.util.LinkedHashSet<>(
                        Arrays.asList(UNRELATED, DEMANDED)),
                LoopBoundPolicy.siteMethods(
                        "L(" + UNRELATED + "#u10+" + DEMANDED + "#u23)"));
        assertTrue(LoopBoundPolicy.siteMethods("").isEmpty());
        assertTrue(LoopBoundPolicy.siteMethods(null).isEmpty());
        assertTrue(LoopBoundPolicy.siteMethods("no-angle-brackets#u1")
                .isEmpty());
    }

    @Test
    public void aConstructorLoopInTheDemandedSliceIsStillRequired() {
        Map<String, Object> plan = plan(closedGoal(CONSTRUCTOR));
        Set<String> scope = RuntimeRegionPlanner.failureDemandedLoopScope(
                plan);

        assertEquals("LOOP_METHOD_IN_FAILURE_DEMANDED_SLICE",
                RuntimeRegionPlanner.demandedLoopReason(scope,
                        loop(CONSTRUCTOR, CONSTRUCTOR + "#u17")));
    }

    // ---- helpers ------------------------------------------------------

    private static Map<String, Object> plan(Map<String, Object> goal) {
        Map<String, Object> plan = new LinkedHashMap<>();
        plan.put("occurrenceId", "occ.P");
        plan.put("regionId", "REGION.P");
        plan.put("closureGoals", Collections.singletonList(goal));
        return plan;
    }

    private static Map<String, Object> closedGoal(String definitionMethod) {
        Map<String, Object> slice = new LinkedHashMap<>();
        slice.put("methods", Collections.singletonList(definitionMethod));
        slice.put("sites", Collections.singletonList(
                definitionMethod + "#u3"));
        Map<String, Object> output = new LinkedHashMap<>();
        output.put("portId", "REGION.P.out.key");
        Map<String, Object> member = new LinkedHashMap<>();
        member.put("output", output);
        member.put("slice", slice);
        Map<String, Object> closure = new LinkedHashMap<>();
        closure.put("members", Collections.singletonList(member));
        Map<String, Object> goal = new LinkedHashMap<>();
        goal.put("kind", "OUTPUT_RELATION_CLOSURE");
        goal.put("runtimeDefinitionMethods",
                Collections.singletonList(definitionMethod));
        Map<String, Object> admission = new LinkedHashMap<>();
        admission.put("state", "READY");
        goal.put("admission", admission);
        goal.put("outputClosure", closure);
        return goal;
    }

    private static Map<String, Object> loop(String enclosingMethod,
                                            String loopSiteId) {
        Map<String, Object> loop = new LinkedHashMap<>();
        if (!enclosingMethod.isEmpty()) {
            loop.put("enclosingMethod", enclosingMethod);
        }
        loop.put(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
        List<String> controls = Collections.emptyList();
        loop.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, controls);
        loop.put(LoopBoundPolicy.LOOP_CLASSIFICATION,
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
        return loop;
    }
}
