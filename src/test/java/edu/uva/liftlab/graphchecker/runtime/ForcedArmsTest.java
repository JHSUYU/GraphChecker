package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The FORCE run (PIPELINE §7.10): armed only in the declared occurrence of
 * a run whose focus row asks it; a decision the VM forced off its concrete
 * arm opens the forced world, where the target row stands; the forced
 * target on its fatal arm is ADMITTED, how the occurrence then ended named;
 * one that closed first, or took its target's healthy arm, is
 * FORCE_DIVERGED with the first exception the forced world threw.
 */
public class ForcedArmsTest {
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String GUARD = METHOD + "#u2";
    private static final String TARGET = METHOD + "#u4";
    private static final String FOCUS =
            "solr/n1#epoch0/region/REGION.1/ctx:Root:OVERSEER#1/idx:"
                    + METHOD + "@0";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Before
    @After
    public void reset() {
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        RowRuntime.resetForTests();
    }

    /** Hands the replay a FORCE focus row at {@link #FOCUS}. */
    private void forcing() throws Exception {
        Path worker = folder.newFolder().toPath();
        Files.write(worker.resolve("focused_task.jsonl"), ("{\"taskId\":"
                + "\"TASK.1\",\"obligationId\":\"FORCE.1\",\"pathId\":\"p\","
                + "\"focused\":\"" + FOCUS + "\",\"focusedOccurrenceId\":\""
                + OccurrenceAddress.parse(FOCUS).id() + "\",\"declaredTarget\""
                + ":\"" + FOCUS + "\",\"seedSessionId\":\"seed\",\"flip\":null,"
                + "\"force\":true,\"inheritedFlips\":[],\"rootAssignments\":{},"
                + "\"clockDeltas\":{},\"answers\":{},\"rootMints\":{}}\n")
                .getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
    }

    /** The declared occurrence's activation, its table forcing the guard
     *  and the target to jump. */
    private static ActiveRegion declared(long token, String at) {
        JsonObject encoded = new JsonParser().parse(
                "{'taskId':'TASK.1','goalId':'GOAL.1','regionId':'REGION.1',"
                + "'goalKind':'TARGET_REACH_CLOSURE','relationKey':'REL.1',"
                + "'sourceKey':'n1#epoch0','rootMethod':'" + METHOD + "',"
                + "'occurrenceId':'REGION.1@n1#epoch0#1','loopBound':"
                + "{'schemaVersion':1,'defaultBackedgeTraversals':8},"
                + "'instrumentationSelector':'sel',"
                + "'admission':{'state':'EXECUTABLE'},'rootSelector':{'kind':"
                + "'GLOBAL_INVOCATION','invocationOrdinal':1,'causalAnchor':"
                + "{'sourceKey':'n1#epoch0','kind':'REGISTERED_SOURCE'}},"
                + "'branchMethods':['" + METHOD + "'],'inputActions':[],"
                + "'targetBranch':{'siteId':'" + TARGET + "','occurrence':1,"
                + "'requiredOutcome':true,'force':[{'siteId':'" + GUARD
                + "','arm':true},{'siteId':'" + TARGET + "','arm':true}]}}")
                .getAsJsonObject();
        ActiveRegion active = new ActiveRegion(token,
                new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(
                        encoded)), null, Thread.currentThread());
        active.d3Address = OccurrenceAddress.parse(at);
        return active;
    }

    /** One decision mapping as BranchObservation states it. */
    private static JsonObject mapping(String site, long event,
                                      boolean outcome) {
        JsonObject mapping = BranchObservation.decisionRow(METHOD,
                Integer.parseInt(site.substring(site.lastIndexOf('u') + 1)),
                1, event, outcome, 0, 0);
        return mapping;
    }

    /** The VM event of a branch it forced, overriding {@code concrete}. */
    private static JsonObject forcedEvent(long concrete) {
        return new JsonParser().parse("{'forced':true,'concrete':" + concrete
                + "}").getAsJsonObject();
    }

    @Test
    public void onlyTheDeclaredOccurrenceOfAForceRunIsArmed()
            throws Exception {
        ActiveRegion plain = declared(1L, FOCUS);
        ForcedArms.arm(plain);
        assertFalse("a run asked no FORCE arms nothing",
                plain.pathRecordingStarted);
        reset();
        forcing();
        ActiveRegion other = declared(2L, FOCUS.replace("@0", "@1"));
        ForcedArms.arm(other);
        assertFalse("another occurrence is never armed",
                other.pathRecordingStarted);
        ActiveRegion active = declared(3L, FOCUS);
        ForcedArms.arm(active);
        assertTrue("the declared one records from its entry",
                active.pathRecordingStarted);
        assertTrue(FocusedReplay.forcing());
        assertFalse("a FORCE run confirms nothing",
                FocusedReplay.confirming());
        assertEquals("FORCE_DIVERGED: the declared occurrence never closed",
                FocusedReplay.results("s").get(0).detail());
    }

    @Test
    public void theForcedWorldOpensAtTheFirstDecisionForcedOffItsArm()
            throws Exception {
        forcing();
        ActiveRegion active = declared(4L, FOCUS);
        ForcedArms.arm(active);
        JsonObject along = mapping(GUARD, 10L, true);
        ForcedArms.mark(active, along, forcedEvent(1L));
        JsonObject off = mapping(GUARD, 12L, true);
        ForcedArms.mark(active, off, forcedEvent(0L));
        JsonObject unforced = mapping(GUARD, 14L, false);
        ForcedArms.mark(active, unforced, new JsonObject());
        Object[][] rows = {
                {"forced along its concrete arm", along, true, true, false},
                {"forced off it", off, true, false, true},
                {"not forced", unforced, false, false, false}};
        for (Object[] row : rows) {
            JsonObject mapping = (JsonObject) row[1];
            assertEquals(row[0] + ": forced", row[2], mapping.has("forced"));
            if (mapping.has("forced")) {
                assertEquals(row[0] + ": concrete", row[3],
                        mapping.get("concreteOutcome").getAsBoolean());
            }
            assertEquals(row[0] + ": against", row[4],
                    mapping.has(ForcedArms.AGAINST));
        }
        assertEquals("no world before its target", 0L,
                ForcedArms.forcedFrom(active));
        ForcedArms.reachedTarget(active, TARGET, 1, true);
        assertEquals(12L, ForcedArms.forcedFrom(active));
        assertEquals("reached: nothing withdraws its session", "",
                ForcedArms.unreached());
        assertEquals("", ForcedArms.finished(active, "THROW",
                "java.lang.IllegalStateException"));
        ObligationResult verdict = FocusedReplay.results("s").get(0);
        assertEquals(Verdict.ADMITTED, verdict.verdict());
        assertTrue(verdict.detail(), verdict.detail().startsWith(
                "FORCED_TARGET") && verdict.detail().contains(TARGET + "#1")
                && verdict.detail().contains(
                "THROW java.lang.IllegalStateException"));
    }

    @Test
    public void anOccurrenceClosedShortOfItsTargetDiverges()
            throws Exception {
        String[][] rows = {
                // {how it ended, what the verdict names}
                {"closed", "before its target decision was forced"},
                {"healthy", "took its healthy arm"}};
        for (String[] row : rows) {
            reset();
            forcing();
            ActiveRegion active = declared(5L, FOCUS);
            ForcedArms.arm(active);
            ForcedArms.mark(active, mapping(GUARD, 20L, true),
                    forcedEvent(0L));
            if ("healthy".equals(row[0])) {
                ForcedArms.reachedTarget(active, TARGET, 1, false);
            }
            pushed(active, () -> ForcedArms.unwinding(
                    new NullPointerException("a forced arm's null")));
            String reason = ForcedArms.finished(active, "THROW",
                    "java.lang.NullPointerException");
            assertTrue(row[0] + ": " + reason, reason.startsWith(
                    "FORCE_DIVERGED") && reason.contains(row[1]));
            assertEquals(row[0] + ": forced from", "closed".equals(row[0]),
                    reason.contains("the forced world first threw "
                            + "java.lang.NullPointerException: a forced"
                            + " arm's null at "));
            assertEquals(Verdict.NOT_ADMITTED,
                    FocusedReplay.results("s").get(0).verdict());
            assertEquals(row[0] + ": its session is withdrawn", reason,
                    ForcedArms.unreached());
        }
        reset();
        forcing();
        ForcedArms.arm(declared(6L, FOCUS));
        assertTrue("one that never closed is withdrawn too",
                ForcedArms.unreached().contains("never closed"));
    }

    /** A decider is forced only in a call of its helper from {@code via}:
     *  the frame one level out, as the weave enters it -- a lambda's
     *  run-minted class name compared by its stable spelling. */
    @Test
    public void aDeciderIsForcedOnlyInACallFromItsVia() {
        String caller = "<a.Caller$$Lambda$12/1830908236: void run()>";
        String helper = "<a.Helper: boolean ok()>";
        Object[][] rows = {
                // {frames, outermost first; via; called from it}
                {new String[] {caller, helper},
                        "<a.Caller$$Lambda$40/99: void run()>", true},
                {new String[] {caller, "<a.Other: void go()>", helper},
                        caller, false},
                {new String[] {helper}, caller, false}};
        for (Object[] row : rows) {
            String[] frames = (String[]) row[0];
            long[] tokens = new long[frames.length];
            for (int index = 0; index < frames.length; index++) {
                tokens[index] = Identity.enterFrame(frames[index], null);
            }
            try {
                assertEquals(String.valueOf(row[1]), row[2],
                        ForcedArms.calledFrom((String) row[1]));
            } finally {
                for (int index = frames.length - 1; index >= 0; index--) {
                    Identity.exitFrame(tokens[index]);
                }
            }
        }
    }

    /** The forced path condition from the forced world's first decision
     *  through the target: each as taken, a concrete one forced off its arm
     *  false, the target's own as phi. */
    @Test
    public void theForcedPhiIsTheWholeWayFromTheFirstForcedDecision() {
        JsonObject before = mapping(GUARD, 5L, false);
        before.add("siteCondition", symbol("M_BEFORE"));
        JsonObject first = mapping(GUARD, 7L, true);
        first.add("siteCondition", symbol("M_A"));
        JsonObject concreteOff = mapping(GUARD, 8L, true);
        concreteOff.addProperty(ForcedArms.AGAINST, true);
        JsonObject concreteAlong = mapping(GUARD, 9L, false);
        JsonObject target = mapping(TARGET, 11L, true);
        target.add("siteCondition", symbol("M_TARGET"));
        List<JsonObject> mappings = new ArrayList<JsonObject>(Arrays.asList(
                before, first, concreteOff, concreteAlong, target));
        String a = RowRuntime.expressionRef(symbol("M_A"));
        assertEquals("(and " + a + " false PHI)",
                RowPublication.forced(mappings, 7L, 11L, "PHI"));
        JsonObject concreteTarget = mapping(TARGET, 11L, true);
        concreteTarget.addProperty(ForcedArms.AGAINST, true);
        mappings.set(4, concreteTarget);
        assertEquals("a concrete target forced off its arm is false too",
                "(and " + a + " false false PHI)",
                RowPublication.forced(mappings, 7L, 11L, "PHI"));
        assertEquals("nothing between: phi alone", "PHI",
                RowPublication.forced(Collections.<JsonObject>emptyList(),
                        7L, 11L, "PHI"));
        // A switch is never forced: its mapping states the case arm and no
        // condition, its predicate rows no arm; between, it adds nothing.
        JsonObject selector = mapping(GUARD, 9L, true);
        JsonObject predicate = BranchObservation.decisionRow(METHOD, 2, 1,
                9L, null, 0, 0);
        predicate.add("witness", symbol("M_KEY"));
        List<JsonObject> switched = new ArrayList<JsonObject>(Arrays.asList(
                first, selector, predicate, target));
        assertEquals("(and " + a + " PHI)",
                RowPublication.forced(switched, 7L, 11L, "PHI"));
    }

    private static JsonObject symbol(String name) {
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "SymbolExpression");
        condition.addProperty("_exp", name);
        condition.addProperty("_java_type", "Z");
        return condition;
    }

    /** Runs {@code body} with {@code active} the thread's region. */
    private static void pushed(ActiveRegion active, Runnable body)
            throws Exception {
        java.lang.reflect.Field field = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        field.setAccessible(true);
        @SuppressWarnings("unchecked")
        java.util.Deque<Long> tokens = ((ThreadLocal<java.util.Deque<Long>>)
                field.get(null)).get();
        ConcolicRegionRuntime.ACTIVE.put(active.token, active);
        tokens.push(active.token);
        try {
            body.run();
        } finally {
            tokens.pop();
            ConcolicRegionRuntime.ACTIVE.remove(active.token);
        }
    }
}
