package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import org.junit.After;
import org.junit.Test;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * Characterization of the branch-observation machinery a region runs for one
 * decision: every row and the target reach it writes down, for a binary
 * branch and for the multiway switch answering the same questions.  One
 * implementation serves both, so these transcripts are what "the same,
 * parameterised by the decision" means.
 */
public class BranchDecisionRecordingTest {
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String DECLARED = METHOD + "#u4";
    private static final String BOUNDARY = METHOD + "#u12";
    private static final String SNAPSHOTS = "<org.apache.hadoop.hdfs.server"
            + ".namenode.snapshot.SnapshotManager: void deleteSnapshot()>";
    private static final String TARGET = SNAPSHOTS + "#u61";
    private static final String ELSEWHERE = SNAPSHOTS + "#u44";

    /** The reach, unchanged by the kind. */
    private static final String REACH = "targetReach={\"kind\":\"TARGET_REACH_EVENT\","
            + "\"occurrence\":1,\"outcome\":true,\"siteId\":\""
            + DECLARED + "\"}\n"
            + "returned=observation\n";

    private final Deque<Long> opened = new ArrayDeque<>();

    @After
    public void releaseRegions() throws Exception {
        while (!opened.isEmpty()) {
            ConcolicRegionRuntime.ACTIVE.remove(opened.pop());
        }
        currentTokens().clear();
        rootInvocationFrames().clear();
        silenced().clear();
        Identity.resetForTests();
        Lineage.resetForTests();
    }

    /**
     * What a region writes down for one binary decision at a declared
     * site: one row naming the site, the arm it took and the empty
     * path-condition window, and the reach.  The switch answers the same
     * questions at the same site and arm: the successor it selected is the
     * replay authority and states no predicate of its own, so the row is
     * the binary one.
     *
     * <p>The site id in that row is also what the VM is told a guarded
     * store depends on: the guarded-store table names the store's method
     * with the internal owner the VM asks with and carries each guard branch
     * site verbatim as its own tab-separated field, exactly as this row
     * spells it -- commas and all, since a site id's parameter list has
     * them (VM25).</p>
     */
    @Test
    public void aBinaryDecisionPublishesOneRowAndTheReach() throws Exception {
        Object[][] decisions = {{"binary", binary(true)},
                {"switch", multiway("0,1,2", 1)}};
        for (Object[] decision : decisions) {
            assertEquals((String) decision[0], "rows=[{"
                    + "\"method\":\"" + METHOD + "\",\"occurrence\":1,"
                    + "\"outcome\":true,"
                    + "\"rawPathConditionBaseline\":0,"
                    + "\"rawPathConditionSize\":0,\"siteId\":\"" + DECLARED
                    + "\",\"unitIndex\":4}]\n" + REACH,
                    publishes(decision[1]));
            releaseRegions();
        }
        GuardedStoreSites table = GuardedStoreSites.of(
                Collections.singletonList(writeSite("a.B#run(I)V",
                        DECLARED, COMMAS)));
        assertEquals("the store's method is internal, each guard a field",
                "a/B#run(I)V\t" + DECLARED + "\t" + COMMAS + "\n",
                table.text());
        assertEquals("the VM keeps every method the table guards", 1,
                table.methods());
    }

    /** A guard whose method takes two parameters, so its id has a comma. */
    private static final String COMMAS =
            "<a.B: void run(int,long)>#u9";

    /** One {@code WRITE_SITE} row of a static scope map, with its guards. */
    private static JsonObject writeSite(String vmSite, String... guards) {
        StringBuilder stated = new StringBuilder();
        for (String guard : guards) {
            if (stated.length() > 0) stated.append(',');
            stated.append('\'').append(guard).append('\'');
        }
        return JsonParser.parseString(("{'kind':'STATIC_SCOPE_SITE','role':"
                + "'WRITE_SITE','regionId':'REGION.1','siteId':'" + METHOD
                + "#u7','vmSite':'" + vmSite + "','cell':'<a.B: int f>',"
                + "'carrier':'<a.B: int f>','portId':'','declaredCallee':'',"
                + "'guards':[" + stated + "]}").replace('\'', '"'))
                .getAsJsonObject();
    }

    /**
     * An activation that decides the addressed target site has reached the
     * target, symbolic predicate or two concrete ints: that is evidence about
     * the anchor, not a condition on publishing it.  Only a decision the VM
     * emitted no event for is silent.
     */
    /**
     * A loop's unroll budget is counted per method activation: a helper
     * called again in one long activation starts afresh (readVLong was cut
     * at its 9th body across a DataXceiver's token fields, a9b
     * token-expired.mirror).
     */
    @Test
    public void aLoopBudgetIsCountedPerCall() throws Exception {
        installPlan();
        ActiveRegion active = region();
        String helper = "<a.W: long readVLong(java.io.DataInput)>";
        for (int call = 0; call < 2; call++) {
            long frame = Identity.enterFrame(helper, null);
            assertEquals(1L, active.traverseBackedge(helper + "#loop:u8"));
            assertEquals(2L, active.traverseBackedge(helper + "#loop:u8"));
            Identity.exitFrame(frame);
        }
    }

    @Test
    public void aConcreteDecisionAtTheTargetSiteIsStillAReach() {
        // site decided, occurrence decided, permuted by a loop, reaches
        Object[][] decisions = {
                {TARGET, 1, false, true}, {TARGET, 2, false, false},
                {TARGET, 3, true, true}, {ELSEWHERE, 1, false, false}};
        for (Object[] decided : decisions) {
            assertEquals(decided[0] + "#" + decided[1], decided[3],
                    ConcolicRegionRuntime.statesTargetReach(true,
                            (Boolean) decided[2], TARGET.equals(decided[0]),
                            1, (Integer) decided[1]));
        }
        assertFalse("a decision with no recorded row states no reach",
                ConcolicRegionRuntime.statesTargetReach(false, false, true,
                        1, 1));
    }

    /**
     * I3: an abandoned occurrence hands its later branches to nobody.
     *
     * <p>A prefix contradiction ends an activation from INSIDE the region
     * method, and the workload's call goes on running.  The activation is
     * popped off the region stack, so every branch the rest of that call
     * took used to be recorded on the ENCLOSING activation, under its
     * address and with ordinals restarting at 1 -- 10 of hdfs-11741's 40
     * nn0-focused sessions show that migration.  After the close there is
     * no active occurrence on the thread: the rest of the frame is concrete
     * and unrecorded, and the enclosing occurrence is the thread's again
     * exactly when the abandoned call returns.</p>
     */
    @Test
    public void anAbandonedOccurrenceHandsItsLaterBranchesToNobody()
            throws Exception {
        Identity.resetForTests();
        Lineage.resetForTests();
        ActiveRegion enclosing = region();
        ActiveRegion abandoned = region();
        Object frame = rootInvocationFrame(abandoned.token);
        assertEquals("the innermost activation is the one about to close",
                abandoned, ConcolicRegionRuntime.activeRegion());

        // What #closeOccurrence states when it closes an activation whose
        // own Java frame is still executing.
        silenceStillRunningFrame(abandoned);
        currentTokens().pop();
        assertNull("no occurrence performs what the rest of that frame does",
                ConcolicRegionRuntime.activeRegion());

        // The region method returns: its root exit hook pops the frame, and
        // the occurrence enclosing the call is the thread's again.
        popRootInvocationFrame(frame);
        assertEquals(enclosing, ConcolicRegionRuntime.activeRegion());
    }

    /**
     * F1: a folded entry starts no activation.
     *
     * <p>The entry hook at one Java entry runs before the plan row's hook,
     * so by the time admission is asked the fold is already standing: this
     * call is a method call INSIDE the occurrence already running, not the
     * entry of one.  An activation here would be a SECOND activation of that
     * occurrence -- two ActivationRows for one address, two branch-ordinal
     * counters to reconcile, and a candidate consumed for an occurrence
     * nothing addressed.  The control is the same call with no fold
     * standing, which does reach admission and gets as far as the VM this
     * unit test has none of.</p>
     */
    @Test
    public void aFoldedEntryStartsNoActivation() throws Exception {
        Identity.resetForTests();
        Lineage.resetForTests();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        installPlan();
        broker().set(null, null);
        try {
            Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
            Identity.enterFrame("<a.B: void outer()>#u1", null);
            assertEquals("the enclosing entry opens the occurrence",
                    "REGION.1", Identity.occurrence(NODE, "REGION.1", true)
                            .regionId());

            Identity.enterFrame(METHOD + "#u0", null);
            Identity.occurrence(NODE, "REGION.2", true);
            assertTrue(Identity.foldedEntry());
            int live = ConcolicRegionRuntime.ACTIVE.size();
            assertEquals("no token, so no activation",
                    0L, ConcolicRegionRuntime.enterRegionFrame("sel", METHOD,
                            null, new Object[0]));
            assertEquals("and nothing was started", live,
                    ConcolicRegionRuntime.ACTIVE.size());
            assertNull("nor is one running on this thread",
                    ConcolicRegionRuntime.activeRegion());
            assertFalse("admission was never asked: the fold never reached"
                            + " the engine this region would start in",
                    brokerLoaded());
            ConcolicRegionRuntime.exitRegionFrame("sel", METHOD);

            // The control: no fold, so the same call does reach admission.
            Identity.resetForTests();
            Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
            Identity.enterFrame(METHOD + "#u0", null);
            Identity.occurrence(NODE, "REGION.2", true);
            assertFalse(Identity.foldedEntry());
            try {
                ConcolicRegionRuntime.enterRegionFrame("sel", METHOD, null,
                        new Object[0]);
            } catch (Throwable withoutAVm) {
                // A unit test has no custom VM to start a region in; what
                // matters is that admission was reached at all.
            }
            assertTrue("the control did reach admission, and admission is"
                            + " what asks the engine for a region",
                    brokerLoaded());
        } finally {
            ConcolicRegionRuntime.exitRegionFrame("sel", METHOD);
            installedPlan(null);
            Identity.resetForTests();
            RowRuntime.resetForTests();
        }
    }

    /** Whether anything on this run has asked for the custom VM yet. */
    private static boolean brokerLoaded() throws Exception {
        return broker().get(null) != null;
    }

    private static Field broker() throws Exception {
        Field field = ConcolicVmBroker.class.getDeclaredField("engineApi");
        field.setAccessible(true);
        return field;
    }

    /** Installs one plan for {@link ConcolicRegionRuntime} to admit from. */
    private void installPlan() throws Exception {
        installedPlan(new ConcolicTaskPlan(null, Collections.singletonList(
                new ConcolicTaskPlan.RuntimeTask(task()))));
    }

    private void installedPlan(ConcolicTaskPlan plan) throws Exception {
        Field field = ConcolicTaskPlan.class.getDeclaredField("plan");
        field.setAccessible(true);
        field.set(null, plan);
    }

    private static final String NODE = "hdfs-11741/dn1#epoch0";

    /** One activation of the task, on this thread's region stack. */
    private ActiveRegion region() throws Exception {
        long token = 900000L + opened.size() + 1;
        ActiveRegion active = new ActiveRegion(token,
                new ConcolicTaskPlan.RuntimeTask(task()), null,
                Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        opened.push(token);
        return active;
    }

    /** One open root invocation frame, as an entry hook pushes one. */
    private static Object rootInvocationFrame(long token) throws Exception {
        Class<?> shape = Class.forName("edu.uva.liftlab.graphchecker.runtime"
                + ".ConcolicRegionRuntime$RootInvocationFrame");
        java.lang.reflect.Constructor<?> open = null;
        for (java.lang.reflect.Constructor<?> declared
                : shape.getDeclaredConstructors()) {
            if (declared.getParameterTypes().length == 4) open = declared;
        }
        open.setAccessible(true);
        Object frame = open.newInstance("sel", METHOD, "group", 0);
        Field owner = shape.getDeclaredField("token");
        owner.setAccessible(true);
        owner.setLong(frame, token);
        rootInvocationFrames().push(frame);
        return frame;
    }

    private static void silenceStillRunningFrame(ActiveRegion active)
            throws Exception {
        Method silence = ConcolicRegionRuntime.class.getDeclaredMethod(
                "silenceStillRunningFrame", ActiveRegion.class);
        silence.setAccessible(true);
        silence.invoke(null, active);
    }

    private static void popRootInvocationFrame(Object frame)
            throws Exception {
        Method pop = ConcolicRegionRuntime.class.getDeclaredMethod(
                "popRootInvocationFrame", String.class, String.class);
        pop.setAccessible(true);
        assertEquals(frame, pop.invoke(null, "sel", METHOD));
    }

    @SuppressWarnings("unchecked")
    private static Deque<Long> silenced() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("SILENCED");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Long>>) field.get(null)).get();
    }

    @SuppressWarnings("unchecked")
    private static Deque<Object> rootInvocationFrames() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("ROOT_INVOCATION_FRAMES");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Object>>) field.get(null)).get();
    }

    /** The transcript one concrete decision at u4 leaves in a fresh region. */
    private String publishes(Object decision) throws Exception {
        ActiveRegion active = region();
        // As production stands: the ordinal is counted on the occurrence
        // running on this thread (Identity.nextBranchOrdinal).
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame(METHOD + "#u0", null);
        Identity.occurrence(NODE, "REGION.1", true);
        Method record = active.getClass().getDeclaredMethod(
                "recordConcreteDecision", String.class, int.class,
                nested("BranchDecision"));
        record.setAccessible(true);
        return transcript(active, record.invoke(active, METHOD, 4, decision));
    }

    /** One branch declared at u4, one loop boundary at u12, one target. */
    private static ExecutionTask task() {
        String plan = ("{'taskId':'TASK.1','goalId':'GOAL.1','goalKind':"
                + "'TARGET_REACH_CLOSURE','regionId':'REGION.1',"
                + "'relationKey':'REL.1','sourceKey':'dn0#epoch0',"
                + "'occurrenceId':'REGION.1@dn0#epoch0#1','rootMethod':'"
                + METHOD + "','instrumentationSelector':'sel','admission':"
                + "{'state':'EXECUTABLE'},'rootSelector':{'kind':"
                + "'GLOBAL_INVOCATION','invocationOrdinal':1,'causalAnchor':"
                + "{'sourceKey':'dn0#epoch0','kind':'REGISTERED_SOURCE'}},"
                + "'branchMethods':['" + METHOD + "'],"
                + "'inputActions':[{'symbol':'sym.f','mode':'SYMBOLIC',"
                + "'bindingMode':'FIELD_ACCESS','accessFieldSignature':"
                + "'<a.B: int f>','accessSites':['" + DECLARED + "']}],"
                + "'loopBound':{'schemaVersion':1,"
                + "'defaultBackedgeTraversals':8},'retainedLoops':[{"
                + "'loopExitDecisions':[{'siteId':'" + BOUNDARY + "'}]}],"
                + "'targetBranch':{'siteId':'" + DECLARED
                + "','occurrence':1,'requiredOutcome':true}}")
                .replace('\'', '"');
        return ExecutionTask.decode(
                JsonParser.parseString(plan).getAsJsonObject());
    }

    private String transcript(ActiveRegion active,
                              Object returned) throws Exception {
        JsonArray rows = new JsonArray();
        for (JsonObject row : active.branchMappings) rows.add(row);
        Object reach = rawField(active, "targetReach");
        StringBuilder text = new StringBuilder("rows=")
                .append(CanonicalJson.render(rows))
                .append("\ntargetReach=").append(reach == null ? "none"
                        : CanonicalJson.render((JsonObject) reach))
                .append("\nreturned=").append(returned == null ? "null"
                        : "observation").append('\n');
        return text.toString();
    }

    private static Object binary(boolean outcome) throws Exception {
        Method factory = nested("BranchDecision")
                .getDeclaredMethod("binary", boolean.class);
        factory.setAccessible(true);
        return factory.invoke(null, outcome);
    }

    private static Object multiway(String keys, int successor)
            throws Exception {
        Method parse = nested("SwitchExpectation").getDeclaredMethod("parse",
                String.class, String.class, int.class);
        parse.setAccessible(true);
        Method factory = nested("BranchDecision").getDeclaredMethod("multiway",
                nested("SwitchExpectation"));
        factory.setAccessible(true);
        return factory.invoke(null, parse.invoke(null, "TABLE_SWITCH", keys,
                successor));
    }

    private static Class<?> nested(String name) throws Exception {
        return Class.forName("edu.uva.liftlab.graphchecker.runtime"
                + ".BranchObservation$" + name);
    }

    private static Object rawField(Object owner, String name)
            throws Exception {
        Field field = owner.getClass().getDeclaredField(name);
        field.setAccessible(true);
        return field.get(owner);
    }

    @SuppressWarnings("unchecked")
    private static Deque<Long> currentTokens() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Long>>) field.get(null)).get();
    }
}
