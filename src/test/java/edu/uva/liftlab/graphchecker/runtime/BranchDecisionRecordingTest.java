package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
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
     * path-condition window, and the reach.
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
        assertEquals("rows=[{"
                + "\"method\":\"" + METHOD + "\",\"occurrence\":1,"
                + "\"outcome\":true,"
                + "\"rawPathConditionBaseline\":0,"
                + "\"rawPathConditionSize\":0,\"siteId\":\"" + DECLARED
                + "\",\"unitIndex\":4}]\n" + REACH,
                publishes(binary(true)));
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
     * The switch answers the same questions: one row, at the same site and
     * the same arm.  The successor it selected is the replay authority and
     * states no predicate of its own, so the row is the binary one.
     */
    @Test
    public void aSwitchDecisionPublishesTheSameRowAndReach() throws Exception {
        assertEquals("rows=[{\"method\":\"" + METHOD
                + "\",\"occurrence\":1,\"outcome\":true,"
                + "\"rawPathConditionBaseline\":0,"
                + "\"rawPathConditionSize\":0,\"siteId\":\"" + DECLARED
                + "\",\"unitIndex\":4}]\n" + REACH,
                publishes(multiway("0,1,2", 1)));
    }

    /**
     * An activation that decides the addressed target site has reached the
     * target, symbolic predicate or two concrete ints: that is evidence about
     * the anchor, not a condition on publishing it.  Only a decision the VM
     * emitted no event for is silent.
     */
    @Test
    public void aConcreteDecisionAtTheTargetSiteIsStillAReach() {
        // site decided, occurrence decided, permuted by a loop, reaches
        Object[][] decisions = {
                {TARGET, 1, false, true}, {TARGET, 2, false, false},
                {TARGET, 3, true, true}, {ELSEWHERE, 1, false, false}};
        for (Object[] decided : decisions) {
            assertEquals(decided[0] + "#" + decided[1], decided[3],
                    ConcolicRegionRuntime.statesTargetReach(true,
                            (Boolean) decided[2], TARGET, 1,
                            (String) decided[0], (Integer) decided[1]));
        }
        assertFalse("a task naming no target reaches none",
                ConcolicRegionRuntime.statesTargetReach(true, false, "", 1,
                        ELSEWHERE, 1));
        assertFalse("a decision with no recorded row states no reach",
                ConcolicRegionRuntime.statesTargetReach(false, false, TARGET,
                        1, TARGET, 1));
    }

    /**
     * I3: the rows and the ordinals of a folded site are the enclosing
     * occurrence's.
     *
     * <p>Under I1 a declared region entered synchronously inside another
     * region's occurrence opens none of its own, so two selected
     * activations can be activations of ONE occurrence.  A decision row is
     * addressed by the occurrence that performed the branch and its ordinal
     * is counted there: counted per activation, both would start at 1 and
     * two rows would collide at (occurrence, site, ordinal) -- the pair an
     * obligation's flip is addressed by.</p>
     */
    @Test
    public void aFoldedSitesRowsAndOrdinalsAreTheEnclosingOccurrences()
            throws Exception {
        Identity.resetForTests();
        Lineage.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("<a.B: void addKeys()>#u1");
        OccurrenceAddress enclosing = Identity.occurrence(NODE,
                "REGION.ba3902cd", true);

        ActiveRegion outer = region(enclosing);
        decide(outer, 4);
        decide(outer, 4);

        // The synchronous call into the nested declared region: its entry
        // folds, so this activation IS an activation of `enclosing`.
        Identity.enterFrame("<a.B: void removeExpiredKeys()>#u7");
        assertEquals(enclosing,
                Identity.occurrence(NODE, "REGION.094a8e3d", true));
        ActiveRegion folded = region(Identity.currentOccurrence(NODE));
        decide(folded, 4);

        assertEquals("the folded activation's row is the enclosing "
                        + "occurrence's", enclosing.render(),
                folded.d3Address.render());
        assertEquals("and its ordinal goes on counting there, so no two "
                        + "rows of this occurrence share (site, ordinal)",
                3, ordinal(folded, 0));
        assertEquals(1, ordinal(outer, 0));
        assertEquals(2, ordinal(outer, 1));
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
        ActiveRegion enclosing = region(null);
        ActiveRegion abandoned = region(null);
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

    private static final String NODE = "hdfs-11741/dn1#epoch0";

    /** One activation of {@code address}, on this thread's region stack. */
    private ActiveRegion region(OccurrenceAddress address) throws Exception {
        long token = 900000L + opened.size() + 1;
        ActiveRegion active = new ActiveRegion(token,
                new ConcolicTaskPlan.RuntimeTask(task()), null,
                Thread.currentThread());
        active.d3Address = address;
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        opened.push(token);
        return active;
    }

    /** One concrete decision at {@code unitIndex} of {@link #METHOD}. */
    private void decide(ActiveRegion active, int unitIndex) throws Exception {
        Method record = ActiveRegion.class.getDeclaredMethod(
                "recordConcreteDecision", String.class, int.class,
                nested("BranchDecision"));
        record.setAccessible(true);
        record.invoke(active, METHOD, unitIndex, binary(true));
    }

    /** The ordinal the n-th row of this activation carries. */
    private static int ordinal(ActiveRegion active, int row) {
        return active.branchMappings.get(row).get("occurrence").getAsInt();
    }

    /** One open root invocation frame, as an entry hook pushes one. */
    private static Object rootInvocationFrame(long token) throws Exception {
        Class<?> shape = Class.forName("edu.uva.liftlab.graphchecker.runtime"
                + ".ConcolicRegionRuntime$RootInvocationFrame");
        java.lang.reflect.Constructor<?> open = null;
        for (java.lang.reflect.Constructor<?> declared
                : shape.getDeclaredConstructors()) {
            if (declared.getParameterTypes().length == 5) open = declared;
        }
        open.setAccessible(true);
        Object frame = open.newInstance("sel", METHOD, "group", 0, token);
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
        long token = 900000L + opened.size() + 1;
        ActiveRegion active =
                new ActiveRegion(token,
                        new ConcolicTaskPlan.RuntimeTask(task()), null,
                        Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        opened.push(token);
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
