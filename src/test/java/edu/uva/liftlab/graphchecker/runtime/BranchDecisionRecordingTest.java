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

    /** The transcript one concrete decision at u4 leaves in a fresh region. */
    private String publishes(Object decision) throws Exception {
        long token = 900000L + opened.size() + 1;
        ConcolicRegionRuntime.ActiveRegion active =
                new ConcolicRegionRuntime.ActiveRegion(token,
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
                + "'branches':[{'siteId':'" + DECLARED + "','policy':'EXPLORE'"
                + ",'selectedOccurrence':1,'requiredOutcome':true}],"
                + "'inputActions':[{'symbol':'sym.f','mode':'SYMBOLIC',"
                + "'bindingMode':'FIELD_ACCESS','accessFieldSignature':"
                + "'<a.B: int f>','accessSites':['" + DECLARED + "']}],"
                + "'loopBound':{'schemaVersion':1},'retainedLoops':[{"
                + "'loopExitDecisions':[{'siteId':'" + BOUNDARY + "'}]}],"
                + "'targetBranch':{'siteId':'" + DECLARED
                + "','occurrence':1}}").replace('\'', '"');
        return ExecutionTask.decode(
                JsonParser.parseString(plan).getAsJsonObject());
    }

    private String transcript(ConcolicRegionRuntime.ActiveRegion active,
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
                + ".ConcolicRegionRuntime$" + name);
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
