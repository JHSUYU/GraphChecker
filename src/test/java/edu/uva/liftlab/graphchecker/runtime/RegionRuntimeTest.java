package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.call;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.get;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.pushed;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.region;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.set;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.taskRow;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.tokens;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * One activation of a planned region ({@link ConcolicRegionRuntime},
 * {@link ActiveRegion}, {@link BranchObservation}): the rows a decision
 * writes, the target reach, loop budgets, folds, abandonment, the end of a
 * run, a doors-only occurrence's pause, and an expression read as a DAG.
 */
public class RegionRuntimeTest {
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String DECLARED = METHOD + "#u4";
    private static final String NODE = "hdfs-11741/dn1#epoch0";
    private static final String MAP = "<a.B: java.util.Map m>";
    /** A guard whose method takes two parameters, so its id has a comma. */
    private static final String COMMAS = "<a.B: void run(int,long)>#u9";
    private static final String SNAPSHOTS = "<org.apache.hadoop.hdfs.server"
            + ".namenode.snapshot.SnapshotManager: void deleteSnapshot()>";
    private static final long STRANDED = 990001L;
    private static final String SYMBOLIC = "'mode':'SYMBOLIC','bindingMode':"
            + "'FIELD_ACCESS','accessFieldSignature':'<a.B: int f>',"
            + "'accessSites':['" + DECLARED + "']";

    @Rule
    public final TemporaryFolder session = new TemporaryFolder();

    @Before
    public void reset() {
        Identity.resetForTests();
        Lineage.resetForTests();
        RowRuntime.resetForTests();
        RuntimeTraceContext.resetForTests();
        set(ConcolicVmBroker.class, "engineApi", null);
    }

    @After
    public void releaseRegions() throws Exception {
        Fixtures.release();
        ConcolicRegionRuntime.STRANDED.remove(STRANDED);
        ((Deque<?>) threadLocal("ROOT_INVOCATION_FRAMES").get()).clear();
        ((Deque<?>) threadLocal("SILENCED").get()).clear();
        threadLocal("DOOR_WINDOW").remove();
        threadLocal("OBSERVATION_PAUSE_DEPTH").remove();
        set(ConcolicVmBroker.class, "engineApi", null);
        set(ConcolicTaskPlan.class, "plan", null);
        Identity.resetForTests();
        Lineage.resetForTests();
        RowRuntime.resetForTests();
    }

    /** REGION.1 on dn0 rooted at {@link #METHOD}, its branches woven. */
    private static JsonObject task(String goal, String members) {
        return taskRow("dn0#epoch0", "REGION.1@dn0#epoch0#1", METHOD, false,
                "'goalKind':'" + goal + "','branchMethods':['" + METHOD + "']"
                        + (members.isEmpty() ? "" : "," + members));
    }

    /** One branch declared at u4, one loop boundary at u12, one target. */
    private static JsonObject declared() {
        return task("TARGET_REACH_CLOSURE", "'inputActions':[{'symbol':"
                + "'sym.f'," + SYMBOLIC + "}],'retainedLoops':[{"
                + "'loopExitDecisions':[{'siteId':'" + METHOD + "#u12'}]}],"
                + "'targetBranch':{'siteId':'" + DECLARED + "','occurrence':1,"
                + "'requiredOutcome':true}");
    }

    /** A doors-only task: a field input and a door marker's. */
    private static JsonObject doorsOnly() {
        return task("REGION_PATH_CLOSURE", "'inputActions':[{'symbol':"
                + "'sym.f'," + SYMBOLIC + "},{'symbol':'sym.door','marker':"
                + "'FAULT:SOLR_HTTP:SEND'," + SYMBOLIC + "}],"
                + "'readsTrackedState':true,'doorsOnly':true");
    }

    private int opened;

    /** A fresh activation of {@code row}, innermost on this thread. */
    private ActiveRegion open(JsonObject row) {
        return pushed(region(900000L + ++opened, row));
    }

    /**
     * What a region writes down for one decision at a declared site: one
     * row naming the site, the arm and the empty path-condition window, and
     * the reach -- the binary branch and the multiway switch alike (one
     * implementation, parameterised by the decision).  That site id is also
     * what the VM's guarded-store table carries for each guard, verbatim,
     * commas and all; the store named as the VM names it; a store into a
     * field only its construction stores is no guarded store.
     */
    @Test
    public void aBinaryDecisionPublishesOneRowAndTheReach() throws Exception {
        for (Object decision : new Object[] {binary(true),
                multiway("0,1,2", 1)}) {
            assertEquals("rows=[{\"method\":\"" + METHOD + "\",\"occurrence\""
                    + ":1,\"outcome\":true,\"rawPathConditionBaseline\":0,"
                    + "\"rawPathConditionSize\":0,\"siteId\":\"" + DECLARED
                    + "\",\"unitIndex\":4}]\ntargetReach={\"kind\":"
                    + "\"TARGET_REACH_EVENT\",\"occurrence\":1,\"outcome\":"
                    + "true,\"siteId\":\"" + DECLARED + "\"}\n"
                    + "returned=observation\n", publishes(decision));
            releaseRegions();
        }
        JsonObject construction = writeSite("a.B#<init>()V", "", DECLARED);
        construction.addProperty("constructionOnly", true);
        GuardedStoreSites table = GuardedStoreSites.of(Arrays.asList(
                writeSite("a.B#run(I)V", "", DECLARED, COMMAS),
                writeSite("a.B#run(I)V", "<java.util.Map: java.lang.Object"
                        + " put(java.lang.Object,java.lang.Object)>",
                        DECLARED), construction));
        assertEquals("a/B#run(I)V\tFIELD a/B.f\t" + DECLARED + "\t" + COMMAS
                + "\na/B#run(I)V\tCALL put\t" + DECLARED + "\n", table.text());
        assertEquals(2, table.sites());
    }

    /** One {@code WRITE_SITE} row storing {@code a.B.f} (by the callee when
     *  one is named), with its guards. */
    private static JsonObject writeSite(String vmSite, String callee,
                                        String... guards) {
        return json("{'kind':'STATIC_SCOPE_SITE','role':'WRITE_SITE',"
                + "'regionId':'REGION.1','siteId':'" + METHOD + "#u7',"
                + "'vmSite':'" + vmSite + "','cell':'<a.B: int f>','carrier':"
                + "'<a.B: int f>','portId':'','declaredCallee':'" + callee
                + "','guards':['" + String.join("','", guards) + "']}");
    }

    /** The transcript one concrete decision at u4 leaves in a fresh
     *  region, its ordinal counted on the occurrence running here. */
    private String publishes(Object decision) throws Exception {
        ActiveRegion active = open(declared());
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame(METHOD + "#u0", null);
        Identity.occurrence(NODE, "REGION.1", true);
        Object returned = call(active, "recordConcreteDecision", new Class<?>[]
                {String.class, int.class, nested("BranchDecision")}, METHOD,
                4, decision);
        JsonArray rows = new JsonArray();
        active.branchMappings.forEach(rows::add);
        Object reach = get(active, "targetReach");
        return "rows=" + CanonicalJson.render(rows) + "\ntargetReach="
                + (reach == null ? "none" : CanonicalJson.render(
                (JsonObject) reach)) + "\nreturned="
                + (returned == null ? "null" : "observation") + "\n";
    }

    /** A loop's unroll budget is counted per method activation: a helper
     *  called again in one activation starts afresh (readVLong cut at its
     *  9th body across a DataXceiver's token fields, a9b). */
    @Test
    public void aLoopBudgetIsCountedPerCall() throws Exception {
        installPlan();
        ActiveRegion active = open(declared());
        String helper = "<a.W: long readVLong(java.io.DataInput)>";
        for (int call = 0; call < 2; call++) {
            long frame = Identity.enterFrame(helper, null);
            active.termedDecisions++;
            assertNull("call " + call + ": its first body",
                    active.traverseBackedge(helper + "#loop:u8", 2));
            active.termedDecisions++;
            assertNotNull("call " + call + ": its second, at K_L 2",
                    active.traverseBackedge(helper + "#loop:u8", 2));
            Identity.exitFrame(frame);
        }
    }

    /**
     * Loop bounds (PIPELINE §2): K_L counts the iterations of a loop call
     * that decided on a term, and every iteration is work, cut past the cap
     * (32 bodies, or a declared K_L above it).  solr-adhoc-19 SG2b: a
     * concrete loop over a core's properties cut the CREATE at its 9th body.
     */
    @Test
    public void kLCountsTheIterationsThatDecidedOnASymbol() {
        int cap = LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES;
        Object[][] rows = {
            // why, K_L (negative: a FORCE run's armed activation), termed
            // decisions per iteration, the traversal cut at, its reason
            {"every iteration decides on a symbol", 8, ones(20), 8,
                "MAX_LOOP_BODY_ITERATIONS_REACHED"},
            {"none does: only the work cap", 8, new int[cap + 5], cap,
                "REPLAY_LOOP_RESOURCE_CAP"},
            {"12 concrete bodies, K_L 8: whole", 8, new int[12], 0, ""},
            {"the first counts, then only the termed ones", 3,
                new int[] {0, 0, 1, 0, 0, 1, 0}, 6,
                "MAX_LOOP_BODY_ITERATIONS_REACHED"},
            {"a declared K_L above the cap raises it", 40, new int[45], 40,
                "REPLAY_LOOP_RESOURCE_CAP"},
            {"the armed FORCE activation: the work cap only", -8, ones(40),
                cap, "REPLAY_LOOP_RESOURCE_CAP"}};
        for (Object[] row : rows) {
            LoopAccounting.LoopBackedgeBudget budget =
                    new LoopAccounting.LoopBackedgeBudget();
            int[] termed = (int[]) row[2];
            int bound = (Integer) row[1];
            int total = 0;
            int cutAt = 0;
            String reason = "";
            for (int traversal = 1; traversal <= termed.length; traversal++) {
                total += termed[traversal - 1];
                Error cut = budget.traverse("L#loop:u4", "key", total,
                        Math.abs(bound), bound < 0);
                if (cut != null) {
                    cutAt = traversal;
                    reason = cut.getMessage().split(" ")[0];
                    break;
                }
            }
            assertEquals((String) row[0], row[3], cutAt);
            assertEquals((String) row[0], row[4], reason);
        }
        // A fixed-count loop's bodies take the same work cap a backedge's
        // traversals do (LoopBoundPolicy#workCap), raised by a K_L above it.
        for (int bound : new int[] {8, 40}) {
            LoopAccounting.LoopBackedgeBudget budget =
                    new LoopAccounting.LoopBackedgeBudget();
            int bodyCut = 0;
            int traversalCut = 0;
            for (int body = 1; body <= 64 && bodyCut == 0; body++) {
                if (budget.body("L#loop:u4", "fixed", bound) != null) {
                    bodyCut = body;
                }
            }
            for (int traversal = 1; traversal <= 64 && traversalCut == 0;
                 traversal++) {
                if (budget.traverse("L#loop:u4", "edge", 0, bound, false)
                        != null) {
                    traversalCut = traversal + 1;
                }
            }
            assertEquals("K_L " + bound, LoopBoundPolicy.workCap(bound) + 1,
                    bodyCut);
            assertEquals("K_L " + bound, bodyCut, traversalCut);
        }
    }

    private static int[] ones(int n) {
        int[] values = new int[n];
        Arrays.fill(values, 1);
        return values;
    }

    /**
     * An activation that decides the addressed target site has reached the
     * target, symbolic or concrete; only a decision with no recorded row is
     * silent.  The declared occurrence decided at its required outcome is
     * the reach, a throw never: the activation keeps no exit kind, and with
     * no target declared there is nothing to reach.  An envelope carrying no
     * expression is still the honest nothing.
     */
    @Test
    public void aConcreteDecisionAtTheTargetSiteIsStillAReach()
            throws Exception {
        String target = SNAPSHOTS + "#u61";
        // site decided, occurrence decided, permuted by a loop, reaches
        Object[][] decisions = {{target, 1, false, true},
                {target, 2, false, false}, {target, 3, true, true},
                {SNAPSHOTS + "#u44", 1, false, false}};
        for (Object[] decided : decisions) {
            assertEquals(decided[0] + "#" + decided[1], decided[3],
                    ConcolicRegionRuntime.statesTargetReach(true,
                            (Boolean) decided[2], target.equals(decided[0]),
                            1, (Integer) decided[1]));
        }
        assertFalse(ConcolicRegionRuntime.statesTargetReach(false, false,
                true, 1, 1));

        ActiveRegion undeclared = open(task("TARGET_REACH_CLOSURE", ""));
        assertNull(ConcolicRegionRuntime.engineExpression("{}"));
        assertFalse("an undeclared target cannot have been reached",
                undeclared.activation.reachedRequiredTargetOutcome(
                        undeclared.targetReach));
        ActiveRegion reached = open(declared());
        set(reached, "targetReach", json("{'kind':'TARGET_REACH_EVENT',"
                + "'siteId':'" + DECLARED + "','occurrence':1,"
                + "'outcome':true}"));
        assertTrue(reached.activation.reachedRequiredTargetOutcome(
                reached.targetReach));
    }

    /**
     * I3: an abandoned occurrence hands its later branches to nobody.  A
     * prefix contradiction ends an activation from INSIDE the region method
     * and the call goes on; its later branches were recorded on the
     * ENCLOSING activation, ordinals restarting at 1 (10 of hdfs-11741's 40
     * nn0-focused sessions).  After the close no occurrence is active, and
     * the enclosing one is the thread's again when the call returns.
     */
    @Test
    public void anAbandonedOccurrenceHandsItsLaterBranchesToNobody()
            throws Exception {
        ActiveRegion enclosing = open(declared());
        ActiveRegion abandoned = open(declared());
        Class<?> shape = Class.forName(ConcolicRegionRuntime.class.getName()
                + "$RootInvocationFrame");
        java.lang.reflect.Constructor<?> constructor =
                shape.getDeclaredConstructor(String.class, String.class);
        constructor.setAccessible(true);
        Object frame = constructor.newInstance("sel", METHOD);
        set(frame, "token", abandoned.token);
        rootInvocationFrames().push(frame);
        assertEquals(abandoned, ConcolicRegionRuntime.activeRegion());
        call(ConcolicRegionRuntime.class, "silenceStillRunningFrame",
                new Class<?>[] {ActiveRegion.class}, abandoned);
        tokens().pop();
        assertNull("no occurrence performs the rest of that frame",
                ConcolicRegionRuntime.activeRegion());
        assertEquals(frame, call(ConcolicRegionRuntime.class,
                "popRootInvocationFrame", new Class<?>[] {String.class,
                        String.class}, "sel", METHOD));
        assertEquals(enclosing, ConcolicRegionRuntime.activeRegion());
    }

    /**
     * IDENTITY §1: a folded entry starts no activation.  The fold already
     * stands when admission would be asked, so this call is a method call
     * INSIDE the running occurrence; an activation would be a second one of
     * it.  The control, no fold standing, does reach admission.
     */
    @Test
    public void aFoldedEntryStartsNoActivation() throws Exception {
        installPlan();
        try {
            Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
            Identity.enterFrame("<a.B: void outer()>#u1", null);
            assertEquals("REGION.1", Identity.occurrence(NODE, "REGION.1",
                    true).regionId());
            Identity.enterFrame(METHOD + "#u0", null);
            Identity.occurrence(NODE, "REGION.2", true);
            assertTrue(Identity.openedNone());
            int live = ConcolicRegionRuntime.ACTIVE.size();
            assertEquals("no token, so no activation", 0L,
                    ConcolicRegionRuntime.enterRegionFrame("sel", METHOD,
                            null, new Object[0]));
            assertEquals(live, ConcolicRegionRuntime.ACTIVE.size());
            assertNull(ConcolicRegionRuntime.activeRegion());
            assertNull("admission was never asked: the fold never reached "
                    + "the engine", get(ConcolicVmBroker.class, "engineApi"));
            ConcolicRegionRuntime.exitRegionFrame("sel", METHOD);

            Identity.resetForTests();
            Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
            Identity.enterFrame(METHOD + "#u0", null);
            Identity.occurrence(NODE, "REGION.2", true);
            assertFalse(Identity.openedNone());
            try {
                ConcolicRegionRuntime.enterRegionFrame("sel", METHOD, null,
                        new Object[0]);
            } catch (Throwable withoutAVm) {
                // No VM to start a region in: reaching admission is enough.
            }
            assertNotNull("the control did reach admission",
                    get(ConcolicVmBroker.class, "engineApi"));
        } finally {
            ConcolicRegionRuntime.exitRegionFrame("sel", METHOD);
        }
    }

    /** A replay on a VM missing a native this side binds fails before its
     *  workload, naming what is missing. */
    @Test
    public void aVmWithoutTheCurrentNativesRefusesTheReplay()
            throws Exception {
        installPlan();
        try {
            ConcolicRegionRuntime.openWorkloadSession();
            fail("a stock JDK opened a concolic session");
        } catch (IllegalStateException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("observeField"));
        }
    }

    private static void installPlan() {
        set(ConcolicTaskPlan.class, "plan", new ConcolicTaskPlan(null,
                Collections.singletonList(Fixtures.runtimeTask(declared()))));
    }

    /**
     * The end of a run: its settle gives up only on a grace in which nothing
     * moved; a stranded activation is settled in one step, its own terminal
     * still finding it; a terminal that wins leaves nothing to strand.
     */
    @Test
    public void aStrandIsOneStepAndTheOwnersTerminalStillTakesIt() {
        ConcolicResultPublisher.Grace grace = new ConcolicResultPublisher
                .Grace(100L, 0L, new long[] {1L, 0L});
        long[][] table = {
            // now, progress..., remaining
            {0L, 1L, 0L, 100L}, {60L, 1L, 0L, 40L}, {70L, 1L, 5L, 100L},
            {150L, 1L, 5L, 20L}, {180L, 1L, 5L, -10L}};
        for (long[] row : table) {
            assertEquals("at " + row[0], row[3], grace.remaining(row[0],
                    new long[] {row[1], row[2]}));
        }
        JsonObject run = taskRow("hdfs/nn0#epoch0",
                "hdfs/nn0#epoch0/region/REGION.1#1", "<a.B: void run()>", true,
                "");
        ActiveRegion won = Fixtures.live(region(STRANDED, run));
        assertTrue(won.finished.compareAndSet(false, true));
        assertFalse(ConcolicRegionRuntime.strand(won));
        assertTrue("still the run's to close",
                ConcolicRegionRuntime.ACTIVE.containsKey(STRANDED));
        assertFalse(ConcolicRegionRuntime.STRANDED.containsKey(STRANDED));

        ActiveRegion active = Fixtures.live(region(STRANDED, run));
        assertTrue(ConcolicRegionRuntime.strand(active));
        assertTrue(active.finished.get() && active.abandoned);
        assertFalse(ConcolicRegionRuntime.ACTIVE.containsKey(STRANDED));
        assertSame(active, ConcolicRegionRuntime.STRANDED.get(STRANDED));
        assertFalse("once", ConcolicRegionRuntime.strand(active));
        try {
            // Its own terminal closes the VM region this JVM has none of.
            ConcolicRegionRuntime.finish(STRANDED, "NORMAL", "", null);
        } catch (RuntimeException noVm) {
            // The region it tried to close is the VM's.
        }
        assertFalse("its terminal took it",
                ConcolicRegionRuntime.STRANDED.containsKey(STRANDED));
    }

    /**
     * An early end strands the live before its settle waits, so the settle
     * waits only for the publications the session owes; a read-out still
     * reading then reads no more pages, and a page of a read-out the
     * session withholds (unsubmitted by the end, or submitted after) files
     * nothing (its table is still the read-out channel's).
     */
    @Test(timeout = 60000L)
    public void anEarlyEndStrandsTheLiveAndDecodesNothingWithheld() {
        JsonObject run = taskRow("hdfs/nn0#epoch0",
                "hdfs/nn0#epoch0/region/REGION.1#1", "<a.B: void run()>", true,
                "");
        ActiveRegion live = Fixtures.live(region(STRANDED, run));
        set(ConcolicResultPublisher.class, "liveSelectedRegions", 1);
        set(ConcolicResultPublisher.class, "concluded",
                ConcolicResultPublisher.Conclusion.STALLED_AFTER_FLIP);
        set(ConcolicResultPublisher.class, "submittedAtEnd", 2L);
        try {
            assertFalse("no page read after the end",
                    ConcolicResultPublisher.awaitDecodeRoom(1L));
            long[][] table = {
                // ordinal, withheld (1 = yes)
                {0L, 1L}, {1L, 0L}, {2L, 0L}, {3L, 1L}};
            for (long[] row : table) {
                SharedStateCapture.SharedStateReadOut readOut =
                        new SharedStateCapture.SharedStateReadOut();
                readOut.ordinal = row[0];
                assertEquals("ordinal " + row[0], row[1] == 1L,
                        ConcolicResultPublisher.withholds(readOut));
            }
            ConcolicResultPublisher.awaitSelectedResultPublications();
            assertSame("stranded before any wait", live,
                    ConcolicRegionRuntime.STRANDED.get(STRANDED));
            assertEquals(0, get(ConcolicResultPublisher.class,
                    "liveSelectedRegions"));
            // A withdrawn session (a stall before any flip) waits for none,
            // not even a publication still running.
            set(ConcolicResultPublisher.class, "strandedAtEnd", false);
            set(ConcolicResultPublisher.class, "concluded",
                    ConcolicResultPublisher.Conclusion.AT_NO_PROGRESS);
            set(ConcolicResultPublisher.class, "resultPublicationsInFlight",
                    1);
            long started = System.nanoTime();
            ConcolicResultPublisher.awaitSelectedResultPublications();
            assertTrue("no wait", System.nanoTime() - started
                    < java.util.concurrent.TimeUnit.SECONDS.toNanos(10L));
        } finally {
            set(ConcolicResultPublisher.class, "resultPublicationsInFlight",
                    0);
            set(ConcolicResultPublisher.class, "concluded", null);
            set(ConcolicResultPublisher.class, "submittedAtEnd",
                    Long.MAX_VALUE);
            set(ConcolicResultPublisher.class, "strandedAtEnd", false);
            set(ConcolicResultPublisher.class, "liveSelectedRegions", 0);
        }
    }

    /** The pause calls and container observations the "VM" was asked. */
    public static final class Vm {
        static int pauses;
        static int resumes;
        static int basePauses;
        static int baseResumes;
        static final List<Boolean> OBSERVED = new ArrayList<>();

        public static void pause() {
            pauses++;
        }

        public static void resume() {
            resumes++;
        }

        public static void pauseBase() {
            basePauses++;
        }

        public static void resumeBase() {
            baseResumes++;
        }

        public static long observe(Object container, boolean afterMutation) {
            OBSERVED.add(afterMutation);
            return 0L;
        }
    }

    /** A VM that records the pause calls it is asked. */
    private static void installVm() throws Exception {
        Vm.pauses = 0;
        Vm.resumes = 0;
        Vm.basePauses = 0;
        Vm.baseResumes = 0;
        Vm.OBSERVED.clear();
        ConcolicVmBroker broker = new ConcolicVmBroker();
        set(broker, "pausePathCondition", Vm.class.getMethod("pause"));
        set(broker, "resumePathCondition", Vm.class.getMethod("resume"));
        set(broker, "pauseBase", Vm.class.getMethod("pauseBase"));
        set(broker, "resumeBase", Vm.class.getMethod("resumeBase"));
        set(broker, "observeContainer", Vm.class.getMethod("observe",
                Object.class, boolean.class));
        set(ConcolicVmBroker.class, "engineApi", broker);
    }

    /**
     * A doors-only occurrence ({@code RuntimeSelectedRegionFinalizer
     * #DOORS_ONLY}) keeps its door markers' inputs alone and reads no tracked
     * state from entry; its VM base pause is taken at the end of its entry
     * hook's bracket, lifted before a named container mutation and at a door
     * decision, never at a read, restored at the next hook and released at
     * the close: pauses and resumes balance.  The hook after a mutation on a
     * thread outside every region marks the log and throws nothing.
     */
    @Test
    public void aDoorsOnlyOccurrenceRunsPausedButForItsDoors()
            throws Exception {
        installVm();
        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_AFTER_MUTATION);
        assertEquals("[true]", Vm.OBSERVED.toString());
        assertEquals(0, Vm.pauses + Vm.resumes + Vm.basePauses
                + Vm.baseResumes);
        Vm.OBSERVED.clear();

        ConcolicTaskPlan.RuntimeTask task = Fixtures.runtimeTask(doorsOnly());
        assertTrue(task.doorsOnly);
        assertFalse(task.readsTrackedState);
        assertEquals(1, task.symbolize.size());
        assertEquals("FAULT:SOLR_HTTP:SEND", task.symbolize.get(0).marker);
        ActiveRegion active = open(doorsOnly());
        ConcolicRegionRuntime.pauseObservation();
        ConcolicRegionRuntime.resumeObservation();
        assertTrue(active.basePaused);
        assertEquals(1, Vm.basePauses);
        assertEquals(1, Vm.pauses);
        assertEquals(1, Vm.resumes);
        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_READ);
        assertEquals("a read stays paused", 0, Vm.baseResumes);
        ConcolicRegionRuntime.pauseObservation();
        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_BEFORE_MUTATION);
        ConcolicRegionRuntime.resumeObservation();
        assertEquals("a mutation runs hooked", 1, Vm.baseResumes);
        assertFalse(active.basePaused);
        ConcolicRegionRuntime.pauseObservation();
        assertTrue("the next hook restores the pause", active.basePaused);
        ConcolicRegionRuntime.resumeObservation();
        ConcolicRegionRuntime.pauseObservation();
        ConcolicRegionRuntime.openDoorWindow(active);
        ConcolicRegionRuntime.resumeObservation();
        assertFalse("a door decides unpaused", active.basePaused);
        ConcolicRegionRuntime.pauseObservation();
        assertTrue(active.basePaused);
        call(ConcolicRegionRuntime.class, "releaseBasePause",
                new Class<?>[] {ActiveRegion.class}, active);
        assertFalse(active.basePaused);
        active.finished.set(true);
        ConcolicRegionRuntime.resumeObservation();
        assertFalse("a closed occurrence holds no pause", active.basePaused);
        assertEquals("balanced", 0, Vm.resumes - Vm.pauses);
        assertEquals(3, Vm.basePauses);
        assertEquals(3, Vm.baseResumes);
        assertEquals("[false, false]", Vm.OBSERVED.toString());
    }

    /**
     * THE RULE: a door window opens only inside a woven observation bracket;
     * asked for outside one it is not opened, an ENGINE_FAULT; so is an
     * activation whose VM refused observation resumes.  A woven branch the
     * VM gives no event while its occurrence records is an UNATTESTED_ARM,
     * named once; under the base pause the VM owes no event.
     */
    @Test
    public void aWindowOutsideEveryBracketAndARefusedResumeAreNamed()
            throws Exception {
        installVm();
        Fixtures.openSession(session.getRoot().toPath());
        ActiveRegion active = open(doorsOnly());
        active.basePaused = true;
        ConcolicRegionRuntime.openDoorWindow(active);
        assertTrue("not opened", active.basePaused);
        assertEquals(0, Vm.baseResumes);
        JsonObject summary = json("{'refusedObservationResumes':0}");
        ConcolicRegionRuntime.refusedResumes(active, summary);
        summary.addProperty("refusedObservationResumes", 2);
        ConcolicRegionRuntime.refusedResumes(active, summary);
        List<GapRow> named = Fixtures.gaps(session.getRoot().toPath());
        assertEquals(2, named.size());
        for (GapRow gap : named) {
            assertEquals(GapKind.ENGINE_FAULT, gap.kind());
            assertEquals(GapClass.BLOCKING, gap.cls());
        }
        assertTrue(named.get(0).detail().contains("outside every woven"));
        assertTrue(named.get(1).detail().startsWith("2 observation"));

        active.pathRecordingStarted = true;
        Class<?>[] observed = {nested("BranchDecision"), long.class,
                long.class, String.class, int.class, String.class};
        long paused = BranchObservation.prepare(METHOD, 9, "x == 0");
        assertTrue(paused > 0L);
        call(BranchObservation.class, "observe", observed, binary(true),
                paused, 0L, METHOD, 9, "x == 0");
        assertEquals("paused, the VM owes no event", 2,
                Fixtures.gaps(session.getRoot().toPath()).size());
        active.basePaused = false;
        long door = BranchObservation.prepare(METHOD, 11, "$fault14 == 0");
        call(BranchObservation.class, "observe", observed, binary(true), door,
                0L, METHOD, 11, "$fault14 == 0");
        GapRow unattested = Fixtures.lastGap(session.getRoot().toPath());
        assertEquals(3, Fixtures.gaps(session.getRoot().toPath()).size());
        assertEquals(GapKind.UNATTESTED_ARM, unattested.kind());
        assertEquals(GapClass.DIAGNOSTIC, unattested.cls());
        assertEquals(METHOD + "#u11", unattested.subject());
        assertTrue("no row states an arm", active.branchMappings.isEmpty());
    }

    private static Object binary(boolean outcome) throws Exception {
        return call(nested("BranchDecision"), "binary",
                new Class<?>[] {boolean.class}, outcome);
    }

    private static Object multiway(String keys, int successor)
            throws Exception {
        return call(nested("BranchDecision"), "multiway",
                new Class<?>[] {nested("SwitchExpectation")},
                call(nested("SwitchExpectation"), "parse", new Class<?>[]
                        {String.class, String.class, int.class},
                        "TABLE_SWITCH", keys, successor));
    }

    private static Class<?> nested(String name) throws Exception {
        return Class.forName(BranchObservation.class.getName() + "$" + name);
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Object> threadLocal(String name) {
        return (ThreadLocal<Object>) get(ConcolicRegionRuntime.class, name);
    }

    @SuppressWarnings("unchecked")
    private static Deque<Object> rootInvocationFrames() {
        return (Deque<Object>) threadLocal("ROOT_INVOCATION_FRAMES").get();
    }

    /**
     * The replay decodes a VM expression as a shared DAG, and a
     * FieldAccessExpression names its owner twice, so a chain of them is
     * 2^depth nodes as a tree; every question the runtime asks walks each
     * node once (SOLR-18413's verifyProp selector was 7.4e10 as a tree).
     */
    @Test(timeout = 20000)
    public void aDoublingChainFortyDeepIsAnsweredAtOnce() {
        // Three conditions of one lookupswitch's default arm: the first and
        // third name one selector node, the second an equal chain decoded
        // apart -- one selector either way.
        PathConditionWindow window = PathConditionWindow.window(envelope(
                new int[] {0, 1000, 0}, chain(0, "s"), chain(1000, "s"),
                chain(2000, "t")), 0, new VmExpressionTable.Store(
                owner -> false));
        JsonArray indices = new JsonArray();
        for (int index = 0; index < 3; index++) indices.add(index);
        VmBranchAttestation.Attestation attested =
                VmBranchAttestation.attestSwitchConditions(json("{'opcode':"
                        + "171,'codePosition':'p'}"),
                        BranchObservation.SwitchExpectation.parse(
                                "LOOKUP_SWITCH", "1,2,3", 3), indices,
                        window);
        assertTrue(attested.error, attested.valid);
        assertEquals(Arrays.asList(0, 1, 2), attested.conditionIndices);
        JsonObject one = selector(window, 0);
        assertFalse("the two chains are two nodes",
                one == selector(window, 1));
        assertTrue(VmBranchAttestation.sameExpression(one,
                selector(window, 1)));
        PathConditionWindow apart = PathConditionWindow.window(envelope(
                new int[] {0, 2000, 0}, chain(0, "s"), chain(1000, "s"),
                chain(2000, "t")), 0, new VmExpressionTable.Store(
                owner -> false));
        assertFalse("another leaf symbol is another selector",
                VmBranchAttestation.sameExpression(selector(apart, 0),
                        selector(apart, 1)));
        try {
            JsonFields.optionalString(one, "owner");
            fail("an object member is not a string");
        } catch (IllegalArgumentException refused) {
            assertTrue("a refusal quotes the member cut: "
                    + refused.getMessage(), refused.getMessage().length()
                    < 1024 && refused.getMessage().contains("...,"));
        }
    }

    private static final int DEPTH = 40;

    private static JsonObject selector(PathConditionWindow window, int index) {
        return window.get(index).getAsJsonObject().getAsJsonObject("_left");
    }

    /** A symbol, then DEPTH field accesses each naming the one below as
     *  owner and concrete owner. */
    private static String chain(int base, String symbol) {
        StringBuilder definitions = new StringBuilder(definition(base + 1,
                "{\"_type\":\"SymbolExpression\",\"_exp\":\"" + symbol
                        + "\",\"_java_type\":\"I\"}"));
        for (int level = 2; level <= DEPTH + 1; level++) {
            String owner = reference(base + level - 1);
            definitions.append(',').append(definition(base + level,
                    "{\"_type\":\"FieldAccessExpression\",\"owner\":" + owner
                            + ",\"concreteOwner\":" + owner
                            + ",\"_java_type\":\"I\"}"));
        }
        return definitions.toString();
    }

    /** A path-condition range of {@code selector != k}, k = 1.., the i-th
     *  over the chain based at {@code bases[i]}. */
    private static String envelope(int[] bases, String... chains) {
        StringBuilder conditions = new StringBuilder();
        for (int index = 0; index < bases.length; index++) {
            conditions.append(index > 0 ? "," : "").append("{\"_type\":"
                    + "\"BinaryExpression\",\"_op\":\"!=\",\"_left\":")
                    .append(reference(bases[index] + DEPTH + 1))
                    .append(",\"_right\":{\"_type\":\"ConstExpr\",\"_exp\":"
                            + "\"Y_I_").append(index + 1).append("\"}}");
        }
        return "{\"startIndex\":0,\"endIndex\":" + bases.length
                + ",\"pathConditionWatermark\":" + bases.length
                + ",\"conditionCount\":" + bases.length + ",\"conditions\":["
                + conditions + "],\"vmExpressionTable\":{\"schemaVersion\":1,"
                + "\"kind\":\"" + VmExpressionTable.KIND + "\",\"authority\":"
                + "\"" + VmExpressionTable.AUTHORITY + "\",\"sessionId\":7,"
                + "\"definitionCount\":" + chains.length * (DEPTH + 1)
                + ",\"definitions\":[" + String.join(",", chains) + "]}}";
    }

    private static String definition(int id, String expression) {
        return "{\"_type\":\"" + VmExpressionTable.DEFINITION_TYPE
                + "\",\"sessionId\":7,\"expressionId\":" + id
                + ",\"expression\":" + expression + "}";
    }

    private static String reference(int id) {
        return "{\"_type\":\"" + VmExpressionTable.REFERENCE_TYPE
                + "\",\"sessionId\":7,\"expressionId\":" + id + "}";
    }
}
