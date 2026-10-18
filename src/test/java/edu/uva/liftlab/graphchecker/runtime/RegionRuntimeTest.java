package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.call;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.get;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.pushed;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.region;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.set;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.taskRow;
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
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;
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
     * reading then hands no page on, and a page of a read-out the session
     * withholds (unsubmitted by the end, or submitted after) is not decoded.
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
            assertFalse("no page handed on after the end",
                    ConcolicResultPublisher.decodeBeforePublication(1L,
                            () -> fail("decoded after the end")));
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
}
