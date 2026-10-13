package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A doors-only occurrence (a control producer's or a store fetch's, {@code
 * RuntimeSelectedRegionFinalizer#DOORS_ONLY}) runs its door markers' inputs
 * alone and with the path condition paused from its start to its close, but
 * for each door decision and each mutation of a tracked container at a named
 * site: the pause lifted there, restored at the next hook, released at the
 * close.  The pause is the VM's base pause ({@code System.pauseConcolicBase}),
 * under which a frame the program pushes keeps its tracking, so a door in a
 * callee decides; a hook's own pause stays the observation pause.  The VM is
 * a recorder of the pause calls it is asked.
 */
public class DoorsOnlyRuntimeTest {
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String MAP = "<a.B: java.util.Map m>";

    /** The pause calls and container observations the "VM" was asked. */
    public static final class Vm {
        static int pauses;
        static int resumes;
        static int basePauses;
        static int baseResumes;
        static final List<Boolean> observed = new ArrayList<>();

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
            observed.add(afterMutation);
            return 0L;
        }
    }

    @Rule
    public final TemporaryFolder session = new TemporaryFolder();

    private Long token;

    @Before
    public void installVm() throws Exception {
        Vm.pauses = 0;
        Vm.resumes = 0;
        Vm.basePauses = 0;
        Vm.baseResumes = 0;
        Vm.observed.clear();
        RowRuntime.resetForTests();
        ConcolicVmBroker broker = new ConcolicVmBroker();
        set(broker, "pausePathCondition", Vm.class.getMethod("pause"));
        set(broker, "resumePathCondition", Vm.class.getMethod("resume"));
        set(broker, "pauseBase", Vm.class.getMethod("pauseBase"));
        set(broker, "resumeBase", Vm.class.getMethod("resumeBase"));
        set(broker, "observeContainer", Vm.class.getMethod("observe",
                Object.class, boolean.class));
        engineApi().set(null, broker);
    }

    @After
    public void releaseVm() throws Exception {
        engineApi().set(null, null);
        if (token != null) {
            ConcolicRegionRuntime.ACTIVE.remove(token);
            currentTokens().clear();
        }
        threadLocal("DOOR_WINDOW").remove();
        threadLocal("OBSERVATION_PAUSE_DEPTH").remove();
        RowRuntime.resetForTests();
    }

    /** The hook after a container mutation on a thread outside every region
     *  marks the log, and throws nothing into the program. */
    @Test
    public void aContainerMutationOutsideEveryRegionIsMarked() {
        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_AFTER_MUTATION);
        assertEquals("[true]", Vm.observed.toString());
        assertEquals(0, Vm.pauses + Vm.resumes + Vm.basePauses
                + Vm.baseResumes);
    }

    /** A doors-only task keeps its door markers' inputs alone and reads no
     *  tracked state from entry; its pause is taken at the end of its entry
     *  hook's bracket, lifted before a named container mutation and at a
     *  door decision, never at a read, restored at the next hook, and
     *  released at the close: the pauses and resumes balance. */
    @Test
    public void aDoorsOnlyOccurrenceRunsPausedButForItsDoors()
            throws Exception {
        ConcolicTaskPlan.RuntimeTask task = new ConcolicTaskPlan.RuntimeTask(
                task());
        assertTrue(task.doorsOnly);
        assertFalse(task.readsTrackedState);
        assertEquals(1, task.symbolize.size());
        assertEquals("FAULT:SOLR_HTTP:SEND", task.symbolize.get(0).marker);
        ActiveRegion active = region(task);
        // The entry hook's bracket ends: the base pause is taken there, as
        // the VM's base pause; the hook's own is an observation pause.
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
        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_BEFORE_MUTATION);
        assertEquals("a mutation runs hooked", 1, Vm.baseResumes);
        assertFalse(active.basePaused);

        ConcolicRegionRuntime.pauseObservation();
        assertTrue("the next hook restores the pause", active.basePaused);
        ConcolicRegionRuntime.resumeObservation();

        // A door's mint runs in its hook's bracket: the bracket's end keeps
        // the window open.
        ConcolicRegionRuntime.pauseObservation();
        ConcolicRegionRuntime.openDoorWindow(active);
        ConcolicRegionRuntime.resumeObservation();
        assertFalse("a door decides unpaused", active.basePaused);
        ConcolicRegionRuntime.pauseObservation();
        assertTrue(active.basePaused);
        Method release = ConcolicRegionRuntime.class.getDeclaredMethod(
                "releaseBasePause", ActiveRegion.class);
        release.setAccessible(true);
        release.invoke(null, active);
        assertFalse(active.basePaused);
        active.finished.set(true);
        ConcolicRegionRuntime.resumeObservation();
        assertFalse("a closed occurrence holds no pause", active.basePaused);
        assertEquals("balanced", 0, Vm.resumes - Vm.pauses);
        assertEquals("the base pause balanced", 3, Vm.basePauses);
        assertEquals(3, Vm.baseResumes);
        assertEquals("[false, false]", Vm.observed.toString());
    }

    /**
     * A woven branch the VM gives no event while its occurrence records
     * there -- its frame does not track -- is named once, never silent: a
     * door there would decide nothing and EXPLORE find its occurrence
     * faultless.  Under the base pause the occurrence records nothing, so
     * there the VM owes no event and nothing is named.
     */
    @Test
    public void aBranchTheVmGivesNoEventWhileRecordingIsNamed()
            throws Exception {
        Path results = session.getRoot().toPath().resolve("iteration-0000")
                .resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        RowRuntime.configure(results);
        ActiveRegion active = region(new ConcolicTaskPlan.RuntimeTask(
                task()));
        active.pathRecordingStarted = true;
        Class<?> decision = Class.forName("edu.uva.liftlab.graphchecker"
                + ".runtime.BranchObservation$BranchDecision");
        Method binary = decision.getDeclaredMethod("binary", boolean.class);
        binary.setAccessible(true);
        Method observe = BranchObservation.class.getDeclaredMethod("observe",
                decision, long.class, long.class, String.class, int.class,
                String.class);
        observe.setAccessible(true);

        active.basePaused = true;
        long paused = BranchObservation.prepare(METHOD, 9, "x == 0");
        assertTrue(paused > 0L);
        observe.invoke(null, binary.invoke(null, true), paused, 0L, METHOD,
                9, "x == 0");
        assertTrue("paused, the VM owes no event", gaps().isEmpty());

        active.basePaused = false;
        long door = BranchObservation.prepare(METHOD, 11, "$fault14 == 0");
        observe.invoke(null, binary.invoke(null, true), door, 0L, METHOD,
                11, "$fault14 == 0");
        List<GapRow> named = gaps();
        assertEquals(1, named.size());
        assertEquals(GapKind.UNATTESTED_ARM, named.get(0).kind());
        assertEquals(GapClass.DIAGNOSTIC, named.get(0).cls());
        assertEquals(METHOD + "#u11", named.get(0).subject());
        assertTrue("and no row states an arm", active.branchMappings
                .isEmpty());
    }

    private List<GapRow> gaps() throws Exception {
        return RowCodec.readAll(SessionDir.of(
                        session.getRoot().toPath().resolve("iteration-0000"),
                        RowRuntime.sessionId()).gaps(),
                RowCodec::readGap);
    }

    private ActiveRegion region(ConcolicTaskPlan.RuntimeTask task)
            throws Exception {
        token = 910000L;
        ActiveRegion active = new ActiveRegion(token, task, null,
                Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        return active;
    }

    private static ExecutionTask task() {
        String access = "'mode':'SYMBOLIC','bindingMode':'FIELD_ACCESS',"
                + "'accessFieldSignature':'<a.B: int f>','accessSites':['"
                + METHOD + "#u4']";
        String plan = ("{'taskId':'TASK.1','goalId':'GOAL.1','goalKind':"
                + "'REGION_PATH_CLOSURE','regionId':'REGION.1',"
                + "'relationKey':'REL.1','sourceKey':'dn0#epoch0',"
                + "'occurrenceId':'REGION.1@dn0#epoch0#1','rootMethod':'"
                + METHOD + "','instrumentationSelector':'sel','admission':"
                + "{'state':'EXECUTABLE'},'rootSelector':{'kind':"
                + "'GLOBAL_INVOCATION','invocationOrdinal':1,'causalAnchor':"
                + "{'sourceKey':'dn0#epoch0','kind':'REGISTERED_SOURCE'}},"
                + "'branchMethods':['" + METHOD + "'],"
                + "'inputActions':[{'symbol':'sym.f'," + access + "},"
                + "{'symbol':'sym.door','marker':'FAULT:SOLR_HTTP:SEND',"
                + access + "}],"
                + "'loopBound':{'schemaVersion':1,"
                + "'defaultBackedgeTraversals':8},"
                + "'readsTrackedState':true,'doorsOnly':true}")
                .replace('\'', '"');
        return ExecutionTask.decode(
                JsonParser.parseString(plan).getAsJsonObject());
    }

    private static void set(Object owner, String name, Object value)
            throws Exception {
        Field field = owner.getClass().getDeclaredField(name);
        field.setAccessible(true);
        field.set(owner, value);
    }

    private static Field engineApi() throws Exception {
        Field field = ConcolicVmBroker.class.getDeclaredField("engineApi");
        field.setAccessible(true);
        return field;
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Object> threadLocal(String name)
            throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(name);
        field.setAccessible(true);
        return (ThreadLocal<Object>) field.get(null);
    }

    @SuppressWarnings("unchecked")
    private static Deque<Long> currentTokens() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Long>>) field.get(null)).get();
    }
}
