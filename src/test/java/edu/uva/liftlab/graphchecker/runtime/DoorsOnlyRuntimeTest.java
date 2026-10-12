package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
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
 * close.  The VM is a recorder of the pause calls it is asked.
 */
public class DoorsOnlyRuntimeTest {
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String MAP = "<a.B: java.util.Map m>";

    /** The pause calls and container observations the "VM" was asked. */
    public static final class Vm {
        static int pauses;
        static int resumes;
        static final List<Boolean> observed = new ArrayList<>();

        public static void pause() {
            pauses++;
        }

        public static void resume() {
            resumes++;
        }

        public static long observe(Object container, boolean afterMutation) {
            observed.add(afterMutation);
            return 0L;
        }
    }

    private Long token;

    @Before
    public void installVm() throws Exception {
        Vm.pauses = 0;
        Vm.resumes = 0;
        Vm.observed.clear();
        ConcolicVmBroker broker = new ConcolicVmBroker();
        set(broker, "pausePathCondition", Vm.class.getMethod("pause"));
        set(broker, "resumePathCondition", Vm.class.getMethod("resume"));
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
    }

    /** The hook after a container mutation on a thread outside every region
     *  marks the log, and throws nothing into the program. */
    @Test
    public void aContainerMutationOutsideEveryRegionIsMarked() {
        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_AFTER_MUTATION);
        assertEquals("[true]", Vm.observed.toString());
        assertEquals(0, Vm.pauses + Vm.resumes);
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
        // The entry hook's bracket ends: the base pause is taken there.
        ConcolicRegionRuntime.pauseObservation();
        ConcolicRegionRuntime.resumeObservation();
        assertTrue(active.basePaused);
        assertEquals(2, Vm.pauses);
        assertEquals(1, Vm.resumes);

        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_READ);
        assertEquals("a read stays paused", 1, Vm.resumes);
        ConcolicRegionRuntime.observeTrackedContainer("s", MAP,
                new HashMap<String, String>(),
                ConcolicRegionRuntime.CONTAINER_BEFORE_MUTATION);
        assertEquals("a mutation runs hooked", 2, Vm.resumes);
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
        assertEquals("[false, false]", Vm.observed.toString());
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
