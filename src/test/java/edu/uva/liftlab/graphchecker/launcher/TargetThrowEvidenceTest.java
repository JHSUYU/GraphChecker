package edu.uva.liftlab.graphchecker.launcher;

import edu.uva.liftlab.graphchecker.causynth.CausynthPipeline;
import edu.uva.liftlab.graphchecker.fixtures.MixedTypeThreeThreadRpcWorkload;
import edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder;

import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import soot.Body;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.Stmt;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * A throw that leaves the annotated target method must leave a record.
 *
 * <p>The defect these tests pin down was not a missing hook and not a trap
 * that failed to cover the throw. On the HDFS-11741 run the catch-all was
 * present and did fire - the instrumented bytecode's exception table reads
 * {@code 17-84 -> 87 any} (javac's monitor release), {@code 87-90 -> 87 any},
 * {@code 8-104 -> 104 any} (the injected catch-all), so the throw at 81 went
 * to the monitor handler and its rethrow at 91 landed in the catch-all. What
 * the catch-all called was {@code throwActiveMethodLite}, which pops the
 * activation and writes nothing, so the whole 370,758-row trace held 369,426
 * {@code METHOD_ENTER} rows and not one {@code METHOD_EXIT_*} row of any kind.
 * A run in which the exception escaped the target twelve times was therefore
 * indistinguishable from one in which it never did.</p>
 *
 * <p>The halves below are the halves of that story: the skeleton pass now
 * installs the row-writing hook on the target and only the target, and the row
 * it writes is the row the launcher counts.</p>
 */
public class TargetThrowEvidenceTest {

    private static final String RECORDER =
            CausynthTraceRecorder.class.getName();

    private static final String TARGET =
            "<example.KeyStore: void retrieveKey(java.lang.Throwable)>";

    private static final String SIBLING =
            "<example.KeyStore: void plain()>";

    private static final String TRACE_DIR_PROPERTY =
            "causynth.trace.output.dir";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
    }

    /**
     * The skeleton pass gives the annotated target a recording exceptional
     * exit, keeps every other envelope silent, and says which it did.
     *
     * <p>The target body is shaped like the HDFS one: the throw sits inside
     * {@code synchronized (this)}, so it is caught first by javac's monitor
     * release handler and only reaches the injected catch-all through that
     * handler's rethrow. The trap assertions are what makes that work - the
     * injected trap has to be last in the table and has to span both
     * throws.</p>
     */
    @Test
    public void theSkeletonPassRecordsTheTargetThrowAndNamesTheDifference()
            throws Exception {
        SootClass owner = scene();
        SynchronizedTarget target = synchronizedThrowingTarget(owner);
        SootMethod sibling = plainMethod(owner);

        Object program = staticProgram();
        traceMethods(program).addAll(Arrays.asList(TARGET, SIBLING));
        regions(program).add(region(TARGET, TARGET, SIBLING));
        targetResolved(program).put("method", TARGET);

        Body body = target.method.getActiveBody();
        List<Trap> before = new ArrayList<>(body.getTraps());

        instrumentSkeleton(program);

        List<String> targetHooks = hookNames(body);
        assertTrue(targetHooks.contains("enterMethodLite"));
        // The whole fix: the target's exceptional exit writes a row.
        assertTrue(targetHooks.contains("throwActiveMethod"));
        assertFalse(targetHooks.contains("throwActiveMethodLite"));
        // Normal exit stays silent on the target too, so the entry-only row
        // counts this pass has always produced do not move.
        assertEquals(1, count(targetHooks, "enterMethodLite"));
        assertEquals(1, count(targetHooks, "exitActiveMethodLite"));

        List<String> siblingHooks = hookNames(sibling.getActiveBody());
        assertTrue(siblingHooks.contains("enterMethodLite"));
        assertTrue(siblingHooks.contains("exitActiveMethodLite"));
        assertTrue(siblingHooks.contains("throwActiveMethodLite"));
        assertFalse(siblingHooks.contains("throwActiveMethod"));

        List<Trap> after = new ArrayList<>(body.getTraps());
        assertEquals(before.size() + 1, after.size());
        // Order is the correctness argument: javac's monitor handlers keep
        // their place at the front, so they still win for a throw inside the
        // monitor, and the injected catch-all takes their rethrow.
        assertSame(before.get(0), after.get(0));
        assertSame(before.get(1), after.get(1));
        Trap injected = after.get(after.size() - 1);
        assertSame(target.entry, injected.getBeginUnit());
        assertSame(injected.getHandlerUnit(), injected.getEndUnit());
        List<Unit> covered = range(body, injected);
        assertTrue(covered.contains(target.targetThrow));
        assertTrue(covered.contains(target.monitorRethrow));
        assertFalse(covered.contains(injected.getHandlerUnit()));

        assertEquals(Boolean.TRUE,
                targetResolved(program).get("skeletonTargetThrowRecorded"));

        body.validate();
        sibling.getActiveBody().validate();
    }

    /**
     * A pass whose annotated target is not among the instrumented methods
     * writes no recording hook at all, and says so in the discovery artifact
     * rather than leaving a later zero count to be read as an observation.
     */
    @Test
    public void anUnresolvedTargetIsNamedRatherThanSilentlyUnrecorded()
            throws Exception {
        SootMethod sibling = plainMethod(scene());

        Object program = staticProgram();
        traceMethods(program).add(SIBLING);
        regions(program).add(region(SIBLING, SIBLING));

        instrumentSkeleton(program);

        assertTrue(hookNames(sibling.getActiveBody())
                .contains("throwActiveMethodLite"));
        assertEquals(Boolean.FALSE,
                targetResolved(program).get("skeletonTargetThrowRecorded"));
    }

    /**
     * The row the fixed hook writes is the row the launcher counts.
     *
     * <p>This drives the real recorder rather than a hand-written line, so the
     * trace schema, the method signature the hook resolves from the
     * thread-local activation stack, and the exception class name are all the
     * real ones. It also pins the name match itself: the scanner's
     * {@code exceptionClass} has to be the runtime binary name, or the
     * launcher's predicate could never match whatever the run threw.</p>
     */
    @Test
    public void aRecordedTargetThrowIsCountedAndIsNotReportedAsAcceptance()
            throws Exception {
        WorkloadTarget target = fixtureTarget();
        Throwable thrown = new MixedTypeThreeThreadRpcWorkload
                .MixedTypeBugReachedException(2, 1);
        assertEquals(target.site().exceptionClass(),
                thrown.getClass().getName());

        Path traceDir = folder.newFolder("recorded").toPath();
        String previous = System.getProperty(TRACE_DIR_PROPERTY);
        try {
            recorder("clearInMemoryTrace");
            System.setProperty(TRACE_DIR_PROPERTY, traceDir.toString());
            // Exactly what the instrumented target does: a lite entry, then
            // the catch-all's recording exceptional exit.
            CausynthTraceRecorder.enterMethodLite(fixtureMethod(target),
                    new Object());
            CausynthTraceRecorder.throwActiveMethod(thrown);
            recorder("shutdown");

            TargetOutcome outcome = TargetOutcome.capture(traceDir,
                    target, "multitype-fixture", 0, null);

            assertEquals(TargetOutcome.Trace.CLOSED, outcome.trace());
            assertEquals(2L, outcome.targetMethodRecords());
            assertEquals(1L, outcome.targetThrowRecords());
            // Observed is still not accepted, and the record has to keep
            // saying so where a reader of the JSON will see it.
            assertTrue(gapsMention(outcome, "not an acceptance criterion"));
            assertTrue(gapsMention(outcome, "candidate.smt2"));
        } finally {
            restoreRecorder(previous);
        }
    }

    /**
     * With no throw row, the record reports a missing row rather than a normal
     * exit it never observed.
     */
    @Test
    public void anAbsentThrowRowIsReportedAsAMissingRowNotAsANormalExit()
            throws Exception {
        WorkloadTarget target = fixtureTarget();
        Path traceDir = folder.newFolder("entered-only").toPath();
        String previous = System.getProperty(TRACE_DIR_PROPERTY);
        try {
            recorder("clearInMemoryTrace");
            System.setProperty(TRACE_DIR_PROPERTY, traceDir.toString());
            CausynthTraceRecorder.enterMethodLite(fixtureMethod(target),
                    new Object());
            recorder("shutdown");

            TargetOutcome outcome = TargetOutcome.capture(traceDir,
                    target, "multitype-fixture", 0, null);

            assertEquals(1L, outcome.targetMethodRecords());
            assertEquals(0L, outcome.targetThrowRecords());
            assertTrue(gapsMention(outcome, "that is a missing row"));
            assertTrue(gapsMention(outcome, "skeletonTargetThrowRecorded"));
        } finally {
            restoreRecorder(previous);
        }
    }

    // --- fixture target -------------------------------------------------

    private static WorkloadTarget fixtureTarget() throws Exception {
        Path fixtures = Paths.get(MixedTypeThreeThreadRpcWorkload.class
                        .getProtectionDomain().getCodeSource().getLocation()
                        .toURI())
                .resolve("edu/uva/liftlab/graphchecker/fixtures");
        return WorkloadTarget.resolve("multitype",
                Collections.singletonList(fixtures));
    }

    private static String fixtureMethod(WorkloadTarget target) {
        return "<" + target.site().className() + ": void executeWorker()>";
    }

    // --- scene construction ---------------------------------------------

    private static SootClass scene() {
        G.reset();
        Scene.v().addClass(new SootClass("java.lang.Object", Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String", Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        SootClass recorder = new SootClass(RECORDER, Modifier.PUBLIC);
        recorder.addMethod(hook("enterMethodLite", LongType.v(),
                RefType.v("java.lang.String"), RefType.v("java.lang.Object")));
        recorder.addMethod(hook("exitActiveMethodLite", VoidType.v()));
        recorder.addMethod(hook("throwActiveMethodLite", VoidType.v(),
                RefType.v("java.lang.Throwable")));
        recorder.addMethod(hook("throwActiveMethod", VoidType.v(),
                RefType.v("java.lang.Throwable")));
        Scene.v().addClass(recorder);
        SootClass owner = new SootClass("example.KeyStore", Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        return owner;
    }

    private static SootMethod hook(String name, Type result,
                                   Type... parameters) {
        return new SootMethod(name, Arrays.asList(parameters), result,
                Modifier.PUBLIC | Modifier.STATIC);
    }

    /** The units of the built body an assertion needs to name. */
    private static final class SynchronizedTarget {
        private final SootMethod method;
        private final Unit entry;
        private final Unit targetThrow;
        private final Unit monitorRethrow;

        private SynchronizedTarget(SootMethod method, Unit entry,
                                   Unit targetThrow, Unit monitorRethrow) {
            this.method = method;
            this.entry = entry;
            this.targetThrow = targetThrow;
            this.monitorRethrow = monitorRethrow;
        }
    }

    /**
     * The HDFS target's shape: a throw inside {@code synchronized (this)},
     * with javac's monitor-release handler and its self-covering trap.
     */
    private static SynchronizedTarget synchronizedThrowingTarget(
            SootClass owner) {
        SootMethod method = new SootMethod("retrieveKey",
                Collections.<Type>singletonList(
                        RefType.v("java.lang.Throwable")),
                VoidType.v(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);

        Local self = Jimple.v().newLocal("self", RefType.v(owner));
        Local failure = Jimple.v().newLocal("failure",
                RefType.v("java.lang.Throwable"));
        Local lock = Jimple.v().newLocal("lock", RefType.v(owner));
        Local flag = Jimple.v().newLocal("flag", IntType.v());
        Local caught = Jimple.v().newLocal("caught",
                RefType.v("java.lang.Throwable"));
        body.getLocals().addAll(
                Arrays.asList(self, failure, lock, flag, caught));

        Unit release = Jimple.v().newExitMonitorStmt(lock);
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit done = Jimple.v().newReturnVoidStmt();
        Unit monitorRethrow = Jimple.v().newThrowStmt(caught);
        Unit targetThrow = Jimple.v().newThrowStmt(failure);
        Unit entry = Jimple.v().newAssignStmt(flag, IntConstant.v(1));

        body.getUnits().add(Jimple.v().newIdentityStmt(self,
                Jimple.v().newThisRef(RefType.v(owner))));
        body.getUnits().add(Jimple.v().newIdentityStmt(failure,
                Jimple.v().newParameterRef(
                        RefType.v("java.lang.Throwable"), 0)));
        body.getUnits().add(entry);
        body.getUnits().add(Jimple.v().newAssignStmt(lock, self));
        body.getUnits().add(Jimple.v().newEnterMonitorStmt(lock));
        Unit guard = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(flag, IntConstant.v(0)), release);
        body.getUnits().add(guard);
        body.getUnits().add(targetThrow);
        body.getUnits().add(release);
        body.getUnits().add(Jimple.v().newGotoStmt(done));
        body.getUnits().add(handler);
        body.getUnits().add(Jimple.v().newExitMonitorStmt(lock));
        body.getUnits().add(monitorRethrow);
        body.getUnits().add(done);

        SootClass throwable = Scene.v().getSootClass("java.lang.Throwable");
        // javac's two entries, in javac's order: the monitor body, then the
        // handler itself minus its final athrow.
        body.getTraps().add(Jimple.v().newTrap(throwable, guard, handler,
                handler));
        body.getTraps().add(Jimple.v().newTrap(throwable, handler,
                monitorRethrow, handler));
        return new SynchronizedTarget(method, entry, targetThrow,
                monitorRethrow);
    }

    private static SootMethod plainMethod(SootClass owner) {
        SootMethod method = new SootMethod("plain",
                Collections.<Type>emptyList(), VoidType.v(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local self = Jimple.v().newLocal("self", RefType.v(owner));
        Local value = Jimple.v().newLocal("value", IntType.v());
        body.getLocals().addAll(Arrays.asList(self, value));
        body.getUnits().add(Jimple.v().newIdentityStmt(self,
                Jimple.v().newThisRef(RefType.v(owner))));
        body.getUnits().add(Jimple.v().newAssignStmt(value, IntConstant.v(7)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    // --- reflective access to the package-private analysis artifact ------

    private static Class<?> staticProgramClass() throws Exception {
        return Class.forName(
                "edu.uva.liftlab.graphchecker.causynth.StaticProgram");
    }

    private static Object staticProgram() throws Exception {
        Constructor<?> constructor =
                staticProgramClass().getDeclaredConstructor();
        constructor.setAccessible(true);
        return constructor.newInstance();
    }

    @SuppressWarnings("unchecked")
    private static List<String> traceMethods(Object program) throws Exception {
        return (List<String>) field(program, "traceMethods");
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> regions(Object program)
            throws Exception {
        return (List<Map<String, Object>>) field(program, "regions");
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> targetResolved(Object program)
            throws Exception {
        return (Map<String, Object>) field(program, "targetResolved");
    }

    private static Object field(Object program, String name)
            throws Exception {
        Field declared = staticProgramClass().getDeclaredField(name);
        declared.setAccessible(true);
        return declared.get(program);
    }

    private static void instrumentSkeleton(Object program) throws Exception {
        Method method = CausynthPipeline.class.getDeclaredMethod(
                "instrumentRegionSkeletonTrace", staticProgramClass());
        method.setAccessible(true);
        method.invoke(new CausynthPipeline(null), program);
    }

    private static void recorder(String name) throws Exception {
        Method method = CausynthTraceRecorder.class.getDeclaredMethod(name);
        method.setAccessible(true);
        method.invoke(null);
    }

    private static void restoreRecorder(String previous) throws Exception {
        recorder("shutdown");
        recorder("clearInMemoryTrace");
        if (previous == null) {
            System.clearProperty(TRACE_DIR_PROPERTY);
        } else {
            System.setProperty(TRACE_DIR_PROPERTY, previous);
        }
    }

    // --- helpers ---------------------------------------------------------

    private static Map<String, Object> region(String root, String... methods) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("kind", "REGION_SKELETON");
        row.put("rootMethod", root);
        row.put("methods", Arrays.asList(methods));
        return row;
    }

    private static List<String> hookNames(Body body) {
        List<String> result = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()) {
                result.add(((Stmt) unit).getInvokeExpr().getMethodRef()
                        .name());
            }
        }
        return result;
    }

    private static int count(List<String> values, String expected) {
        int result = 0;
        for (String value : values) {
            if (expected.equals(value)) {
                result++;
            }
        }
        return result;
    }

    /** The units a trap protects: {@code [begin, end)} in chain order. */
    private static List<Unit> range(Body body, Trap trap) {
        List<Unit> covered = new ArrayList<>();
        boolean inside = false;
        for (Unit unit : body.getUnits()) {
            if (unit == trap.getBeginUnit()) {
                inside = true;
            }
            if (unit == trap.getEndUnit()) {
                inside = false;
            }
            if (inside) {
                covered.add(unit);
            }
        }
        return covered;
    }

    private static boolean gapsMention(TargetOutcome outcome,
                                       String fragment) {
        for (String gap : outcome.gaps()) {
            if (gap.contains(fragment)) {
                return true;
            }
        }
        return false;
    }
}
