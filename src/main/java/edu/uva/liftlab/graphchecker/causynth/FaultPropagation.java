package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.FastHierarchy;
import soot.Local;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Where a door fault can go (SYMBOL-SCOPE §2.2): which units of the analysed
 * program raise one, which handler catches it, and what escapes a method.
 * The one exception model of the slice; {@link SiteControlDependence} adds
 * its handler edges to the CFG and {@link SeedBackwardStaticAnalyzer} follows
 * its origins.
 *
 * <p>A <em>raise</em> is a unit that can throw a door kind (a catalog door's
 * checked exception, never a {@code RuntimeException} or {@code Error}):
 * <ul>
 *   <li>a woven door throw ({@link DoorWeave#woven}) of a catalog
 *       transport;</li>
 *   <li>a throw of a checked exception on the failing arm of a demanded
 *       door's result ({@link DoorWeave#wovenResult}): {@code if
 *       (!f.renameTo(g)) throw new IOException(..)}, from its marker;</li>
 *   <li>a call whose targets (CHA over the analysed program) let one
 *       escape;</li>
 *   <li>a call of an interface method no analysed class implements (a
 *       proxy), declaring a checked exception a door kind is assignable to:
 *       it raises the kinds of the doors an analysed
 *       {@code InvocationHandler#invoke} reaches, calls through (JDK proxy
 *       semantics);</li>
 *   <li>a throw of what a handler caught (a {@code finally} or
 *       {@code synchronized} block's rethrow), with the kinds that handler
 *       caught.</li>
 * </ul>
 * A kind raised at a unit goes to the handler of the first trap covering the
 * unit whose type it is assignable to -- a handler edge -- else it escapes
 * the method.  The origins of a raise are the cells the fault comes from:
 * {@code <callee>.throws} of each target it escapes (of each door method a
 * proxy reaches), or the woven throw's marker local.</p>
 *
 * <p>The {@link #latent} model is the root demand's alone (SYMBOL-SCOPE
 * §4.6): it adds, where no door stands yet, every call of a demanded
 * door's anchor that throws (its kinds) and every checked throw on the
 * failing arm of a failing-result anchor's call, each a raise whose origin
 * is that call ({@link Raise#latent}), and every call into the system
 * outside the analysed program that declares a checked exception
 * ({@link Raise#frontier}): where a door could stand, and where growing the
 * scope could find one.  The slice never reads it.</p>
 */
final class FaultPropagation {
    static final String THROWS = ".throws";

    /** The model of the Scene it was built over. */
    private static FaultPropagation current;

    private final Scene scene;
    private final boolean latent;
    /** Per analysed method. */
    private final Map<String, MethodFaults> byMethod = new LinkedHashMap<>();

    /** One raise: the kinds it throws, and its origins. */
    static final class Raise {
        final Unit unit;
        final Set<String> kinds = new TreeSet<>();
        /** {@code <method>.throws} cells, in name order. */
        final Set<String> callees = new TreeSet<>();
        /** The marker locals of the woven throws it throws (itself, or what
         *  a handler rethrows). */
        final Set<Local> markers = new LinkedHashSet<>();
        /** The raises of this method a rethrow throws again. */
        final Set<Raise> origins = new LinkedHashSet<>();
        /** The branch whose arm an in-method throw stands on: a woven
         *  throw's marker branch, a failing result's test; null for a
         *  call, which is its own fault branch. */
        Unit branch;
        /** The latent model's: the call of a demanded door's anchor whose
         *  fault this raise throws, where no door stands yet; else null. */
        Stmt latent;
        /** The latent model's: a call into the system outside the analysed
         *  program declaring a checked exception, else null. */
        String frontier;

        private Raise(Unit unit) {
            this.unit = unit;
        }
    }

    private static final class MethodFaults {
        final Body body;
        final List<Raise> raises = new ArrayList<>();
        /** Raise unit -> the handlers its kinds go to. */
        final Map<Unit, Set<Unit>> handlers = new IdentityHashMap<>();
        /** The kinds that escape the method. */
        final Set<String> escaping = new TreeSet<>();
        /** The raises something escapes from. */
        final Set<Raise> escapes = new LinkedHashSet<>();
        /** Handler -> its rethrows. */
        final Map<Unit, List<Unit>> rethrows = new IdentityHashMap<>();

        MethodFaults(Body body) {
            this.body = body;
        }
    }

    private FaultPropagation(Scene scene, boolean latent) {
        this.scene = scene;
        this.latent = latent;
    }

    /** The model of the analysed program, built at first use over each
     *  Scene. */
    static synchronized FaultPropagation current() {
        if (current == null || current.scene != Scene.v()) {
            current = build(Scene.v(), false);
        }
        return current;
    }

    /**
     * The woven program's model with every latent fault added: the calls
     * where a demanded door could stand and the calls into the system
     * outside the analysed program ({@code systemClass}), for the root
     * demand to choose from.
     */
    static FaultPropagation latent(
            java.util.function.Predicate<String> systemClass) {
        FaultPropagation model = new FaultPropagation(Scene.v(), true);
        model.systemClass = systemClass;
        return model.settled();
    }

    private java.util.function.Predicate<String> systemClass;

    /** The raises whose fault branch is {@code unit}: a call raising
     *  itself, or the in-method throws standing on its arm. */
    List<Raise> decidedBy(String method, Unit unit) {
        List<Raise> found = new ArrayList<>();
        MethodFaults faults = byMethod.get(method);
        if (faults == null) return found;
        for (Raise raise : faults.raises) {
            if (raise.unit == unit || raise.branch == unit) found.add(raise);
        }
        return found;
    }

    /** The handlers a raise unit's door kinds go to; none for any other
     *  unit. */
    Set<Unit> handlers(String method, Unit unit) {
        MethodFaults faults = byMethod.get(method);
        Set<Unit> found = faults == null ? null : faults.handlers.get(unit);
        return found == null ? Collections.<Unit>emptySet() : found;
    }

    /** The raise at {@code unit}, or null. */
    Raise raise(String method, Unit unit) {
        MethodFaults faults = byMethod.get(method);
        if (faults == null) return null;
        for (Raise raise : faults.raises) {
            if (raise.unit == unit) return raise;
        }
        return null;
    }

    /** The raises a door kind escapes {@code method} from. */
    Collection<Raise> escapes(String method) {
        MethodFaults faults = byMethod.get(method);
        return faults == null ? Collections.<Raise>emptySet()
                : faults.escapes;
    }

    /** The {@code .throws} cell of a method. */
    static String throwsCell(String method) {
        return method + THROWS;
    }

    // ---- the model -----------------------------------------------------

    private static FaultPropagation build(Scene scene, boolean latent) {
        return new FaultPropagation(scene, latent).settled();
    }

    private FaultPropagation settled() {
        FaultPropagation model = this;
        Scene scene = this.scene;
        Set<String> transports = LibraryCatalog.transports();
        List<SootMethod> invokes = new ArrayList<>();
        for (SootClass owner : new ArrayList<>(scene.getApplicationClasses())) {
            for (SootMethod method : new ArrayList<>(owner.getMethods())) {
                Body body = CausynthStaticFacts.activeBody(method);
                if (body == null) continue;
                model.byMethod.put(method.getSignature(),
                        new MethodFaults(body));
                if ("invoke".equals(method.getName())
                        && method.getParameterCount() == 3) {
                    invokes.add(method);
                }
            }
        }
        // The raises every body states by itself: its woven throws, the
        // checked throws on a woven result's failing arm, and in the latent
        // model the calls where a door could stand.
        boolean raised = false;
        for (Map.Entry<String, MethodFaults> entry
                : model.byMethod.entrySet()) {
            MethodFaults faults = entry.getValue();
            for (Unit unit : new ArrayList<>(faults.body.getUnits())) {
                raised |= model.ownRaises(faults, unit, transports);
            }
        }
        if (!raised) return model;
        FastHierarchy hierarchy = scene.getOrMakeFastHierarchy();
        List<SootMethod> handlers = new ArrayList<>();
        for (SootMethod invoke : invokes) {
            if (implementsHandler(invoke.getDeclaringClass(), hierarchy)) {
                handlers.add(invoke);
            }
        }
        Map<String, Set<String>> proxyReach = model.proxyReach(handlers);
        // Calls and rethrows, to a fixed point: escapes only grow.
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Map.Entry<String, MethodFaults> entry
                    : model.byMethod.entrySet()) {
                changed |= model.settle(entry.getValue(), proxyReach,
                        hierarchy);
            }
        }
        return model;
    }

    /** The raises {@code unit} states by itself; whether there are any. */
    private boolean ownRaises(MethodFaults faults, Unit unit,
                              Set<String> transports) {
        DoorWeave.Fault woven = DoorWeave.woven(faults.body, unit);
        if (woven != null) {
            if (!transports.contains(woven.name.split(":", -1)[1])) {
                return false;
            }
            Raise raise = raiseAt(faults, unit);
            raise.markers.add(woven.marker);
            raise.kinds.add(woven.kind);
            raise.branch = woven.branch;
            return true;
        }
        DoorWeave.Fault result = DoorWeave.wovenResult(faults.body, unit);
        if (result != null) {
            return failingArm(faults, result.call,
                    raise -> raise.markers.add(result.marker));
        }
        if (!latent || !((Stmt) unit).containsInvokeExpr()
                || DoorWeave.doorSite(unit)
                || !DoorWeave.analysed(faults.body.getMethod()
                .getDeclaringClass())) {
            return false;
        }
        Stmt call = (Stmt) unit;
        LibraryCatalog.Door door = LibraryCatalog.demandedDoor(
                call.getInvokeExpr().getMethodRef().getSignature());
        if (door == null) return frontier(faults, call);
        if (door.result != LibraryCatalog.Result.NONE) {
            return call instanceof AssignStmt && failingArm(faults,
                    (AssignStmt) call, raise -> raise.latent = call);
        }
        Raise raise = raiseAt(faults, unit);
        raise.kinds.addAll(door.faults);
        raise.latent = call;
        return true;
    }

    /**
     * A call into the system outside the analysed program declaring a
     * checked exception: a raise of the latent model naming its callee, so
     * the demand can grow the scope where a door could stand.
     */
    private boolean frontier(MethodFaults faults, Stmt call) {
        SootMethod callee;
        try {
            callee = call.getInvokeExpr().getMethod();
        } catch (RuntimeException unresolved) {
            return false;
        }
        String owner = callee.getDeclaringClass().getName();
        if (byMethod.containsKey(callee.getSignature())
                || systemClass == null || !systemClass.test(owner)
                || callee.getExceptionsUnsafe() == null) {
            return false;
        }
        Set<String> kinds = new TreeSet<>();
        for (SootClass declared : callee.getExceptionsUnsafe()) {
            if (checked(declared.getType())) {
                kinds.add(declared.getName());
            }
        }
        if (kinds.isEmpty()) return false;
        Raise raise = raiseAt(faults, call);
        raise.kinds.addAll(kinds);
        raise.frontier = callee.getSignature();
        return true;
    }

    /**
     * The checked throws on the failing arm of {@code call}'s result: the
     * first test of its result local that the call falls through to
     * ({@code if r == 0}, {@code if r == null}), and the throws its failing
     * arm reaches that its other arm does not, each a raise on that test.
     */
    private boolean failingArm(MethodFaults faults, AssignStmt call,
                               java.util.function.Consumer<Raise> origin) {
        if (!(call.getLeftOp() instanceof Local)) return false;
        Local result = (Local) call.getLeftOp();
        soot.util.Chain<Unit> units = faults.body.getUnits();
        Unit at = units.getSuccOf(call);
        while (at != null && !(at instanceof soot.jimple.IfStmt)) {
            if (!at.fallsThrough() || at.branches()
                    || at.getDefBoxes().stream().anyMatch(
                    box -> box.getValue() == result)) {
                return false;
            }
            at = units.getSuccOf(at);
        }
        if (at == null) return false;
        soot.jimple.IfStmt test = (soot.jimple.IfStmt) at;
        Value condition = test.getCondition();
        if (!(condition instanceof soot.jimple.EqExpr
                || condition instanceof soot.jimple.NeExpr)
                || ((soot.jimple.BinopExpr) condition).getOp1() != result) {
            return false;
        }
        // r == 0 / r == null jumps on failure; r != .. falls through on it.
        Unit failing = condition instanceof soot.jimple.EqExpr
                ? test.getTarget() : units.getSuccOf(test);
        Unit holding = condition instanceof soot.jimple.EqExpr
                ? units.getSuccOf(test) : test.getTarget();
        BriefUnitGraph cfg = new BriefUnitGraph(faults.body);
        Set<Unit> other = reach(cfg, holding, test);
        boolean raised = false;
        for (Unit unit : reach(cfg, failing, test)) {
            if (!(unit instanceof ThrowStmt) || other.contains(unit)) continue;
            Type thrown = ((ThrowStmt) unit).getOp().getType();
            if (!(thrown instanceof RefType)
                    || !checked((RefType) thrown)) {
                continue;
            }
            Raise raise = raiseAt(faults, unit);
            raise.kinds.add(((RefType) thrown).getClassName());
            raise.branch = test;
            origin.accept(raise);
            raised = true;
        }
        return raised;
    }

    /** The units {@code start} reaches, never through {@code barrier}. */
    private static Set<Unit> reach(BriefUnitGraph cfg, Unit start,
                                   Unit barrier) {
        Set<Unit> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<Unit> work = new ArrayDeque<>();
        if (start != null) work.add(start);
        while (!work.isEmpty()) {
            Unit unit = work.removeFirst();
            if (unit == barrier || !seen.add(unit)) continue;
            work.addAll(cfg.getSuccsOf(unit));
        }
        return seen;
    }

    /** A checked exception: an Exception that is no RuntimeException. */
    private boolean checked(RefType type) {
        FastHierarchy hierarchy = scene.getOrMakeFastHierarchy();
        SootClass exception = Scene.v().getSootClassUnsafe(
                "java.lang.Exception", false);
        SootClass runtime = Scene.v().getSootClassUnsafe(
                "java.lang.RuntimeException", false);
        return exception != null && hierarchy.canStoreType(type,
                exception.getType()) && (runtime == null
                || !hierarchy.canStoreType(type, runtime.getType()));
    }

    private static boolean implementsHandler(SootClass owner,
                                             FastHierarchy hierarchy) {
        SootClass handler = Scene.v().getSootClassUnsafe(
                "java.lang.reflect.InvocationHandler", false);
        return handler != null && !owner.isInterface()
                && hierarchy.canStoreType(owner.getType(), handler.getType());
    }

    /**
     * Door method -> the kinds it throws, for the door methods an analysed
     * {@code InvocationHandler#invoke} reaches by calls (CHA over the
     * analysed program), whether or not the handler lets the fault out: a
     * proxy call is where the fault the handler meets comes back.
     */
    private Map<String, Set<String>> proxyReach(List<SootMethod> handlers) {
        Map<String, Set<String>> reached = new LinkedHashMap<>();
        Deque<String> work = new ArrayDeque<>();
        Set<String> seen = new LinkedHashSet<>();
        for (SootMethod handler : handlers) work.add(handler.getSignature());
        while (!work.isEmpty()) {
            String method = work.removeFirst();
            MethodFaults faults = byMethod.get(method);
            if (!seen.add(method) || faults == null) continue;
            for (Raise raise : faults.raises) {
                if (raise.markers.isEmpty()) continue;
                reached.computeIfAbsent(method, m -> new TreeSet<>())
                        .addAll(raise.kinds);
            }
            for (Unit unit : faults.body.getUnits()) {
                if (!((Stmt) unit).containsInvokeExpr()) continue;
                for (SootMethod target
                        : targets(((Stmt) unit).getInvokeExpr())) {
                    work.add(target.getSignature());
                }
            }
        }
        return reached;
    }

    /** One pass over a method's calls and handlers; whether anything
     *  grew. */
    private boolean settle(MethodFaults faults,
                           Map<String, Set<String>> proxyReach,
                           FastHierarchy hierarchy) {
        boolean changed = false;
        for (Unit unit : faults.body.getUnits()) {
            if (!((Stmt) unit).containsInvokeExpr()) continue;
            InvokeExpr call = ((Stmt) unit).getInvokeExpr();
            Raise raise = null;
            List<SootMethod> targets = targets(call);
            for (SootMethod target : targets) {
                MethodFaults callee = byMethod.get(target.getSignature());
                if (callee == null || callee.escaping.isEmpty()) continue;
                if (raise == null) raise = raiseAt(faults, unit);
                changed |= raise.callees.add(throwsCell(
                        target.getSignature()));
                changed |= raise.kinds.addAll(callee.escaping);
            }
            if (targets.isEmpty() && proxied(call)) {
                for (Map.Entry<String, Set<String>> door
                        : proxyReach.entrySet()) {
                    for (String kind : door.getValue()) {
                        if (!declares(call, kind, hierarchy)) continue;
                        if (raise == null) raise = raiseAt(faults, unit);
                        changed |= raise.callees.add(throwsCell(door.getKey()));
                        changed |= raise.kinds.add(kind);
                    }
                }
            }
        }
        // Each raise's kinds to a handler or out; a handler's rethrows raise
        // what it caught, until nothing moves.
        boolean moved = true;
        while (moved) {
            moved = false;
            for (Raise raise : new ArrayList<>(faults.raises)) {
                for (String kind : new ArrayList<>(raise.kinds)) {
                    Unit handler = handler(faults.body, raise.unit, kind,
                            hierarchy);
                    if (handler == null) {
                        boolean grew = faults.escapes.add(raise);
                        grew |= faults.escaping.add(kind);
                        moved |= grew;
                        continue;
                    }
                    moved |= faults.handlers.computeIfAbsent(raise.unit,
                            u -> new LinkedHashSet<>()).add(handler);
                    for (Unit rethrow : faults.rethrows.computeIfAbsent(
                            handler, h -> rethrows(faults.body, h))) {
                        Raise again = raiseAt(faults, rethrow);
                        moved |= again.kinds.add(kind);
                        moved |= again.callees.addAll(raise.callees);
                        moved |= again.markers.addAll(raise.markers);
                        moved |= again.origins.add(raise);
                    }
                }
            }
            changed |= moved;
        }
        return changed;
    }

    private static Raise raiseAt(MethodFaults faults, Unit unit) {
        for (Raise raise : faults.raises) {
            if (raise.unit == unit) return raise;
        }
        Raise raise = new Raise(unit);
        faults.raises.add(raise);
        return raise;
    }

    /** The methods one call may run in the analysed program; none when the
     *  hierarchy cannot resolve it. */
    private List<SootMethod> targets(InvokeExpr call) {
        List<SootMethod> found = new ArrayList<>();
        try {
            SootMethod declared = call.getMethod();
            Collection<SootMethod> candidates = call instanceof StaticInvokeExpr
                    || call instanceof SpecialInvokeExpr
                    ? Collections.singletonList(declared)
                    : Scene.v().getOrMakeFastHierarchy()
                    .resolveAbstractDispatch(declared.getDeclaringClass(),
                            declared);
            for (SootMethod candidate : candidates) {
                if (byMethod.containsKey(candidate.getSignature())) {
                    found.add(candidate);
                }
            }
        } catch (RuntimeException unresolved) {
            return Collections.emptyList();
        }
        found.sort((a, b) -> a.getSignature().compareTo(b.getSignature()));
        return found;
    }

    /** A call of an application interface's method: with no analysed
     *  target, a proxy's (a JDK interface's is not a remote protocol). */
    private static boolean proxied(InvokeExpr call) {
        return call instanceof InterfaceInvokeExpr
                && !call.getMethodRef().getDeclaringClass()
                .isJavaLibraryClass();
    }

    /** Whether the called method declares a checked exception {@code kind}
     *  is assignable to. */
    private static boolean declares(InvokeExpr call, String kind,
                                    FastHierarchy hierarchy) {
        SootClass thrown = Scene.v().getSootClassUnsafe(kind, false);
        SootMethod method;
        try {
            method = call.getMethod();
        } catch (RuntimeException unresolved) {
            return false;
        }
        if (thrown == null || method.getExceptionsUnsafe() == null) {
            return false;
        }
        for (SootClass declared : method.getExceptionsUnsafe()) {
            if (hierarchy.canStoreType(thrown.getType(),
                    declared.getType())) {
                return true;
            }
        }
        return false;
    }

    /** The handler of the first trap covering {@code unit} that catches
     *  {@code kind}, or null. */
    private static Unit handler(Body body, Unit unit, String kind,
                                FastHierarchy hierarchy) {
        SootClass thrown = Scene.v().getSootClassUnsafe(kind, false);
        if (thrown == null) return null;
        RefType type = thrown.getType();
        for (Trap trap : body.getTraps()) {
            if (!covers(body, trap, unit)) continue;
            if (hierarchy.canStoreType(type, trap.getException().getType())) {
                return trap.getHandlerUnit();
            }
        }
        return null;
    }

    private static boolean covers(Body body, Trap trap, Unit unit) {
        for (Unit at = trap.getBeginUnit(); at != null
                && at != trap.getEndUnit();
             at = body.getUnits().getSuccOf(at)) {
            if (at == unit) return true;
        }
        return false;
    }

    /** The throws of what the handler caught, or a copy of it, before it is
     *  redefined. */
    private static List<Unit> rethrows(Body body, Unit handler) {
        List<Unit> found = new ArrayList<>();
        if (!(handler instanceof IdentityStmt) || !(((IdentityStmt) handler)
                .getRightOp() instanceof CaughtExceptionRef)) {
            return found;
        }
        BriefUnitGraph cfg = new BriefUnitGraph(body);
        Set<Value> caught = new LinkedHashSet<>();
        caught.add(((IdentityStmt) handler).getLeftOp());
        Deque<Unit> work = new ArrayDeque<>(cfg.getSuccsOf(handler));
        Set<Unit> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        while (!work.isEmpty()) {
            Unit unit = work.removeFirst();
            if (!seen.add(unit)) continue;
            if (unit instanceof ThrowStmt) {
                if (caught.contains(((ThrowStmt) unit).getOp())) {
                    found.add(unit);
                }
                continue;
            }
            if (unit instanceof AssignStmt) {
                Value left = ((AssignStmt) unit).getLeftOp();
                Value right = ((AssignStmt) unit).getRightOp();
                Value copied = right instanceof CastExpr
                        ? ((CastExpr) right).getOp() : right;
                if (left instanceof Local) {
                    if (caught.contains(copied)) {
                        caught.add(left);
                    } else {
                        caught.remove(left);
                    }
                }
            }
            work.addAll(cfg.getSuccsOf(unit));
        }
        return found;
    }
}
