package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.FastHierarchy;
import soot.Local;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
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
 */
final class FaultPropagation {
    static final String THROWS = ".throws";

    /** The model of the Scene it was built over. */
    private static FaultPropagation current;

    private final Scene scene;
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

    private FaultPropagation(Scene scene) {
        this.scene = scene;
    }

    /** The model of the analysed program, built at first use over each
     *  Scene. */
    static synchronized FaultPropagation current() {
        if (current == null || current.scene != Scene.v()) {
            current = build(Scene.v());
        }
        return current;
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

    private static FaultPropagation build(Scene scene) {
        FaultPropagation model = new FaultPropagation(scene);
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
        // The raises every body states by itself: its woven throws.
        boolean raised = false;
        for (MethodFaults faults : model.byMethod.values()) {
            for (Unit unit : faults.body.getUnits()) {
                DoorWeave.Fault woven = DoorWeave.woven(faults.body, unit);
                String transport = woven == null ? null
                        : woven.name.split(":", -1)[1];
                if (transport == null || !transports.contains(transport)) {
                    continue;
                }
                Raise raise = raiseAt(faults, unit);
                raise.markers.add(woven.marker);
                raise.kinds.add(woven.kind);
                raised = true;
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
