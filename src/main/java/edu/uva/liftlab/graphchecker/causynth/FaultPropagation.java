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

final class FaultPropagation {
    static final String THROWS = ".throws";

    private static FaultPropagation current;

    private final Scene scene;
    private final boolean latent;
    private final Map<String, MethodFaults> byMethod = new LinkedHashMap<>();

    static final class Raise {
        final Unit unit;
        final Set<String> kinds = new TreeSet<>();
        final Set<String> callees = new TreeSet<>();
        final Set<Local> markers = new LinkedHashSet<>();
        final Set<Raise> origins = new LinkedHashSet<>();
        Unit branch;
        Stmt latent;
        String frontier;

        private Raise(Unit unit) {
            this.unit = unit;
        }
    }

    private static final class MethodFaults {
        final Body body;
        final List<Raise> raises = new ArrayList<>();
        final Map<Unit, Set<Unit>> handlers = new IdentityHashMap<>();
        final Set<String> escaping = new TreeSet<>();
        final Set<Raise> escapes = new LinkedHashSet<>();
        final Map<Unit, List<Unit>> rethrows = new IdentityHashMap<>();

        MethodFaults(Body body) {
            this.body = body;
        }
    }

    private FaultPropagation(Scene scene, boolean latent) {
        this.scene = scene;
        this.latent = latent;
    }

    static synchronized FaultPropagation current() {
        if (current == null || current.scene != Scene.v()) {
            current = build(Scene.v(), false);
        }
        return current;
    }

    static FaultPropagation latent(
            java.util.function.Predicate<String> systemClass) {
        FaultPropagation model = new FaultPropagation(Scene.v(), true);
        model.systemClass = systemClass;
        return model.settled();
    }

    private java.util.function.Predicate<String> systemClass;

    List<Raise> decidedBy(String method, Unit unit) {
        List<Raise> found = new ArrayList<>();
        MethodFaults faults = byMethod.get(method);
        if (faults == null) return found;
        for (Raise raise : faults.raises) {
            if (raise.unit == unit || raise.branch == unit) found.add(raise);
        }
        return found;
    }

    Set<Unit> handlers(String method, Unit unit) {
        MethodFaults faults = byMethod.get(method);
        Set<Unit> found = faults == null ? null : faults.handlers.get(unit);
        return found == null ? Collections.<Unit>emptySet() : found;
    }

    Raise raise(String method, Unit unit) {
        MethodFaults faults = byMethod.get(method);
        if (faults == null) return null;
        for (Raise raise : faults.raises) {
            if (raise.unit == unit) return raise;
        }
        return null;
    }

    Collection<Raise> escapes(String method) {
        MethodFaults faults = byMethod.get(method);
        return faults == null ? Collections.<Raise>emptySet()
                : faults.escapes;
    }

    static String throwsCell(String method) {
        return method + THROWS;
    }


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

    static boolean checked(RefType type) {
        FastHierarchy hierarchy = Scene.v().getOrMakeFastHierarchy();
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

    private List<SootMethod> targets(InvokeExpr call) {
        SootMethod declared;
        try {
            declared = call.getMethod();
        } catch (RuntimeException unresolved) {
            return Collections.emptyList();
        }
        if (call instanceof StaticInvokeExpr
                || call instanceof SpecialInvokeExpr) {
            return analysed(Collections.singletonList(declared));
        }
        return dispatched.computeIfAbsent(declared, method -> {
            try {
                return analysed(Scene.v().getOrMakeFastHierarchy()
                        .resolveAbstractDispatch(method.getDeclaringClass(),
                                method));
            } catch (RuntimeException unresolved) {
                return Collections.emptyList();
            }
        });
    }

    private final Map<SootMethod, List<SootMethod>> dispatched =
            new java.util.HashMap<>();

    private List<SootMethod> analysed(Collection<SootMethod> candidates) {
        List<SootMethod> found = new ArrayList<>();
        for (SootMethod candidate : candidates) {
            if (byMethod.containsKey(candidate.getSignature())) {
                found.add(candidate);
            }
        }
        found.sort((a, b) -> a.getSignature().compareTo(b.getSignature()));
        return Collections.unmodifiableList(found);
    }

    private static boolean proxied(InvokeExpr call) {
        return call instanceof InterfaceInvokeExpr
                && !call.getMethodRef().getDeclaringClass()
                .isJavaLibraryClass();
    }

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

    static boolean covers(Body body, Trap trap, Unit unit) {
        for (Unit at = trap.getBeginUnit(); at != null
                && at != trap.getEndUnit();
             at = body.getUnits().getSuccOf(at)) {
            if (at == unit) return true;
        }
        return false;
    }

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
