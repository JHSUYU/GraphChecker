package edu.uva.liftlab.graphchecker.causynth;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import edu.uva.liftlab.graphchecker.plan.WorkStartSites;
import soot.Body;
import soot.BooleanType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.EqExpr;
import soot.jimple.IfStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;
import soot.tagkit.Tag;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

final class DoorWeave {
    private static final Logger LOG = LoggerFactory.getLogger(DoorWeave.class);
    private static final String GENERIC = "java.io.IOException";
    private static final Pattern SIGNATURE =
            Pattern.compile("<([^:\\s]+): (.+)>");
    private static final String MARKER_CLASS =
            "edu.uva.liftlab.graphchecker.annotation.Debug";

    private DoorWeave() {
    }

    static void apply() {
        UNPLACED.clear();
        Map<String, List<String>> missed = new LinkedHashMap<>();
        Set<String> doorMethods = new LinkedHashSet<>();
        List<String> woven = new ArrayList<>();
        List<SootClass> analysed = new ArrayList<>();
        for (SootClass type : Scene.v().getApplicationClasses()) {
            if (analysed(type)) analysed.add(type);
        }
        analysed.sort((a, b) -> a.getName().compareTo(b.getName()));
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (door.demanded) continue;
            if (door.atCalls()) {
                for (SootMethod caller : callers(analysed, door.anchor)) {
                    weave(door, caller);
                    woven.add(door.name() + " at " + caller.getSignature());
                }
                continue;
            }
            if (!analysed(Scene.v().getSootClassUnsafe(door.family(),
                    false))) {
                continue;
            }
            String miss = weave(door);
            if (miss.isEmpty()) {
                doorMethods.add(door.doorMethod());
                woven.add(door.name() + " at " + door.method);
                woven.addAll(weaveMoved(door, analysed));
            } else {
                missed.computeIfAbsent(door.doorMethod(),
                        method -> new ArrayList<>()).add(miss);
            }
        }
        missed.keySet().removeAll(doorMethods);
        if (!missed.isEmpty()) {
            throw new IllegalStateException(
                    "DOOR_METHOD_UNAVAILABLE: " + missed);
        }
        for (DemandedDoors.Site site : DemandedDoors.woven()) {
            weave(site);
            woven.add("FAULT:" + site.callee + " at " + site.key());
        }
        LOG.info("Library doors woven: {}", woven);
    }

    private static void weave(DemandedDoors.Site site) {
        LibraryCatalog.Door door = LibraryCatalog.demandedDoor(site.callee);
        SootMethod method = CausynthStaticFacts.method(site.caller);
        Body body = method == null || !method.isConcrete()
                || !analysed(method.getDeclaringClass()) ? null
                : CausynthStaticFacts.activeBody(method);
        Stmt call = body == null ? null : call(body, site.callee,
                site.ordinal);
        if (door == null || call == null || doorSite(call)
                || door.result != LibraryCatalog.Result.NONE
                && !(call instanceof AssignStmt)) {
            throw new IllegalStateException("DEMANDED_DOOR_UNAVAILABLE: "
                    + site.key() + (door == null ? " is no demanded door"
                    : " names no call of an analysed method that can "
                    + "carry it"));
        }
        if (door.result == LibraryCatalog.Result.NONE) {
            weave(door, method, call);
        } else {
            weaveResult(door, body, (AssignStmt) call);
        }
        call.addTag(DOOR_SITE);
    }

    static Stmt call(Body body, String callee, int ordinal) {
        int seen = 0;
        for (Unit unit : body.getUnits()) {
            Stmt stmt = (Stmt) unit;
            if (stmt.containsInvokeExpr() && callee.equals(
                    stmt.getInvokeExpr().getMethodRef().getSignature())
                    && seen++ == ordinal) {
                return stmt;
            }
        }
        return null;
    }

    static int ordinal(Body body, Stmt call) {
        String callee = call.getInvokeExpr().getMethodRef().getSignature();
        int seen = 0;
        for (Unit unit : body.getUnits()) {
            if (unit == call) return seen;
            Stmt stmt = (Stmt) unit;
            if (stmt.containsInvokeExpr() && callee.equals(
                    stmt.getInvokeExpr().getMethodRef().getSignature())) {
                seen++;
            }
        }
        throw new IllegalArgumentException(call + " is not in its body");
    }

    static boolean doorSite(Unit call) {
        return call.hasTag(DOOR_SITE.getName());
    }

    private static void weaveResult(LibraryCatalog.Door door, Body body,
                                    AssignStmt call) {
        Jimple jimple = Jimple.v();
        Unit next = body.getUnits().getSuccOf(call);
        Local chosen = CausynthPipeline.newTraceLocal(body, BooleanType.v(),
                "$fault");
        Unit entry = jimple.newNopStmt();
        call.redirectJumpsToThisTo(entry);
        List<Unit> units = new ArrayList<Unit>();
        units.add(entry);
        units.add(jimple.newAssignStmt(chosen, jimple.newStaticInvokeExpr(
                makeSymbolic(), StringConstant.v(door.name()))));
        units.add(jimple.newIfStmt(jimple.newEqExpr(chosen,
                IntConstant.v(0)), call));
        units.addAll(guard(body, door, null, door.name(), call, call));
        units.add(jimple.newAssignStmt(call.getLeftOp(),
                door.result == LibraryCatalog.Result.NULL ? NullConstant.v()
                        : call.getLeftOp().getType() instanceof LongType
                        ? LongConstant.v(0L) : IntConstant.v(0)));
        units.add(jimple.newGotoStmt(next));
        for (Unit unit : units) {
            unit.addTag(WOVEN);
            body.getUnits().insertBeforeNoRedirect(unit, call);
        }
    }

    static boolean analysed(SootClass type) {
        return type != null && !type.isPhantom() && type.isApplicationClass()
                && !LineageScope.lineageOnly(type.getName());
    }

    private static List<SootMethod> callers(List<SootClass> analysed,
                                            String anchor) {
        List<SootMethod> found = new ArrayList<>();
        for (SootClass type : analysed) {
            List<SootMethod> methods = new ArrayList<>(type.getMethods());
            methods.sort((a, b) -> a.getSignature().compareTo(
                    b.getSignature()));
            for (SootMethod method : methods) {
                Body body = CausynthStaticFacts.activeBody(method);
                if (body != null && call(body, anchor, 0) != null) {
                    found.add(method);
                }
            }
        }
        return found;
    }

    private static final List<Map<String, Object>> UNPLACED =
            new ArrayList<>();

    static List<Map<String, Object>> unplaced() {
        return Collections.unmodifiableList(UNPLACED);
    }

    static Map<SootMethod, Set<Stmt>> moved(LibraryCatalog.Door door,
                                           List<SootClass> analysed) {
        Map<SootMethod, Set<Stmt>> found = new LinkedHashMap<>();
        if (door.relocated == null || door.relocated.equals(door.method)) {
            return found;
        }
        Matcher target = SIGNATURE.matcher(door.relocated);
        if (!target.matches()) {
            throw new IllegalStateException("DOOR_METHOD_UNAVAILABLE: "
                    + door.relocated + " is no method signature");
        }
        SootMethod moved = CausynthStaticFacts.method(door.relocated);
        Body own = moved == null ? null : CausynthStaticFacts.activeBody(moved);
        if (own != null && call(own, door.method, 0) != null) return found;
        SootMethod hook = CausynthStaticFacts.method(door.method);
        for (SootClass type : analysed) {
            boolean family = type.getName().equals(door.family())
                    || type.getName().startsWith(door.family() + "$");
            List<SootMethod> methods = new ArrayList<>(type.getMethods());
            methods.sort((a, b) -> a.getSignature().compareTo(
                    b.getSignature()));
            for (SootMethod method : methods) {
                if (method.equals(hook)) continue;
                Body body = CausynthStaticFacts.activeBody(method);
                if (body == null) continue;
                UnitGraph graph = null;
                for (Unit unit : body.getUnits()) {
                    Stmt stmt = (Stmt) unit;
                    if (!stmt.containsInvokeExpr() || !calls(
                            stmt.getInvokeExpr().getMethodRef(),
                            target.group(1), target.group(2))) {
                        continue;
                    }
                    if (!family) {
                        unplaced(door, method, body, stmt, "it is made outside"
                                + " the class family of its hook, "
                                + door.family());
                        continue;
                    }
                    if (graph == null) graph = new BriefUnitGraph(body);
                    Set<Stmt> reached = hookCallsReached(graph, stmt,
                            door.anchor, target.group(1), target.group(2),
                            door.after);
                    if (reached.size() == 1) {
                        found.computeIfAbsent(method,
                                ignored -> new LinkedHashSet<>())
                                .addAll(reached);
                    } else {
                        unplaced(door, method, body, stmt, reached.isEmpty()
                                ? "no call of its hook " + door.anchor
                                        + (door.after ? " follows" : " precedes")
                                        + " it in its method: its"
                                        + " door is the one its caller's"
                                        + " hook call carries, if any"
                                : "it reaches " + reached.size() + " calls"
                                        + " of its hook " + door.anchor);
                    }
                }
            }
        }
        return found;
    }

    static List<String> weaveMoved(LibraryCatalog.Door door,
                                   List<SootClass> analysed) {
        List<String> woven = new ArrayList<>();
        for (Map.Entry<SootMethod, Set<Stmt>> hooked
                : moved(door, analysed).entrySet()) {
            for (Stmt call : hooked.getValue()) {
                weave(door, hooked.getKey(), call);
            }
            woven.add(door.name() + " at " + hooked.getKey().getSignature());
        }
        return woven;
    }

    private static Set<Stmt> hookCallsReached(UnitGraph graph, Stmt call,
                                              String anchor, String owner,
                                              String subSignature,
                                              boolean after) {
        Set<Stmt> reached = new LinkedHashSet<>();
        Set<Unit> seen = new java.util.HashSet<>();
        java.util.ArrayDeque<Unit> pending = new java.util.ArrayDeque<>(
                after ? graph.getSuccsOf(call) : graph.getPredsOf(call));
        while (!pending.isEmpty()) {
            Stmt next = (Stmt) pending.poll();
            if (!seen.add(next)) continue;
            if (next.containsInvokeExpr()) {
                SootMethodRef ref = next.getInvokeExpr().getMethodRef();
                if (anchor.equals(ref.getSignature())) {
                    reached.add(next);
                    continue;
                }
                if (calls(ref, owner, subSignature)) continue;
            }
            pending.addAll(after ? graph.getSuccsOf(next)
                    : graph.getPredsOf(next));
        }
        return reached;
    }

    private static void unplaced(LibraryCatalog.Door door, SootMethod method,
                                 Body body, Stmt call, String why) {
        String site = method.getSignature() + "#u" + unitIndex(body, call);
        UNPLACED.add(CommunicationCatalogPlanner.gap(GapKind.DOOR_UNPLACED,
                GapClass.DIAGNOSTIC, why, method.getSignature(), site,
                "the direct call of " + door.relocated + " at " + site
                        + " carries no " + door.name() + " door: " + why));
    }

    private static int unitIndex(Body body, Unit unit) {
        int index = 0;
        for (Unit next : body.getUnits()) {
            if (next == unit) return index;
            index++;
        }
        return -1;
    }

    private static boolean calls(SootMethodRef ref, String owner,
                                 String subSignature) {
        if (!ref.getSubSignature().getString().equals(subSignature)) {
            return false;
        }
        for (SootClass type = ref.getDeclaringClass(); type != null;
             type = type.hasSuperclass() ? type.getSuperclass() : null) {
            if (type.getName().equals(owner)) return true;
            if (type.isPhantom()) return false;
        }
        return false;
    }

    private static String weave(LibraryCatalog.Door door) {
        SootMethod method = CausynthStaticFacts.method(door.method);
        if (method == null || !method.isConcrete()
                || !method.getDeclaringClass().isApplicationClass()) {
            return "no method " + door.method;
        }
        if (call(method.retrieveActiveBody(), door.anchor, 0) == null) {
            return door.method + " calls no " + door.anchor;
        }
        weave(door, method);
        return "";
    }

    private static void weave(LibraryCatalog.Door door, SootMethod method) {
        weave(door, method, call(method.retrieveActiveBody(), door.anchor,
                0));
    }

    private static void weave(LibraryCatalog.Door door, SootMethod method,
                              Stmt site) {
        Body body = method.retrieveActiveBody();
        Unit next = door.after ? body.getUnits().getSuccOf(site) : site;
        List<Unit> units = new ArrayList<Unit>();
        if (!door.after) {
            Unit entry = Jimple.v().newNopStmt();
            site.redirectJumpsToThisTo(entry);
            units.add(entry);
        }
        List<Unit> faults = new ArrayList<Unit>();
        List<String> kinds = new ArrayList<>(door.faults);
        Collections.reverse(kinds);
        for (String kind : kinds) {
            List<Unit> fault = fault(body, door, kind, next, site);
            faults.addAll(0, fault);
            next = fault.get(0);
        }
        units.addAll(faults);
        Unit at = site;
        for (Unit unit : units) {
            unit.addTag(WOVEN);
            if (door.after) {
                body.getUnits().insertAfter(unit, at);
                at = unit;
            } else {
                body.getUnits().insertBeforeNoRedirect(unit, site);
            }
        }
    }

    static boolean isWoven(Unit unit) {
        return unit.hasTag(WOVEN.getName());
    }

    private static final Tag WOVEN = tag("CausynthDoorWoven");
    private static final Tag DOOR_SITE = tag("CausynthDoorSite");

    private static Tag tag(final String name) {
        return new Tag() {
            @Override
            public String getName() {
                return name;
            }

            @Override
            public byte[] getValue() {
                return new byte[0];
            }
        };
    }

    static final class Fault {
        final Local marker;
        final IfStmt branch;
        final String name;
        final String kind;
        final AssignStmt call;

        private Fault(Local marker, IfStmt branch, String name, String kind,
                      AssignStmt call) {
            this.marker = marker;
            this.branch = branch;
            this.name = name;
            this.kind = kind;
            this.call = call;
        }
    }

    static Fault wovenResult(Body body, Unit unit) {
        if (!(unit instanceof AssignStmt) || !doorSite(unit)) return null;
        soot.util.Chain<Unit> units = body.getUnits();
        Unit jump = units.getPredOf(unit);
        Unit failing = jump == null ? null : units.getPredOf(jump);
        Unit test = failing == null ? null
                : markerTest(units, units.getPredOf(failing));
        Unit call = test == null ? null : units.getPredOf(test);
        if (!(jump instanceof GotoStmt) || !(failing instanceof AssignStmt)
                || !(test instanceof IfStmt)
                || ((IfStmt) test).getTarget() != unit) {
            return null;
        }
        Fault marker = marker(call, (IfStmt) test, null, null);
        return marker == null ? null : new Fault(marker.marker,
                marker.branch, marker.name, null, (AssignStmt) unit);
    }

    static Fault woven(Body body, Unit unit) {
        if (!(unit instanceof ThrowStmt)) return null;
        soot.util.Chain<Unit> units = body.getUnits();
        Unit init = units.getPredOf(unit);
        Unit allocation = init == null ? null : units.getPredOf(init);
        Unit test = allocation == null ? null
                : markerTest(units, units.getPredOf(allocation));
        Unit call = test == null ? null : units.getPredOf(test);
        if (!(init instanceof InvokeStmt)
                || !(((InvokeStmt) init).getInvokeExpr()
                instanceof SpecialInvokeExpr)
                || !(allocation instanceof AssignStmt)
                || !(((AssignStmt) allocation).getRightOp()
                instanceof NewExpr)
                || ((AssignStmt) allocation).getLeftOp()
                != ((ThrowStmt) unit).getOp()
                || !(test instanceof IfStmt)) {
            return null;
        }
        return marker(call, (IfStmt) test, ((NewExpr) ((AssignStmt)
                allocation).getRightOp()).getBaseType().getClassName(), null);
    }

    private static Fault marker(Unit call, IfStmt test, String kind,
                                AssignStmt result) {
        if (!(test.getCondition() instanceof EqExpr)
                || !(call instanceof AssignStmt)
                || !(((AssignStmt) call).getRightOp()
                instanceof StaticInvokeExpr)) {
            return null;
        }
        StaticInvokeExpr marker = (StaticInvokeExpr)
                ((AssignStmt) call).getRightOp();
        Value tested = ((EqExpr) test.getCondition()).getOp1();
        if (!MARKER_CLASS.equals(marker.getMethodRef().getDeclaringClass()
                .getName())
                || marker.getArgCount() != 1
                || !(marker.getArg(0) instanceof StringConstant)
                || ((AssignStmt) call).getLeftOp() != tested
                || !(tested instanceof Local)) {
            return null;
        }
        String name = ((StringConstant) marker.getArg(0)).value;
        return name.startsWith("FAULT:") ? new Fault((Local) tested, test,
                name, kind, result) : null;
    }

    private static List<Unit> fault(Body body, LibraryCatalog.Door door,
                                    String kind, Unit next, Stmt site) {
        String name = door.name();
        String marker = GENERIC.equals(kind) ? name
                : name + ":" + kind.substring(kind.lastIndexOf('.') + 1);
        SootMethodRef makeSymbolic = makeSymbolic();
        List<Type> parameters = messageConstructor(kind)
                ? Collections.<Type>singletonList(
                RefType.v("java.lang.String"))
                : Collections.<Type>emptyList();
        SootMethodRef init = Scene.v().makeMethodRef(
                CausynthPipeline.phantomClass(kind), "<init>", parameters,
                VoidType.v(), false);
        Local chosen = CausynthPipeline.newTraceLocal(body, BooleanType.v(),
                "$fault");
        Local failure = CausynthPipeline.newTraceLocal(body, RefType.v(kind),
                "$fault");
        Jimple jimple = Jimple.v();
        List<Unit> units = new ArrayList<Unit>();
        units.add(jimple.newAssignStmt(chosen, jimple.newStaticInvokeExpr(
                makeSymbolic, StringConstant.v(marker))));
        units.add(jimple.newIfStmt(jimple.newEqExpr(chosen,
                IntConstant.v(0)), next));
        units.addAll(guard(body, door, kind, marker, site, next));
        units.add(jimple.newAssignStmt(failure,
                jimple.newNewExpr(RefType.v(kind))));
        units.add(jimple.newInvokeStmt(parameters.isEmpty()
                ? jimple.newSpecialInvokeExpr(failure, init)
                : jimple.newSpecialInvokeExpr(failure, init,
                StringConstant.v("symbolic " + marker))));
        units.add(jimple.newThrowStmt(failure));
        return units;
    }

    private static List<Unit> guard(Body body, LibraryCatalog.Door door,
                                     String kind, String marker, Stmt call,
                                     Unit to) {
        if (LibraryCatalog.SESSION_EXPIRED.equals(kind)) {
            return expiry(body, marker, call, to);
        }
        if (!LibraryCatalog.TIMED_WAIT.equals(door.transport)) {
            return Collections.emptyList();
        }
        InvokeExpr invoke = call.getInvokeExpr();
        Value receiver = invoke instanceof InstanceInvokeExpr
                ? ((InstanceInvokeExpr) invoke).getBase() : NullConstant.v();
        Value permits = invoke.getArgCount() > 0
                && invoke.getMethodRef().getParameterType(0)
                instanceof IntType ? invoke.getArg(0) : IntConstant.v(1);
        Local taken = CausynthPipeline.newTraceLocal(body, BooleanType.v(),
                "$timesOut");
        Jimple jimple = Jimple.v();
        List<Unit> units = new ArrayList<Unit>();
        units.add(jimple.newAssignStmt(taken, jimple.newStaticInvokeExpr(
                timesOut(), receiver, permits, StringConstant.v(marker))));
        units.add(jimple.newIfStmt(jimple.newEqExpr(taken, IntConstant.v(0)),
                to));
        return units;
    }

    private static List<Unit> expiry(Body body, String marker, Stmt call,
                                     Unit to) {
        InvokeExpr invoke = call.containsInvokeExpr() ? call.getInvokeExpr()
                : null;
        Value owner = !body.getMethod().isStatic() ? body.getThisLocal()
                : invoke instanceof InstanceInvokeExpr
                ? ((InstanceInvokeExpr) invoke).getBase() : NullConstant.v();
        Local taken = CausynthPipeline.newTraceLocal(body, BooleanType.v(),
                "$expires");
        Jimple jimple = Jimple.v();
        List<Unit> units = new ArrayList<Unit>();
        units.add(jimple.newAssignStmt(taken, jimple.newStaticInvokeExpr(
                Scene.v().makeMethodRef(CausynthPipeline.phantomClass(
                        SESSIONS_CLASS), GUARD_EXPIRES, Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")), BooleanType.v(),
                        true), owner, StringConstant.v(marker))));
        units.add(jimple.newIfStmt(jimple.newEqExpr(taken, IntConstant.v(0)),
                to));
        return units;
    }

    static final String SESSIONS_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.Sessions";
    private static final String GUARD_TIMES_OUT = "timesOut";
    private static final String GUARD_EXPIRES = "expires";
    private static final List<String> GUARDS = Arrays.asList(GUARD_TIMES_OUT,
            GUARD_EXPIRES);

    private static SootMethodRef timesOut() {
        return Scene.v().makeMethodRef(CausynthPipeline.phantomClass(
                WorkStartSites.TIMED_WAITS_CLASS), GUARD_TIMES_OUT, Arrays.asList(
                RefType.v("java.lang.Object"), IntType.v(),
                RefType.v("java.lang.String")), BooleanType.v(), true);
    }

    private static Unit markerTest(soot.util.Chain<Unit> units, Unit test) {
        Unit assigned = test == null ? null : units.getPredOf(test);
        if (!(test instanceof IfStmt) || !(assigned instanceof AssignStmt)
                || !(((AssignStmt) assigned).getRightOp()
                instanceof StaticInvokeExpr)
                || !GUARDS.contains(((StaticInvokeExpr) ((AssignStmt)
                assigned).getRightOp()).getMethodRef().getName())) {
            return test;
        }
        return units.getPredOf(assigned);
    }

    private static SootMethodRef makeSymbolic() {
        return Scene.v().makeMethodRef(
                CausynthPipeline.phantomClass(MARKER_CLASS),
                "makeSymbolicBoolean",
                Collections.singletonList(RefType.v("java.lang.String")),
                BooleanType.v(), true);
    }

    private static boolean messageConstructor(String kind) {
        SootClass type = Scene.v().forceResolve(kind, SootClass.SIGNATURES);
        if (type.isPhantom()) {
            throw new IllegalStateException("DOOR_FAULT_KIND_UNAVAILABLE: "
                    + kind);
        }
        return type.declaresMethod("<init>", Collections.<Type>singletonList(
                RefType.v("java.lang.String")));
    }
}
