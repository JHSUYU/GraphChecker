package edu.uva.liftlab.graphchecker.causynth;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.Body;
import soot.BooleanType;
import soot.Local;
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
import soot.jimple.EqExpr;
import soot.jimple.IfStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;
import soot.tagkit.Tag;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The transport doors' fault points, the {@code DOOR} rows of the engine's
 * library catalog ({@link LibraryCatalog}), woven into the program before any
 * analysis, so every pass sees them as program text: one boolean marker per
 * fault kind, {@code if (Debug.makeSymbolicBoolean(name)) throw new
 * Kind(..)}, in the row's order, at the first call of the row's anchor.  The
 * marker is the one the analysis already roots ({@code
 * EXPLICIT_SYMBOLIC_FAULT}); false is the recorded polarity.
 *
 * <p>A door applies where its class family is analysed: an application
 * class of this run that is not there for its lineage alone (no pass analyses
 * or weaves such a class's text).  There every row whose method and anchor
 * resolve is woven, and a door method none of whose rows resolves is refused
 * ({@code DOOR_METHOD_UNAVAILABLE}): the library moved under the catalog.
 * A door at every call of its anchor ({@link LibraryCatalog.Door#atCalls})
 * is woven in each analysed method that makes the call, at its first; a
 * program that makes none has none.  A demanded door ({@code sites}
 * DEMANDED, a local file operation) is woven only at the calls the root
 * demand chose ({@link DemandedDoors}), before the call: its markers throw
 * its kinds, or, for a failing result, {@code r = marker ? failing :
 * call(..)}, so a failed operation never happens.</p>
 *
 * <p>A kind is an ENVIRONMENT failure the transport can raise and a caller
 * distinguishes (e.g. {@code RetryPolicies} fails over on
 * {@code ConnectTimeoutException}/{@code EOFException} but retries a generic
 * {@code IOException} only when idempotent).  A semantic server exception is
 * never a kind: it must come from the causal chain.  {@code IOException} keeps
 * the bare name {@code FAULT:<TRANSPORT>:<DIRECTION>}; any other kind appends
 * its simple class name.</p>
 */
final class DoorWeave {
    private static final Logger LOG = LoggerFactory.getLogger(DoorWeave.class);
    private static final String GENERIC = "java.io.IOException";
    private static final String MARKER_CLASS =
            "edu.uva.liftlab.graphchecker.annotation.Debug";

    private DoorWeave() {
    }

    /** Weaves every catalog door of an analysed family, and every door at
     *  calls into the analysed methods making them. */
    static void apply() {
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

    /** Weaves one demanded door at its chosen call; a site no catalog row
     *  or no analysed call answers is refused by name. */
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

    /** The call of {@code callee} that is the {@code ordinal}-th (from 0) in
     *  body order, or null. */
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

    /** A call's ordinal among its body's calls of the same callee. */
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

    /** Whether a demanded door already stands at this call. */
    static boolean doorSite(Unit call) {
        return call.hasTag(DOOR_SITE.getName());
    }

    /**
     * A failing result's door: {@code m = marker; if m == 0 goto call; r =
     * failing; goto next; call: r = callee(..); next: ..}, every jump to
     * the call taken to its marker first.
     */
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
        units.add(jimple.newAssignStmt(call.getLeftOp(),
                door.result == LibraryCatalog.Result.FALSE
                        ? IntConstant.v(0) : NullConstant.v()));
        units.add(jimple.newGotoStmt(next));
        for (Unit unit : units) {
            unit.addTag(WOVEN);
            body.getUnits().insertBeforeNoRedirect(unit, call);
        }
    }

    /** Whether a class is this run's analysed program. */
    static boolean analysed(SootClass type) {
        return type != null && !type.isPhantom() && type.isApplicationClass()
                && !LineageScope.lineageOnly(type.getName());
    }

    /** The concrete methods of the analysed classes that call
     *  {@code anchor}, in class and then method order. */
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

    /** Weaves one door into its method; "" when woven, else why not. */
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

    /** Weaves one door at the first call of its anchor in {@code method},
     *  which makes one. */
    private static void weave(LibraryCatalog.Door door, SootMethod method) {
        weave(door, method, call(method.retrieveActiveBody(), door.anchor,
                0));
    }

    /** Weaves one door's markers at {@code site}, a call of its anchor. */
    private static void weave(LibraryCatalog.Door door, SootMethod method,
                              Stmt site) {
        Body body = method.retrieveActiveBody();
        Unit next = door.after ? body.getUnits().getSuccOf(site) : site;
        List<Unit> units = new ArrayList<Unit>();
        if (!door.after) {
            // Every path that reached the site passes the door first; taken
            // before the markers' own branches to the site exist.
            Unit entry = Jimple.v().newNopStmt();
            site.redirectJumpsToThisTo(entry);
            units.add(entry);
        }
        // Built back to front: each marker's false arm falls to the next.
        List<Unit> faults = new ArrayList<Unit>();
        List<String> kinds = new ArrayList<>(door.faults);
        Collections.reverse(kinds);
        for (String kind : kinds) {
            List<Unit> fault = fault(body, door.name(), kind, next);
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

    /** Whether the weave inserted {@code unit}: the engine's text, never
     *  counted among the program's own (a declared throw's ordinal among
     *  its method's constructions of its type). */
    static boolean isWoven(Unit unit) {
        return unit.hasTag(WOVEN.getName());
    }

    private static final Tag WOVEN = tag("CausynthDoorWoven");
    /** The program's call a demanded door stands at. */
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

    /** One woven fault: the marker local its branch tests, that branch,
     *  the marker's name and the kind thrown -- or, for a failing result,
     *  no kind, and the call whose result local it sets. */
    static final class Fault {
        final Local marker;
        final IfStmt branch;
        final String name;
        final String kind;
        /** A failing result's call ({@code r = callee(..)}), else null. */
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

    /**
     * The failing-result door standing at {@code unit}, or null: the shape
     * {@link #weaveResult} weaves -- {@code m = makeSymbolicBoolean(FAULT:..);
     * if m == 0 goto call; r = failing; goto next; call: r = callee(..)} --
     * read back off the unit chain from the call.
     */
    static Fault wovenResult(Body body, Unit unit) {
        if (!(unit instanceof AssignStmt) || !doorSite(unit)) return null;
        soot.util.Chain<Unit> units = body.getUnits();
        Unit jump = units.getPredOf(unit);
        Unit failing = jump == null ? null : units.getPredOf(jump);
        Unit test = failing == null ? null : units.getPredOf(failing);
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

    /**
     * The woven fault {@code unit} throws, or null: the shape {@link #fault}
     * weaves -- {@code m = makeSymbolicBoolean(FAULT:..); if m == 0 goto ..;
     * e = new Kind; e.<init>(..); throw e} -- read back off the unit chain.
     */
    static Fault woven(Body body, Unit unit) {
        if (!(unit instanceof ThrowStmt)) return null;
        soot.util.Chain<Unit> units = body.getUnits();
        Unit init = units.getPredOf(unit);
        Unit allocation = init == null ? null : units.getPredOf(init);
        Unit test = allocation == null ? null : units.getPredOf(allocation);
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

    /** {@code m = makeSymbolicBoolean("FAULT:..")} at {@code call}, tested
     *  by {@code test} ({@code if m == 0}), as a fault; else null. */
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

    /** {@code if (marker) throw new kind("..")}, falling to {@code next}. */
    private static List<Unit> fault(Body body, String name, String kind,
                                    Unit next) {
        String marker = GENERIC.equals(kind) ? name
                : name + ":" + kind.substring(kind.lastIndexOf('.') + 1);
        SootMethodRef makeSymbolic = makeSymbolic();
        // (String) where the kind declares it, else (): ZooKeeper's
        // KeeperException.ConnectionLossException has only the latter.
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
        units.add(jimple.newAssignStmt(failure,
                jimple.newNewExpr(RefType.v(kind))));
        units.add(jimple.newInvokeStmt(parameters.isEmpty()
                ? jimple.newSpecialInvokeExpr(failure, init)
                : jimple.newSpecialInvokeExpr(failure, init,
                StringConstant.v("symbolic " + marker))));
        units.add(jimple.newThrowStmt(failure));
        return units;
    }

    private static SootMethodRef makeSymbolic() {
        return Scene.v().makeMethodRef(
                CausynthPipeline.phantomClass(MARKER_CLASS),
                "makeSymbolicBoolean",
                Collections.singletonList(RefType.v("java.lang.String")),
                BooleanType.v(), true);
    }

    /** Whether the kind declares a {@code (String)} constructor. */
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
