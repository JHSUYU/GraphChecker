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
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
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
 * program that makes none has none.</p>
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
        LOG.info("Library doors woven: {}", woven);
    }

    /** Whether a class is this run's analysed program. */
    private static boolean analysed(SootClass type) {
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
                if (body != null && firstCall(body, anchor) != null) {
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
        if (firstCall(method.retrieveActiveBody(), door.anchor) == null) {
            return door.method + " calls no " + door.anchor;
        }
        weave(door, method);
        return "";
    }

    /** Weaves one door at the first call of its anchor in {@code method},
     *  which makes one. */
    private static void weave(LibraryCatalog.Door door, SootMethod method) {
        Body body = method.retrieveActiveBody();
        Stmt site = firstCall(body, door.anchor);
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

    private static final Tag WOVEN = new Tag() {
        @Override
        public String getName() {
            return "CausynthDoorWoven";
        }

        @Override
        public byte[] getValue() {
            return new byte[0];
        }
    };

    /** One woven fault's throw: the marker local its branch tests, the
     *  marker's name and the kind thrown. */
    static final class Fault {
        final Local marker;
        final String name;
        final String kind;

        private Fault(Local marker, String name, String kind) {
            this.marker = marker;
            this.name = name;
            this.kind = kind;
        }
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
                || !(test instanceof IfStmt)
                || !(((IfStmt) test).getCondition() instanceof EqExpr)
                || !(call instanceof AssignStmt)
                || !(((AssignStmt) call).getRightOp()
                instanceof StaticInvokeExpr)) {
            return null;
        }
        StaticInvokeExpr marker = (StaticInvokeExpr)
                ((AssignStmt) call).getRightOp();
        Value tested = ((EqExpr) ((IfStmt) test).getCondition()).getOp1();
        if (!MARKER_CLASS.equals(marker.getMethodRef().getDeclaringClass()
                .getName())
                || marker.getArgCount() != 1
                || !(marker.getArg(0) instanceof StringConstant)
                || ((AssignStmt) call).getLeftOp() != tested
                || !(tested instanceof Local)) {
            return null;
        }
        String name = ((StringConstant) marker.getArg(0)).value;
        return name.startsWith("FAULT:") ? new Fault((Local) tested, name,
                ((NewExpr) ((AssignStmt) allocation).getRightOp())
                        .getBaseType().getClassName()) : null;
    }

    /** {@code if (marker) throw new kind("..")}, falling to {@code next}. */
    private static List<Unit> fault(Body body, String name, String kind,
                                    Unit next) {
        String marker = GENERIC.equals(kind) ? name
                : name + ":" + kind.substring(kind.lastIndexOf('.') + 1);
        SootMethodRef makeSymbolic = Scene.v().makeMethodRef(
                CausynthPipeline.phantomClass(MARKER_CLASS),
                "makeSymbolicBoolean",
                Collections.singletonList(RefType.v("java.lang.String")),
                BooleanType.v(), true);
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

    private static Stmt firstCall(Body body, String callee) {
        for (Unit unit : body.getUnits()) {
            Stmt stmt = (Stmt) unit;
            if (stmt.containsInvokeExpr() && callee.equals(
                    stmt.getInvokeExpr().getMethodRef().getSignature())) {
                return stmt;
            }
        }
        return null;
    }
}
