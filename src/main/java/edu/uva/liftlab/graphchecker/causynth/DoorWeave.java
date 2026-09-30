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
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
 * or weaves such a class's text).  Of the rows of one transport direction in
 * one family, those whose method and anchor resolve are woven; none resolving
 * is refused ({@code DOOR_METHOD_UNAVAILABLE}): the library moved under the
 * catalog.</p>
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

    /** Weaves every catalog door of an analysed family. */
    static void apply() {
        // "<name> in <family>" -> why its rows were not woven; empty once one
        // of them was.
        Map<String, List<String>> missed =
                new LinkedHashMap<String, List<String>>();
        List<String> woven = new ArrayList<String>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (!analysed(door.family())) continue;
            String group = door.name() + " in " + door.family();
            String miss = weave(door);
            if (miss.isEmpty()) {
                missed.put(group, Collections.<String>emptyList());
                woven.add(door.name() + " at " + door.method);
            } else if (!missed.containsKey(group)
                    || !missed.get(group).isEmpty()) {
                missed.computeIfAbsent(group,
                        at -> new ArrayList<String>()).add(miss);
            }
        }
        for (Map.Entry<String, List<String>> group : missed.entrySet()) {
            if (!group.getValue().isEmpty()) {
                throw new IllegalStateException("DOOR_METHOD_UNAVAILABLE: "
                        + group.getKey() + ": " + group.getValue());
            }
        }
        LOG.info("Library doors woven: {}", woven);
    }

    /** Whether a class family is this run's analysed program. */
    private static boolean analysed(String family) {
        SootClass type = Scene.v().getSootClassUnsafe(family, false);
        return type != null && !type.isPhantom() && type.isApplicationClass()
                && !LineageScope.lineageOnly(family);
    }

    /** Weaves one door; "" when woven, else why not. */
    private static String weave(LibraryCatalog.Door door) {
        SootMethod method = CausynthStaticFacts.method(door.method);
        if (method == null || !method.isConcrete()
                || !method.getDeclaringClass().isApplicationClass()) {
            return "no method " + door.method;
        }
        Body body = method.retrieveActiveBody();
        Stmt site = firstCall(body, door.anchor);
        if (site == null) {
            return door.method + " calls no " + door.anchor;
        }
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
        List<String> kinds = new ArrayList<String>(door.faults);
        Collections.reverse(kinds);
        for (String kind : kinds) {
            List<Unit> fault = fault(body, door.name(), kind, next);
            faults.addAll(0, fault);
            next = fault.get(0);
        }
        units.addAll(faults);
        Unit at = site;
        for (Unit unit : units) {
            if (door.after) {
                body.getUnits().insertAfter(unit, at);
                at = unit;
            } else {
                body.getUnits().insertBeforeNoRedirect(unit, site);
            }
        }
        return "";
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
