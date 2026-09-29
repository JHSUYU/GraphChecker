package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * The transport doors' fault points, declared by {@code DOOR} rows of the
 * communication mapping and woven into the program before any analysis, so
 * every pass sees them as program text: one boolean marker per fault kind,
 * {@code if (Debug.makeSymbolicBoolean(name)) throw new Kind(..)}, in the
 * row's order.  The marker is the one the analysis already roots
 * ({@code EXPLICIT_SYMBOLIC_FAULT}); false is the recorded polarity.
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
    static final String KIND = "DOOR";
    private static final String GENERIC = "java.io.IOException";
    private static final String MARKER_CLASS =
            "edu.uva.liftlab.graphchecker.annotation.Debug";

    private DoorWeave() {
    }

    /** Weaves every declared door; refuses a door that names no site. */
    static void apply() throws IOException {
        for (JsonObject door : WireFlowCatalog.rowsOfKind(KIND)) {
            weave(door);
        }
    }

    private static void weave(JsonObject door) {
        String name = "FAULT:" + text(door, "transport") + ":"
                + text(door, "direction").toUpperCase();
        String signature = text(door, "method");
        SootMethod method = CausynthStaticFacts.method(signature);
        if (method == null || !method.isConcrete()) {
            throw new IllegalStateException("DOOR_METHOD_UNAVAILABLE: "
                    + name + " at " + signature);
        }
        Body body = method.retrieveActiveBody();
        boolean after = !text(door, "after").isEmpty();
        String callee = after ? text(door, "after") : text(door, "before");
        Stmt site = firstCall(body, callee);
        if (site == null) {
            throw new IllegalStateException("DOOR_SITE_UNAVAILABLE: " + name
                    + " calls no " + callee + " in " + signature);
        }
        List<String> kinds = new ArrayList<String>();
        for (JsonElement kind : door.getAsJsonArray("faults")) {
            kinds.add(kind.getAsString());
        }
        Unit next = after ? body.getUnits().getSuccOf(site) : site;
        List<Unit> units = new ArrayList<Unit>();
        if (!after) {
            // Every path that reached the site passes the door first; taken
            // before the markers' own branches to the site exist.
            Unit entry = Jimple.v().newNopStmt();
            site.redirectJumpsToThisTo(entry);
            units.add(entry);
        }
        // Built back to front: each marker's false arm falls to the next.
        List<Unit> faults = new ArrayList<Unit>();
        Collections.reverse(kinds);
        for (String kind : kinds) {
            List<Unit> fault = fault(body, name, kind, next);
            faults.addAll(0, fault);
            next = fault.get(0);
        }
        units.addAll(faults);
        Unit at = site;
        for (Unit unit : units) {
            if (after) {
                body.getUnits().insertAfter(unit, at);
                at = unit;
            } else {
                body.getUnits().insertBeforeNoRedirect(unit, site);
            }
        }
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

    private static String text(JsonObject row, String field) {
        JsonElement value = row.get(field);
        return value == null || value.isJsonNull() ? ""
                : value.getAsString().trim();
    }
}
