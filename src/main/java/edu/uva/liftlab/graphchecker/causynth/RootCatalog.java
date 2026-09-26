package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.InvokeExpr;
import soot.jimple.NegExpr;
import soot.jimple.ReturnStmt;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * The roots of the world a program reads, recognized by category from the
 * program text rather than listed per case (GreyGraph SS3.1: the analysis
 * derives its inputs).  A CLOCK is one of the JVM's clocks, or a method with
 * no parameter whose every returned value is a clock under constant
 * arithmetic -- {@code Time.now()}, {@code Time.monotonicNow()} ({@code
 * nanoTime / 1000000}), {@code Timer.now()} -- read off its body, library or
 * application alike.  A fault point is not listed here: the weave marks it
 * ({@link DoorWeave}).
 */
final class RootCatalog {
    private static final Set<String> JVM_CLOCKS = new LinkedHashSet<String>(
            java.util.Arrays.asList(
                    "<java.lang.System: long currentTimeMillis()>",
                    "<java.lang.System: long nanoTime()>"));
    /** How many wrappers deep a clock is followed. */
    private static final int MAX_DEPTH = 4;

    private final Map<String, Boolean> clocks = new HashMap<String, Boolean>();

    /** The clock callees among the candidate graph's call returns. */
    static Set<String> clockCallees(Collection<Map<String, Object>> edges) {
        RootCatalog catalog = new RootCatalog();
        Set<String> found = new TreeSet<String>();
        for (Map<String, Object> edge : edges) {
            if (!"call_return".equals(MapFields.text(edge.get("kind")))) {
                continue;
            }
            String callee = MapFields.text(edge.get("invoke"));
            if (!callee.isEmpty() && catalog.clock(callee, 0)) {
                found.add(callee);
            }
        }
        return found;
    }

    private boolean clock(String signature, int depth) {
        if (JVM_CLOCKS.contains(signature)) return true;
        Boolean known = clocks.get(signature);
        if (known != null) return known;
        // Cycles and depth answer no, and are not remembered as an answer.
        if (depth >= MAX_DEPTH) return false;
        clocks.put(signature, Boolean.FALSE);
        boolean answer = wrapsAClock(signature, depth);
        clocks.put(signature, answer);
        return answer;
    }

    /** Whether every value the method returns is a clock's. */
    private boolean wrapsAClock(String signature, int depth) {
        SootMethod method = CausynthStaticFacts.method(signature);
        if (method == null || method.getParameterCount() != 0) return false;
        String type = method.getReturnType().toString();
        if (!"long".equals(type) && !"int".equals(type)) return false;
        Body body = CausynthStaticFacts.activeBody(method);
        if (body == null) return false;
        Map<Local, Value> definitions = new HashMap<Local, Value>();
        for (Unit unit : body.getUnits()) {
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getLeftOp() instanceof Local) {
                Local local = (Local) ((AssignStmt) unit).getLeftOp();
                // A local defined twice is not a function of one clock.
                if (definitions.put(local,
                        ((AssignStmt) unit).getRightOp()) != null) {
                    return false;
                }
            }
        }
        boolean returns = false;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof ReturnStmt)) continue;
            returns = true;
            if (!clockValue(((ReturnStmt) unit).getOp(), definitions,
                    depth, true)) {
                return false;
            }
        }
        return returns;
    }

    /**
     * A clock's value under constant arithmetic; {@code needClock} because
     * a constant alone is no clock.
     */
    private boolean clockValue(Value value, Map<Local, Value> definitions,
                               int depth, boolean needClock) {
        if (value instanceof Constant) return !needClock;
        if (value instanceof Local) {
            Value definition = definitions.get(value);
            return definition != null
                    && clockValue(definition, definitions, depth, needClock);
        }
        if (value instanceof InvokeExpr) {
            return ((InvokeExpr) value).getArgCount() == 0
                    && clock(((InvokeExpr) value).getMethodRef()
                    .getSignature(), depth + 1);
        }
        if (value instanceof CastExpr) {
            return clockValue(((CastExpr) value).getOp(), definitions,
                    depth, needClock);
        }
        if (value instanceof NegExpr) {
            return clockValue(((NegExpr) value).getOp(), definitions,
                    depth, needClock);
        }
        if (value instanceof BinopExpr) {
            BinopExpr binop = (BinopExpr) value;
            boolean left = clockValue(binop.getOp1(), definitions, depth,
                    false);
            boolean right = clockValue(binop.getOp2(), definitions, depth,
                    false);
            if (!left || !right) return false;
            return !needClock || clockValue(binop.getOp1(), definitions,
                    depth, true) || clockValue(binop.getOp2(), definitions,
                    depth, true);
        }
        return false;
    }
}
