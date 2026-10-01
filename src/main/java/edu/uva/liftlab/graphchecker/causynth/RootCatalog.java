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
import soot.jimple.DivExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.LongConstant;
import soot.jimple.MulExpr;
import soot.jimple.NegExpr;
import soot.jimple.ReturnStmt;
import edu.uva.liftlab.graphchecker.contract.Clock;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * The roots of the world a program reads, recognized by category from the
 * program text rather than listed per case (GreyGraph §3.1: the analysis
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
    /** The methods whose answer is being computed (a cycle reads them). */
    private final Set<String> open = new HashSet<String>();
    /** Whether the answer being computed read a cut: the depth bound or an
     *  open method's placeholder. */
    private boolean cut;
    /** Nanoseconds per tick of each clock found ({@link #tick}). */
    private final Map<String, Long> ticks = new HashMap<String, Long>();
    /** The JVM clock each wrapper found reads ({@link #source}). */
    private final Map<String, String> sources = new HashMap<String, String>();

    /**
     * The clock callees among the candidate graph's call returns, each with
     * the JVM clock it wraps and its tick in nanoseconds: 1,000,000 for
     * {@code currentTimeMillis}, 1 for {@code nanoTime}, and a wrapper's
     * scaled by its arithmetic ({@code Time.monotonicNow()} = {@code
     * nanoTime / 1000000}: {@code nanoTime} in ms).  A clock's window and
     * margin are a span of time, so each is stated in the clock's own tick;
     * which clock it is, the wrapper's body says ({@link Clock}).
     */
    static Map<String, Clock> clocks(
            Collection<Map<String, Object>> edges) {
        RootCatalog catalog = new RootCatalog();
        Map<String, Clock> found = new TreeMap<String, Clock>();
        for (Map<String, Object> edge : edges) {
            if (!"call_return".equals(MapFields.text(edge.get("kind")))) {
                continue;
            }
            String callee = MapFields.text(edge.get("invoke"));
            if (!callee.isEmpty() && catalog.clock(callee, 0)) {
                found.put(callee, Clock.of(catalog.tick(callee),
                        catalog.source(callee)));
            }
        }
        return found;
    }

    /** The JVM clock a found clock reads; {@code ""} for a wrapper whose
     *  value mixes both. */
    private String source(String signature) {
        if ("<java.lang.System: long nanoTime()>".equals(signature)) {
            return Clock.MONOTONIC;
        }
        if ("<java.lang.System: long currentTimeMillis()>".equals(signature)) {
            return Clock.WALL;
        }
        String known = sources.get(signature);
        return known == null ? "" : known;
    }

    /** A found clock's tick; a wrapper whose arithmetic scales it by no
     *  constant it can read ticks in milliseconds, as most clocks do. */
    private long tick(String signature) {
        if ("<java.lang.System: long nanoTime()>".equals(signature)) {
            return 1L;
        }
        if ("<java.lang.System: long currentTimeMillis()>".equals(signature)) {
            return MILLISECOND;
        }
        Long known = ticks.get(signature);
        return known == null ? MILLISECOND : known;
    }

    private static final long MILLISECOND = 1_000_000L;

    /** Whether a callee is a clock: its value is a root, whatever state
     *  its receiver holds. */
    boolean clock(String signature) {
        return clock(signature, 0);
    }

    private boolean clock(String signature, int depth) {
        if (JVM_CLOCKS.contains(signature)) return true;
        // Cycles and depth answer no, and a no that read one is not
        // remembered: asked from elsewhere, the method may be a clock.
        if (open.contains(signature) || depth >= MAX_DEPTH) {
            cut = true;
            return false;
        }
        Boolean known = clocks.get(signature);
        if (known != null) return known;
        boolean outer = cut;
        cut = false;
        open.add(signature);
        boolean answer = wrapsAClock(signature, depth);
        open.remove(signature);
        if (answer || !cut) clocks.put(signature, answer);
        cut |= outer;
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
        Long tick = null;
        String source = null;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof ReturnStmt)) continue;
            returns = true;
            Value returned = ((ReturnStmt) unit).getOp();
            if (!clockValue(returned, definitions, depth, true)) {
                return false;
            }
            Long scaled = tickOf(returned, definitions);
            tick = tick == null || tick.equals(scaled) ? scaled : null;
            source = either(source, sourceOf(returned, definitions));
        }
        if (returns && tick != null) ticks.put(signature, tick);
        if (returns) sources.put(signature, source == null ? "" : source);
        return returns;
    }

    /**
     * The JVM clock a clock value reads, read like {@link #tickOf}; {@code
     * ""} where it mixes two, null where it reads none.
     */
    private String sourceOf(Value value, Map<Local, Value> definitions) {
        if (value instanceof Local) {
            Value definition = definitions.get(value);
            return definition == null ? null
                    : sourceOf(definition, definitions);
        }
        if (value instanceof InvokeExpr) {
            String callee = ((InvokeExpr) value).getMethodRef().getSignature();
            return Boolean.TRUE.equals(clocks.get(callee))
                    || JVM_CLOCKS.contains(callee) ? source(callee) : null;
        }
        if (value instanceof CastExpr) {
            return sourceOf(((CastExpr) value).getOp(), definitions);
        }
        if (value instanceof NegExpr) {
            return sourceOf(((NegExpr) value).getOp(), definitions);
        }
        if (value instanceof BinopExpr) {
            BinopExpr binop = (BinopExpr) value;
            return either(sourceOf(binop.getOp1(), definitions),
                    sourceOf(binop.getOp2(), definitions));
        }
        return null;
    }

    /** One source of two: the one stated, or {@code ""} for two. */
    private static String either(String one, String other) {
        if (one == null) return other;
        if (other == null || one.equals(other)) return one;
        return "";
    }

    /**
     * The tick of a clock value under constant arithmetic, in nanoseconds:
     * a division by a constant multiplies it, a multiplication divides it,
     * an offset keeps it; null when no constant scale can be read.
     */
    private Long tickOf(Value value, Map<Local, Value> definitions) {
        if (value instanceof Local) {
            Value definition = definitions.get(value);
            return definition == null ? null : tickOf(definition, definitions);
        }
        if (value instanceof InvokeExpr) {
            String callee = ((InvokeExpr) value).getMethodRef().getSignature();
            return Boolean.TRUE.equals(clocks.get(callee))
                    || "<java.lang.System: long nanoTime()>".equals(callee)
                    || "<java.lang.System: long currentTimeMillis()>"
                    .equals(callee) ? tick(callee) : null;
        }
        if (value instanceof CastExpr) {
            return tickOf(((CastExpr) value).getOp(), definitions);
        }
        if (value instanceof NegExpr) {
            return tickOf(((NegExpr) value).getOp(), definitions);
        }
        if (value instanceof BinopExpr) {
            BinopExpr binop = (BinopExpr) value;
            Long left = binop.getOp1() instanceof Constant ? null
                    : tickOf(binop.getOp1(), definitions);
            Long right = binop.getOp2() instanceof Constant ? null
                    : tickOf(binop.getOp2(), definitions);
            long scale = constant(binop.getOp2());
            if (binop instanceof DivExpr) {
                return left == null || scale <= 0 ? null : left * scale;
            }
            if (binop instanceof MulExpr) {
                Long clock = left != null ? left : right;
                long factor = left != null ? scale : constant(binop.getOp1());
                return clock == null || factor <= 0 || clock % factor != 0
                        ? null : clock / factor;
            }
            return left != null ? left : right;
        }
        return null;
    }

    /** A positive integral constant's value, else 0. */
    private static long constant(Value value) {
        if (value instanceof LongConstant) return ((LongConstant) value).value;
        if (value instanceof IntConstant) return ((IntConstant) value).value;
        return 0L;
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
