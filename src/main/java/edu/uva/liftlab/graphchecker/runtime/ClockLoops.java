package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Whether a waiting thread's loop reads a CLOCK root: the scope map
 * ({@code static_scope_map.jsonl}) declares a CLOCK root -- a {@code
 * DECLARED_SITE} of {@code inputKind} CLOCK -- in a method on the thread's
 * stack at the wait.  Such a loop waits for time only the clock brings (a
 * rule's expiry), so {@code ScheduleLog} never holds it for the order to
 * move.
 *
 * <p>The methods are installed when the workload session opens, from the
 * rows {@link GuardedStoreSites#install} reads, before the workload runs.
 * Read at the first wait instead, the 3 MB map of an HDFS ad-hoc check held
 * a BPServiceActor's first tick 2-3 s on the concolic VM mid-run, and every
 * other thread's first wait behind it (hdfs ad-hoc FileChecksumHelper-496),
 * long enough for an IPC caller's one-second hand-off to its sender thread
 * to time out and the replay to leave the recorded order.</p>
 *
 * <p>PRECISION.  By method, along the stack.  A frame whose method reads a
 * clock root anywhere counts, inside the loop or not: the wait then runs as
 * it did before any poll was held, so this errs toward the old behavior.  A
 * loop that reads the root in a callee returned before the wait ({@code
 * while (!rule.isExpired()) sleep(..)}) is not seen, and polls once per move
 * of the order or per let-go.  Only the fatal slice's clocks are roots: a
 * loop over another clock (a {@code TimeOut} the workload bounds) is a poll
 * like any other.</p>
 */
final class ClockLoops {
    /** {@code class#method} of every method declaring a CLOCK root. */
    private static volatile Set<String> methods = Collections.emptySet();

    private ClockLoops() {
    }

    /** Whether a frame of {@code stack} is a method declaring a CLOCK root. */
    static boolean reads(StackTraceElement[] stack) {
        Set<String> declared = methods;
        if (declared.isEmpty()) return false;
        for (StackTraceElement frame : stack) {
            if (declared.contains(frame.getClassName() + "#"
                    + frame.getMethodName())) {
                return true;
            }
        }
        return false;
    }

    /** Installs the CLOCK methods of the session's scope map rows. */
    static void install(List<JsonObject> rows) {
        Set<String> found = new HashSet<String>();
        for (JsonObject row : rows) {
            String method = clockMethod(row);
            if (!method.isEmpty()) found.add(method);
        }
        methods = found;
    }

    /** {@code class#method} of a CLOCK root row's {@code vmSite}, or "". */
    static String clockMethod(JsonObject row) {
        if (!StaticScopeMap.SITE_KIND.equals(member(row, "kind"))
                || !StaticScopeMap.DECLARED_SITE.equals(member(row, "role"))
                || !StaticScopeMap.CLOCK_INPUT.equals(
                        member(row, "inputKind"))) {
            return "";
        }
        String site = member(row, "vmSite");
        int owner = site.indexOf('#');
        int descriptor = site.indexOf('(', owner + 1);
        if (owner <= 0 || descriptor <= owner + 1) return "";
        return site.substring(0, descriptor);
    }

    private static String member(JsonObject row, String name) {
        JsonElement value = row.get(name);
        return value == null || !value.isJsonPrimitive() ? ""
                : value.getAsString();
    }

    static void useForTests(Set<String> declared) {
        methods = declared;
    }

    static void resetForTests() {
        methods = Collections.emptySet();
    }
}
