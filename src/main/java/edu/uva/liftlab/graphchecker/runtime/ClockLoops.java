package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Whether a waiting thread's loop reads a CLOCK root: the scope map
 * ({@code static_scope_map.jsonl}, named by {@link
 * GuardedStoreSites#PATH_ENVIRONMENT}) declares a CLOCK root -- a {@code
 * DECLARED_SITE} of {@code inputKind} CLOCK -- in a method on the thread's
 * stack at the wait.  Such a loop waits for time only the clock brings (a
 * rule's expiry), so {@code ScheduleLog} never holds it for the order to
 * move.
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
    private static volatile Set<String> methods;

    private ClockLoops() {
    }

    /**
     * Whether a frame of {@code stack} is a method declaring a CLOCK root.
     * The map was read when the wait's event was computed ({@link #load}),
     * before the schedule's lock was taken.
     */
    static boolean reads(StackTraceElement[] stack) {
        load();
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

    /** Reads the scope map's CLOCK methods once; a volatile read after. */
    static void load() {
        if (methods != null) return;
        synchronized (ClockLoops.class) {
            if (methods == null) methods = read();
        }
    }

    /** The scope map's CLOCK methods; none, said once, when it is unread. */
    private static Set<String> read() {
        String named = Text.safe(System.getenv(
                GuardedStoreSites.PATH_ENVIRONMENT));
        if (named.isEmpty()) {
            EngineConsole.println("Causynth schedule: $"
                    + GuardedStoreSites.PATH_ENVIRONMENT + " names no scope"
                    + " map: no loop is known to read a CLOCK root, and"
                    + " every poll past its recorded count is held");
            return Collections.emptySet();
        }
        Set<String> found = new HashSet<String>();
        try {
            for (JsonObject row : ArtifactIO.readJsonl(Paths.get(named))) {
                String method = clockMethod(row);
                if (!method.isEmpty()) found.add(method);
            }
        } catch (IOException | RuntimeException unreadable) {
            EngineConsole.println("Causynth schedule: the scope map " + named
                    + " is unreadable (" + unreadable + "): no loop is known"
                    + " to read a CLOCK root");
            return Collections.emptySet();
        }
        return found;
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
        methods = null;
    }
}
