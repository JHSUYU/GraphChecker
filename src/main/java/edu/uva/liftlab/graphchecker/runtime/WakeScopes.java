package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayDeque;
import java.util.Deque;

/**
 * One turn of a service loop (heartbeat, monitor, key updater) is one root
 * scope, so daemon traffic is not all addressed {@code Lost}.
 *
 * <p>The WAKE of a timed wait opens the turn (role {@code WAKE}, api = the
 * loop's site, k = the k-th turn of that loop on that node in the window);
 * the next wait closes it.  Only on threads attributed to a node.  A turn
 * scope that is not innermost at the wait is left standing and closes the
 * next time it is.</p>
 */
final class WakeScopes {
    private static final ThreadLocal<Deque<Long>> OPEN =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<Long>();
                }
            };

    private WakeScopes() {
    }

    /** The loop waits: the turn it was running is over. */
    static void waiting() {
        ScheduleLog.mute();
        try {
            Deque<Long> open = OPEN.get();
            while (!open.isEmpty()
                    && RuntimeTraceContext.endWakeIfInnermost(open.peek())) {
                open.pop();
            }
        } catch (Throwable ignored) {
            // A hook never turns a wait into a failure.
        } finally {
            ScheduleLog.unmute();
        }
    }

    /** The wait returned: the loop's next turn begins. */
    static void woke(String site) {
        if (!RecordingWindow.opened()) return;
        ScheduleLog.mute();
        try {
            long token = RuntimeTraceContext.beginWake(api(site));
            if (token > 0L) OPEN.get().push(token);
        } catch (Throwable ignored) {
        } finally {
            ScheduleLog.unmute();
        }
    }

    /** {@code Class.method} of the wait: two waits of one loop are one loop. */
    static String api(String site) {
        String value = Text.safe(site);
        int open = value.indexOf('<');
        int colon = value.indexOf(':', open + 1);
        int paren = value.indexOf('(', colon + 1);
        if (open < 0 || colon < 0 || paren < 0) return value;
        String owner = value.substring(open + 1, colon).trim();
        int dot = owner.lastIndexOf('.');
        String simple = dot < 0 ? owner : owner.substring(dot + 1);
        String head = value.substring(colon + 1, paren).trim();
        int space = head.lastIndexOf(' ');
        String method = space < 0 ? head : head.substring(space + 1);
        return simple + "." + method;
    }
}
