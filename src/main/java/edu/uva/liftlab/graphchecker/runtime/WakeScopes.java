package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayDeque;
import java.util.Deque;

/**
 * One turn of a service loop is one root scope.
 *
 * <p>A daemon loop -- a heartbeat, a monitor, a key updater -- is started by
 * no request and serves none, so what it sends carried no request flow and
 * everything that served it was addressed {@code Lost}: two heartbeats on one
 * NameNode handler shared one address.  The turn is the unit: the WAKE of a
 * timed wait hands the thread its next turn, so the turn is opened there as a
 * root of its own -- role {@code WAKE}, its api the loop's site, its k the
 * k-th turn of that loop on that node in the window -- with a request flow the
 * turn's messages carry, and closed when the loop waits again.  This is what
 * replaced the heartbeat scopes hand-woven into each Hadoop tree.</p>
 *
 * <p>Opened only on a thread the attribution rule names a node for: a turn of
 * a node the run does not know is not a request of anybody's, and stays what
 * it was.  A turn scope that is not the innermost scope when the loop waits
 * again -- something opened inside it and did not close -- is left standing
 * rather than torn out from under that scope's owner; it closes the next time
 * it is innermost.</p>
 */
final class WakeScopes {
    /** On or off (A/B switch); on unless a run says otherwise. */
    static final String PROPERTY = "causynth.wake.scope";

    private static final ThreadLocal<Deque<Long>> OPEN =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<Long>();
                }
            };

    private WakeScopes() {
    }

    private static boolean enabled() {
        return !"false".equalsIgnoreCase(
                Text.safe(System.getProperty(PROPERTY)));
    }

    /** The loop waits: the turn it was running is over. */
    static void waiting(String site) {
        if (!enabled()) return;
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
        if (!enabled()) return;
        if (!CausynthTraceRecorder.recordingStarted()) return;
        ScheduleLog.mute();
        try {
            long token = RuntimeTraceContext.beginWake(api(site));
            if (token > 0L) OPEN.get().push(token);
        } catch (Throwable ignored) {
            // Same rule: the turn runs whether or not it could be named.
        } finally {
            ScheduleLog.unmute();
        }
    }

    /**
     * The api a turn is counted under: the loop's class and method, which is
     * stable across runs and readable in an address; the unit index of the
     * wait is left out so a loop with two waits is one loop.
     */
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

    static void resetForTests() {
        OPEN.remove();
    }
}
