package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.LockSupport;

/**
 * THE timed waits of the application scope: where a service loop hands its
 * thread the next turn, and one turn is one root scope.
 *
 * <p>A daemon loop -- a heartbeat, a monitor, a key updater -- is started by
 * no request and serves none, so what it sends carried no request flow and
 * everything that served it was addressed {@code Lost}: two heartbeats on one
 * NameNode handler shared one address.  The turn is the unit.  The weave
 * replaces every call of a timed-wait shape ({@code WorkStartSites.timedWait})
 * in an application method with the method of the same shape here, in BOTH
 * passes: the receiver becomes the first argument and the call site the
 * last.  Each does exactly what the call did, and around it closes the turn
 * the loop was running ({@link #waiting}) and opens the next one when the
 * wait returns ({@link #woke}) -- role {@code WAKE}, its api the loop's
 * site, its k the k-th turn of that loop on that node in the window
 * ({@link RuntimeTraceContext#beginWake}).</p>
 *
 * <p>A wait that throws opens no turn: the loop leaves.  A timed poll that
 * returns an element opens none either: the element is the CLAIM of the work
 * a producer handed over ({@code Identity.claimStart}), not the next turn of
 * a loop of the consumer's.</p>
 *
 * <p>Turns are opened only on a thread the attribution rule names a node for:
 * a turn of a node the run does not know is not a request of anybody's, and
 * stays what it was.  A turn scope that is not the innermost scope when the
 * loop waits again -- something opened inside it and did not close -- is
 * left standing rather than torn out from under that scope's owner; it
 * closes the next time it is innermost.</p>
 */
public final class TimedWaits {
    private static final ThreadLocal<Deque<Long>> OPEN =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<Long>();
                }
            };

    private TimedWaits() {
    }

    public static void sleep(long millis, String site)
            throws InterruptedException {
        waiting();
        Thread.sleep(millis);
        woke(site);
    }

    public static void sleep(long millis, int nanos, String site)
            throws InterruptedException {
        waiting();
        Thread.sleep(millis, nanos);
        woke(site);
    }

    public static void sleep(TimeUnit unit, long timeout, String site)
            throws InterruptedException {
        waiting();
        unit.sleep(timeout);
        woke(site);
    }

    public static void parkNanos(long nanos, String site) {
        waiting();
        LockSupport.parkNanos(nanos);
        woke(site);
    }

    public static void parkNanos(Object blocker, long nanos, String site) {
        waiting();
        LockSupport.parkNanos(blocker, nanos);
        woke(site);
    }

    public static void waitOn(Object monitor, long millis, String site)
            throws InterruptedException {
        waiting();
        monitor.wait(millis);
        woke(site);
    }

    public static void waitOn(Object monitor, long millis, int nanos,
                              String site) throws InterruptedException {
        waiting();
        monitor.wait(millis, nanos);
        woke(site);
    }

    public static long awaitNanos(Condition condition, long nanos,
                                  String site) throws InterruptedException {
        waiting();
        long left = condition.awaitNanos(nanos);
        woke(site);
        return left;
    }

    public static boolean await(Condition condition, long time,
                                TimeUnit unit, String site)
            throws InterruptedException {
        waiting();
        boolean signalled = condition.await(time, unit);
        woke(site);
        return signalled;
    }

    public static Object poll(BlockingQueue<?> queue, long timeout,
                              TimeUnit unit, String site)
            throws InterruptedException {
        waiting();
        Object element = queue.poll(timeout, unit);
        if (element == null) woke(site);
        return element;
    }

    /** The loop waits: the turn it was running is over. */
    private static void waiting() {
        try {
            Deque<Long> open = OPEN.get();
            while (!open.isEmpty()
                    && RuntimeTraceContext.endWakeIfInnermost(open.peek())) {
                open.pop();
            }
        } catch (Throwable ignored) {
            // A hook never turns a wait into a failure.
        }
    }

    /** The wait returned: the loop's next turn begins. */
    private static void woke(String site) {
        if (!RecordingWindow.opened()) return;
        try {
            long token = RuntimeTraceContext.beginWake(api(site));
            if (token > 0L) OPEN.get().push(token);
        } catch (Throwable ignored) {
            // Same rule: the turn runs whether or not it could be named.
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
}
