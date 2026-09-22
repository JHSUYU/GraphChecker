package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.LockSupport;

/**
 * THE timed waits of the application scope: where a service loop hands its
 * thread the next turn.
 *
 * <p>The weave replaces every call of a timed-wait shape
 * ({@code WorkStartSites.timedWait}) in an application method with the method
 * of the same shape here, in BOTH passes, from the one application-scope walk
 * that already files work starts and claims.  The receiver becomes the first
 * argument and the call site the last.  What each does:</p>
 *
 * <ul>
 *   <li>FREE (the recording, a replay with no prefix, a replay past its
 *       prefix): the original wait, unchanged, and a WAKE event when it
 *       returns -- normally or not.</li>
 *   <li>HELD to a prefix: VIRTUAL TIME.  The wait does not read the wall
 *       clock; it returns when its WAKE is the prefix's next event, which is
 *       the turn the discovering session's thread woke at.  A wait that holds
 *       a monitor or a lock waits on its own primitive for a short quantum
 *       between asks, so whatever it holds is released while it waits and
 *       the thread whose event IS next can run.</li>
 * </ul>
 *
 * <p>An element a timed poll returns is not a WAKE: it is the CLAIM of the
 * work a producer handed over ({@code Identity.claimStart}), and it is
 * returned the moment it arrives.</p>
 */
public final class TimedWaits {
    /** How long a monitor-holding wait releases its monitor between asks. */
    private static final long QUANTUM_MS = 10L;

    private TimedWaits() {
    }

    // ---- Thread.sleep / TimeUnit.sleep / LockSupport.parkNanos -----------

    public static void sleep(long millis, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        if (heldWake(site)) return;
        try {
            Thread.sleep(millis);
        } finally {
            wake(site);
        }
    }

    public static void sleep(long millis, int nanos, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        if (heldWake(site)) return;
        try {
            Thread.sleep(millis, nanos);
        } finally {
            wake(site);
        }
    }

    public static void sleep(TimeUnit unit, long timeout, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        if (heldWake(site)) return;
        try {
            unit.sleep(timeout);
        } finally {
            wake(site);
        }
    }

    public static void parkNanos(long nanos, String site) {
        WakeScopes.waiting(site);
        if (heldWakeUninterruptibly(site)) return;
        try {
            LockSupport.parkNanos(nanos);
        } finally {
            wake(site);
        }
    }

    public static void parkNanos(Object blocker, long nanos, String site) {
        WakeScopes.waiting(site);
        if (heldWakeUninterruptibly(site)) return;
        try {
            LockSupport.parkNanos(blocker, nanos);
        } finally {
            wake(site);
        }
    }

    // ---- Object.wait(long) ------------------------------------------------

    public static void waitOn(Object monitor, long millis, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        if (ScheduleLog.enforcing()) {
            // The caller holds the monitor.  It is released for a quantum
            // at a time, so a notifier -- or the thread whose turn it is --
            // can take it; the wait returns when its WAKE is admitted.
            while (!ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
                monitor.wait(QUANTUM_MS);
            }
            WakeScopes.woke(site);
            return;
        }
        try {
            monitor.wait(millis);
        } finally {
            wake(site);
        }
    }

    public static void waitOn(Object monitor, long millis, int nanos,
                              String site) throws InterruptedException {
        WakeScopes.waiting(site);
        if (ScheduleLog.enforcing()) {
            while (!ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
                monitor.wait(QUANTUM_MS);
            }
            WakeScopes.woke(site);
            return;
        }
        try {
            monitor.wait(millis, nanos);
        } finally {
            wake(site);
        }
    }

    // ---- Condition.awaitNanos / await(long, TimeUnit) ---------------------

    public static long awaitNanos(Condition condition, long nanos,
                                  String site) throws InterruptedException {
        WakeScopes.waiting(site);
        if (ScheduleLog.enforcing()) {
            boolean signalled = false;
            while (!ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
                if (condition.awaitNanos(
                        TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS)) > 0L) {
                    signalled = true;
                }
            }
            WakeScopes.woke(site);
            // Virtual time: the turn came.  Whether it came by a signal is
            // what the quanta saw; a caller that re-checks its condition --
            // every loop that waits this way does -- reads the rest.
            return signalled ? Math.max(1L, nanos) : 0L;
        }
        try {
            return condition.awaitNanos(nanos);
        } finally {
            wake(site);
        }
    }

    public static boolean await(Condition condition, long time,
                                TimeUnit unit, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        if (ScheduleLog.enforcing()) {
            boolean signalled = false;
            while (!ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
                if (condition.await(QUANTUM_MS, TimeUnit.MILLISECONDS)) {
                    signalled = true;
                }
            }
            WakeScopes.woke(site);
            return signalled;
        }
        try {
            return condition.await(time, unit);
        } finally {
            wake(site);
        }
    }

    // ---- BlockingQueue.poll(long, TimeUnit) -------------------------------

    public static Object poll(BlockingQueue<?> queue, long timeout,
                              TimeUnit unit, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        if (ScheduleLog.enforcing()) {
            while (true) {
                Object element = queue.poll(QUANTUM_MS,
                        TimeUnit.MILLISECONDS);
                if (element != null) return element;
                if (ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
                    WakeScopes.woke(site);
                    return null;
                }
            }
        }
        Object element = null;
        try {
            element = queue.poll(timeout, unit);
            return element;
        } finally {
            // A poll that timed out is a WAKE; one that returned an element
            // is the consumer's CLAIM of it, which the weave states after
            // the call returns (Identity.claimStart), not here.
            if (element == null) wake(site);
        }
    }

    // ---- the two halves ---------------------------------------------------

    /**
     * Under a prefix, blocks until this wait's WAKE is admitted: the wait is
     * then taken over and the caller skips the real one.
     *
     * <p>An interrupt that arrives while it waits for its turn ends the wait
     * the way the real one would have ended: by throwing.</p>
     */
    private static boolean heldWake(String site) throws InterruptedException {
        if (!ScheduleLog.enforcing()) return false;
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        WakeScopes.woke(site);
        if (Thread.interrupted()) throw new InterruptedException();
        return true;
    }

    private static boolean heldWakeUninterruptibly(String site) {
        if (!ScheduleLog.enforcing()) return false;
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        WakeScopes.woke(site);
        return true;
    }

    private static void wake(String site) {
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        WakeScopes.woke(site);
    }
}
