package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.util.Map;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
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
 *       prefix, anything before the recording window opens): the original
 *       wait's semantics, on the wall clock, and a WAKE event when it
 *       returns.</li>
 *   <li>HELD to a prefix: VIRTUAL TIME.  The wait does not read the wall
 *       clock; it returns when its WAKE is the prefix's next event, which is
 *       the turn the discovering session's thread woke at.  A wait that holds
 *       a monitor or a lock waits on its own primitive for a short quantum
 *       between asks, so whatever it holds is released while it waits and
 *       the thread whose event IS next can run.</li>
 * </ul>
 *
 * <p>A wait already in progress when the window opens -- an idle IPC
 * connection, a daemon's first sleep -- converts: the window's opening wakes
 * it ({@link #windowOpened}) and from there it is held like any other.  The
 * discovering session's schedule states when that thread woke inside the
 * window, and a replay that left it on the wall clock would hold everything
 * behind it for as long as its real timeout ran.</p>
 *
 * <p>An element a timed poll returns is not a WAKE: it is the CLAIM of the
 * work a producer handed over ({@code Identity.claimStart}), and it is
 * returned the moment it arrives.</p>
 */
public final class TimedWaits {
    /** How long a wait polls between asks, in ms. */
    private static final long QUANTUM_MS = 10L;

    /** A wait that can be woken early: what the window's opening wakes. */
    private static final Map<Thread, Object> WAITING =
            new ConcurrentHashMap<Thread, Object>();
    /** Stands for a parked thread, which is woken by unpark. */
    private static final Object PARKED = new Object();

    private TimedWaits() {
    }

    /**
     * The recording window opened under a prefix: every free wait in
     * progress is woken, and converts to virtual time where it stands.
     *
     * <p>A monitor wait is woken by a notify on its monitor, which every
     * waiter must already treat as possibly spurious; a sleep waits on a
     * lock of its own for exactly this; a park is unparked.  Called with no
     * lock of this runtime held.</p>
     */
    static void windowOpened() {
        for (Map.Entry<Thread, Object> waiting : WAITING.entrySet()) {
            Object on = waiting.getValue();
            if (on == PARKED) {
                LockSupport.unpark(waiting.getKey());
                continue;
            }
            synchronized (on) {
                on.notifyAll();
            }
        }
    }

    // ---- Thread.sleep / TimeUnit.sleep / LockSupport.parkNanos -----------

    public static void sleep(long millis, String site)
            throws InterruptedException {
        sleepFor(millis, 0, site);
    }

    public static void sleep(long millis, int nanos, String site)
            throws InterruptedException {
        sleepFor(millis, nanos, site);
    }

    public static void sleep(TimeUnit unit, long timeout, String site)
            throws InterruptedException {
        if (timeout <= 0L) {
            WakeScopes.waiting(site);
            wake(site);
            return;
        }
        long millis = unit.toMillis(timeout);
        long nanos = unit.toNanos(timeout)
                - TimeUnit.MILLISECONDS.toNanos(millis);
        sleepFor(millis, (int) Math.max(0L, Math.min(999999L, nanos)), site);
    }

    /**
     * A sleep: on the wall clock while free, on a lock of its own so the
     * window's opening can wake it; held to its turn once enforced.
     */
    private static void sleepFor(long millis, int nanos, String site)
            throws InterruptedException {
        if (millis < 0L || nanos < 0 || nanos > 999999) {
            // The JDK's own refusal, unchanged.
            Thread.sleep(millis, nanos);
        }
        WakeScopes.waiting(site);
        if (heldWake(site)) return;
        Object lock = new Object();
        long deadline = System.nanoTime()
                + TimeUnit.MILLISECONDS.toNanos(millis) + nanos;
        Thread self = Thread.currentThread();
        WAITING.put(self, lock);
        try {
            synchronized (lock) {
                while (!ScheduleLog.enforcing()) {
                    long left = deadline - System.nanoTime();
                    if (left <= 0L) break;
                    lock.wait(Math.max(1L,
                            TimeUnit.NANOSECONDS.toMillis(left)));
                }
            }
        } catch (InterruptedException interrupted) {
            WAITING.remove(self);
            ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
            throw interrupted;
        } finally {
            WAITING.remove(self);
        }
        if (heldWake(site)) return;
        wake(site);
    }

    public static void parkNanos(long nanos, String site) {
        WakeScopes.waiting(site);
        if (heldWakeUninterruptibly(site)) return;
        Thread self = Thread.currentThread();
        WAITING.put(self, PARKED);
        try {
            LockSupport.parkNanos(nanos);
        } finally {
            WAITING.remove(self);
        }
        if (heldWakeUninterruptibly(site)) return;
        wake(site);
    }

    public static void parkNanos(Object blocker, long nanos, String site) {
        WakeScopes.waiting(site);
        if (heldWakeUninterruptibly(site)) return;
        Thread self = Thread.currentThread();
        WAITING.put(self, PARKED);
        try {
            LockSupport.parkNanos(blocker, nanos);
        } finally {
            WAITING.remove(self);
        }
        if (heldWakeUninterruptibly(site)) return;
        wake(site);
    }

    // ---- Object.wait(long) ------------------------------------------------

    public static void waitOn(Object monitor, long millis, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        if (!ScheduleLog.enforcing()) {
            freeMonitorWait(monitor, millis, 0, site);
        }
        admitHolding(monitor, site);
    }

    public static void waitOn(Object monitor, long millis, int nanos,
                              String site) throws InterruptedException {
        WakeScopes.waiting(site);
        if (!ScheduleLog.enforcing()) {
            freeMonitorWait(monitor, millis, nanos, site);
        }
        admitHolding(monitor, site);
    }

    /** One free monitor wait, woken early by the window's opening. */
    private static void freeMonitorWait(Object monitor, long millis,
                                        int nanos, String site)
            throws InterruptedException {
        Thread self = Thread.currentThread();
        WAITING.put(self, monitor);
        try {
            monitor.wait(millis, nanos);
        } catch (InterruptedException interrupted) {
            WAITING.remove(self);
            ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
            throw interrupted;
        } finally {
            WAITING.remove(self);
        }
    }

    /**
     * Admits a WAKE whose thread holds {@code monitor}: asks without
     * blocking, and between asks releases the monitor for a quantum, so
     * whoever's event IS next can take it.  Free, the first ask admits.
     */
    private static void admitHolding(Object monitor, String site)
            throws InterruptedException {
        while (!ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
            monitor.wait(QUANTUM_MS);
        }
        WakeScopes.woke(site);
    }

    // ---- Condition.awaitNanos / await(long, TimeUnit) ---------------------

    public static long awaitNanos(Condition condition, long nanos,
                                  String site) throws InterruptedException {
        WakeScopes.waiting(site);
        long deadline = System.nanoTime() + nanos;
        boolean signalled = false;
        // Free: in quanta, so the window's opening is seen within one; a
        // quantum that returns early is the signal the caller waits for.
        while (!ScheduleLog.enforcing()) {
            long left = deadline - System.nanoTime();
            if (left <= 0L) {
                ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
                WakeScopes.woke(site);
                return 0L;
            }
            long quantum = Math.min(left,
                    TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS));
            long rest;
            try {
                rest = condition.awaitNanos(quantum);
            } catch (InterruptedException interrupted) {
                ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
                throw interrupted;
            }
            if (rest > 0L) {
                if (!ScheduleLog.enforcing()) {
                    ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
                    WakeScopes.woke(site);
                    return Math.max(1L, deadline - System.nanoTime());
                }
                signalled = true;
            }
        }
        while (!ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
            if (condition.awaitNanos(
                    TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS)) > 0L) {
                signalled = true;
            }
        }
        WakeScopes.woke(site);
        // Virtual time: the turn came.  Whether it came by a signal is what
        // the quanta saw; a caller that re-checks its condition -- every
        // loop that waits this way does -- reads the rest.
        return signalled ? Math.max(1L, deadline - System.nanoTime()) : 0L;
    }

    public static boolean await(Condition condition, long time,
                                TimeUnit unit, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        long deadline = System.nanoTime() + unit.toNanos(time);
        boolean signalled = false;
        while (!ScheduleLog.enforcing()) {
            long left = deadline - System.nanoTime();
            if (left <= 0L) {
                ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
                WakeScopes.woke(site);
                return false;
            }
            boolean early;
            try {
                early = condition.await(Math.min(left,
                        TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS)),
                        TimeUnit.NANOSECONDS);
            } catch (InterruptedException interrupted) {
                ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
                throw interrupted;
            }
            if (early) {
                if (!ScheduleLog.enforcing()) {
                    ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
                    WakeScopes.woke(site);
                    return true;
                }
                signalled = true;
            }
        }
        while (!ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
            if (condition.await(QUANTUM_MS, TimeUnit.MILLISECONDS)) {
                signalled = true;
            }
        }
        WakeScopes.woke(site);
        return signalled;
    }

    // ---- BlockingQueue.poll(long, TimeUnit) -------------------------------

    public static Object poll(BlockingQueue<?> queue, long timeout,
                              TimeUnit unit, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        // Free: in quanta, so the window's opening is seen within one.  An
        // element is returned the moment it arrives -- the consumer's CLAIM
        // of it, which the weave states after the call returns.
        while (!ScheduleLog.enforcing()) {
            long left = deadline - System.nanoTime();
            if (left <= 0L) {
                wake(site);
                return null;
            }
            Object element = queue.poll(Math.min(left,
                    TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS)),
                    TimeUnit.NANOSECONDS);
            if (element != null) return element;
        }
        while (true) {
            Object element = queue.poll(QUANTUM_MS, TimeUnit.MILLISECONDS);
            if (element != null) return element;
            if (ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site)) {
                WakeScopes.woke(site);
                return null;
            }
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
