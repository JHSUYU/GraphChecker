package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.util.Map;
import java.util.Set;
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
 *       wait's semantics, on the wall clock, and a WAKE event when its
 *       TIMEOUT ends it.  A wait a signal ends (a notify, a condition
 *       signal, an unpark) is no event: another thread ended it, and that
 *       thread's own events are the schedule's ({@link #takeTurn}).</li>
 *   <li>HELD to a prefix: VIRTUAL TIME, which stands in for the CLOCK and
 *       never for the NOTIFIER.  The wait does not read the wall clock: it
 *       ends when a real signal comes, or when its timeout WAKE is the
 *       prefix's next event.  hdfs-17967 is why the notifier is never
 *       stood in for: an idle IPC connection the recording saw woken by the
 *       call it then served returned at a turn before the call was added,
 *       found nothing to read, and closed itself.  A wait that holds a
 *       monitor or a lock waits on its own primitive between asks, so
 *       whatever it holds is released while it waits and the thread whose
 *       event IS next can run.</li>
 * </ul>
 *
 * <p>A wait already in progress when the window opens -- an idle IPC
 * connection, a daemon's first sleep -- converts: the window's opening wakes
 * it ({@link #windowOpened}), which is not a signal, and from there it is
 * held like any other.  The discovering session's schedule states when that
 * thread woke inside the window, and a replay that left it on the wall clock
 * would hold everything behind it for as long as its real timeout ran.</p>
 *
 * <p>An element a timed poll returns is not a WAKE: it is the CLAIM of the
 * work a producer handed over ({@code Identity.claimStart}), and it is
 * returned the moment it arrives.  A poll's WAKE is always its timeout.</p>
 */
public final class TimedWaits {
    /** How long a wait polls between asks for its turn, in ms. */
    private static final long QUANTUM_MS = 10L;
    /**
     * A quantum that ends at least this much before its time was ended by a
     * signal.  Small, because a notify can only land while the waiter is in
     * its quantum -- between two quanta the waiter holds the monitor -- and
     * one that lands in this last sliver is taken for the quantum's end.
     */
    private static final long EARLY_NANOS = TimeUnit.MICROSECONDS.toNanos(50L);

    /** A wait that can be woken early: what the window's opening wakes. */
    private static final Map<Thread, Object> WAITING =
            new ConcurrentHashMap<Thread, Object>();
    /** The waits the window's opening woke: their return is no signal. */
    private static final Set<Thread> WINDOW_WOKEN =
            ConcurrentHashMap.<Thread>newKeySet();
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
     * lock of its own for exactly this; a park is unparked.  Each is marked
     * first, so the wait it ends does not read it as a signal.  Called with
     * no lock of this runtime held.</p>
     */
    static void windowOpened() {
        for (Map.Entry<Thread, Object> waiting : WAITING.entrySet()) {
            WINDOW_WOKEN.add(waiting.getKey());
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

    // ---- Thread.sleep / TimeUnit.sleep ------------------------------------

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
     * window's opening can wake it; held to its turn once enforced.  Nothing
     * signals a sleep, so its WAKE is always its timeout.
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
        WINDOW_WOKEN.remove(self);
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
            WINDOW_WOKEN.remove(self);
        }
        if (heldWake(site)) return;
        wake(site);
    }

    // ---- LockSupport.parkNanos ------------------------------------------

    public static void parkNanos(long nanos, String site) {
        park(null, nanos, site);
    }

    public static void parkNanos(Object blocker, long nanos, String site) {
        park(blocker, nanos, site);
    }

    /**
     * A park: free, on the wall clock, and signalled when it returned before
     * its time (an unpark); held, until an unpark or its timeout turn.
     */
    private static void park(Object blocker, long nanos, String site) {
        WakeScopes.waiting(site);
        boolean signalled = false;
        if (!ScheduleLog.enforcing()) {
            Thread self = Thread.currentThread();
            WINDOW_WOKEN.remove(self);
            WAITING.put(self, PARKED);
            long before = System.nanoTime();
            try {
                LockSupport.parkNanos(blocker, nanos);
            } finally {
                WAITING.remove(self);
            }
            boolean byWindow = WINDOW_WOKEN.remove(self);
            signalled = !byWindow && System.nanoTime() - before < nanos;
        }
        try {
            takeTurn(site, signalled, parkQuantum(blocker));
        } catch (InterruptedException impossible) {
            // A park is never interrupted by throwing; its quantum is not.
            Thread.currentThread().interrupt();
        }
    }

    private static Quantum parkQuantum(final Object blocker) {
        return new Quantum() {
            @Override
            boolean endsNow() {
                // A park returns at once for an interrupted thread, and the
                // caller reads the flag; so does this one, turn or no turn.
                return Thread.currentThread().isInterrupted();
            }

            @Override
            boolean await(long millis) {
                long nanos = TimeUnit.MILLISECONDS.toNanos(millis);
                long before = System.nanoTime();
                LockSupport.parkNanos(blocker, nanos);
                return System.nanoTime() - before < nanos - EARLY_NANOS;
            }
        };
    }

    // ---- Object.wait(long) ------------------------------------------------

    public static void waitOn(Object monitor, long millis, String site)
            throws InterruptedException {
        monitorWait(monitor, millis, 0, site);
    }

    public static void waitOn(Object monitor, long millis, int nanos,
                              String site) throws InterruptedException {
        monitorWait(monitor, millis, nanos, site);
    }

    private static void monitorWait(Object monitor, long millis, int nanos,
                                    String site) throws InterruptedException {
        WakeScopes.waiting(site);
        boolean signalled = false;
        if (!ScheduleLog.enforcing()) {
            signalled = freeMonitorWait(monitor, millis, nanos, site);
        }
        takeTurn(site, signalled, monitorQuantum(monitor));
    }

    /**
     * One free monitor wait, woken early by the window's opening.  True when
     * a notify ended it: it returned before its timeout, and not because the
     * window opened.  An untimed wait ({@code wait(0)}) ends only by one.
     */
    private static boolean freeMonitorWait(Object monitor, long millis,
                                           int nanos, String site)
            throws InterruptedException {
        Thread self = Thread.currentThread();
        WINDOW_WOKEN.remove(self);
        WAITING.put(self, monitor);
        long before = System.nanoTime();
        try {
            monitor.wait(millis, nanos);
        } catch (InterruptedException interrupted) {
            WAITING.remove(self);
            WINDOW_WOKEN.remove(self);
            ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
            throw interrupted;
        } finally {
            WAITING.remove(self);
        }
        boolean byWindow = WINDOW_WOKEN.remove(self);
        if (byWindow) return false;
        long timeout = TimeUnit.MILLISECONDS.toNanos(millis) + nanos;
        return timeout == 0L || System.nanoTime() - before < timeout;
    }

    private static Quantum monitorQuantum(final Object monitor) {
        return new Quantum() {
            @Override
            boolean await(long millis) throws InterruptedException {
                long nanos = TimeUnit.MILLISECONDS.toNanos(millis);
                long before = System.nanoTime();
                monitor.wait(millis);
                return System.nanoTime() - before < nanos - EARLY_NANOS;
            }
        };
    }

    // ---- Condition.awaitNanos / await(long, TimeUnit) ---------------------

    public static long awaitNanos(Condition condition, long nanos,
                                  String site) throws InterruptedException {
        WakeScopes.waiting(site);
        long deadline = System.nanoTime() + nanos;
        boolean signalled = freeConditionWait(condition, deadline, site);
        boolean outcome =
                takeTurn(site, signalled, conditionQuantum(condition));
        // Virtual time: the turn came, by a signal or not as the prefix
        // said; a caller that re-checks its condition -- every loop that
        // waits this way does -- reads the rest.
        return outcome ? Math.max(1L, deadline - System.nanoTime()) : 0L;
    }

    public static boolean await(Condition condition, long time,
                                TimeUnit unit, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        long deadline = System.nanoTime() + unit.toNanos(time);
        boolean signalled = freeConditionWait(condition, deadline, site);
        return takeTurn(site, signalled, conditionQuantum(condition));
    }

    /**
     * The free part of a condition wait: in quanta, so the window's opening
     * is seen within one.  True when a signal ended it; false at its
     * deadline, or when the window opened first.
     */
    private static boolean freeConditionWait(Condition condition,
                                             long deadline, String site)
            throws InterruptedException {
        while (!ScheduleLog.enforcing()) {
            long left = deadline - System.nanoTime();
            if (left <= 0L) return false;
            long rest;
            try {
                rest = condition.awaitNanos(Math.min(left,
                        TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS)));
            } catch (InterruptedException interrupted) {
                ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
                throw interrupted;
            }
            if (rest > 0L) return true;
        }
        return false;
    }

    private static Quantum conditionQuantum(final Condition condition) {
        return new Quantum() {
            @Override
            boolean await(long millis) throws InterruptedException {
                return condition.awaitNanos(
                        TimeUnit.MILLISECONDS.toNanos(millis)) > 0L;
            }
        };
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

    // ---- taking the turn --------------------------------------------------

    /** What a wait does between two asks: one quantum on its own primitive. */
    private abstract static class Quantum {
        /** Waits at most {@code millis}; true when a signal ended it early. */
        abstract boolean await(long millis) throws InterruptedException;

        /**
         * Whether the wait must end now, whatever the prefix says: only an
         * interrupted park, which cannot throw.  An interrupted monitor or
         * condition wait ends by its quantum throwing, as the real one does.
         */
        boolean endsNow() {
            return false;
        }
    }

    /**
     * Ends one wait, and says how it ended: true by a signal.
     *
     * <p>A WAKE is the turn TIME hands a thread, so only a wait its timeout
     * ended is an event.  A wait a signal ended -- a notify, a condition
     * signal, an unpark -- was ended by another thread, whose own events the
     * schedule already orders; it is no turn of its own, and it is neither
     * recorded nor held.  hdfs-17899-bug3 is why: an idle IPC connection the
     * recording saw notified at one point was, in every replay, notified
     * somewhere else or not at all -- what notifies it is the state the
     * connection was left in before the window -- and a replay held to that
     * wake waited for a signal that never came.</p>
     *
     * <p>Free, the wait already ended: a timeout is recorded, a signal is
     * not.  Held to a prefix, the wait waits in quanta on its own primitive
     * for a signal -- which ends it at once, no event -- or for its timeout
     * WAKE to be the prefix's next event, which ends it at that turn without
     * reading the clock (virtual time).  Asking for the turn every quantum
     * is also what keeps the watchdog looking.</p>
     */
    private static boolean takeTurn(String site, boolean signalled,
                                    Quantum quantum)
            throws InterruptedException {
        ScheduleLog.Wake wake = ScheduleLog.wake(site);
        if (wake == null) {
            // The window is not open, or the event has no name: the wait
            // ends as it did, and there is no turn to take.
            WakeScopes.woke(site);
            return signalled;
        }
        while (true) {
            if (signalled) {
                WakeScopes.woke(site);
                return true;
            }
            if (quantum.endsNow()) {
                // The same rule an interrupted admission follows: the wait
                // ends where it is, and the prefix stands for the rest.
                ScheduleLog.admitNow(wake);
                WakeScopes.woke(site);
                return true;
            }
            if (ScheduleLog.tryAdmit(wake)) {
                WakeScopes.woke(site);
                return false;
            }
            if (quantum.await(QUANTUM_MS)) signalled = true;
        }
    }

    /**
     * Under a prefix, blocks until this wait's WAKE is admitted: the wait is
     * then taken over and the caller skips the real one.  Only for a sleep,
     * which nothing signals.
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

    private static void wake(String site) {
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        WakeScopes.woke(site);
    }
}
