package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.util.ArrayDeque;
import java.util.IdentityHashMap;
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
 *   <li>FREE (the recording, a replay with no prefix, a replay whose
 *       order no longer names the wait's timeout -- free, or past its
 *       prefix where the rest does not name it -- anything before the
 *       recording window opens): the original wait's semantics, on the
 *       wall clock, and a WAKE event when its TIMEOUT ends it.  A wait a signal ends (a notify, a condition
 *       signal, an unpark) is no event: another thread ended it, and that
 *       thread's own events are the schedule's ({@link #takeTurn}).</li>
 *   <li>HELD to a prefix: VIRTUAL TIME, which stands in for the CLOCK and
 *       never for the NOTIFIER.  The wait does not read the wall clock: it
 *       ends when a real signal comes, or when its timeout WAKE is the
 *       prefix's next event -- or, past the prefix, when the rest of the
 *       order names it and it is due ({@code ScheduleLog.turn}).
 *       hdfs-17967 is why the notifier is never stood in for: an idle IPC connection the recording saw woken by the
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
 *
 * <p>A SIGNAL IS STATE.  A notify or a condition signal reaches only a thread
 * that is in the wait set at that instant, and a real wait is there for its
 * whole length; a held wait is not -- it leaves at the end of every quantum
 * to ask for its turn, and the window's opening takes a free one out too.  A
 * notify that lands in such a gap finds nobody, and the waiter, which never
 * returns to its caller's own condition check, waits for a signal already
 * sent.  hdfs-17967 path C: the window's opening woke helper-dn's idle IPC
 * connection, the heartbeat's {@code addCall} took the monitor before the
 * connection re-entered its wait, its notify found an empty wait set, and the
 * response the connection should have read sat unread until the watchdog
 * gave the prefix up.  So the weave replaces the notifiers as well --
 * {@code notify}, {@code notifyAll}, {@code Condition.signal} and
 * {@code signalAll} -- and every wait on a monitor or a condition, timed or
 * not, registers for the whole of its length: a woven signal marks the wait
 * it chose, and the wait reads the mark whether or not it was in the wait
 * set when the signal came.  A notify marks the longest-standing unmarked
 * wait and a notifyAll every one; the monitor is then notified in full and
 * the waits that were not chosen go back to waiting, as the waits the JDK did
 * not choose never left.  A wait that returns early with no woven signal and
 * no window's wake behind it was ended by a notifier outside the weave, and
 * ends as it did before.</p>
 *
 * <p>AN INTERRUPT IS THE WORKLOAD'S: a wait it ends writes its WAKE where
 * it stands, free or held -- held whether or not it is the prefix's next
 * event, the rule an interrupted admission of any event already follows
 * ({@code ScheduleLog.admitNow}) -- and throws as the JDK's wait would (a
 * park returns).  Written early, such a WAKE leaves its later slot in the
 * prefix to the watchdog: the prefix stands for everyone else, and a thread
 * the workload interrupted is not held to it.  A park entered with its
 * interrupt pending writes nothing, since the JDK's park returns at once and
 * a loop around it spins.</p>
 *
 * <p>ONE LIMIT, stated: a notify from outside the weave that wakes a
 * registered wait is invisible to the registry, so a woven notify that
 * follows it on the same monitor may mark the wait it already woke.  Inside
 * the application scope every notifier is woven; it takes a notifier
 * outside it on an application monitor.</p>
 */
public final class TimedWaits {
    /** How long a wait polls between asks for its turn, in ms. */
    private static final long QUANTUM_MS = 10L;
    /**
     * A wait that ends at least this much before its time, with no woven
     * signal or window's wake sent, was ended by a notifier outside the weave
     * (or an unpark, for a park).  A woven signal needs no such guess: it is
     * read from the wait's mark.
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

    /**
     * The waits standing on each monitor or condition, and the signals sent
     * to them.  Guarded by itself, and the innermost of every lock: taken
     * with the application's monitor or lock held, never the other way.
     */
    private static final Map<Object, Waits> WAITS =
            new IdentityHashMap<Object, Waits>();

    /** One wait on a monitor or a condition: its signal, as state. */
    private static final class Waiter {
        /** Set by the woven signal that chose this wait. */
        volatile boolean signalled;
        /** Whether the wait stands on the wall clock, to {@link #deadline}. */
        volatile boolean onTheClock;
        volatile long deadline;

        /**
         * Whether the wall clock has already ended this wait: the JDK took
         * it out of the wait set at its timeout, so no signal is its.
         */
        boolean expired() {
            return onTheClock && System.nanoTime() - deadline >= 0L;
        }
    }

    /** The waits registered on one monitor or condition. */
    private static final class Waits {
        final ArrayDeque<Waiter> waiters = new ArrayDeque<Waiter>();
        /** Woven signals and window wakes sent here while a wait stood. */
        long sent;
    }

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
                // Counted as sent, so no other wait on this monitor reads
                // the wake as a notifier's.
                touch(on);
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
     * window's opening can wake it; held to its turn once enforced, and back
     * on the wall clock, to its own deadline, when the run goes free before
     * the turn came ({@code ScheduleLog.turn}).  Nothing signals a sleep, so
     * its WAKE is always its timeout.
     */
    private static void sleepFor(long millis, int nanos, String site)
            throws InterruptedException {
        if (millis < 0L || nanos < 0 || nanos > 999999) {
            // The JDK's own refusal, unchanged.
            Thread.sleep(millis, nanos);
        }
        WakeScopes.waiting(site);
        // Thread.sleep throws on a pending interrupt, even sleep(0).
        interruptedAtEntry(site);
        long deadline = System.nanoTime()
                + TimeUnit.MILLISECONDS.toNanos(millis) + nanos;
        while (true) {
            if (ScheduleLog.enforcing()) {
                ScheduleLog.Turn turn = heldWake(site);
                if (turn == ScheduleLog.Turn.ADMITTED) return;
                // No event to hold it to, or no order holds it any more --
                // free, or past the prefix with a WAKE the rest does not
                // name: the sleep is the wall clock's, to its own deadline.
                try {
                    wallSleep(deadline);
                } catch (InterruptedException interrupted) {
                    interruptedWake(site);
                    throw interrupted;
                }
                break;
            }
            if (!freeSleep(deadline, site)) break;
        }
        wake(site);
    }

    /** Sleeps on the wall clock to {@code deadline}, the window aside. */
    private static void wallSleep(long deadline) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        while (true) {
            long left = deadline - System.nanoTime();
            if (left <= 0L) return;
            long millis = TimeUnit.NANOSECONDS.toMillis(left);
            Thread.sleep(millis, (int) (left - TimeUnit.MILLISECONDS
                    .toNanos(millis)));
        }
    }

    /**
     * Sleeps on the wall clock to {@code deadline}.  True when the window
     * opened under a prefix first, and the sleep is to take its turn.
     */
    private static boolean freeSleep(long deadline, String site)
            throws InterruptedException {
        Object lock = new Object();
        Thread self = Thread.currentThread();
        WINDOW_WOKEN.remove(self);
        WAITING.put(self, lock);
        try {
            synchronized (lock) {
                while (true) {
                    if (ScheduleLog.enforcing()) return true;
                    long left = deadline - System.nanoTime();
                    if (left <= 0L) return false;
                    lock.wait(Math.max(1L, (left + 999999L) / 1000000L));
                }
            }
        } catch (InterruptedException interrupted) {
            WAITING.remove(self);
            interruptedWake(site);
            throw interrupted;
        } finally {
            WAITING.remove(self);
            WINDOW_WOKEN.remove(self);
        }
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
        if (Thread.currentThread().isInterrupted()) {
            // The JDK's park returns at once for a thread already
            // interrupted, and keeps the flag, so a loop that parks again
            // spins: no event, held or free, or it would write one per spin
            // and no two runs would write the same number.
            WakeScopes.woke(site);
            return;
        }
        long deadline = System.nanoTime() + nanos;
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
            if (self.isInterrupted()) {
                // An interrupt ended it while it was parked: the held park
                // writes its WAKE where it stands (takeTurn asks
                // Quantum#endsNow before anything), and so does the free one.
                interruptedWake(site);
                WakeScopes.woke(site);
                return;
            }
            signalled = !byWindow && System.nanoTime() - before < nanos;
        }
        try {
            takeTurn(site, signalled, parkQuantum(blocker), deadline);
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
                // An interrupt is no unpark: endsNow answers it next.
                if (Thread.currentThread().isInterrupted()) return false;
                return System.nanoTime() - before < nanos - EARLY_NANOS;
            }
        };
    }

    // ---- Object.wait / notify / notifyAll ---------------------------------

    public static void waitOn(Object monitor, String site)
            throws InterruptedException {
        if (!Thread.holdsLock(monitor)) {
            // The JDK's own refusal, unchanged.
            monitor.wait();
            return;
        }
        untimedMonitorWait(monitor);
    }

    public static void waitOn(Object monitor, long millis, String site)
            throws InterruptedException {
        monitorWait(monitor, millis, 0, site);
    }

    public static void waitOn(Object monitor, long millis, int nanos,
                              String site) throws InterruptedException {
        monitorWait(monitor, millis, nanos, site);
    }

    /**
     * A notify: marks the longest-standing unmarked wait on the monitor, then
     * notifies every wait there so the marked one sees it wherever it
     * stands; the rest go back to waiting.  With no wait of the weave's on
     * it, the plain notify.
     */
    public static void notifyOn(Object monitor, String site) {
        if (!Thread.holdsLock(monitor)) {
            // The JDK's own refusal, unchanged.
            monitor.notify();
            return;
        }
        if (send(monitor, false)) {
            monitor.notifyAll();
        } else {
            monitor.notify();
        }
    }

    /** A notifyAll: marks every wait on the monitor. */
    public static void notifyAllOn(Object monitor, String site) {
        if (Thread.holdsLock(monitor)) send(monitor, true);
        monitor.notifyAll();
    }

    private static void monitorWait(Object monitor, long millis, int nanos,
                                    String site) throws InterruptedException {
        if (!Thread.holdsLock(monitor) || millis < 0L || nanos < 0
                || nanos > 999999) {
            // The JDK's own refusal, unchanged.
            monitor.wait(millis, nanos);
            return;
        }
        WakeScopes.waiting(site);
        if (millis == 0L && nanos == 0) {
            // wait(0) waits for a signal and nothing else: no timeout, so no
            // turn of time's, held or free.
            untimedMonitorWait(monitor);
            WakeScopes.woke(site);
            return;
        }
        interruptedAtEntry(site);
        long deadline = System.nanoTime()
                + TimeUnit.MILLISECONDS.toNanos(millis) + nanos;
        Waiter self = enter(monitor);
        try {
            boolean signalled = false;
            if (!ScheduleLog.enforcing()) {
                signalled = freeMonitorWait(monitor, self, deadline, site);
            }
            takeTurn(site, signalled, monitorQuantum(monitor, self),
                    deadline);
        } finally {
            leave(monitor, self);
        }
    }

    /**
     * An untimed wait: registered, so a woven notify meant for it is not
     * lost, and a notifyAll's wake meant for another wait is not taken for
     * one.  Held or free alike, since time never ends it.
     */
    private static void untimedMonitorWait(Object monitor)
            throws InterruptedException {
        Waiter self = enter(monitor);
        try {
            while (!self.signalled) {
                long seen = sent(monitor);
                waitMarked(monitor, 0L, self);
                if (!self.signalled && sent(monitor) == seen) {
                    // A notifier outside the weave, or a spurious wakeup:
                    // the caller checks its condition, as it must anyway.
                    return;
                }
            }
        } finally {
            leave(monitor, self);
        }
    }

    /**
     * One free timed monitor wait, on the wall clock, woken early by the
     * window's opening.  True when a signal ended it; false at its timeout,
     * or when the window opened first -- it then converts to virtual time.
     */
    private static boolean freeMonitorWait(Object monitor, Waiter self,
                                           long deadline, String site)
            throws InterruptedException {
        Thread thread = Thread.currentThread();
        WINDOW_WOKEN.remove(thread);
        WAITING.put(thread, monitor);
        self.deadline = deadline;
        self.onTheClock = true;
        try {
            while (true) {
                if (self.signalled) return true;
                // Asked after this wait stands in WAITING, so a window that
                // opened without finding it there is seen here.
                if (WINDOW_WOKEN.remove(thread) || ScheduleLog.enforcing()) {
                    return false;
                }
                long left = deadline - System.nanoTime();
                if (left <= 0L) return false;
                long asked = Math.max(1L, (left + 999999L) / 1000000L);
                long seen = sent(monitor);
                long before = System.nanoTime();
                waitMarked(monitor, asked, self);
                if (self.signalled) return true;
                if (sent(monitor) == seen && System.nanoTime() - before
                        < TimeUnit.MILLISECONDS.toNanos(asked)
                                - EARLY_NANOS) {
                    // Early, and no woven signal or window wake was sent: a
                    // notifier outside the weave.
                    return true;
                }
            }
        } catch (InterruptedException interrupted) {
            WAITING.remove(thread);
            WINDOW_WOKEN.remove(thread);
            interruptedWake(site);
            throw interrupted;
        } finally {
            self.onTheClock = false;
            WAITING.remove(thread);
            WINDOW_WOKEN.remove(thread);
        }
    }

    /**
     * One physical wait of a registered monitor wait ({@code millis} 0 is
     * untimed).  An interrupt that finds the wait already MARKED by a woven
     * notify does not throw: the notify chose this wait, and a wait that
     * threw would take the notify with it, which JLS 17.2.4 forbids -- the
     * thread returns normally with its interrupt still pending, one of the
     * two outcomes the JLS allows a thread both notified and interrupted.
     */
    private static void waitMarked(Object monitor, long millis, Waiter self)
            throws InterruptedException {
        try {
            monitor.wait(millis);
        } catch (InterruptedException interrupted) {
            if (!self.signalled) throw interrupted;
            Thread.currentThread().interrupt();
        }
    }

    /**
     * A timed wait entered with its interrupt pending throws at once, as the
     * JDK's does ({@code Object.wait}, AQS {@code await}) -- held or free,
     * and before any turn is asked for, so a held wait whose WAKE happens to
     * be next is not taken for a timeout.  Its WAKE is written first, as any
     * wait an interrupt ends writes it ({@link #interruptedWake}).
     */
    private static void interruptedAtEntry(String site)
            throws InterruptedException {
        if (!Thread.interrupted()) return;
        interruptedWake(site);
        throw new InterruptedException();
    }

    /**
     * THE WAKE OF A WAIT AN INTERRUPT ENDED, one rule for free and held:
     * the interrupt is the workload's, the wait ends where it stands, and
     * its WAKE is written there -- free, as any free event is; held, whether
     * or not it is the prefix's next event, the rule an interrupted
     * admission follows.  The recording wrote one for every such wait, so a
     * replay that wrote none asked the prefix for an event nobody would
     * make, and every thread behind it waited out the watchdog.
     */
    private static void interruptedWake(String site) {
        if (ScheduleLog.enforcing()) {
            ScheduleLog.admitNow(ScheduleLog.wake(site));
        } else {
            ScheduleLog.tryObserve(ScheduleEvent.Kind.WAKE, site);
        }
    }

    /** {@link #waitMarked}'s rule for a condition's untimed await. */
    private static void awaitMarked(Condition condition, Waiter self)
            throws InterruptedException {
        try {
            condition.await();
        } catch (InterruptedException interrupted) {
            if (!self.signalled) throw interrupted;
            Thread.currentThread().interrupt();
        }
    }

    /**
     * {@link #waitMarked}'s rule for a condition's timed await; a marked
     * wait that was interrupted states time left, as a signalled one does.
     */
    private static long awaitNanosMarked(Condition condition, long nanos,
                                         Waiter self)
            throws InterruptedException {
        try {
            return condition.awaitNanos(nanos);
        } catch (InterruptedException interrupted) {
            if (!self.signalled) throw interrupted;
            Thread.currentThread().interrupt();
            return 1L;
        }
    }

    private static Quantum monitorQuantum(final Object monitor,
                                          final Waiter self) {
        return new Quantum() {
            @Override
            boolean signalled() {
                return self.signalled;
            }

            @Override
            void onTheClock(long deadline) {
                self.deadline = deadline;
                self.onTheClock = true;
            }

            @Override
            boolean await(long millis) throws InterruptedException {
                long seen = sent(monitor);
                long before = System.nanoTime();
                waitMarked(monitor, millis, self);
                if (self.signalled) return true;
                return sent(monitor) == seen && System.nanoTime() - before
                        < TimeUnit.MILLISECONDS.toNanos(millis) - EARLY_NANOS;
            }
        };
    }

    // ---- Condition.await / signal / signalAll -----------------------------

    public static long awaitNanos(Condition condition, long nanos,
                                  String site) throws InterruptedException {
        WakeScopes.waiting(site);
        interruptedAtEntry(site);
        long deadline = System.nanoTime() + nanos;
        Waiter self = enter(condition);
        try {
            boolean signalled =
                    freeConditionWait(condition, self, deadline, site);
            boolean outcome = takeTurn(site, signalled,
                    conditionQuantum(condition, self), deadline);
            // Virtual time: the turn came, by a signal or not as the prefix
            // said; a caller that re-checks its condition -- every loop that
            // waits this way does -- reads the rest.
            return outcome ? Math.max(1L, deadline - System.nanoTime()) : 0L;
        } finally {
            leave(condition, self);
        }
    }

    public static boolean await(Condition condition, long time,
                                TimeUnit unit, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        interruptedAtEntry(site);
        long deadline = System.nanoTime() + unit.toNanos(time);
        Waiter self = enter(condition);
        try {
            boolean signalled =
                    freeConditionWait(condition, self, deadline, site);
            return takeTurn(site, signalled,
                    conditionQuantum(condition, self), deadline);
        } finally {
            leave(condition, self);
        }
    }

    /** An untimed condition wait: {@link #untimedMonitorWait}'s rule. */
    public static void await(Condition condition, String site)
            throws InterruptedException {
        Waiter self = enter(condition);
        try {
            while (!self.signalled) {
                long seen = sent(condition);
                awaitMarked(condition, self);
                if (!self.signalled && sent(condition) == seen) return;
            }
        } finally {
            leave(condition, self);
        }
    }

    public static void awaitUninterruptibly(Condition condition,
                                            String site) {
        Waiter self = enter(condition);
        try {
            while (!self.signalled) {
                long seen = sent(condition);
                condition.awaitUninterruptibly();
                if (!self.signalled && sent(condition) == seen) return;
            }
        } finally {
            leave(condition, self);
        }
    }

    /**
     * A signal: {@link #notifyOn}'s rule.  The condition cannot say whether
     * this thread holds its lock, so the real signal goes first and refuses
     * a caller that does not; one that does holds every wait on the
     * condition still, and the mark is set before any of them can look.
     */
    public static void signal(Condition condition, String site) {
        boolean registered = standing(condition);
        if (registered) {
            condition.signalAll();
            send(condition, false);
        } else {
            condition.signal();
        }
    }

    public static void signalAll(Condition condition, String site) {
        boolean registered = standing(condition);
        condition.signalAll();
        if (registered) send(condition, true);
    }

    /**
     * The free part of a timed condition wait: in quanta, so the window's
     * opening is seen within one.  True when a signal ended it; false at its
     * deadline, or when the window opened first.
     */
    private static boolean freeConditionWait(Condition condition,
                                             Waiter self, long deadline,
                                             String site)
            throws InterruptedException {
        self.deadline = deadline;
        self.onTheClock = true;
        try {
            while (!ScheduleLog.enforcing()) {
                if (self.signalled) return true;
                long left = deadline - System.nanoTime();
                if (left <= 0L) return false;
                long seen = sent(condition);
                long rest;
                try {
                    rest = awaitNanosMarked(condition, Math.min(left,
                            TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS)), self);
                } catch (InterruptedException interrupted) {
                    interruptedWake(site);
                    throw interrupted;
                }
                if (self.signalled) return true;
                if (rest > 0L && sent(condition) == seen) return true;
            }
            return self.signalled;
        } finally {
            self.onTheClock = false;
        }
    }

    private static Quantum conditionQuantum(final Condition condition,
                                            final Waiter self) {
        return new Quantum() {
            @Override
            boolean signalled() {
                return self.signalled;
            }

            @Override
            void onTheClock(long deadline) {
                self.deadline = deadline;
                self.onTheClock = true;
            }

            @Override
            boolean await(long millis) throws InterruptedException {
                long seen = sent(condition);
                long rest = awaitNanosMarked(condition,
                        TimeUnit.MILLISECONDS.toNanos(millis), self);
                if (self.signalled) return true;
                return rest > 0L && sent(condition) == seen;
            }
        };
    }

    // ---- the registry of waits --------------------------------------------

    private static Waiter enter(Object on) {
        Waiter waiter = new Waiter();
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            if (waits == null) {
                waits = new Waits();
                WAITS.put(on, waits);
            }
            waits.waiters.addLast(waiter);
        }
        return waiter;
    }

    private static void leave(Object on, Waiter waiter) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            if (waits == null) return;
            waits.waiters.remove(waiter);
            if (waits.waiters.isEmpty()) WAITS.remove(on);
        }
    }

    private static boolean standing(Object on) {
        synchronized (WAITS) {
            return WAITS.containsKey(on);
        }
    }

    /** The signals sent to {@code on} while any wait stood there. */
    private static long sent(Object on) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            return waits == null ? 0L : waits.sent;
        }
    }

    /**
     * Marks the longest-standing unmarked wait on {@code on}, or every wait
     * when {@code all}.  True when any wait stood there.
     */
    private static boolean send(Object on, boolean all) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            if (waits == null) return false;
            waits.sent++;
            for (Waiter waiter : waits.waiters) {
                // A wait the wall clock already ended is out of the JDK's
                // wait set: the signal goes to one still in it.
                if (waiter.signalled || waiter.expired()) continue;
                waiter.signalled = true;
                if (!all) break;
            }
            return true;
        }
    }

    /** A window's wake on {@code on}: counted, so it is no notifier's. */
    private static void touch(Object on) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            if (waits != null) waits.sent++;
        }
    }

    // ---- BlockingQueue.poll(long, TimeUnit) -------------------------------

    public static Object poll(BlockingQueue<?> queue, long timeout,
                              TimeUnit unit, String site)
            throws InterruptedException {
        WakeScopes.waiting(site);
        // The JDK's timed poll takes its lock interruptibly, even poll(0).
        interruptedAtEntry(site);
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
        ScheduleLog.Wake wake = ScheduleLog.wake(site);
        try {
            return heldPoll(queue, wake, deadline, site);
        } finally {
            // However it ended, it no longer waits for a turn.
            ScheduleLog.withdraw(wake);
        }
    }

    private static Object heldPoll(BlockingQueue<?> queue,
                                   ScheduleLog.Wake wake, long deadline,
                                   String site) throws InterruptedException {
        long wait = TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS);
        while (true) {
            Object element = queue.poll(wait, TimeUnit.NANOSECONDS);
            if (element != null) return element;
            ScheduleLog.Turn turn = ScheduleLog.turn(wake);
            if (turn == ScheduleLog.Turn.ADMITTED) {
                WakeScopes.woke(site);
                return null;
            }
            wait = TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS);
            if (turn == ScheduleLog.Turn.FREE
                    || turn == ScheduleLog.Turn.NO_EVENT) {
                // The run went free: the rest on the wall clock.
                wait = deadline - System.nanoTime();
                if (wait <= 0L) {
                    ScheduleLog.admitNow(wake);
                    WakeScopes.woke(site);
                    return null;
                }
            }
        }
    }

    // ---- taking the turn --------------------------------------------------

    /** What a wait does between two asks: one quantum on its own primitive. */
    private abstract static class Quantum {
        /** Waits at most {@code millis}; true when a signal ended it early. */
        abstract boolean await(long millis) throws InterruptedException;

        /** Whether a woven signal marked the wait: read before every ask. */
        boolean signalled() {
            return false;
        }

        /**
         * The wait now stands on the wall clock to {@code deadline}: no
         * prefix holds it any more ({@link Waiter#expired}).
         */
        void onTheClock(long deadline) {
        }

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
     *
     * <p>When no order holds its timeout any more -- the run is free, or
     * past its prefix with a WAKE the rest does not name -- a held wait is
     * not ended: it waits on for a signal or to its own deadline, on the
     * wall clock, as the same wait does in a replay with no prefix, and its
     * WAKE is written only if that deadline ends it
     * ({@code ScheduleLog.turn}).</p>
     */
    private static boolean takeTurn(String site, boolean signalled,
                                    Quantum quantum, long deadline)
            throws InterruptedException {
        // Null: the window is not open, or the event has no name.  The wait
        // then has no turn to take, and ends as a free one does.
        ScheduleLog.Wake wake = ScheduleLog.wake(site);
        try {
            return turns(site, signalled, quantum, deadline, wake);
        } finally {
            // However it ended -- a signal above all -- it no longer waits
            // at the position it asked at.
            ScheduleLog.withdraw(wake);
        }
    }

    private static boolean turns(String site, boolean signalled,
                                 Quantum quantum, long deadline,
                                 ScheduleLog.Wake wake)
            throws InterruptedException {
        while (true) {
            if (quantum.endsNow()) {
                // The same rule an interrupted admission follows: the wait
                // ends where it is, and the prefix stands for the rest.
                // Asked first, as the free park asks: an interrupt beats an
                // unpark.
                ScheduleLog.admitNow(wake);
                WakeScopes.woke(site);
                return true;
            }
            if (signalled || quantum.signalled()) {
                WakeScopes.woke(site);
                return true;
            }
            ScheduleLog.Turn turn = ScheduleLog.turn(wake);
            if (turn == ScheduleLog.Turn.ADMITTED) {
                WakeScopes.woke(site);
                return false;
            }
            long wait = QUANTUM_MS;
            if (turn == ScheduleLog.Turn.FREE
                    || turn == ScheduleLog.Turn.NO_EVENT) {
                // No prefix holds it: its own deadline, on the wall clock.
                quantum.onTheClock(deadline);
                long left = deadline - System.nanoTime();
                if (left <= 0L) {
                    ScheduleLog.admitNow(wake);
                    WakeScopes.woke(site);
                    return false;
                }
                wait = Math.max(1L, (left + 999999L) / 1000000L);
            }
            try {
                if (quantum.await(wait)) signalled = true;
            } catch (InterruptedException interrupted) {
                // The wait ends where it is, held or free, and its WAKE is
                // written there, as the free wait's is: a prefix that holds a
                // wait an interrupt ended asks for that WAKE.
                ScheduleLog.admitNow(wake);
                throw interrupted;
            }
        }
    }

    /**
     * Under a prefix, blocks until this sleep's WAKE is admitted: the sleep
     * is then taken over and the caller skips the real one.  False when the
     * run went free before the turn came; the caller sleeps on.
     *
     * <p>An interrupt that arrives while it waits for its turn ends the wait
     * the way the real one would have ended: by throwing.</p>
     */
    private static ScheduleLog.Turn heldWake(String site)
            throws InterruptedException {
        ScheduleLog.Turn turn =
                ScheduleLog.awaitTurn(ScheduleEvent.Kind.WAKE, site);
        if (turn != ScheduleLog.Turn.ADMITTED) return turn;
        WakeScopes.woke(site);
        if (Thread.interrupted()) throw new InterruptedException();
        return turn;
    }

    private static void wake(String site) {
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        WakeScopes.woke(site);
    }
}
