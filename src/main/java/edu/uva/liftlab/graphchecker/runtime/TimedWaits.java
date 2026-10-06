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
 * thread the next turn.  The weave replaces every timed-wait call
 * ({@code WorkStartSites.timedWait}) with the method of the same shape here,
 * in BOTH passes; receiver first, call site last.
 *
 * <ul>
 *   <li>FREE (recording, no order, no WAKE slot, before the window): the
 *       original semantics on the wall clock, and a WAKE only when the
 *       TIMEOUT ends it ({@link #takeTurn}).</li>
 *   <li>HELD (a WAKE slot holds its timeout): VIRTUAL TIME stands in for
 *       the CLOCK, never for the NOTIFIER.  It ends at a real signal or when
 *       its slot is due; between asks it waits on its own primitive, so what
 *       it holds is released.  A wait with no slot the prefix still holds
 *       (unrecorded, or past its recorded count) ends at a real signal or
 *       when the order lets it go, then on its own deadline.</li>
 *   <li>NO WAIT (a timeout that is not positive): the JDK's call, and
 *       nothing else.  It returns at once and its loop spins, so an event
 *       per call would differ run to run; held, a {@code poll(0)} would miss
 *       the hand-off it exists for (a DataNode proxy's IPC sender polls its
 *       SynchronousQueue at maxIdleTime 0).</li>
 * </ul>
 *
 * <p>A wait in progress when the window opens is woken ({@link
 * #windowOpened}) and from then on held.  A poll's returned element is a
 * CLAIM ({@code Identity.claimStart}), never a WAKE.</p>
 *
 * <p>A SIGNAL IS STATE.  A held wait leaves the wait set every quantum, so a
 * notify in that gap would be lost.  Hence notifiers are woven too and each
 * monitor or condition wait registers for its whole length: a notify marks
 * the longest-standing unmarked wait, a notifyAll every one, and the wait
 * reads its mark.</p>
 *
 * <p>AN INTERRUPT IS THE WORKLOAD'S: it writes an INTERRUPT where the wait
 * stands, never held, and throws as the JDK would (a park returns).</p>
 *
 * <p>LIMIT: an unwoven notify on an application monitor is invisible to the
 * registry, so a later woven notify may mark the wait it already woke.</p>
 */
public final class TimedWaits {
    /** How long a wait polls between asks for its turn, in ms. */
    private static final long QUANTUM_MS = 10L;
    /**
     * Returning this early with no woven signal or window wake sent means a
     * notifier outside the weave (or an unpark).
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
     * Waits and signals per monitor or condition.  Guarded by itself, the
     * INNERMOST lock: never held while taking an application lock.
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

        /** No slot holds the wait: it stands on the wall clock. */
        void clockUntil(long deadline) {
            this.deadline = deadline;
            this.onTheClock = true;
        }

        /** The JDK already took it out of the wait set at its timeout. */
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
     * The window opened under an order: every free wait is woken (marked first,
     * so it is no signal) and converts to virtual time.  Called with no lock of
     * this runtime held.
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
                // Counted as sent: no other wait reads it as a notifier's.
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
        // NO WAIT: TimeUnit.sleep does nothing at all.
        if (timeout <= 0L) return;
        long millis = unit.toMillis(timeout);
        long nanos = unit.toNanos(timeout)
                - TimeUnit.MILLISECONDS.toNanos(millis);
        sleepFor(millis, (int) Math.max(0L, Math.min(999999L, nanos)), site);
    }

    /**
     * A sleep: wall clock while free, held to its turn once enforced.  Nothing
     * signals a sleep, so its WAKE is always its timeout.
     */
    private static void sleepFor(long millis, int nanos, String site)
            throws InterruptedException {
        if (millis <= 0L && nanos <= 0 || nanos > 999999) {
            // The JDK's own refusal, or NO WAIT: sleep(0) only yields, and
            // throws on a pending interrupt.
            Thread.sleep(millis, nanos);
            return;
        }
        WakeScopes.waiting();
        // Thread.sleep throws on a pending interrupt, even sleep(0).
        interruptedAtEntry(site);
        long deadline = System.nanoTime()
                + TimeUnit.MILLISECONDS.toNanos(millis) + nanos;
        if (ScheduleLog.enforcing() || freeSleep(deadline, site)) {
            // Held: its turn, or the wall clock once no slot holds it.
            takeTurn(site, false, sleepQuantum(), deadline);
            return;
        }
        wake(site);
    }

    /** A sleep's quantum: only time or an interrupt ends it. */
    private static Quantum sleepQuantum() {
        final Object lock = new Object();
        return new Quantum() {
            @Override
            boolean await(long millis) throws InterruptedException {
                synchronized (lock) {
                    lock.wait(Math.max(1L, millis));
                }
                return false;
            }
        };
    }

    /** Sleeps on the wall clock; true when the window opened first. */
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

    /** A park: free on the wall clock, held until an unpark or its turn. */
    private static void park(Object blocker, long nanos, String site) {
        if (nanos <= 0L) {
            // NO WAIT.
            LockSupport.parkNanos(blocker, nanos);
            return;
        }
        WakeScopes.waiting();
        if (Thread.currentThread().isInterrupted()) {
            // An interrupted park returns at once and its loop spins: no event,
            // or no two runs would write the same number.
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
                // Interrupted while parked: its WAKE is written in place.
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
                // An interrupted thread's park returns at once.
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
     * A notify: marks the longest-standing unmarked wait, then notifies all;
     * the unchosen go back to waiting.
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
        WakeScopes.waiting();
        if (millis == 0L && nanos == 0) {
            // wait(0) has no timeout, so no turn of time's.
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

    private static void untimedMonitorWait(Object monitor)
            throws InterruptedException {
        untimed(monitor, self -> waitMarked(monitor, 0L, self));
    }

    /** One physical untimed wait of a registered waiter. */
    private interface Untimed {
        void await(Waiter self) throws InterruptedException;
    }

    /** An untimed wait, registered so a woven signal meant for it is kept. */
    private static void untimed(Object on, Untimed wait)
            throws InterruptedException {
        Waiter self = enter(on);
        try {
            while (!self.signalled) {
                long seen = sent(on);
                wait.await(self);
                if (!self.signalled && sent(on) == seen) {
                    // Outside notifier or spurious wakeup: caller re-checks.
                    return;
                }
            }
        } finally {
            leave(on, self);
        }
    }

    /** One free timed monitor wait; true when a signal ended it. */
    private static boolean freeMonitorWait(Object monitor, Waiter self,
                                           long deadline, String site)
            throws InterruptedException {
        Thread thread = Thread.currentThread();
        WINDOW_WOKEN.remove(thread);
        WAITING.put(thread, monitor);
        self.clockUntil(deadline);
        try {
            while (true) {
                if (self.signalled) return true;
                // Asked after entering WAITING: sees a window opened meanwhile.
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
                    // Early with nothing sent: a notifier outside the weave.
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
     * One physical wait ({@code millis} 0 is untimed).  A MARKED wait that is
     * interrupted returns normally with the interrupt pending: throwing would
     * lose the notify (JLS 17.2.4).
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
     * A timed wait entered interrupted throws at once, as the JDK's does,
     * before any turn is asked; its INTERRUPT is written first ({@link
     * #interruptedWake}).
     */
    private static void interruptedAtEntry(String site)
            throws InterruptedException {
        if (!Thread.interrupted()) return;
        interruptedWake(site);
        throw new InterruptedException();
    }

    /** THE INTERRUPT OF A WAIT, free or held: written in place, never held. */
    private static void interruptedWake(String site) {
        ScheduleLog.observe(ScheduleEvent.Kind.INTERRUPT, site);
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

    /** {@link #waitMarked}'s rule for a timed await; states time left. */
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
        return new Registered(self) {
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
        // NO WAIT.
        if (nanos <= 0L) return condition.awaitNanos(nanos);
        WakeScopes.waiting();
        interruptedAtEntry(site);
        long deadline = System.nanoTime() + nanos;
        Waiter self = enter(condition);
        try {
            boolean signalled =
                    freeConditionWait(condition, self, deadline, site);
            boolean outcome = takeTurn(site, signalled,
                    conditionQuantum(condition, self), deadline);
            // Virtual time: the caller re-checks its condition.
            return outcome ? Math.max(1L, deadline - System.nanoTime()) : 0L;
        } finally {
            leave(condition, self);
        }
    }

    public static boolean await(Condition condition, long time,
                                TimeUnit unit, String site)
            throws InterruptedException {
        // NO WAIT.
        if (time <= 0L) return condition.await(time, unit);
        WakeScopes.waiting();
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

    /** An untimed condition wait: {@link #untimed}'s rule. */
    public static void await(Condition condition, String site)
            throws InterruptedException {
        untimed(condition, self -> awaitMarked(condition, self));
    }

    public static void awaitUninterruptibly(Condition condition,
                                            String site) {
        try {
            untimed(condition, self -> condition.awaitUninterruptibly());
        } catch (InterruptedException impossible) {
            // awaitUninterruptibly never throws it.
            Thread.currentThread().interrupt();
        }
    }

    /**
     * A signal: {@link #notifyOn}'s rule.  The real signal goes first, so a
     * caller without the lock is refused before any mark is set.
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

    /** The free part of a timed condition wait, in quanta; true on a signal. */
    private static boolean freeConditionWait(Condition condition,
                                             Waiter self, long deadline,
                                             String site)
            throws InterruptedException {
        self.clockUntil(deadline);
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
        return new Registered(self) {
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

    /** Marks the longest-standing unmarked wait, or all; true if any stood. */
    private static boolean send(Object on, boolean all) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            if (waits == null) return false;
            waits.sent++;
            for (Waiter waiter : waits.waiters) {
                // A wait its clock already ended is out of the JDK's wait set.
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
        // NO WAIT: poll(0) takes what is offered right now.
        if (timeout <= 0L) return queue.poll(timeout, unit);
        WakeScopes.waiting();
        // The JDK's timed poll takes its lock interruptibly.
        interruptedAtEntry(site);
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        // Free, in quanta.  A returned element is a CLAIM, not a WAKE.
        while (!ScheduleLog.enforcing()) {
            long left = deadline - System.nanoTime();
            if (left <= 0L) {
                wake(site);
                return null;
            }
            Object element;
            try {
                element = queue.poll(Math.min(left,
                        TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS)),
                        TimeUnit.NANOSECONDS);
            } catch (InterruptedException interrupted) {
                interruptedWake(site);
                throw interrupted;
            }
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
            Object element;
            try {
                element = queue.poll(wait, TimeUnit.NANOSECONDS);
            } catch (InterruptedException interrupted) {
                interruptedWake(site);
                throw interrupted;
            }
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
                    timedOut(sleepQuantum(), wake);
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

        /** No slot holds the wait any more: it stands on the wall clock. */
        void onTheClock(long deadline) {
        }

        /** Only an interrupted park, which cannot throw, must end now. */
        boolean endsNow() {
            return false;
        }
    }

    /** A registered wait's quantum: its mark is its signal. */
    private abstract static class Registered extends Quantum {
        private final Waiter self;

        Registered(Waiter self) {
            this.self = self;
        }

        @Override
        boolean signalled() {
            return self.signalled;
        }

        @Override
        void onTheClock(long deadline) {
            self.clockUntil(deadline);
        }
    }

    /**
     * Ends one wait; true when a signal ended it.
     *
     * <p>Only a TIMEOUT is a WAKE.  A signal is another thread's doing, which
     * the schedule already orders; holding a replay to a recorded signal waits
     * for one that may never come.</p>
     *
     * <p>Held, the wait asks every quantum (which also drives the watchdog) and
     * ends at a signal or when its WAKE slot is due.  With no slot left it is
     * held for as long as the order holds it (a poll past its recorded count
     * waits for the order to move, {@code ScheduleLog#waitsAtLocked}), then
     * waits out its own deadline on the wall clock ({@code ScheduleLog.turn},
     * {@code timedOut}): a poll never comes sooner than its timeout.  Its
     * WAKE then asks for its turn the same way ({@link #timedOut}), never
     * holding what the wait released.</p>
     */
    private static boolean takeTurn(String site, boolean signalled,
                                    Quantum quantum, long deadline)
            throws InterruptedException {
        // Null: no window or no name; ends as a free wait.
        ScheduleLog.Wake wake = ScheduleLog.wake(site);
        try {
            return turns(site, signalled, quantum, deadline, wake);
        } finally {
            ScheduleLog.withdraw(wake);
        }
    }

    private static boolean turns(String site, boolean signalled,
                                 Quantum quantum, long deadline,
                                 ScheduleLog.Wake wake)
            throws InterruptedException {
        while (true) {
            if (quantum.endsNow()) {
                // Interrupt first: it beats an unpark.
                interruptedWake(site);
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
                // No slot holds it: its own deadline, on the wall clock.
                quantum.onTheClock(deadline);
                long left = deadline - System.nanoTime();
                if (left <= 0L) {
                    timedOut(quantum, wake);
                    WakeScopes.woke(site);
                    return false;
                }
                wait = Math.max(1L, (left + 999999L) / 1000000L);
            }
            try {
                if (quantum.await(wait)) signalled = true;
            } catch (InterruptedException interrupted) {
                // Interrupted: its INTERRUPT is written here.
                interruptedWake(site);
                throw interrupted;
            }
        }
    }

    /**
     * A wait the wall clock ended: its WAKE asks for its turn every quantum,
     * the quantum spent on the wait's own primitive, so the monitor or lock
     * the wait released stays released until the WAKE is written ({@code
     * ScheduleLog#timedOut}).  A signal meanwhile changes nothing: the wait
     * already ran its time out, and its caller re-checks.  An interrupt
     * meanwhile is kept pending, as a wait that has ended keeps one.
     */
    private static void timedOut(Quantum quantum, ScheduleLog.Wake wake) {
        boolean interrupted = false;
        while (!ScheduleLog.timedOut(wake)) {
            try {
                quantum.await(QUANTUM_MS);
            } catch (InterruptedException interrupt) {
                interrupted = true;
            }
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    private static void wake(String site) {
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        WakeScopes.woke(site);
    }
}
