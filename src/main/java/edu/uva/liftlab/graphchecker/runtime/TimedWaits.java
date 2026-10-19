package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.util.ArrayDeque;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Future;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.LockSupport;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public final class TimedWaits {
    private static final long QUANTUM_MS = 10L;
    private static final long EARLY_NANOS = TimeUnit.MICROSECONDS.toNanos(50L);

    private static final Map<Thread, Object> WAITING =
            new ConcurrentHashMap<Thread, Object>();
    private static final Set<Thread> WINDOW_WOKEN =
            ConcurrentHashMap.<Thread>newKeySet();
    private static final Object PARKED = new Object();

    private static final Map<Object, Waits> WAITS =
            new IdentityHashMap<Object, Waits>();

    private static final class Waiter {
        volatile boolean signalled;
        volatile boolean onTheClock;
        volatile long deadline;

        void clockUntil(long deadline) {
            this.deadline = deadline;
            this.onTheClock = true;
        }

        boolean expired() {
            return onTheClock && System.nanoTime() - deadline >= 0L;
        }
    }

    private static final class Waits {
        final ArrayDeque<Waiter> waiters = new ArrayDeque<Waiter>();
        long sent;
    }

    private TimedWaits() {
    }

    static void windowOpened() {
        for (Map.Entry<Thread, Object> waiting : WAITING.entrySet()) {
            WINDOW_WOKEN.add(waiting.getKey());
            Object on = waiting.getValue();
            if (on == PARKED) {
                LockSupport.unpark(waiting.getKey());
                continue;
            }
            synchronized (on) {
                touch(on);
                on.notifyAll();
            }
        }
    }


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
        if (timeout <= 0L) return;
        long millis = unit.toMillis(timeout);
        long nanos = unit.toNanos(timeout)
                - TimeUnit.MILLISECONDS.toNanos(millis);
        sleepFor(millis, (int) Math.max(0L, Math.min(999999L, nanos)), site);
    }

    private static void sleepFor(long millis, int nanos, String site)
            throws InterruptedException {
        if (millis <= 0L && nanos <= 0 || nanos > 999999) {
            Thread.sleep(millis, nanos);
            return;
        }
        WakeScopes.waiting();
        interruptedAtEntry(site);
        long deadline = System.nanoTime()
                + TimeUnit.MILLISECONDS.toNanos(millis) + nanos;
        if (ScheduleLog.enforcing() || freeSleep(deadline, site)) {
            takeTurn(site, false, sleepQuantum(), deadline);
            return;
        }
        wake(site);
    }

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


    public static void parkNanos(long nanos, String site) {
        park(null, nanos, site);
    }

    public static void parkNanos(Object blocker, long nanos, String site) {
        park(blocker, nanos, site);
    }

    private static void park(Object blocker, long nanos, String site) {
        if (nanos <= 0L) {
            LockSupport.parkNanos(blocker, nanos);
            return;
        }
        WakeScopes.waiting();
        if (Thread.currentThread().isInterrupted()) {
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
                interruptedWake(site);
                WakeScopes.woke(site);
                return;
            }
            signalled = !byWindow && System.nanoTime() - before < nanos;
        }
        try {
            takeTurn(site, signalled, parkQuantum(blocker), deadline);
        } catch (InterruptedException impossible) {
            Thread.currentThread().interrupt();
        }
    }

    private static Quantum parkQuantum(final Object blocker) {
        return new Quantum() {
            @Override
            boolean endsNow() {
                return Thread.currentThread().isInterrupted();
            }

            @Override
            boolean await(long millis) {
                long nanos = TimeUnit.MILLISECONDS.toNanos(millis);
                long before = System.nanoTime();
                LockSupport.parkNanos(blocker, nanos);
                if (Thread.currentThread().isInterrupted()) return false;
                return System.nanoTime() - before < nanos - EARLY_NANOS;
            }
        };
    }


    public static void waitOn(Object monitor, String site)
            throws InterruptedException {
        if (!Thread.holdsLock(monitor)) {
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

    public static void notifyOn(Object monitor, String site) {
        if (!Thread.holdsLock(monitor)) {
            monitor.notify();
            return;
        }
        if (send(monitor, false)) {
            monitor.notifyAll();
        } else {
            monitor.notify();
        }
    }

    public static void notifyAllOn(Object monitor, String site) {
        if (Thread.holdsLock(monitor)) send(monitor, true);
        monitor.notifyAll();
    }

    private static void monitorWait(Object monitor, long millis, int nanos,
                                    String site) throws InterruptedException {
        if (!Thread.holdsLock(monitor) || millis < 0L || nanos < 0
                || nanos > 999999) {
            monitor.wait(millis, nanos);
            return;
        }
        WakeScopes.waiting();
        if (millis == 0L && nanos == 0) {
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

    private interface Untimed {
        void await(Waiter self) throws InterruptedException;
    }

    private static void untimed(Object on, Untimed wait)
            throws InterruptedException {
        Waiter self = enter(on);
        try {
            while (!self.signalled) {
                long seen = sent(on);
                wait.await(self);
                if (!self.signalled && sent(on) == seen) {
                    return;
                }
            }
        } finally {
            leave(on, self);
        }
    }

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

    private static void waitMarked(Object monitor, long millis, Waiter self)
            throws InterruptedException {
        try {
            monitor.wait(millis);
        } catch (InterruptedException interrupted) {
            if (!self.signalled) throw interrupted;
            Thread.currentThread().interrupt();
        }
    }

    private static void interruptedAtEntry(String site)
            throws InterruptedException {
        if (!Thread.interrupted()) return;
        interruptedWake(site);
        throw new InterruptedException();
    }

    private static void interruptedWake(String site) {
        ScheduleLog.observe(ScheduleEvent.Kind.INTERRUPT, site);
    }

    private static void awaitMarked(Condition condition, Waiter self)
            throws InterruptedException {
        try {
            condition.await();
        } catch (InterruptedException interrupted) {
            if (!self.signalled) throw interrupted;
            Thread.currentThread().interrupt();
        }
    }

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


    public static long awaitNanos(Condition condition, long nanos,
                                  String site) throws InterruptedException {
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
            return outcome ? Math.max(1L, deadline - System.nanoTime()) : 0L;
        } finally {
            leave(condition, self);
        }
    }

    public static boolean await(Condition condition, long time,
                                TimeUnit unit, String site)
            throws InterruptedException {
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

    public static void await(Condition condition, String site)
            throws InterruptedException {
        untimed(condition, self -> awaitMarked(condition, self));
    }

    public static void awaitUninterruptibly(Condition condition,
                                            String site) {
        try {
            untimed(condition, self -> condition.awaitUninterruptibly());
        } catch (InterruptedException impossible) {
            Thread.currentThread().interrupt();
        }
    }

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

    private static long sent(Object on) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            return waits == null ? 0L : waits.sent;
        }
    }

    private static boolean send(Object on, boolean all) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            if (waits == null) return false;
            waits.sent++;
            for (Waiter waiter : waits.waiters) {
                if (waiter.signalled || waiter.expired()) continue;
                waiter.signalled = true;
                if (!all) break;
            }
            return true;
        }
    }

    private static void touch(Object on) {
        synchronized (WAITS) {
            Waits waits = WAITS.get(on);
            if (waits != null) waits.sent++;
        }
    }


    public static boolean timesOut(Object waitedOn, int permits,
                                   String marker) {
        try {
            String answered = answeredAtOnce(waitedOn, permits);
            if (answered == null) return true;
            if (!RecordingPlant.plantRefused(marker, answered)) {
                ActiveRegion active = ConcolicRegionRuntime.activeRegion();
                RowRuntime.gap(GapKind.ASSIGNMENT_UNPLANTED, GapClass.BLOCKING,
                        marker + (active == null ? "" : " at "
                                + active.address()), "the planted timeout "
                                + "cannot happen: " + answered + ", so the "
                                + "call ran");
            }
            return false;
        } catch (RuntimeException unreadable) {
            return true;
        }
    }

    static String answeredAtOnce(Object waitedOn, int permits) {
        if (Thread.currentThread().isInterrupted()) {
            return "the thread is interrupted, so the wait throws at once";
        }
        if (waitedOn instanceof CountDownLatch
                && ((CountDownLatch) waitedOn).getCount() == 0L) {
            return "the latch is open";
        }
        if (waitedOn instanceof Future && ((Future<?>) waitedOn).isDone()) {
            return "the future is done";
        }
        if (waitedOn instanceof BlockingQueue
                && !((BlockingQueue<?>) waitedOn).isEmpty()) {
            return "the queue holds an element";
        }
        if (waitedOn instanceof ReentrantLock
                && (((ReentrantLock) waitedOn).isHeldByCurrentThread()
                || !((ReentrantLock) waitedOn).isLocked())) {
            return "the lock is free or held by this thread";
        }
        if (waitedOn instanceof ReentrantReadWriteLock.WriteLock
                && ((ReentrantReadWriteLock.WriteLock) waitedOn)
                .isHeldByCurrentThread()) {
            return "the write lock is held by this thread";
        }
        if (waitedOn instanceof Semaphore
                && ((Semaphore) waitedOn).availablePermits() >= permits) {
            return "the semaphore has the permits";
        }
        return null;
    }


    public static Object poll(BlockingQueue<?> queue, long timeout,
                              TimeUnit unit, String site)
            throws InterruptedException {
        if (timeout <= 0L) return queue.poll(timeout, unit);
        WakeScopes.waiting();
        interruptedAtEntry(site);
        long deadline = System.nanoTime() + unit.toNanos(timeout);
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
                outlast(sleepQuantum(), deadline);
                WakeScopes.woke(site);
                return null;
            }
            wait = TimeUnit.MILLISECONDS.toNanos(QUANTUM_MS);
            if (turn == ScheduleLog.Turn.FREE
                    || turn == ScheduleLog.Turn.NO_EVENT) {
                wait = deadline - System.nanoTime();
                if (wait <= 0L) {
                    timedOut(sleepQuantum(), wake);
                    WakeScopes.woke(site);
                    return null;
                }
            }
        }
    }


    private abstract static class Quantum {
        abstract boolean await(long millis) throws InterruptedException;

        boolean signalled() {
            return false;
        }

        void onTheClock(long deadline) {
        }

        boolean endsNow() {
            return false;
        }
    }

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

    private static boolean takeTurn(String site, boolean signalled,
                                    Quantum quantum, long deadline)
            throws InterruptedException {
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
                outlast(quantum, deadline);
                WakeScopes.woke(site);
                return false;
            }
            long wait = QUANTUM_MS;
            if (turn == ScheduleLog.Turn.FREE
                    || turn == ScheduleLog.Turn.NO_EVENT) {
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
                interruptedWake(site);
                throw interrupted;
            }
        }
    }

    private static void timedOut(Quantum quantum, ScheduleLog.Wake wake) {
        boolean interrupted = false;
        while (!ScheduleLog.timedOut(wake)) {
            interrupted |= pause(quantum, QUANTUM_MS);
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    private static void outlast(Quantum quantum, long deadline) {
        quantum.onTheClock(System.nanoTime());
        boolean interrupted = false;
        for (long left = deadline - System.nanoTime(); left > 0L;
                left = deadline - System.nanoTime()) {
            interrupted |= pause(quantum, Math.max(1L,
                    (left + 999999L) / 1000000L));
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    private static boolean pause(Quantum quantum, long millis) {
        boolean interrupted = Thread.interrupted();
        try {
            quantum.await(millis);
        } catch (InterruptedException interrupt) {
            interrupted = true;
        }
        return interrupted;
    }

    private static void wake(String site) {
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        WakeScopes.woke(site);
    }
}
