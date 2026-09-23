package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * The schedule: what the recorder writes, and how the turnstile holds a
 * replay to a prefix -- order, timeout, release, and an interrupt that is the
 * workload's and not a divergence.
 */
public class ScheduleLogTest {
    private final List<JsonObject> written =
            Collections.synchronizedList(new ArrayList<JsonObject>());

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        ScheduleLog.resetForTests();
        RecordingWindow.open();
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        ScheduleLog.install(new ScheduleLog.Sink() {
            @Override
            public void write(JsonObject row) {
                written.add(row);
            }
        });
    }

    @After
    public void tearDown() {
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        ScheduleLog.resetForTests();
    }

    @Test
    public void anEventRoundTripsThroughItsRow() {
        ScheduleEvent event = ScheduleEvent.of(7L, ScheduleEvent.Kind.RECV,
                "hdfs/nn0#epoch0|Anchor:ab12@HADOOP_IPC/heartbeat",
                "HADOOP_IPC#REQUEST", 3, "occ-1");
        ScheduleEvent back = RowCodec.readScheduleEvent(RowCodec.fromLine(
                RowCodec.toLine(RowCodec.writeScheduleEvent(event))));
        assertEquals(event, back);
        assertEquals(event.key(), back.key());
        ScheduleEvent bare = ScheduleEvent.of(0L, ScheduleEvent.Kind.WAKE,
                "", "tick.KEY_MANAGER_TICK", 0, "");
        assertEquals(bare, RowCodec.readScheduleEvent(RowCodec.fromLine(
                RowCodec.toLine(RowCodec.writeScheduleEvent(bare)))));
    }

    @Test
    public void aTruncatedTailEndsTheReadThere() throws Exception {
        Path file = Files.createTempFile("schedule", ".jsonl");
        String one = RowCodec.toLine(RowCodec.writeScheduleEvent(
                ScheduleEvent.of(0L, ScheduleEvent.Kind.SEND, "c", "s", 0,
                        "")));
        Files.write(file, (one + "\n" + one.substring(0, one.length() / 2))
                .getBytes(StandardCharsets.UTF_8));
        assertEquals(1, SessionReader.readSchedule(file).size());
        Files.delete(file);
    }

    @Test
    public void theRecorderCountsKPerKeyAndDrainsWhatCameFirst() {
        ScheduleLog.resetForTests();
        written.clear();
        ScheduleLog.observe(ScheduleEvent.Kind.START, "<A: void a()>#u1");
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "HADOOP_IPC#REQUEST");
        ScheduleLog.install(new ScheduleLog.Sink() {
            @Override
            public void write(JsonObject row) {
                written.add(row);
            }
        });
        ScheduleLog.observe(ScheduleEvent.Kind.START, "<A: void a()>#u1");
        List<ScheduleEvent> events = events();
        assertEquals(3, events.size());
        assertEquals(Arrays.asList(0L, 1L, 2L), Arrays.asList(
                events.get(0).seq(), events.get(1).seq(),
                events.get(2).seq()));
        assertEquals(0, events.get(0).k());
        assertEquals(0, events.get(1).k());
        assertEquals(1, events.get(2).k());
    }

    @Test
    public void nothingIsRecordedBeforeTheWindowOpens() {
        RecordingWindow.reset();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "HADOOP_IPC#REQUEST");
        assertTrue(written.isEmpty());
    }

    @Test
    public void aThreadWhoseEventIsNotNextWaitsForItsTurn() throws Exception {
        ScheduleLog.enforceForTests(prefix("x", "y"));
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread late = new Thread(new Runnable() {
            @Override
            public void run() {
                waiting.countDown();
                ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
            }
        });
        late.start();
        waiting.await();
        Thread.sleep(200L);
        assertTrue("y must wait for x", written.isEmpty());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        late.join(5000L);
        assertFalse(late.isAlive());
        assertEquals(Arrays.asList("x", "y"), sites());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
        assertFalse("the prefix is used up", ScheduleLog.enforcing());
    }

    @Test
    public void aStalledSlotIsGivenUpAndAnEventTheOrderLacksRunsFree()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        ScheduleLog.enforceForTests(prefix("x", "z"));
        long before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "w");
        assertTrue("no slot holds w: it runs free at once",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 200L);
        Thread waiter = new Thread(new Runnable() {
            @Override
            public void run() {
                ScheduleLog.observe(ScheduleEvent.Kind.SEND, "z");
            }
        });
        waiter.start();
        waiter.join(10000L);
        assertFalse("the idle stall gives x up and z takes its slot",
                waiter.isAlive());
        assertEquals(Arrays.asList("w", "z"), sites());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains(" 1 given up"));
        assertFalse(ScheduleLog.enforcing());
        before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "q");
        assertTrue("a free run admits at once",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 200L);
    }

    @Test
    public void anInterruptedAdmissionTakesItsSlotAndTheOrderStands() throws Exception {
        ScheduleLog.enforceForTests(prefix("x", "y"));
        final boolean[] flagged = new boolean[1];
        Thread waiter = new Thread(new Runnable() {
            @Override
            public void run() {
                ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
                flagged[0] = Thread.currentThread().isInterrupted();
            }
        });
        waiter.start();
        Thread.sleep(200L);
        waiter.interrupt();
        waiter.join(5000L);
        assertFalse(waiter.isAlive());
        assertTrue("the interrupt is the workload's to see", flagged[0]);
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
        assertTrue("the prefix still stands", ScheduleLog.enforcing());
    }

    @Test
    public void aMonitorHoldingWaitAsksWithoutBlocking() {
        ScheduleLog.enforceForTests(Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "x"),
                event(ScheduleEvent.Kind.WAKE, "<L: void loop()>#u2")));
        ScheduleLog.Wake wake = ScheduleLog.wake("<L: void loop()>#u2");
        assertEquals(ScheduleLog.Turn.NOT_YET, ScheduleLog.turn(wake));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertEquals(ScheduleLog.Turn.ADMITTED, ScheduleLog.turn(wake));
        assertEquals(Arrays.asList("x", "<L: void loop()>#u2"), sites());
    }

    @Test
    public void aTimedWaitUnderThePrefixDoesNotReadTheWallClock()
            throws Exception {
        ScheduleLog.enforceForTests(Collections.singletonList(
                event(ScheduleEvent.Kind.WAKE, "<L: void loop()>#u9")));
        long before = System.nanoTime();
        TimedWaits.sleep(60000L, "<L: void loop()>#u9");
        assertTrue("virtual time: the turn came, the minute did not",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 5000L);
        assertEquals(Collections.singletonList("<L: void loop()>#u9"),
                sites());
    }

    @Test
    public void aWaitBegunBeforeTheWindowConvertsWhenItOpens()
            throws Exception {
        RecordingWindow.reset();
        final String site = "<L: void idle()>#u3";
        ScheduleLog.enforceForTests(Collections.singletonList(
                event(ScheduleEvent.Kind.WAKE, site)));
        final long[] took = new long[1];
        Thread idle = new Thread(new Runnable() {
            @Override
            public void run() {
                long before = System.nanoTime();
                try {
                    TimedWaits.sleep(60000L, site);
                } catch (InterruptedException interrupted) {
                    return;
                }
                took[0] = TimeUnit.NANOSECONDS.toMillis(
                        System.nanoTime() - before);
            }
        });
        idle.start();
        Thread.sleep(200L);
        assertTrue("before the window it waits on the wall clock",
                idle.isAlive());
        RecordingWindow.open();
        TimedWaits.windowOpened();
        idle.join(5000L);
        assertFalse("the window's opening converts it", idle.isAlive());
        assertTrue(took[0] < 5000L);
        assertEquals(Collections.singletonList(site), sites());
    }

    @Test
    public void aSignalledWaitIsNoEventAndATimedOutOneIs() throws Exception {
        final Object monitor = new Object();
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread woken = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    waiting.countDown();
                    try {
                        TimedWaits.waitOn(monitor, 60000L, "<C: void w()>#u1");
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                }
            }
        });
        woken.start();
        waiting.await();
        synchronized (monitor) {
            monitor.notifyAll();
        }
        woken.join(5000L);
        assertFalse(woken.isAlive());
        assertTrue("a notify ended it: another thread's doing, no turn",
                written.isEmpty());
        synchronized (monitor) {
            TimedWaits.waitOn(monitor, 50L, "<C: void t()>#u2");
        }
        assertEquals("its timeout ended this one: a turn",
                Collections.singletonList("<C: void t()>#u2"), sites());
    }

    @Test
    public void underAPrefixASignalEndsAWaitWithoutATurn() throws Exception {
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        Thread idle = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    try {
                        TimedWaits.waitOn(monitor, 60000L, site);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                }
            }
        });
        idle.start();
        Thread.sleep(200L);
        assertTrue("virtual time: the minute does not run out",
                idle.isAlive());
        synchronized (monitor) {
            monitor.notifyAll();
        }
        idle.join(5000L);
        assertFalse("the signal ends it at once", idle.isAlive());
        assertTrue("and it is no event", written.isEmpty());
        assertTrue("the prefix still stands", ScheduleLog.enforcing());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
    }

    @Test
    public void aWakeThePrefixSaysTimedOutNeedsNoSignal() throws Exception {
        final String site = "<L: void loop()>#u4";
        ScheduleLog.enforceForTests(Collections.singletonList(
                event(ScheduleEvent.Kind.WAKE, site)));
        final Object monitor = new Object();
        long before = System.nanoTime();
        synchronized (monitor) {
            TimedWaits.waitOn(monitor, 60000L, site);
        }
        assertTrue("virtual time: the turn came, the minute did not",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 5000L);
        assertEquals(Collections.singletonList(site), sites());
    }

    @Test
    public void aWaitNoSlotHoldsRunsOnTheWallClockAndGivesNothingUp()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        long before = System.nanoTime();
        synchronized (monitor) {
            TimedWaits.waitOn(monitor, 1500L, site);
        }
        assertTrue("its own deadline ended it",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        >= 1400L);
        assertEquals(Collections.singletonList(site), sites());
        assertTrue("x still holds", ScheduleLog.enforcing());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
    }

    @Test
    public void aHeldWaitOutlivesThePrefixOnTheWallClock() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        final boolean[] ended = new boolean[1];
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread idle = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    waiting.countDown();
                    try {
                        TimedWaits.waitOn(monitor, 60000L, site);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                    ended[0] = true;
                }
            }
        });
        idle.start();
        waiting.await();
        synchronized (monitor) {
            // The wait has entered it, held: the prefix still stands.
        }
        // The prefix's last event: the run is free from here.
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertFalse(ScheduleLog.enforcing());
        Thread.sleep(500L);
        assertTrue("the prefix's end is no timeout of this wait",
                idle.isAlive());
        synchronized (monitor) {
            assertFalse(ended[0]);
            TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
        }
        idle.join(5000L);
        assertFalse(idle.isAlive());
        assertEquals("a signal ended it: only the prefix's event is written",
                Collections.singletonList("x"), sites());
    }

    @Test
    public void aHeldPollOutlivesThePrefixAndTakesWhatArrives()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<S: void run()>#u12";
        ScheduleLog.enforceForTests(prefix("x"));
        final java.util.concurrent.BlockingQueue<Object> queue =
                new java.util.concurrent.LinkedBlockingQueue<Object>();
        final Object[] taken = new Object[1];
        Thread sender = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    taken[0] = TimedWaits.poll(queue, 60L, TimeUnit.SECONDS,
                            site);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        });
        sender.start();
        Thread.sleep(200L);
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        Thread.sleep(300L);
        assertTrue("the prefix's end is no timeout of this poll",
                sender.isAlive());
        queue.put("call");
        sender.join(5000L);
        assertFalse(sender.isAlive());
        assertEquals("call", taken[0]);
        assertEquals(Collections.singletonList("x"), sites());
    }

    @Test
    public void aNotifySentWhileAHeldWaitIsOutOfTheWaitSetIsNotLost()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread idle = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    waiting.countDown();
                    try {
                        TimedWaits.waitOn(monitor, 60000L, site);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                }
            }
        });
        idle.start();
        waiting.await();
        synchronized (monitor) {
            // Held longer than a quantum: the wait's quantum ends and it
            // stands outside the wait set, blocked on the monitor this
            // thread holds, when the notify is sent.
            Thread.sleep(200L);
            TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
        }
        idle.join(5000L);
        assertFalse("the notify was state the wait read", idle.isAlive());
        assertTrue("and it is no event", written.isEmpty());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
    }

    @Test
    public void theWindowsOpeningDoesNotSwallowASignalSentBeforeTheWaitSeesIt()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        RecordingWindow.reset();
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread idle = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    waiting.countDown();
                    try {
                        TimedWaits.waitOn(monitor, 60000L, site);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                }
            }
        });
        idle.start();
        waiting.await();
        synchronized (monitor) {
            // The wait is free, on the wall clock, in the wait set.
        }
        Thread.sleep(100L);
        synchronized (monitor) {
            RecordingWindow.open();
            // The opening takes the wait out of the wait set; the notify
            // that follows, before it can re-enter, reaches only its mark.
            TimedWaits.windowOpened();
            TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
        }
        idle.join(5000L);
        assertFalse("the call's notify ended the wait", idle.isAlive());
        assertTrue("a signal is no event", written.isEmpty());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
    }

    @Test
    public void aNotifyEndsOneWaitAndANotifyAllEndsEvery() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        List<Thread> first = heldWaits(monitor, 2);
        synchronized (monitor) {
            TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
        }
        Thread.sleep(300L);
        assertEquals("one notify, one wait ended", 1, alive(first));
        synchronized (monitor) {
            TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
        }
        join(first);
        assertEquals(0, alive(first));
        List<Thread> second = heldWaits(monitor, 2);
        synchronized (monitor) {
            TimedWaits.notifyAllOn(monitor, "<C: void n()>#u2");
        }
        join(second);
        assertEquals(0, alive(second));
        assertTrue(written.isEmpty());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
    }

    @Test
    public void aSignalSentWhileAHeldAwaitReacquiresTheLockIsNotLost()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<Q: java.lang.Object take()>#u8";
        ScheduleLog.enforceForTests(prefix("x"));
        final java.util.concurrent.locks.ReentrantLock lock =
                new java.util.concurrent.locks.ReentrantLock();
        final java.util.concurrent.locks.Condition ready = lock.newCondition();
        final boolean[] signalled = new boolean[1];
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread taker = new Thread(new Runnable() {
            @Override
            public void run() {
                lock.lock();
                try {
                    waiting.countDown();
                    signalled[0] = TimedWaits.await(ready, 60L,
                            TimeUnit.SECONDS, site);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                } finally {
                    lock.unlock();
                }
            }
        });
        taker.start();
        waiting.await();
        lock.lock();
        try {
            Thread.sleep(200L);
            TimedWaits.signal(ready, "<Q: void put(java.lang.Object)>#u2");
        } finally {
            lock.unlock();
        }
        taker.join(5000L);
        assertFalse("the signal was state the await read", taker.isAlive());
        assertTrue(signalled[0]);
        assertTrue(written.isEmpty());
    }

    @Test
    public void anUntimedWaitEndsByItsOwnNotifyAndNotByAnother()
            throws Exception {
        final Object monitor = new Object();
        final int[] ended = new int[1];
        List<Thread> waits = new ArrayList<Thread>();
        final CountDownLatch waiting = new CountDownLatch(2);
        for (int index = 0; index < 2; index++) {
            Thread thread = new Thread(new Runnable() {
                @Override
                public void run() {
                    synchronized (monitor) {
                        waiting.countDown();
                        try {
                            TimedWaits.waitOn(monitor, "<C: void w()>#u5");
                        } catch (InterruptedException interrupted) {
                            return;
                        }
                        ended[0]++;
                    }
                }
            });
            waits.add(thread);
            thread.start();
        }
        waiting.await();
        synchronized (monitor) {
            TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
        }
        Thread.sleep(300L);
        synchronized (monitor) {
            assertEquals("the notifyAll that carried it woke both; one left",
                    1, ended[0]);
            TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
        }
        join(waits);
        assertEquals(2, ended[0]);
    }

    @Test
    public void aTurnTheWindowSawBeginStatesItsEnd() {
        Object daemon = new Object();
        long tick = RuntimeTraceContext.beginTick(daemon, "HEARTBEAT_TICK");
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "HADOOP_IPC#REQUEST");
        RuntimeTraceContext.endTick(tick);
        List<ScheduleEvent> events = events();
        assertEquals(Arrays.asList(ScheduleEvent.Kind.WAKE,
                ScheduleEvent.Kind.SEND, ScheduleEvent.Kind.END),
                Arrays.asList(events.get(0).kind(), events.get(1).kind(),
                        events.get(2).kind()));
        assertEquals("the END stands in the turn's own context",
                events.get(0).context(), events.get(2).context());
        assertEquals("tick.HEARTBEAT_TICK", events.get(2).site());
    }

    @Test
    public void aTurnBegunBeforeTheWindowStatesNoEnd() {
        RecordingWindow.reset();
        long tick = RuntimeTraceContext.beginTick(new Object(),
                "BP_SERVICE_ACTOR");
        RecordingWindow.open();
        RuntimeTraceContext.endTick(tick);
        assertTrue("the set-up's turn is not the window's", written.isEmpty());
    }

    @Test
    public void aTurnsEndIsHeldToItsPlaceInThePrefix() throws Exception {
        // One free turn: its WAKE and END as this JVM computes them.  The
        // prefix below is a discovering run whose turn ended AFTER a send.
        final Object monitor = new Object();
        Thread turn = daemonTurn(monitor, null);
        turn.start();
        turn.join(5000L);
        List<ScheduleEvent> free = events();
        ScheduleEvent wake = free.get(0);
        ScheduleEvent end = free.get(1);
        assertEquals(ScheduleEvent.Kind.END, end.kind());

        written.clear();
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        ScheduleLog.resetForTests();
        ScheduleLog.install(new ScheduleLog.Sink() {
            @Override
            public void write(JsonObject row) {
                written.add(row);
            }
        });
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(Arrays.asList(wake,
                event(ScheduleEvent.Kind.SEND, "y"), end));
        final CountDownLatch ending = new CountDownLatch(1);
        Thread held = daemonTurn(monitor, ending);
        held.start();
        assertTrue(ending.await(5L, TimeUnit.SECONDS));
        Thread.sleep(200L);
        assertTrue("the turn's END waits for the send before it",
                held.isAlive());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
        held.join(5000L);
        assertFalse(held.isAlive());
        assertEquals(Arrays.asList("tick.HEARTBEAT_TICK", "y",
                "tick.HEARTBEAT_TICK"), sites());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
    }

    @Test
    public void aWaitAWovenNotifyMarkedKeepsItThroughAnInterrupt()
            throws Exception {
        final Object monitor = new Object();
        final String[] outcome = new String[2];
        final CountDownLatch waiting = new CountDownLatch(2);
        Thread first = untimedWaiter(monitor, outcome, 0, waiting);
        first.start();
        waitUntilWaiting(first);
        Thread second = untimedWaiter(monitor, outcome, 1, waiting);
        second.start();
        waiting.await();
        waitUntilWaiting(second);
        synchronized (monitor) {
            // The first wait leaves the wait set on its interrupt, and
            // stands on the monitor this thread holds when the notify comes.
            first.interrupt();
            Thread.sleep(200L);
            TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
        }
        first.join(5000L);
        second.join(300L);
        // JLS 17.2.4: a notify is never lost to an interrupt.  Either the
        // interrupted wait returns NORMALLY with its interrupt pending, or
        // it throws and the other wait is woken.
        boolean kept = "normal+interrupted".equals(outcome[0])
                || ("threw".equals(outcome[0]) && "normal".equals(outcome[1]));
        assertTrue("the notify was lost: " + Arrays.toString(outcome), kept);
        synchronized (monitor) {
            TimedWaits.notifyAllOn(monitor, "<C: void n()>#u1");
        }
        second.join(5000L);
        assertFalse(second.isAlive());
    }

    @Test
    public void aWaitTheWallClockEndedTakesNoNotify() throws Exception {
        final Object monitor = new Object();
        final String[] outcome = new String[2];
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread timed = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    try {
                        TimedWaits.waitOn(monitor, 100L, "<C: void t()>#u2");
                        outcome[0] = "returned";
                    } catch (InterruptedException interrupted) {
                        outcome[0] = "threw";
                    }
                }
            }
        });
        timed.start();
        waitUntilWaiting(timed);
        Thread untimed = untimedWaiter(monitor, outcome, 1, waiting);
        untimed.start();
        waiting.await();
        waitUntilWaiting(untimed);
        synchronized (monitor) {
            // The timed wait's 100 ms run out while this thread holds the
            // monitor: the JDK has taken it out of the wait set already.
            Thread.sleep(300L);
            TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
        }
        untimed.join(5000L);
        timed.join(5000L);
        assertEquals("the notify goes to the wait still in the wait set",
                "normal", outcome[1]);
        assertEquals("and the one the clock ended is a timeout, a WAKE",
                Collections.singletonList("<C: void t()>#u2"), sites());
    }

    @Test(timeout = 20000L)
    public void aSleepWithNoEventToMakeRunsOnTheWallClock() throws Exception {
        // A wait at a site the identity cannot name makes no event
        // (ScheduleLog.pending), so no order holds it.
        ScheduleLog.enforceForTests(prefix("x"));
        assertTrue(ScheduleLog.enforcing());
        long before = System.nanoTime();
        TimedWaits.sleep(300L, "");
        long took = TimeUnit.NANOSECONDS.toMillis(
                System.nanoTime() - before);
        assertTrue("neither skipped nor spun forever: " + took,
                took >= 250L && took < 5000L);
    }

    @Test
    public void observeSaysWhetherItWrote() {
        assertTrue(ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x"));
        RecordingWindow.reset();
        assertFalse(ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y"));
    }

    @Test
    public void aHeldWaitAnInterruptEndsWritesItsWake() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        final String[] outcome = new String[1];
        Thread held = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    try {
                        TimedWaits.waitOn(monitor, 60000L, site);
                        outcome[0] = "returned";
                    } catch (InterruptedException interrupted) {
                        outcome[0] = "threw";
                    }
                }
            }
        });
        held.start();
        waitUntilWaiting(held);
        held.interrupt();
        held.join(5000L);
        assertEquals("the interrupt ends the held wait by throwing", "threw",
                outcome[0]);
        assertEquals("and writes its INTERRUPT where it stands",
                Collections.singletonList(site), sites());
        assertEquals(ScheduleEvent.Kind.INTERRUPT, events().get(0).kind());
    }

    @Test
    public void aTimedWaitEnteredInterruptedThrowsEvenWhenItsTurnIsNext()
            throws Exception {
        final String site = "<L: void loop()>#u4";
        ScheduleLog.enforceForTests(Collections.singletonList(
                event(ScheduleEvent.Kind.WAKE, site)));
        final Object monitor = new Object();
        Thread.currentThread().interrupt();
        boolean threw = false;
        synchronized (monitor) {
            try {
                TimedWaits.waitOn(monitor, 60000L, site);
            } catch (InterruptedException interrupted) {
                threw = true;
            }
        }
        assertTrue("Object.wait entered interrupted throws, turn or no turn",
                threw);
        assertFalse("and clears the flag, as the JDK's does",
                Thread.currentThread().isInterrupted());

        java.util.concurrent.locks.ReentrantLock lock =
                new java.util.concurrent.locks.ReentrantLock();
        java.util.concurrent.locks.Condition ready = lock.newCondition();
        Thread.currentThread().interrupt();
        threw = false;
        lock.lock();
        try {
            TimedWaits.awaitNanos(ready, 0L, "<Q: void take()>#u8");
        } catch (InterruptedException interrupted) {
            threw = true;
        } finally {
            lock.unlock();
        }
        assertTrue("so does awaitNanos(0), as AQS's does", threw);
    }

    @Test
    public void aParkEnteredInterruptedReturnsAtOnceAndWritesNothing() {
        final String site = "<P: void spin()>#u3";
        Thread.currentThread().interrupt();
        long before = System.nanoTime();
        TimedWaits.parkNanos(TimeUnit.SECONDS.toNanos(10L), site);
        assertTrue("a park returns at once for an interrupted thread",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 5000L);
        assertTrue("and leaves the flag for its caller",
                Thread.interrupted());
        assertTrue("a loop around it would spin: no event per spin",
                written.isEmpty());
    }

    @Test
    public void aParkAnInterruptEndsWritesItsWakeFreeOrHeld()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<P: void spin()>#u3";
        for (boolean held : new boolean[] {false, true}) {
            written.clear();
            ScheduleLog.resetForTests();
            ScheduleLog.install(new ScheduleLog.Sink() {
                @Override
                public void write(JsonObject row) {
                    written.add(row);
                }
            });
            if (held) ScheduleLog.enforceForTests(prefix("x"));
            final boolean[] flagged = new boolean[1];
            Thread parker = new Thread(new Runnable() {
                @Override
                public void run() {
                    // JDK 8 hands a new thread a finished thread's park
                    // state with its permit still set: an inherited permit
                    // would return the first park at once, an unpark.
                    java.util.concurrent.locks.LockSupport.parkNanos(1L);
                    TimedWaits.parkNanos(TimeUnit.SECONDS.toNanos(20L), site);
                    flagged[0] = Thread.currentThread().isInterrupted();
                }
            });
            parker.start();
            waitUntilWaiting(parker);
            Thread.sleep(30L);
            parker.interrupt();
            parker.join(5000L);
            assertFalse(parker.isAlive());
            assertTrue("the park leaves the flag", flagged[0]);
            assertEquals((held ? "held" : "free") + ": the interrupt that "
                            + "ended the park writes its WAKE",
                    Collections.singletonList(site), sites());
        }
    }

    @Test
    public void aSleepOrPollEnteredInterruptedThrows() throws Exception {
        Thread.currentThread().interrupt();
        boolean threw = false;
        try {
            TimedWaits.sleep(0L, "<L: void loop()>#u9");
        } catch (InterruptedException interrupted) {
            threw = true;
        }
        assertTrue("Thread.sleep(0) throws on a pending interrupt", threw);
        Thread.currentThread().interrupt();
        threw = false;
        try {
            TimedWaits.poll(new java.util.concurrent.LinkedBlockingQueue<Object>(),
                    0L, TimeUnit.MILLISECONDS, "<S: void run()>#u12");
        } catch (InterruptedException interrupted) {
            threw = true;
        }
        assertTrue("so does a timed poll(0)", threw);
    }

    /** An untimed woven wait that writes how it ended into outcome[at]. */
    private static Thread untimedWaiter(final Object monitor,
                                        final String[] outcome, final int at,
                                        final CountDownLatch waiting) {
        return new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    waiting.countDown();
                    try {
                        TimedWaits.waitOn(monitor, "<C: void w()>#u5");
                        outcome[at] = Thread.currentThread().isInterrupted()
                                ? "normal+interrupted" : "normal";
                    } catch (InterruptedException interrupted) {
                        outcome[at] = "threw";
                    }
                }
            }
        });
    }

    /** Until the thread stands in a wait, the monitor it holds released. */
    private static void waitUntilWaiting(Thread thread)
            throws InterruptedException {
        for (int tries = 0; tries < 500; tries++) {
            Thread.State state = thread.getState();
            if (state == Thread.State.WAITING
                    || state == Thread.State.TIMED_WAITING) {
                return;
            }
            Thread.sleep(2L);
        }
    }

    /** One daemon turn on a thread of its own; counts down before its end. */
    private static Thread daemonTurn(final Object owner,
                                     final CountDownLatch ending) {
        return new Thread(new Runnable() {
            @Override
            public void run() {
                long tick = RuntimeTraceContext.beginTick(owner,
                        "HEARTBEAT_TICK");
                if (ending != null) ending.countDown();
                RuntimeTraceContext.endTick(tick);
            }
        });
    }

    /** {@code count} held waits on {@code monitor}, each standing. */
    private static List<Thread> heldWaits(final Object monitor, int count)
            throws InterruptedException {
        final CountDownLatch waiting = new CountDownLatch(count);
        List<Thread> threads = new ArrayList<Thread>();
        for (int index = 0; index < count; index++) {
            Thread thread = new Thread(new Runnable() {
                @Override
                public void run() {
                    synchronized (monitor) {
                        waiting.countDown();
                        try {
                            TimedWaits.waitOn(monitor, 60000L,
                                    "<C: void loop()>#u7");
                        } catch (InterruptedException interrupted) {
                            Thread.currentThread().interrupt();
                        }
                    }
                }
            });
            threads.add(thread);
            thread.start();
        }
        waiting.await();
        synchronized (monitor) {
            // Every wait has entered it.
        }
        return threads;
    }

    private static int alive(List<Thread> threads) {
        int alive = 0;
        for (Thread thread : threads) {
            if (thread.isAlive()) alive++;
        }
        return alive;
    }

    private static void join(List<Thread> threads)
            throws InterruptedException {
        for (Thread thread : threads) {
            thread.join(5000L);
        }
    }

    @Test
    public void pastThePrefixATimeoutWaitsForTheEventsItFollowed()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(prefix("x"), Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "a"),
                event(ScheduleEvent.Kind.WAKE, "tick.d")));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertTrue("the rest's timeout is still to come",
                ScheduleLog.enforcing());
        Thread daemon = observer(ScheduleEvent.Kind.WAKE, "tick.d");
        Thread.sleep(300L);
        assertTrue("the daemon's turn waits for what it followed",
                daemon.isAlive());
        assertEquals(Collections.singletonList("x"), sites());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "a");
        daemon.join(5000L);
        assertFalse(daemon.isAlive());
        assertEquals(Arrays.asList("x", "a", "tick.d"), sites());
        assertFalse("no timeout of the rest is still to come",
                ScheduleLog.enforcing());
    }

    @Test
    public void pastThePrefixEverythingButTheRestsTimeoutsRunsFree() {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(prefix("x"), Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "a"),
                event(ScheduleEvent.Kind.WAKE, "tick.d")));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        long before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "unnamed");
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.other");
        assertEquals(ScheduleLog.Turn.FREE,
                ScheduleLog.turn(ScheduleLog.wake("<L: void other()>#u1")));
        assertTrue("nothing the rest does not hold waits",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 200L);
        assertEquals(ScheduleLog.Turn.NOT_YET,
                ScheduleLog.turn(ScheduleLog.wake("tick.d")));
        assertEquals(Arrays.asList("x", "unnamed", "tick.other"), sites());
        assertTrue(ScheduleLog.enforcing());
    }

    @Test
    public void theRestGivesUpOnlyWhatCameBeforeTheEarliestWaitingTimeout()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "1000");
        ScheduleLog.enforceForTests(prefix("x"), Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "never"),
                event(ScheduleEvent.Kind.WAKE, "tick.d"),
                event(ScheduleEvent.Kind.SEND, "y"),
                event(ScheduleEvent.Kind.WAKE, "tick.e")));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        Thread later = observer(ScheduleEvent.Kind.WAKE, "tick.e");
        Thread earlier = observer(ScheduleEvent.Kind.WAKE, "tick.d");
        earlier.join(10000L);
        assertFalse("the earliest waiting timeout gives up what it followed",
                earlier.isAlive());
        assertTrue("the later one still waits for y, which is no older than"
                + " the give-up", later.isAlive());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
        later.join(5000L);
        assertFalse(later.isAlive());
        assertEquals(Arrays.asList("x", "tick.d", "y", "tick.e"), sites());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains(" 1 given up"));
    }

    @Test
    public void aStalledPrefixGivesUpOnlyWhatIsBeforeTheEarliestWaiter()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        ScheduleLog.enforceForTests(Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "never"),
                event(ScheduleEvent.Kind.WAKE, "tick.d"),
                event(ScheduleEvent.Kind.SEND, "y")),
                Collections.singletonList(
                        event(ScheduleEvent.Kind.WAKE, "tick.e")));
        Thread daemon = observer(ScheduleEvent.Kind.WAKE, "tick.d");
        daemon.join(10000L);
        assertFalse(daemon.isAlive());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains(" 1 given up"));
        assertTrue("tick.e is still to come", ScheduleLog.enforcing());
        Thread other = observer(ScheduleEvent.Kind.WAKE, "tick.e");
        Thread.sleep(100L);
        assertTrue("tick.e follows y", other.isAlive());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
        other.join(5000L);
        assertFalse(other.isAlive());
        assertEquals(Arrays.asList("tick.d", "y", "tick.e"), sites());
        assertFalse(ScheduleLog.enforcing());
    }

    @Test
    public void aSleepTheRestDoesNotNameRunsOnTheWallClock()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<L: void loop()>#u9";
        ScheduleLog.enforceForTests(prefix("x"), Collections.singletonList(
                event(ScheduleEvent.Kind.WAKE, "tick.d")));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        long before = System.nanoTime();
        TimedWaits.sleep(500L, site);
        long took = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before);
        assertTrue("to its own deadline, not at once: " + took,
                took >= 450L);
        assertTrue("and not held for the rest: " + took, took < 5000L);
        assertEquals(Arrays.asList("x", site), sites());
    }

    @Test
    public void aHeldWaitPastThePrefixTakesItsTurnFromTheRest()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"), Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "a"),
                event(ScheduleEvent.Kind.WAKE, site)));
        final Object monitor = new Object();
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread idle = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    waiting.countDown();
                    try {
                        TimedWaits.waitOn(monitor, 60000L, site);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                }
            }
        });
        long before = System.nanoTime();
        idle.start();
        waiting.await();
        synchronized (monitor) {
            // The wait has entered it, held.
        }
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        Thread.sleep(300L);
        assertTrue("past the prefix its timeout follows a", idle.isAlive());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "a");
        idle.join(5000L);
        assertFalse(idle.isAlive());
        assertTrue("virtual time, not its 60 s",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 10000L);
        assertEquals(Arrays.asList("x", "a", site), sites());
    }

    @Test
    public void aStallGivesUpOnlyTheSlotThatNeverCame()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        for (int round = 0; round < 5; round++) {
            written.clear();
            ScheduleLog.resetForTests();
            ScheduleLog.install(new ScheduleLog.Sink() {
                @Override
                public void write(JsonObject row) {
                    written.add(row);
                }
            });
            ScheduleLog.enforceForTests(Arrays.asList(
                    event(ScheduleEvent.Kind.SEND, "never"),
                    event(ScheduleEvent.Kind.SEND, "refresh"),
                    event(ScheduleEvent.Kind.WAKE, "tick.hb")));
            // Whichever of them the watchdog wakes first, the heartbeat
            // does not jump the refresh the prefix held back.
            Thread heartbeat = observer(ScheduleEvent.Kind.WAKE, "tick.hb");
            Thread refresh = observer(ScheduleEvent.Kind.SEND, "refresh");
            heartbeat.join(5000L);
            refresh.join(5000L);
            assertFalse(heartbeat.isAlive() || refresh.isAlive());
            assertEquals("round " + round,
                    Arrays.asList("refresh", "tick.hb"), sites());
        }
    }

    @Test
    public void aTurnsEndSettlesWhatTheTurnDidNotDo() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(prefix("x"), Arrays.asList(
                event(ScheduleEvent.Kind.WAKE, "tick.a"),
                event(ScheduleEvent.Kind.SEND, "heartbeat"),
                event(ScheduleEvent.Kind.START, "call"),
                event(ScheduleEvent.Kind.END, "tick.a"),
                event(ScheduleEvent.Kind.WAKE, "tick.b")));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        long before = System.nanoTime();
        // The turn found its heartbeat not due: WAKE, then END.
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.a");
        ScheduleLog.observe(ScheduleEvent.Kind.END, "tick.a");
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.b");
        assertTrue("the next turn does not wait for what this one skipped",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 1000L);
        assertEquals(Arrays.asList("x", "tick.a", "tick.a", "tick.b"),
                sites());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains("2 settled"));
    }

    @Test
    public void theRestIsLetGoAfterItsStalls() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        List<ScheduleEvent> after = new ArrayList<ScheduleEvent>();
        for (int turn = 1; turn <= 4; turn++) {
            after.add(event(ScheduleEvent.Kind.SEND, "never" + turn));
            after.add(event(ScheduleEvent.Kind.WAKE, "tick.d" + turn));
        }
        ScheduleLog.enforceForTests(prefix("x"), after);
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        for (int turn = 1; turn <= ScheduleLog.REST_STALLS; turn++) {
            ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.d" + turn);
            assertTrue("stall " + turn + " holds", ScheduleLog.enforcing());
        }
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE,
                "tick.d" + (ScheduleLog.REST_STALLS + 1));
        assertFalse("the stall after them lets the rest go",
                ScheduleLog.enforcing());
        long before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.d4");
        assertTrue(TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                < 200L);
    }

    @Test
    public void aWaitASignalEndedNoLongerDefersAGiveUp() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "400");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"), Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "never"),
                event(ScheduleEvent.Kind.WAKE, site),
                event(ScheduleEvent.Kind.SEND, "never2"),
                event(ScheduleEvent.Kind.WAKE, "tick.e")));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        final Object monitor = new Object();
        Thread idle = new Thread(new Runnable() {
            @Override
            public void run() {
                synchronized (monitor) {
                    try {
                        TimedWaits.waitOn(monitor, 60000L, site);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                }
            }
        });
        idle.start();
        Thread.sleep(200L);
        synchronized (monitor) {
            TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
        }
        idle.join(5000L);
        assertFalse(idle.isAlive());
        long before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.e");
        long took = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before);
        assertTrue("released by the watchdog, not by an ask gone stale: "
                + took, took < 5000L);
        assertEquals(Arrays.asList("x", "tick.e"), sites());
    }

    @Test
    public void anOccurrencesCloseSettlesWhatItDidNotMake() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        // The recording: a send inside occurrence o1 that the replay never
        // makes (a stale connection's attempt), a connection set-up, then
        // the retry's send inside o2.
        ScheduleLog.enforceForTests(Arrays.asList(
                inOccurrence(ScheduleEvent.Kind.SEND, "req", "o1"),
                event(ScheduleEvent.Kind.START, "conn"),
                inOccurrence(ScheduleEvent.Kind.SEND, "req", "o2")));
        Thread setUp = observer(ScheduleEvent.Kind.START, "conn");
        Thread.sleep(200L);
        assertTrue("conn waits for the slot before it", setUp.isAlive());
        long before = System.nanoTime();
        ScheduleLog.closed("o1");
        setUp.join(5000L);
        assertFalse(setUp.isAlive());
        assertTrue("no watchdog: the close settled it",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 2000L);
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "req");
        assertEquals(Arrays.asList("conn", "req"), sites());
        assertFalse("the retry took o2's slot, not the dead one",
                ScheduleLog.enforcing());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains(" 1 settled by their"
                        + " occurrence's close"));
    }

    @Test
    public void aComputingRunIsNoStall() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        ScheduleLog.enforceForTests(Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "x"),
                event(ScheduleEvent.Kind.WAKE, "tick.d")));
        Thread daemon = observer(ScheduleEvent.Kind.WAKE, "tick.d");
        // The thread that makes x computes for well past the timeout.
        long until = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(1800L);
        long sink = 0L;
        while (System.nanoTime() < until) sink += System.nanoTime() % 7L;
        assertTrue(sink >= 0L);
        assertTrue("the daemon still waits: computing is progress",
                daemon.isAlive());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        daemon.join(5000L);
        assertFalse(daemon.isAlive());
        assertEquals(Arrays.asList("x", "tick.d"), sites());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress().contains(" 0 given up"));
    }

    @Test
    public void aWaitTheRecordingSawInterruptedIsNoTurnOfTime()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<D: void run()>#u29";
        ScheduleLog.enforceForTests(Collections.singletonList(
                event(ScheduleEvent.Kind.INTERRUPT, site)));
        final boolean[] threw = new boolean[1];
        Thread daemon = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    TimedWaits.sleep(60000L, site);
                } catch (InterruptedException interrupted) {
                    threw[0] = true;
                }
            }
        });
        daemon.start();
        Thread.sleep(300L);
        assertTrue("no WAKE slot: virtual time does not end it",
                daemon.isAlive());
        daemon.interrupt();
        daemon.join(5000L);
        assertTrue(threw[0]);
        assertEquals(ScheduleEvent.Kind.INTERRUPT, events().get(0).kind());
        assertFalse("the INTERRUPT took its slot", ScheduleLog.enforcing());
    }

    /** One event of this thread's context inside a recorded occurrence. */
    private static ScheduleEvent inOccurrence(ScheduleEvent.Kind kind,
                                              String site, String occurrence) {
        return ScheduleEvent.of(0L, kind, ScheduleLog.contextHere(), site, 0,
                occurrence);
    }

    /** A thread that makes one event, blocking for its turn; started. */
    private static Thread observer(final ScheduleEvent.Kind kind,
                                   final String site) {
        Thread thread = new Thread(new Runnable() {
            @Override
            public void run() {
                ScheduleLog.observe(kind, site);
            }
        });
        thread.start();
        return thread;
    }

    /** A prefix of SEND events at these sites, on this thread's context. */
    private static List<ScheduleEvent> prefix(String... sites) {
        List<ScheduleEvent> events = new ArrayList<ScheduleEvent>();
        for (String site : sites) {
            events.add(event(ScheduleEvent.Kind.SEND, site));
        }
        return events;
    }

    /**
     * One event as this JVM's threads compute it: none of them is attributed
     * to a node, so every one of them states the same context.
     */
    private static ScheduleEvent event(ScheduleEvent.Kind kind, String site) {
        return ScheduleEvent.of(0L, kind, ScheduleLog.contextHere(), site, 0,
                "");
    }

    private List<ScheduleEvent> events() {
        List<ScheduleEvent> events = new ArrayList<ScheduleEvent>();
        synchronized (written) {
            for (JsonObject row : written) {
                events.add(RowCodec.readScheduleEvent(row));
            }
        }
        return events;
    }

    private List<String> sites() {
        List<String> sites = new ArrayList<String>();
        for (ScheduleEvent event : events()) {
            sites.add(event.site());
        }
        return sites;
    }
}
