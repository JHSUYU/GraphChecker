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
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.LockSupport;
import java.util.concurrent.locks.ReentrantLock;
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
    private final ScheduleLog.Sink writer = new ScheduleLog.Sink() {
        @Override
        public void write(JsonObject row) {
            written.add(row);
        }
    };

    /**
     * The node every test's threads run for.  An event with no identity
     * holds no place in the order, so the test thread opens one request and
     * every thread a test starts inherits it, as work a request starts does:
     * they all state one context.
     */
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private long request;

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        ScheduleLog.resetForTests();
        openRequest();
        RecordingWindow.open();
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        ScheduleLog.install(writer);
    }

    /** The test's one request, on a freshly reset runtime. */
    private void openRequest() {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        request = RuntimeTraceContext.beginRequest(node, "schedule-test");
    }

    /** A fresh schedule, written into {@link #written} again. */
    private void restart() {
        written.clear();
        ScheduleLog.resetForTests();
        ScheduleLog.install(writer);
    }

    @After
    public void tearDown() {
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        ScheduleLog.resetForTests();
        if (request != 0L) RuntimeTraceContext.endRequest(request);
    }

    @Test
    public void anEventWithNoIdentityHoldsNoPlace() {
        RuntimeTraceContext.endRequest(request);
        request = 0L;
        assertTrue(Identity.contextHere().isLost());
        ScheduleLog.observe(ScheduleEvent.Kind.START, "<A: void a()>#u1");
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "HADOOP_IPC#REQUEST");
        assertTrue("every unattributed thread shares one context, so its k "
                + "would be a cross-thread counter: " + events(),
                written.isEmpty());
    }

    /**
     * A response stands where its request was received, whichever thread
     * sends it: a thread serving other work (a deferred RPC response's
     * sender) writes it under the receipt's context, not its own.
     */
    @Test
    public void aResponseStandsWhereItsRequestWasReceived() throws Exception {
        ScheduleLog.Stance receipt = ScheduleLog.stanceHere();
        ScheduleLog.observe(ScheduleEvent.Kind.RECV, "HADOOP_IPC#REQUEST");
        Object other = new Object();
        RuntimeTraceContext.registerSource(other, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "t/dn1", 0L));
        Thread sender = new Thread(() -> {
            long own = RuntimeTraceContext.beginRequest(other, "sync");
            ScheduleLog.observe(ScheduleEvent.Kind.START, "<A: void a()>#u1");
            ScheduleLog.observe(ScheduleEvent.Kind.SEND,
                    "HADOOP_IPC#RESPONSE", "endpoint-at-receipt", receipt);
            RuntimeTraceContext.endRequest(own);
        });
        sender.start();
        sender.join();
        List<ScheduleEvent> events = events();
        assertEquals(3, events.size());
        assertFalse("the sender has a context of its own",
                events.get(0).context().equals(events.get(1).context()));
        assertEquals(events.get(0).context(), events.get(2).context());
        assertEquals("endpoint-at-receipt", events.get(2).endpoint());
    }

    /** An event survives its row, and a torn last row ends the read. */
    @Test
    public void aTruncatedTailEndsTheReadThere() throws Exception {
        ScheduleEvent event = ScheduleEvent.of(7L, ScheduleEvent.Kind.RECV,
                "hdfs/nn0#epoch0|Anchor:ab12@HADOOP_IPC/heartbeat",
                "HADOOP_IPC#REQUEST", 3, "occ-1");
        ScheduleEvent bare = ScheduleEvent.of(0L, ScheduleEvent.Kind.WAKE,
                "", "tick.KEY_MANAGER_TICK", 0, "");
        String last = RowCodec.toLine(RowCodec.writeScheduleEvent(bare));
        Path file = Files.createTempFile("schedule", ".jsonl");
        Files.write(file, (RowCodec.toLine(RowCodec.writeScheduleEvent(event))
                + "\n" + last + "\n" + last.substring(0, last.length() / 2))
                .getBytes(StandardCharsets.UTF_8));
        assertEquals(Arrays.asList(event, bare),
                SessionReader.readSchedule(file));
        Files.delete(file);
    }

    @Test
    public void theRecorderCountsKPerKeyAndDrainsWhatCameFirst() {
        ScheduleLog.resetForTests();
        written.clear();
        ScheduleLog.observe(ScheduleEvent.Kind.START, "<A: void a()>#u1");
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "HADOOP_IPC#REQUEST");
        ScheduleLog.install(writer);
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

    /**
     * Threads started inside one scope count their events apart: the start
     * frame is part of an event's context, so the k-th send of each thread
     * is its own whatever the other one did in between (G8).  A thread no
     * woven start handed work to keeps the scope's context unchanged.
     */
    @Test
    public void threadsStartedInOneScopeCountTheirOwnEvents() throws Exception {
        written.clear();
        final String site = "<A: void spawn()>#u2";
        List<Thread> started = new ArrayList<Thread>();
        for (int index = 0; index < 2; index++) {
            Thread thread = new Thread(new Runnable() {
                @Override
                public void run() {
                    ScheduleLog.observe(ScheduleEvent.Kind.SEND,
                            "HADOOP_IPC#REQUEST");
                    ScheduleLog.observe(ScheduleEvent.Kind.SEND,
                            "HADOOP_IPC#REQUEST");
                }
            });
            Identity.startWork(site, thread);
            started.add(thread);
        }
        // The second thread runs first: its sends are still its own 0 and 1.
        for (int index = started.size() - 1; index >= 0; index--) {
            started.get(index).start();
            started.get(index).join();
        }
        Thread plain = new Thread(new Runnable() {
            @Override
            public void run() {
                ScheduleLog.observe(ScheduleEvent.Kind.SEND,
                        "HADOOP_IPC#REQUEST");
            }
        });
        plain.start();
        plain.join();
        String scope = ScheduleLog.contextHere();
        List<String> sends = new ArrayList<String>();
        for (ScheduleEvent event : events()) {
            if (event.kind() == ScheduleEvent.Kind.SEND) {
                sends.add(event.context() + " k=" + event.k());
            }
        }
        assertEquals(Arrays.asList(
                scope + "|" + site + "@1 k=0", scope + "|" + site + "@1 k=1",
                scope + "|" + site + "@0 k=0", scope + "|" + site + "@0 k=1",
                scope + " k=0"), sends);
    }

    /** And observe answers whether it wrote. */
    @Test
    public void nothingIsRecordedBeforeTheWindowOpens() {
        assertTrue(ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x"));
        RecordingWindow.reset();
        assertFalse(ScheduleLog.observe(ScheduleEvent.Kind.SEND,
                "HADOOP_IPC#REQUEST"));
        assertEquals(Collections.singletonList("x"), sites());
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

    /** A sleep's or a wait's WAKE the prefix states needs no signal. */
    @Test
    public void aTimedWaitUnderThePrefixDoesNotReadTheWallClock()
            throws Exception {
        ScheduleLog.enforceForTests(Arrays.asList(
                event(ScheduleEvent.Kind.WAKE, "<L: void loop()>#u9"),
                event(ScheduleEvent.Kind.WAKE, "<L: void loop()>#u4")));
        long before = System.nanoTime();
        TimedWaits.sleep(60000L, "<L: void loop()>#u9");
        final Object monitor = new Object();
        synchronized (monitor) {
            TimedWaits.waitOn(monitor, 60000L, "<L: void loop()>#u4");
        }
        assertTrue("virtual time: the turns came, the minutes did not",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 5000L);
        assertEquals(Arrays.asList("<L: void loop()>#u9",
                "<L: void loop()>#u4"), sites());
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

    /**
     * A signal ends a wait with no turn, free or under a prefix it leaves
     * standing; a timeout is a turn.
     */
    @Test
    public void aSignalledWaitIsNoEventAndATimedOutOneIs() throws Exception {
        final Object monitor = new Object();
        for (boolean held : new boolean[] {false, true}) {
            restart();
            if (held) ScheduleLog.enforceForTests(prefix("x"));
            Thread woken = waits(monitor, "<C: void w()>#u1", 1, true).get(0);
            if (held) {
                Thread.sleep(200L);
                assertTrue("virtual time: the minute does not run out",
                        woken.isAlive());
            }
            synchronized (monitor) {
                monitor.notifyAll();
            }
            woken.join(5000L);
            assertFalse(woken.isAlive());
            assertTrue("a notify ended it: another thread's doing, no turn",
                    written.isEmpty());
            if (held) {
                assertTrue("the prefix still stands", ScheduleLog.enforcing());
                assertTrue(ScheduleLog.progress(),
                        ScheduleLog.progress().contains(" 0 given up"));
            }
        }
        restart();
        synchronized (monitor) {
            TimedWaits.waitOn(monitor, 50L, "<C: void t()>#u2");
        }
        assertEquals("its timeout ended this one: a turn",
                Collections.singletonList("<C: void t()>#u2"), sites());
    }

    /**
     * A wait no slot holds waits at the cut; with the run idle it is let
     * go, and its own deadline ends it.  Nothing gives x up: no one waits
     * for it.
     */
    @Test(timeout = 20000L)
    public void aWaitNoSlotHoldsWaitsAtTheCutUntilTheRunIdles()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        long before = System.nanoTime();
        synchronized (monitor) {
            TimedWaits.waitOn(monitor, 1500L, site);
        }
        assertTrue("held, then its own deadline ended it",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        >= 1400L);
        assertEquals(Collections.singletonList(site), sites());
        assertTrue("nothing made x, and no one waits for it",
                ScheduleLog.enforcing());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains("1 of them let go"));
    }

    /**
     * A wait the recording made, polled once more than recorded (what it
     * polls for came later on a free thread), goes once its context's next
     * slot is due: only its next turn makes that slot's event.
     */
    @Test(timeout = 20000L)
    public void aRecordedWaitPolledOnceMoreGoesWhenItsNextSlotIsDue()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        String site = "tick.poll";
        List<ScheduleEvent> order = new ArrayList<ScheduleEvent>();
        order.add(event(ScheduleEvent.Kind.WAKE, site));
        order.addAll(prefix("x"));
        ScheduleLog.enforceForTests(order);
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertEquals(Arrays.asList(site, site, "x"), sites());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains("2 taken, 0 given up"));
    }

    /**
     * The request that makes x first sleeps a wait the recording never
     * made: held at the cut, with the run idle, it is let go before x is
     * given up, and x is taken.  The turn it let go is vacant; x's is not.
     */
    @Test(timeout = 20000L)
    public void anIdleRunLetsTheCutsWaitsGoBeforeGivingUp() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "1000");
        String site = "tick.once";
        ScheduleLog.enforceForTests(prefix("x"));
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site);
        assertTrue("a turn let go is vacant", ScheduleLog.vacated());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertFalse("a slotted event is not", ScheduleLog.vacated());
        assertEquals(Arrays.asList(site, "x"), sites());
        String progress = ScheduleLog.progress();
        assertTrue(progress, progress.contains("1 taken, 0 given up"));
        assertTrue(progress, progress.contains("1 of them let go"));
    }

    /** The workload closes its window: what the order still holds goes. */
    @Test(timeout = 20000L)
    public void closingTheWindowLetsTheOrderGo() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(prefix("x", "y"));
        Thread y = observer(ScheduleEvent.Kind.SEND, "y");
        Thread.sleep(200L);
        assertTrue("y waits for x", y.isAlive());
        CausynthTraceRecorder.stopRecording();
        y.join(5000L);
        assertFalse(y.isAlive());
        assertFalse(ScheduleLog.enforcing());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains("2 open at the window's close"));
    }

    /**
     * A store's notification is awaited by no order, and neither is the
     * work it causes: an event after the callback's read is free.
     */
    @Test(timeout = 20000L)
    public void aStoreNotificationsWorkIsNoPartOfTheOrder() throws Exception {
        final Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NODE);
        MessageDoors.stored("STORE", "/k@1", owner);
        written.clear();
        Thread callback = new Thread(new Runnable() {
            @Override
            public void run() {
                MessageDoors.notified("Watcher", new Runnable() {
                    @Override
                    public void run() {
                        MessageDoors.fetched("STORE", "/k@1", owner);
                        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
                    }
                });
            }
        });
        callback.start();
        callback.join(5000L);
        assertTrue(sites().toString(), sites().isEmpty());
    }

    /** A WAKE or turn the recording did not make before x waits at the cut. */
    @Test(timeout = 20000L)
    public void aWakeTheRecordingDidNotMakeSleepsThroughThePrefix()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<D: void offerService()>#u4";
        ScheduleLog.enforceForTests(prefix("x"));
        Thread daemon = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    TimedWaits.sleep(10L, site);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        });
        daemon.start();
        Thread turn = observer(ScheduleEvent.Kind.WAKE, "tick.e");
        Thread.sleep(500L);
        assertTrue("its 10 ms are long past on the wall clock, and the "
                + "recording made no such WAKE before x", daemon.isAlive());
        assertTrue("nor such a turn: it waits at the cut", turn.isAlive());
        assertTrue(written.isEmpty());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        daemon.join(5000L);
        turn.join(5000L);
        assertFalse("the prefix settled: the wait is the clock's again",
                daemon.isAlive());
        assertFalse(turn.isAlive());
        List<String> sites = sites();
        assertEquals(sites.toString(), 3, sites.size());
        assertEquals("x", sites.get(0));
        assertTrue(sites.toString(),
                sites.containsAll(Arrays.asList(site, "tick.e")));
    }

    @Test(timeout = 20000L)
    public void nobodyWaitsForALateWakeAndItStillTakesItsSlot()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(Arrays.asList(
                event(ScheduleEvent.Kind.WAKE, "tick.d"),
                event(ScheduleEvent.Kind.SEND, "x"),
                event(ScheduleEvent.Kind.SEND, "y")));
        long before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertTrue("x did not wait for the daemon's turn before it",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 5000L);
        ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.d");
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
        assertEquals(Arrays.asList("x", "tick.d", "y"), sites());
        assertTrue(ScheduleLog.progress(),
                ScheduleLog.progress().contains(" 0 given up"));
        assertFalse("every slot taken", ScheduleLog.enforcing());
    }

    /** A held wait, and a held poll, outlive the prefix's end. */
    @Test
    public void aHeldWaitOutlivesThePrefixOnTheWallClock() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        Thread idle = waits(monitor, "<C: boolean waitForWork()>#u21", 1,
                true).get(0);
        final BlockingQueue<Object> queue = new LinkedBlockingQueue<Object>();
        final Object[] taken = new Object[1];
        Thread sender = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    taken[0] = TimedWaits.poll(queue, 60L, TimeUnit.SECONDS,
                            "<S: void run()>#u12");
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        });
        sender.start();
        Thread.sleep(200L);
        // The prefix's last event: the run is free from here.
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertFalse(ScheduleLog.enforcing());
        Thread.sleep(500L);
        assertTrue("the prefix's end is no timeout of this wait",
                idle.isAlive());
        assertTrue("nor of this poll", sender.isAlive());
        synchronized (monitor) {
            TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
        }
        queue.put("call");
        idle.join(5000L);
        sender.join(5000L);
        assertFalse(idle.isAlive());
        assertFalse(sender.isAlive());
        assertEquals("the poll takes what arrives", "call", taken[0]);
        assertEquals("a signal ended each: only the prefix's event is written",
                Collections.singletonList("x"), sites());
    }

    /**
     * A signal sent while a held wait stands outside the wait set is state
     * the wait reads: after its quantum ran out under the notifier's
     * monitor, after the window's opening took it out, and while a held
     * await reacquires its lock.
     */
    @Test
    public void aNotifySentWhileAHeldWaitIsOutOfTheWaitSetIsNotLost()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<C: boolean waitForWork()>#u21";
        final Object monitor = new Object();
        for (boolean opening : new boolean[] {false, true}) {
            restart();
            // Opening: the wait starts free, on the wall clock, in the set.
            if (opening) RecordingWindow.reset();
            ScheduleLog.enforceForTests(prefix("x"));
            Thread idle = waits(monitor, site, 1, true).get(0);
            if (opening) Thread.sleep(100L);
            synchronized (monitor) {
                if (opening) {
                    // The opening takes the wait out of the wait set; the
                    // notify that follows, before it can re-enter, reaches
                    // only its mark.
                    RecordingWindow.open();
                    TimedWaits.windowOpened();
                } else {
                    // Held longer than a quantum: the wait's quantum ends
                    // and it stands outside the wait set, blocked on the
                    // monitor this thread holds, when the notify is sent.
                    Thread.sleep(200L);
                }
                TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
            }
            idle.join(5000L);
            String row = opening ? "the window opened" : "a quantum ran out";
            assertFalse(row + ": the notify was state the wait read",
                    idle.isAlive());
            assertTrue(row + ": and it is no event", written.isEmpty());
            assertTrue(ScheduleLog.progress(),
                    ScheduleLog.progress().contains(" 0 given up"));
        }

        restart();
        ScheduleLog.enforceForTests(prefix("x"));
        final ReentrantLock lock = new ReentrantLock();
        final Condition ready = lock.newCondition();
        final boolean[] signalled = new boolean[1];
        final CountDownLatch waiting = new CountDownLatch(1);
        Thread taker = new Thread(new Runnable() {
            @Override
            public void run() {
                lock.lock();
                try {
                    waiting.countDown();
                    signalled[0] = TimedWaits.await(ready, 60L,
                            TimeUnit.SECONDS,
                            "<Q: java.lang.Object take()>#u8");
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

    /**
     * A notify ends one wait and a notifyAll every one, held or free.  An
     * untimed wait the notifyAll carrying another's notify woke goes back
     * to waiting: it ends by its own notify only.
     */
    @Test
    public void aNotifyEndsOneWaitAndANotifyAllEndsEvery() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final Object monitor = new Object();
        for (boolean held : new boolean[] {true, false}) {
            restart();
            if (held) ScheduleLog.enforceForTests(prefix("x"));
            String row = held ? "held, timed" : "free, untimed";
            List<Thread> first = waits(monitor, "<C: void loop()>#u7", 2,
                    held);
            synchronized (monitor) {
                TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
            }
            Thread.sleep(300L);
            assertEquals(row + ": one notify, one wait ended", 1,
                    alive(first));
            synchronized (monitor) {
                TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
            }
            join(first);
            assertEquals(row, 0, alive(first));
            List<Thread> second = waits(monitor, "<C: void loop()>#u7", 2,
                    held);
            synchronized (monitor) {
                TimedWaits.notifyAllOn(monitor, "<C: void n()>#u2");
            }
            join(second);
            assertEquals(row, 0, alive(second));
            assertTrue(row, written.isEmpty());
            if (held) {
                assertTrue(ScheduleLog.progress(),
                        ScheduleLog.progress().contains(" 0 given up"));
            }
        }
    }

    /** A turn the window saw begin states its END; the set-up's, none. */
    @Test
    public void aTurnTheWindowSawBeginStatesItsEnd() {
        RecordingWindow.reset();
        long setUp = RuntimeTraceContext.beginTick(new Object(),
                "BP_SERVICE_ACTOR");
        RecordingWindow.open();
        RuntimeTraceContext.endTick(setUp);
        assertTrue("the set-up's turn is not the window's", written.isEmpty());

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

        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        restart();
        openRequest();
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

    /**
     * What no order holds runs on the wall clock: a wait at a site the
     * identity cannot name, a sleep the rest does not name, and a poll(0),
     * which is no wait at all.
     */
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

        restart();
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<L: void loop()>#u9";
        ScheduleLog.enforceForTests(prefix("x"), Collections.singletonList(
                event(ScheduleEvent.Kind.WAKE, "tick.d")));
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        before = System.nanoTime();
        TimedWaits.sleep(500L, site);
        took = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before);
        assertTrue("to its own deadline, not at once: " + took,
                took >= 450L);
        assertTrue("and not held for the rest: " + took, took < 5000L);
        assertEquals(Arrays.asList("x", site), sites());

        // A poll(0) takes what another thread offers right now.  A DataNode
        // proxy's IPC sender polls its SynchronousQueue at maxIdleTime 0,
        // and the caller's offer is only ever taken that way.
        final SynchronousQueue<String> queue = new SynchronousQueue<String>();
        Thread caller = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    while (!queue.offer("call", 1L, TimeUnit.SECONDS)) {
                        // As Client.Connection.sendRpcRequest does.
                    }
                } catch (InterruptedException stopped) {
                    Thread.currentThread().interrupt();
                }
            }
        });
        caller.start();
        Object taken = null;
        long end = System.nanoTime() + TimeUnit.SECONDS.toNanos(10L);
        while (taken == null && System.nanoTime() < end) {
            taken = TimedWaits.poll(queue, 0L, TimeUnit.MILLISECONDS,
                    "sender#u0");
        }
        caller.interrupt();
        caller.join();
        assertEquals("call", taken);
    }

    /**
     * An interrupt that ends a wait writes where it stands: a held monitor
     * wait throws and writes its INTERRUPT, and a park, free or held,
     * leaves the flag and writes its WAKE.
     */
    @Test
    public void aHeldWaitAnInterruptEndsWritesItsWake() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"));
        final Object monitor = new Object();
        final String[] outcome = new String[1];
        Thread waiter = new Thread(new Runnable() {
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
        waiter.start();
        waitUntilWaiting(waiter);
        waiter.interrupt();
        waiter.join(5000L);
        assertEquals("the interrupt ends the held wait by throwing", "threw",
                outcome[0]);
        assertEquals("and writes its INTERRUPT where it stands",
                Collections.singletonList(site), sites());
        assertEquals(ScheduleEvent.Kind.INTERRUPT, events().get(0).kind());

        final String spin = "<P: void spin()>#u3";
        for (boolean held : new boolean[] {false, true}) {
            restart();
            if (held) ScheduleLog.enforceForTests(prefix("x"));
            final boolean[] flagged = new boolean[1];
            Thread parker = new Thread(new Runnable() {
                @Override
                public void run() {
                    // JDK 8 hands a new thread a finished thread's park
                    // state with its permit still set: an inherited permit
                    // would return the first park at once, an unpark.
                    LockSupport.parkNanos(1L);
                    TimedWaits.parkNanos(TimeUnit.SECONDS.toNanos(20L), spin);
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
                    Collections.singletonList(spin), sites());
        }
    }

    /**
     * Entered with an interrupt pending, a wait does what the JDK's does:
     * a park returns at once with no event and the flag left; sleep(0),
     * poll(0) and awaitNanos(0) throw, and so does Object.wait, turn or no
     * turn.
     */
    @Test
    public void aTimedWaitEnteredInterruptedThrowsEvenWhenItsTurnIsNext()
            throws Exception {
        final String site = "<L: void loop()>#u4";
        ScheduleLog.enforceForTests(Collections.singletonList(
                event(ScheduleEvent.Kind.WAKE, site)));
        Thread.currentThread().interrupt();
        long before = System.nanoTime();
        TimedWaits.parkNanos(TimeUnit.SECONDS.toNanos(10L),
                "<P: void spin()>#u3");
        assertTrue("a park returns at once for an interrupted thread",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 5000L);
        assertTrue("and leaves the flag for its caller",
                Thread.interrupted());
        assertTrue("a loop around it would spin: no event per spin",
                written.isEmpty());

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
            TimedWaits.poll(new LinkedBlockingQueue<Object>(), 0L,
                    TimeUnit.MILLISECONDS, "<S: void run()>#u12");
        } catch (InterruptedException interrupted) {
            threw = true;
        }
        assertTrue("so does a timed poll(0)", threw);

        final Object monitor = new Object();
        Thread.currentThread().interrupt();
        threw = false;
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

        ReentrantLock lock = new ReentrantLock();
        Condition ready = lock.newCondition();
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

    /**
     * {@code count} woven waits at {@code site} on {@code monitor}, each
     * standing in it: a minute long when {@code timed}, else untimed.
     */
    private static List<Thread> waits(final Object monitor, final String site,
                                      int count, final boolean timed)
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
                            if (timed) {
                                TimedWaits.waitOn(monitor, 60000L, site);
                            } else {
                                TimedWaits.waitOn(monitor, site);
                            }
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

    /**
     * Past the prefix a timeout the rest holds waits for the events it
     * followed -- a daemon's turn and a held wait's WAKE alike.
     */
    @Test
    public void pastThePrefixATimeoutWaitsForTheEventsItFollowed()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final String site = "<C: boolean waitForWork()>#u21";
        ScheduleLog.enforceForTests(prefix("x"), Arrays.asList(
                event(ScheduleEvent.Kind.SEND, "a"),
                event(ScheduleEvent.Kind.WAKE, "tick.d"),
                event(ScheduleEvent.Kind.WAKE, site)));
        long before = System.nanoTime();
        Thread idle = waits(new Object(), site, 1, true).get(0);
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        assertTrue("the rest's timeouts are still to come",
                ScheduleLog.enforcing());
        Thread daemon = observer(ScheduleEvent.Kind.WAKE, "tick.d");
        Thread.sleep(300L);
        assertTrue("the daemon's turn waits for what it followed",
                daemon.isAlive());
        assertTrue("and so does the held wait's timeout", idle.isAlive());
        assertEquals(Collections.singletonList("x"), sites());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "a");
        daemon.join(5000L);
        idle.join(5000L);
        assertFalse(daemon.isAlive());
        assertFalse(idle.isAlive());
        assertTrue("virtual time, not its 60 s",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 10000L);
        assertEquals(Arrays.asList("x", "a", "tick.d", site), sites());
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

    /**
     * A stall gives up only what came before the earliest waiting timeout,
     * past the prefix or inside it: a later timeout still waits for what it
     * followed.
     */
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

        // Inside the prefix: the same give-up, and the rest still to come.
        restart();
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
    public void aStallGivesUpOnlyTheSlotThatNeverCame()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        for (int round = 0; round < 5; round++) {
            restart();
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
        Thread idle = waits(monitor, site, 1, true).get(0);
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

    /**
     * An occurrence's close settles the slots it held and made nothing
     * for, and only those: another occurrence's close shifts none of them.
     */
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

        restart();
        ScheduleLog.enforceForTests(Arrays.asList(
                inOccurrence(ScheduleEvent.Kind.SEND, "req", "o1"),
                event(ScheduleEvent.Kind.START, "a"),
                inOccurrence(ScheduleEvent.Kind.SEND, "req", "o2"),
                event(ScheduleEvent.Kind.START, "b")));
        ScheduleLog.closed("o2");
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "req");
        ScheduleLog.observe(ScheduleEvent.Kind.START, "a");
        before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.START, "b");
        assertTrue("o2's dead slot does not hold b",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 1000L);
        assertEquals(Arrays.asList("req", "a", "b"), sites());
        assertFalse(ScheduleLog.enforcing());
    }

    /**
     * A waiter gives up at once what its own occurrence passed: only its
     * thread could make it, and that thread waits beyond it.
     */
    @Test
    public void aWaiterGivesUpWhatItsOwnOccurrencePassed() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        Identity.occurrence(NODE.key(), "REGION.handler", true);
        String own = Identity.innermostRegionId();
        written.clear();
        ScheduleLog.enforceForTests(Arrays.asList(
                inOccurrence(ScheduleEvent.Kind.START, "enqueue", own),
                event(ScheduleEvent.Kind.SEND, "x"),
                inOccurrence(ScheduleEvent.Kind.SEND, "response", own)));
        Thread other = observer(ScheduleEvent.Kind.SEND, "x");
        Thread.sleep(200L);
        assertTrue("x waits behind the handler's enqueue", other.isAlive());
        long before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "response");
        other.join(5000L);
        assertTrue("no watchdog: the handler passed its enqueue",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 2000L);
        assertEquals(Arrays.asList("x", "response"), sites());
        assertTrue(ScheduleLog.progress(), ScheduleLog.progress()
                .contains(" 1 passed by their own occurrence"));
    }

    /**
     * Computing is progress only on a thread that owes the stalled slot: one
     * whose last event stood in x's context.  The same computation on a
     * thread no event bound (a store notification's parse, the result
     * publication), or on one whose last event was a poll past its recorded
     * count, is no one's progress, and x is given up after a timeout.
     */
    @Test
    public void onlyTheThreadThatOwesTheStalledSlotComputesForIt()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "600");
        final String w = "w";
        final String p = "tick.poll";
        // row: what the worker made before it computes, the order, the
        // sites written, whether x was given up.
        Object[][] rows = {
            {"made w", Arrays.asList(ScheduleEvent.Kind.SEND),
                    w, Arrays.asList(w, "x", "tick.d"), false},
            {"made nothing", Collections.emptyList(),
                    w, Arrays.asList(w, "tick.d", "x"), true},
            {"polled once past its recorded count",
                    Arrays.asList(ScheduleEvent.Kind.WAKE,
                            ScheduleEvent.Kind.WAKE),
                    p, Arrays.asList(p, p, "tick.d", "x"), true},
        };
        for (Object[] row : rows) {
            restart();
            final String name = "a worker that " + row[0] + " computes";
            @SuppressWarnings("unchecked")
            final List<ScheduleEvent.Kind> before =
                    (List<ScheduleEvent.Kind>) row[1];
            final String first = (String) row[2];
            ScheduleLog.enforceForTests(Arrays.asList(
                    event(first.equals(w) ? ScheduleEvent.Kind.SEND
                            : ScheduleEvent.Kind.WAKE, first),
                    event(ScheduleEvent.Kind.SEND, "x"),
                    event(ScheduleEvent.Kind.WAKE, "tick.d")));
            if (before.isEmpty()) {
                ScheduleLog.observe(ScheduleEvent.Kind.SEND, w);
            }
            Thread worker = new Thread(new Runnable() {
                @Override
                public void run() {
                    for (ScheduleEvent.Kind kind : before) {
                        ScheduleLog.observe(kind, first);
                    }
                    spin(3500L);
                    ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
                }
            });
            worker.start();
            Thread daemon = observer(ScheduleEvent.Kind.WAKE, "tick.d");
            worker.join(10000L);
            daemon.join(10000L);
            assertFalse(name, worker.isAlive() || daemon.isAlive());
            assertEquals(name, row[3], sites());
            assertTrue(name + ": " + ScheduleLog.progress(),
                    ScheduleLog.progress().contains(
                            (Boolean) row[4] ? " 1 given up" : " 0 given up"));
        }
    }

    /**
     * A loop polling past its recorded count, its context's next slot due,
     * does not spin: its first poll past the count goes (its last recorded
     * WAKE's slot moved the order), and every later one waits for the order
     * to move again -- another context's event -- or for the watchdog to let
     * it go when the run idles.  A loop that reads a CLOCK root waits for
     * time only the clock brings, and is never held so.
     */
    @Test(timeout = 30000L)
    public void aPollPastItsRecordedCountWaitsForTheOrderToMove()
            throws Exception {
        final String loop = "<L: boolean poll()>#u5";
        final String clock = ScheduleLogTest.class.getName() + "#pollLoop";
        // A clock loop's method, as the scope map declares its CLOCK root.
        JsonObject root = new JsonObject();
        root.addProperty("kind", "STATIC_SCOPE_SITE");
        root.addProperty("role", "DECLARED_SITE");
        root.addProperty("inputKind", "CLOCK");
        root.addProperty("vmSite", "org.a.RoutingRule#isExpired()Z");
        assertEquals("org.a.RoutingRule#isExpired",
                ClockLoops.clockMethod(root));
        root.addProperty("inputKind", "FAULT");
        assertEquals("", ClockLoops.clockMethod(root));
        // row: released by, timeout, the loop reads a clock, the sites.
        Object[][] rows = {
            {"another context's event", "30000", false,
                    Arrays.asList(loop, loop, "tick.d", loop, "y")},
            {"the run idling", "300", false,
                    Arrays.asList(loop, loop, loop, "y")},
            {"nothing: its loop reads a CLOCK root", "30000", true,
                    Arrays.asList(loop, loop, loop, "y")},
        };
        for (Object[] row : rows) {
            restart();
            String name = "released by " + row[0];
            System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, (String) row[1]);
            boolean reads = (Boolean) row[2];
            ClockLoops.useForTests(reads ? Collections.singleton(clock)
                    : Collections.<String>emptySet());
            ScheduleLog.enforceForTests(Arrays.asList(
                    event(ScheduleEvent.Kind.WAKE, loop),
                    event(ScheduleEvent.Kind.WAKE, "tick.d"),
                    event(ScheduleEvent.Kind.SEND, "y")));
            long before = System.nanoTime();
            Thread poller = new Thread(new Runnable() {
                @Override
                public void run() {
                    pollLoop(loop, 3);
                }
            });
            poller.start();
            if (name.contains("event")) {
                Thread.sleep(500L);
                assertTrue(name + ": the third poll waits", poller.isAlive());
                ScheduleLog.observe(ScheduleEvent.Kind.WAKE, "tick.d");
            }
            poller.join(10000L);
            long took = TimeUnit.NANOSECONDS.toMillis(
                    System.nanoTime() - before);
            assertFalse(name, poller.isAlive());
            assertEquals(name, row[3], sites());
            String progress = ScheduleLog.progress();
            assertTrue(name + ": " + progress, progress.contains(
                    name.contains("idling") ? "1 of them let go"
                            : "0 of them let go"));
            if (reads) {
                assertTrue(name + ", at its own pace: " + took, took < 2000L);
            } else {
                assertTrue(name + ", held: " + took, took >= 300L);
            }
        }
    }

    /**
     * {@code polls} sleeps of 50 ms at {@code site}, then the loop's exit:
     * a send of y.
     */
    private static void pollLoop(String site, int polls) {
        try {
            for (int poll = 0; poll < polls; poll++) {
                TimedWaits.sleep(50L, site);
            }
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            return;
        }
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
    }

    /**
     * An event that never comes costs a timeout, then a grace after the
     * waits held at the cut are let go -- not {@link ScheduleLog#CEILING}
     * timeouts twice over while a thread that owes nothing computes.
     */
    @Test(timeout = 30000L)
    public void aNeverComingEventCostsATimeoutAndAGrace() throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "1000");
        ScheduleLog.enforceForTests(prefix("never", "y"));
        final boolean[] stop = new boolean[1];
        Thread busy = new Thread(new Runnable() {
            @Override
            public void run() {
                while (!stop[0]) spin(50L);
            }
        });
        busy.start();
        long before = System.nanoTime();
        Thread held = observer(ScheduleEvent.Kind.WAKE, "tick.idle");
        Thread y = observer(ScheduleEvent.Kind.SEND, "y");
        y.join(20000L);
        long took = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before);
        stop[0] = true;
        busy.join();
        held.join(5000L);
        assertFalse(y.isAlive() || held.isAlive());
        assertTrue("a timeout, then the let-go's grace: " + took,
                took >= 1000L + ScheduleLog.LET_GO_GRACE_MS);
        assertTrue("well inside the ceiling: " + took,
                took < ScheduleLog.CEILING * 1000L - 500L);
        assertEquals(Arrays.asList("tick.idle", "y"), sites());
        String progress = ScheduleLog.progress();
        assertTrue(progress, progress.contains(" 1 given up"));
        assertTrue(progress, progress.contains("1 of them let go"));
    }

    /** Burns this thread's CPU for {@code millis}. */
    private static void spin(long millis) {
        long until = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(millis);
        long sink = 0L;
        while (System.nanoTime() < until) sink += System.nanoTime() % 7L;
        assertTrue(sink >= 0L);
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
     * One event as this JVM's threads compute it: every one of them runs in
     * the test's one request, so every one states the same context.
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
