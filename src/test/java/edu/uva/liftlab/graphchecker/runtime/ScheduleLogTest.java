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
        CausynthTraceRecorder.setRecordingStartedForTests(true);
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
        CausynthTraceRecorder.setRecordingStartedForTests(false);
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
        assertEquals("", ScheduleLog.divergence());
        assertFalse("the prefix is used up", ScheduleLog.enforcing());
    }

    @Test
    public void nothingAdmittedForTheTimeoutReleasesEveryWaiter()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        ScheduleLog.enforceForTests(prefix("x", "z"));
        final List<Thread> waiters = new ArrayList<Thread>();
        for (final String site : new String[] {"z", "w"}) {
            Thread thread = new Thread(new Runnable() {
                @Override
                public void run() {
                    ScheduleLog.observe(ScheduleEvent.Kind.SEND, site);
                }
            });
            waiters.add(thread);
            thread.start();
        }
        for (Thread thread : waiters) {
            thread.join(5000L);
            assertFalse("a waiter is released", thread.isAlive());
        }
        assertTrue(ScheduleLog.divergence().contains("prefix position 0"));
        assertFalse(ScheduleLog.enforcing());
        long before = System.nanoTime();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "q");
        assertTrue("a free run admits at once",
                TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - before)
                        < 200L);
    }

    @Test
    public void anInterruptEndsOneWaitAndIsNoDivergence() throws Exception {
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
        assertEquals("", ScheduleLog.divergence());
        assertTrue("the prefix still stands", ScheduleLog.enforcing());
    }

    @Test
    public void aMonitorHoldingWaitAsksWithoutBlocking() {
        ScheduleLog.enforceForTests(prefix("x", "y"));
        assertFalse(ScheduleLog.tryObserve(ScheduleEvent.Kind.SEND, "y"));
        assertTrue(ScheduleLog.tryObserve(ScheduleEvent.Kind.SEND, "x"));
        assertTrue(ScheduleLog.tryObserve(ScheduleEvent.Kind.SEND, "y"));
        assertEquals(Arrays.asList("x", "y"), sites());
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
        CausynthTraceRecorder.setRecordingStartedForTests(false);
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
        CausynthTraceRecorder.setRecordingStartedForTests(true);
        TimedWaits.windowOpened();
        idle.join(5000L);
        assertFalse("the window's opening converts it", idle.isAlive());
        assertTrue(took[0] < 5000L);
        assertEquals(Collections.singletonList(site), sites());
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
