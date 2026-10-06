package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * The application's clocks: a recording reads the host and states where it
 * read; a replay reads its order's timeline from its own first read on,
 * never past what it has not reached, never behind what it has, never back;
 * a cap that stands a timeout with nothing to move it is lifted by name.
 */
public class ClocksTest {
    private static final long MS = 1_000_000L;
    /** A cap stands one millisecond tick past its instant. */
    private static final long TICK = Clocks.TICK_NANOS;
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private final List<JsonObject> rows =
            Collections.synchronizedList(new ArrayList<JsonObject>());
    private long request;
    private Path order;

    @Before
    @After
    public void freshRun() throws Exception {
        if (request != 0L) RuntimeTraceContext.endRequest(request);
        request = 0L;
        System.clearProperty(ScheduleLog.PREFIX_PROPERTY);
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        ScheduleLog.resetForTests();
        StartupOrder.resetForTests();
        RecordingWindow.reset();
        rows.clear();
        ScheduleLog.install(rows::add);
        if (order != null) Files.deleteIfExists(order);
    }

    @Test
    public void aRecordingReadsTheHostAndStatesItsFirstRead() {
        long before = System.nanoTime();
        long read = Clocks.nanos();
        long after = System.nanoTime();
        assertTrue(before <= read && read <= after);
        assertTrue(Math.abs(Clocks.millis() - System.currentTimeMillis())
                < 1000L);
        Clocks.nanos();
        List<JsonObject> origins = marks(ScheduleEvent.ORIGIN);
        assertEquals("its first read is its origin, stated once", 1,
                origins.size());
        long origin = RowCodec.scheduleNanos(origins.get(0));
        assertTrue(before <= origin && origin <= after);
    }

    @Test
    public void aReplayReadsItsOrdersTimelineAsItReachesIt()
            throws Exception {
        follow(time(ScheduleEvent.ORIGIN, 0L),
                startup("register", "dn0", 100L), time(ScheduleEvent.OPEN,
                        300L));
        Clocks.nanos();
        // Its own origin: its first read, where the order's origin stands.
        long first = RowCodec.scheduleNanos(marks(ScheduleEvent.ORIGIN)
                .get(0));
        long firstMillis = RowCodec.scheduleMillis(marks(
                ScheduleEvent.ORIGIN).get(0));
        Thread.sleep(150L);
        atCap("never past a startup pass it has not made",
                first + 100L * MS, Clocks.nanos());
        assertEquals("on both clocks", firstMillis + 100L, Clocks.millis());
        StartupOrder.done(StartupOrder.begin("register", "dn0"));
        long passed = Clocks.nanos();
        assertTrue(passed >= first + 100L * MS
                && passed < first + 300L * MS);
        assertTrue("its own mark states the instant it passed at",
                RowCodec.scheduleNanos(marks(ScheduleEvent.STARTUP).get(0))
                        >= first + 100L * MS);
        Thread.sleep(250L);
        atCap("from a pass on, time stands exactly at the pass reached",
                first + 100L * MS, Clocks.nanos());
        long standing = Clocks.nanos();
        long standingMillis = Clocks.millis();
        Thread.sleep(50L);
        assertEquals("time stands", standing, Clocks.nanos());
        TimedWaits.sleep(50L, "<ClocksTest: void sleep()>#u1");
        long slept = Clocks.nanos();
        assertTrue("but a sleep moves it a nanosecond", slept > standing
                && slept < standing + 1000L);
        assertTrue("for every thread", elsewhere(true) >= slept);
        assertEquals("and the sleeper's millisecond clock a millisecond",
                standingMillis + 1L, Clocks.millis());
        assertEquals("for the sleeper alone", standingMillis,
                elsewhere(false));

        openWindow();
        long opened = Clocks.nanos();
        assertTrue("the opening: time reaches the order's opening",
                opened >= first + 300L * MS && opened < first + 400L * MS);
        ScheduleLog.enforceForTests(Arrays.asList(
                event("x", 400L), event("y", 2000L)));
        Thread.sleep(150L);
        atCap("inside, never past the frontier's instant",
                first + 400L * MS + TICK, Clocks.nanos());
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        long atX = Clocks.nanos();
        assertTrue("an event made: its instant is reached",
                atX >= first + 400L * MS && atX < first + 2000L * MS);
        assertTrue("and stamps its row", events().get(0).nanos()
                >= first + 400L * MS);
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "y");
        long atY = Clocks.nanos();
        assertTrue("time jumps ahead only to a place the replay reached",
                atY >= first + 2000L * MS);
        Thread.sleep(50L);
        assertTrue("and past the order runs free", Clocks.nanos() > atY);
        assertTrue(Clocks.progress(), Clocks.progress().contains(
                " 0 cap(s) lifted"));
    }

    /**
     * Before the window a timed wait that ran out past the cap time stands
     * at lifts it to its deadline, no further: at once at a mark time ran
     * up to, at a pass this run made only after it stood a timeout, never
     * beside a held startup taker, never for a wait a signal ended.
     */
    @Test
    public void aWaitThatRanOutPastAStandingCapLiftsItToItsDeadline()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "400");
        follow(time(ScheduleEvent.ORIGIN, 0L),
                startup("register", "dn0", 50L),
                startup("register", "dn1", 60L),
                startup("register", "dn2", 70L),
                time(ScheduleEvent.OPEN, 10_000L));
        Clocks.nanos();
        long first = RowCodec.scheduleNanos(marks(ScheduleEvent.ORIGIN)
                .get(0));
        Thread.sleep(100L);
        atCap("time ran up to the first mark", first + 50L * MS,
                Clocks.nanos());
        ranOut(200L);
        atCap("a mark not passed yet: its pass comes from the start-up's"
                + " progress, no wait lifts it", first + 50L * MS,
                Clocks.nanos() - 1L);

        StartupOrder.done(StartupOrder.begin("register", "dn0"));
        standAtCap(450L);
        // dn2's taker is held until dn1 passes: its hold bounds the wait.
        Thread taker = new Thread(() -> StartupOrder.done(
                StartupOrder.begin("register", "dn2")));
        taker.start();
        long until = System.nanoTime() + 300L * MS;
        while (!StartupOrder.holding() && System.nanoTime() < until) {
            Thread.sleep(5L);
        }
        assertTrue("dn2 is held", StartupOrder.holding());
        ranOut(200L);
        atCap("a wait beside a held taker lifts nothing, however long time"
                + " stood", first + 50L * MS, Clocks.nanos() - 2L);
        StartupOrder.done(StartupOrder.begin("register", "dn1"));
        taker.join();
        atCap("every pass made: time stands at the last", first + 70L * MS,
                Clocks.nanos());
        ranOut(200L);
        atCap("at a pass this run made, a wait lifts nothing at first",
                first + 70L * MS, Clocks.nanos() - 1L);
        standAtCap(450L);
        long[] signalled = Clocks.waitBegins(300L * MS);
        Clocks.waited(signalled);
        atCap("nor one a signal ended", first + 70L * MS,
                Clocks.nanos() - 2L);
        long deadline = ranOut(200L);
        atCap("once it stood a timeout there, a wait that ran out lifts the"
                + " cap to its deadline", deadline, Clocks.nanos());
        assertTrue(deadline - (first + 270L * MS) < 10L);
        Thread.sleep(100L);
        atCap("and no further", deadline, Clocks.nanos());
        assertTrue(Clocks.progress(), Clocks.progress().contains(
                "1 to a timed wait's deadline before the window"));
        freshRun();

        follow(time(ScheduleEvent.ORIGIN, 0L), time(ScheduleEvent.OPEN,
                10_000L));
        Clocks.nanos();
        first = RowCodec.scheduleNanos(marks(ScheduleEvent.ORIGIN).get(0));
        Thread.sleep(60L);
        Clocks.nanos();
        long far = ranOut(20_000L);
        atCap("at the opening time ran up to, at once", far, Clocks.nanos());
        assertTrue(far - (first + 10_000L * MS) > 0L);
    }

    /** Reads at the cap for {@code ms}, so time is seen standing there. */
    private static void standAtCap(long ms) throws Exception {
        long until = System.nanoTime() + ms * MS;
        while (System.nanoTime() < until) {
            Clocks.nanos();
            Thread.sleep(20L);
        }
    }

    /** A timed wait of {@code ms} begun now, ended by its timeout;
     *  returns its deadline. */
    private static long ranOut(long ms) {
        long[] wait = Clocks.waitBegins(ms * MS);
        Clocks.timedOut(wait);
        Clocks.waited(wait);
        return wait[0] + ms * MS;
    }

    @Test
    public void aFrontierNoThreadWaitsOnIsLiftedAfterAStall()
            throws Exception {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "200");
        follow(time(ScheduleEvent.ORIGIN, 0L), time(ScheduleEvent.OPEN,
                10_000L));
        Clocks.nanos();
        long first = RowCodec.scheduleNanos(marks(ScheduleEvent.ORIGIN)
                .get(0));
        openWindow();
        ScheduleLog.enforceForTests(Collections.singletonList(
                event("x", 10_050L)));
        Thread.sleep(100L);
        atCap("at the frontier", first + 10_050L * MS + TICK,
                Clocks.nanos());
        standUntilLifted("1 with no thread waiting on the order");
        Thread.sleep(100L);
        assertTrue("a frontier no thread waits on: time runs past it",
                Clocks.nanos() > first + 10_100L * MS);
    }

    /**
     * ScheduleLog owns the cap: an opening publishes the order's at once,
     * whatever the open window let in first, and none for an order that
     * holds no event.
     */
    @Test
    public void theOpeningPublishesTheOrdersCapAtOnce() throws Exception {
        follow(time(ScheduleEvent.ORIGIN, 0L), time(ScheduleEvent.OPEN,
                100L));
        Clocks.nanos();
        long first = RowCodec.scheduleNanos(marks(ScheduleEvent.ORIGIN)
                .get(0));
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        request = RuntimeTraceContext.beginRequest(node, "clocks-test");
        ScheduleLog.enforceForTests(Arrays.asList(event("x", 150L),
                event("y", 2000L)));
        RecordingWindow.open();
        ScheduleLog.observe(ScheduleEvent.Kind.SEND, "x");
        ScheduleLog.windowOpened();
        Thread.sleep(150L);
        long read = Clocks.nanos();
        assertTrue("from the slot reached toward the frontier's instant, not"
                + " held at the opening's", read >= first + 250L * MS
                && read < first + 2000L * MS);
        freshRun();

        follow(time(ScheduleEvent.ORIGIN, 0L), time(ScheduleEvent.OPEN,
                100L));
        Clocks.nanos();
        first = RowCodec.scheduleNanos(marks(ScheduleEvent.ORIGIN).get(0));
        openWindow();
        Thread.sleep(150L);
        assertTrue("an order with no event caps nothing",
                Clocks.nanos() > first + 200L * MS);
    }

    @Test
    public void anOrderStatingNoOriginLeavesTheHostsClocks() throws Exception {
        follow(startup("register", "dn0", 50L));
        long before = System.nanoTime();
        long read = Clocks.nanos();
        assertTrue("the host's clock", before <= read
                && read <= System.nanoTime());
        JsonObject preContract = RowCodec.writeScheduleEvent(event("x", 1L));
        preContract.remove("ns");
        try {
            RowCodec.readScheduleEvent(preContract);
            assertTrue("a row with no clock stamp is refused", false);
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .startsWith(RowCodec.PRE_CLOCK_CONTRACT));
        }
    }

    /** A read at a cap: never past it. */
    private static void atCap(String why, long cap, long read) {
        assertEquals(why, cap, read);
    }

    /** Reads at the cap, idle between, until the lift is counted. */
    private static void standUntilLifted(String counted) throws Exception {
        long until = System.nanoTime() + 6000L * MS;
        while (!Clocks.progress().contains(counted)
                && System.nanoTime() < until) {
            Clocks.nanos();
            Thread.sleep(100L);
        }
        assertTrue(Clocks.progress(), Clocks.progress().contains(counted));
    }

    @Test
    public void aWaitThatRanItsTimeOutReadsItsDeadlineNeverPastTheCap()
            throws Exception {
        follow(time(ScheduleEvent.ORIGIN, 0L),
                startup("register", "dn0", 100L), time(ScheduleEvent.OPEN,
                        200L));
        Clocks.nanos();
        long first = RowCodec.scheduleNanos(marks(ScheduleEvent.ORIGIN)
                .get(0));
        StartupOrder.done(StartupOrder.begin("register", "dn0"));
        // Standing at the pass, a DataNode waits for its next heartbeat;
        // the window opens and the order stands far ahead of it.
        long[] heartbeat = Clocks.waitBegins(2000L * MS);
        long[] lease = Clocks.waitBegins(10_000L * MS);
        openWindow();
        ScheduleLog.enforceForTests(Collections.singletonList(
                event("x", 5000L)));
        Clocks.timedOut(heartbeat);
        Clocks.waited(heartbeat);
        assertTrue("a wait that ran out reads its deadline",
                Clocks.nanos() >= first + 2100L * MS);
        assertTrue("and so does every thread after it (a value it sets,"
                + " another compares)", elsewhere(true) >= first + 2100L * MS);
        Clocks.timedOut(lease);
        Clocks.waited(lease);
        atCap("and never past the cap", first + 5000L * MS + TICK,
                Clocks.nanos());
    }

    /** What another thread's clock reads now. */
    private static long elsewhere(boolean nanos) throws Exception {
        final long[] read = new long[1];
        Thread reader = new Thread(() -> read[0] = nanos ? Clocks.nanos()
                : Clocks.millis());
        reader.start();
        reader.join();
        return read[0];
    }

    /** This replay follows an order stating these marks. */
    private void follow(JsonObject... marks) throws Exception {
        order = Files.createTempFile("clocks", ".jsonl");
        RowCodec.writeJsonl(order, Arrays.asList(marks));
        System.setProperty(ScheduleLog.PREFIX_PROPERTY, order.toString());
    }

    /** The window opens, in the test's one request. */
    private void openWindow() {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        request = RuntimeTraceContext.beginRequest(node, "clocks-test");
        RecordingWindow.open();
        ScheduleLog.windowOpened();
    }

    private static JsonObject time(String mark, long ms) {
        return RowCodec.writeScheduleTime(mark, ms * MS, ms);
    }

    private static JsonObject startup(String step, String who, long ms) {
        return RowCodec.writeScheduleStartup(step, who, ms * MS, ms);
    }

    /** A SEND of this thread's context the recording made at {@code ms}. */
    private static ScheduleEvent event(String site, long ms) {
        return ScheduleEvent.of(0L, ScheduleEvent.Kind.SEND,
                ScheduleLog.contextOf(Identity.contextHere()), site, 0, "")
                .stamped(ms * MS, ms);
    }

    private List<JsonObject> marks(String kind) {
        List<JsonObject> marks = new ArrayList<JsonObject>();
        synchronized (rows) {
            for (JsonObject row : rows) {
                if (row.has("mark")
                        && kind.equals(row.get("mark").getAsString())) {
                    marks.add(row);
                }
            }
        }
        return marks;
    }

    private List<ScheduleEvent> events() {
        List<ScheduleEvent> events = new ArrayList<ScheduleEvent>();
        synchronized (rows) {
            for (JsonObject row : rows) {
                if (!row.has("mark")) {
                    events.add(RowCodec.readScheduleEvent(row));
                }
            }
        }
        return events;
    }
}
