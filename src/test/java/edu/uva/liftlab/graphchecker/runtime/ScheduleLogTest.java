package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.PUBLISH;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.RECV;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.SEND;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.START;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.WAKE;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.WRITE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind;
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
import java.util.concurrent.locks.Condition;
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
    private final ScheduleLog.Sink writer = written::add;

    /**
     * The node every test's threads run for.  An event with no identity
     * holds no place in the order, so the test thread opens one request and
     * every thread a test starts inherits it: they all state one context.
     */
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private static final String VIEW_NODE = "auto0/node0#epoch0";
    private static final LocationId VIEW = view(VIEW_NODE, "/c.json");
    private static final String V8 = published(8L);
    private static final String V9 = published(9L);
    private static final String WORK = "<C: boolean waitForWork()>#u21";
    private long request;
    private Object node;

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
        node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        request = RuntimeTraceContext.beginRequest(node, "schedule-test");
    }

    /** A fresh schedule, written into {@link #written} again. */
    private void restart() {
        written.clear();
        ScheduleLog.resetForTests();
        ScheduleLog.install(writer);
    }

    /** A fresh schedule and publication account. */
    private void fresh() {
        restart();
        Confirmation.resetForTests();
    }

    @After
    public void tearDown() {
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        Confirmation.resetForTests();
        ScheduleLog.resetForTests();
        StartupOrder.resetForTests();
        if (request != 0L) RuntimeTraceContext.endRequest(request);
    }

    private static void send(String site) {
        ScheduleLog.observe(SEND, site);
    }

    private static void timeout(long millis) {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY,
                String.valueOf(millis));
    }

    /** Milliseconds since {@code nanos}. */
    private static long since(long nanos) {
        return TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - nanos);
    }

    /** The order's account states {@code fragment}. */
    private static void progress(String fragment) {
        progress("", fragment);
    }

    private static void progress(String why, String fragment) {
        String progress = ScheduleLog.progress();
        assertTrue(why + progress, progress.contains(fragment));
    }

    private static Thread started(Runnable work) {
        Thread thread = new Thread(work);
        thread.start();
        return thread;
    }

    /** Each thread joined and gone. */
    private static void joined(Thread... threads) throws InterruptedException {
        for (Thread thread : threads) {
            thread.join(10000L);
            assertFalse(thread.getName() + " still runs", thread.isAlive());
        }
    }

    private static List<String> applied() {
        return Collections.synchronizedList(new ArrayList<String>());
    }

    /**
     * A NATIVE REPRODUCTION HOLDS THE CONFIRMED WORLD'S ORDER at admission
     * (explore.RealizedOrder): an event waits until the event its row orders
     * before it was made in another context; one whose before-event does not
     * come within the order's timeout goes on, and every hold of the run
     * gives way after it.
     */
    @Test
    public void aPlantedRunHoldsTheRealizedOrder() throws Exception {
        Object other = new Object();
        RuntimeTraceContext.registerSource(other, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "t/dn1", 0L));
        runBoth(other, 0L);
        List<ScheduleEvent> free = events();
        assertEquals(SEND, free.get(0).kind());
        String ours = free.get(0).context();
        String theirs = free.get(1).context();
        restart();
        // Ours waits for theirs; a second of ours for an event never made.
        Path plant = Files.createTempFile("plant", ".jsonl");
        Files.write(plant, Arrays.asList(
                order(0, theirs, "WRITE", "ZK:/a", ours, "SEND", "x"),
                order(1, theirs, "WRITE", "ZK:/never", ours, "SEND", "y")),
                StandardCharsets.UTF_8);
        ScheduleLog.realizedForTests(plant);
        System.setProperty(Confirmation.ORDER_TIMEOUT_PROPERTY, "400");
        try {
            runBoth(other, 300L);
            assertEquals("held until theirs: " + events(),
                    Arrays.asList(WRITE, SEND), kinds());
            assertFalse(RecordingPlant.orderGaveWay());
            long started = System.nanoTime();
            send("y");
            assertTrue("an order never met goes on at its timeout",
                    since(started) >= 300L);
            assertTrue(RecordingPlant.orderGaveWay());
        } finally {
            System.clearProperty(Confirmation.ORDER_TIMEOUT_PROPERTY);
            RecordingPlant.resetForTests();
            Files.delete(plant);
        }
    }

    /** Ours SENDs x while another context WRITEs ZK:/a {@code late} ms
     *  after both started. */
    private static void runBoth(Object other, long late) throws Exception {
        CountDownLatch go = new CountDownLatch(1);
        Thread theirs = started(() -> {
            long own = RuntimeTraceContext.beginRequest(other, "theirs");
            try {
                go.await();
                Thread.sleep(late + 50L);
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
            ScheduleLog.observe(WRITE, "ZK:/a");
            RuntimeTraceContext.endRequest(own);
        });
        go.countDown();
        send("x");
        theirs.join();
    }

    /** One realized ORDER row of the plant. */
    private static String order(int row, String beforeContext,
                                String beforeKind, String beforeSite,
                                String afterContext, String afterKind,
                                String afterSite) {
        JsonObject order = new JsonObject();
        order.addProperty(RecordingPlant.KIND, RecordingPlant.ORDER);
        order.addProperty(RecordingPlant.SCOPE, "EVENT");
        order.add("before", Fixtures.json("{'kind':'" + beforeKind
                + "','context':'" + beforeContext + "','site':'" + beforeSite
                + "','k':0}"));
        order.add("after", Fixtures.json("{'kind':'" + afterKind
                + "','context':'" + afterContext + "','site':'" + afterSite
                + "','k':0}"));
        order.addProperty(RecordingPlant.ROW, row);
        return order.toString();
    }

    /**
     * An event survives its row, and a torn last row ends the read; the
     * recorder counts k per key, drains what came before it was installed,
     * and nothing is recorded before the window opens.
     */
    @Test
    public void theRecorderCountsKPerKeyAndDrainsWhatCameFirst()
            throws Exception {
        ScheduleEvent event = ScheduleEvent.of(7L, RECV,
                "hdfs/nn0#epoch0|Anchor:ab12@HADOOP_IPC/heartbeat",
                "HADOOP_IPC#REQUEST", 3, "occ-1", "");
        ScheduleEvent bare = ScheduleEvent.of(0L, WAKE, "",
                "tick.KEY_MANAGER_TICK", 0, "", "");
        String last = RowCodec.toLine(RowCodec.writeScheduleEvent(bare));
        Path file = Files.createTempFile("schedule", ".jsonl");
        Files.write(file, (RowCodec.toLine(RowCodec.writeScheduleEvent(event))
                + "\n" + last + "\n" + last.substring(0, last.length() / 2))
                .getBytes(StandardCharsets.UTF_8));
        assertEquals(Arrays.asList(event, bare),
                SessionReader.readSchedule(file));
        Files.delete(file);

        ScheduleLog.resetForTests();
        written.clear();
        ScheduleLog.observe(START, "<A: void a()>#u1");
        send("HADOOP_IPC#REQUEST");
        ScheduleLog.install(writer);
        ScheduleLog.observe(START, "<A: void a()>#u1");
        List<ScheduleEvent> events = events();
        assertEquals(3, events.size());
        for (int at = 0; at < 3; at++) {
            assertEquals((long) at, events.get(at).seq());
            assertEquals(at == 2 ? 1 : 0, events.get(at).k());
        }
        assertTrue("observe answers whether it wrote", ScheduleLog.observe(
                SEND, "x"));
        RecordingWindow.reset();
        assertFalse(ScheduleLog.observe(SEND, "HADOOP_IPC#REQUEST"));
        assertEquals(4, sites().size());
    }

    /**
     * Threads started inside one scope count their events apart: the start
     * frame is part of an event's context (IDENTITY §8); a thread no woven
     * start handed work keeps the scope's context.
     */
    @Test
    public void threadsStartedInOneScopeCountTheirOwnEvents() throws Exception {
        written.clear();
        String site = "<A: void spawn()>#u2";
        List<Thread> spawned = new ArrayList<Thread>();
        for (int index = 0; index < 2; index++) {
            Thread thread = new Thread(() -> {
                send("HADOOP_IPC#REQUEST");
                send("HADOOP_IPC#REQUEST");
            });
            Identity.startWork(site, thread, null);
            spawned.add(thread);
        }
        // The second thread runs first: its sends are still its own 0 and 1.
        for (int index = spawned.size() - 1; index >= 0; index--) {
            spawned.get(index).start();
            spawned.get(index).join();
        }
        started(() -> send("HADOOP_IPC#REQUEST")).join();
        String scope = ScheduleLog.contextOf(Identity.contextHere());
        assertEquals(Arrays.asList(
                scope + "|" + site + "@1 k=0", scope + "|" + site + "@1 k=1",
                scope + "|" + site + "@0 k=0", scope + "|" + site + "@0 k=1",
                scope + " k=0"), sends());
    }

    /** The SENDs written, each by its context and k. */
    private List<String> sends() {
        List<String> sends = new ArrayList<String>();
        for (ScheduleEvent event : events()) {
            if (event.kind() == SEND) {
                sends.add(event.context() + " k=" + event.k());
            }
        }
        return sends;
    }

    /**
     * A NODE'S VIEW PUBLICATION IS AN EVENT OF ITS OWN (PUBLISH; SGF2
     * snapshot-no-active: the seed published v8 after the CREATESNAPSHOT
     * read the recording ran after it): it stands at the node's |VIEW
     * stance, whatever callback made it, and holds its place.  A
     * notification's publication whose turn is not due is handed to the
     * node's publisher; the callback goes on at once (it holds its
     * collection's refresh lock).  Where no order holds it is published at
     * once, its event written when the callback ends.
     */
    @Test
    public void aViewsPublicationIsHeldAtItsPlaceByTheNodesPublisher()
            throws Exception {
        Confirmation.resetForTests();
        String path = "/collections/c/state.json";
        String site = ScheduleEvent.published("SOLR_ZK", path, 8L);
        enforce(Arrays.asList(event(SEND, "before"), publish(VIEW_NODE, site),
                event(SEND, "after")));
        assertFalse("behind the SEND the recording made first",
                ScheduleLog.dueNow(PUBLISH, site,
                        ScheduleLog.viewStance(VIEW_NODE)));
        LocationId view = view(VIEW_NODE, path);
        List<String> applied = applied();
        long started = System.nanoTime();
        assertTrue("handed to the node's publisher", door(view, 8L,
                () -> applied.add("v8"), site));
        assertTrue("the callback goes on at once", since(started) < 200L);
        boolean[] sawApplied = new boolean[1];
        Thread after = started(() -> {
            send("after");
            sawApplied[0] = applied.contains("v8");
        });
        Thread.sleep(200L);
        assertTrue("nothing applied before its turn: " + applied,
                applied.isEmpty());
        assertTrue("nothing past the frontier: " + sites(), sites().isEmpty());
        send("before");
        joined(after);
        awaitSize(applied, 1);
        assertEquals(Arrays.asList("v8"), applied);
        assertTrue("the successor is let go once v8 is in force",
                sawApplied[0]);
        assertEquals(Arrays.asList("before", site, "after"), sites());
        progress(" 0 given up");

        fresh();
        String next = ScheduleEvent.published("SOLR_ZK", path, 9L);
        assertFalse("no order: in force at once", door(view, 9L,
                () -> send("inside"), next));
        assertEquals(Arrays.asList("inside", next), sites());
        assertEquals(PUBLISH, events().get(1).kind());
        assertEquals(VIEW_NODE + "|VIEW", events().get(1).context());
    }

    /**
     * A NEWER VERSION'S DOOR NEVER GIVES UP AN OLDER ONE IN FLIGHT (review
     * SA): v8's callback has begun its turn and is still publishing when
     * v9's reaches its door.  v8's slot is on its way, so v9's turn is not
     * due: v9 goes to the publisher, the order stays v8 then v9, and what v8
     * holds back sees v8.  Given up at v9's door, v8's slot let it read v7.
     */
    @Test(timeout = 30000L)
    public void aNewerVersionsDoorKeepsAnOlderOneInFlight() throws Exception {
        Confirmation.resetForTests();
        enforce(Arrays.asList(publish(VIEW_NODE, V8), publish(VIEW_NODE, V9),
                event(SEND, "after")));
        List<String> applied = applied();
        CountDownLatch publishing = new CountDownLatch(1);
        CountDownLatch constructed = new CountDownLatch(1);
        Thread first = started(() -> door(VIEW, 8L, () -> {
            publishing.countDown();
            try {
                constructed.await();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
            applied.add("v8");
        }, V8));
        publishing.await();
        boolean[] sawV8 = new boolean[1];
        Thread after = started(() -> {
            send("after");
            sawV8[0] = applied.contains("v8");
        });
        assertTrue("v8 in flight: v9's turn is not due, handed to the"
                + " publisher", door(VIEW, 9L, () -> applied.add("v9"), V9));
        Thread.sleep(200L);
        assertTrue("nothing past v8 before it is in force: " + applied,
                applied.isEmpty());
        constructed.countDown();
        first.join(5000L);
        joined(after);
        assertTrue("what v8 holds back sees it", sawV8[0]);
        awaitSize(applied, 2);
        assertEquals(Arrays.asList("v8", "v9"), applied);
        assertEquals(Arrays.asList(V8, V9, "after"), sites());
        progress(" 0 given up");
    }

    /** Spins {@code millis}, asking the order between spins where
     *  {@code asking} (review R2b: blocked on the watchdog, no cycle). */
    private static void held(long millis, boolean asking) {
        long until = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(millis);
        while (System.nanoTime() < until) {
            if (asking) ScheduleLog.waitsNoMore();
        }
    }

    /**
     * A notification's publication at its node's door, as a store
     * notification's callback makes it: deferred to the node's publisher,
     * or published by the caller, its turn settled when the callback ends.
     *
     * @return whether it was deferred to the node's publisher
     */
    private static boolean door(LocationId view, long version, Runnable apply,
                                String turn) {
        int callback = Confirmation.notificationBegins();
        try {
            boolean deferred = Confirmation.publishing(view, version, null,
                    view.owner().substring("SOLR_ZK@".length()), null, apply,
                    turn);
            if (!deferred) apply.run();
            return deferred;
        } finally {
            Confirmation.notificationEnded(callback);
        }
    }

    private static String published(long version) {
        return ScheduleEvent.published("SOLR_ZK", "/c.json", version);
    }

    private static ScheduleEvent publish(String node, String site) {
        return ScheduleEvent.of(0L, PUBLISH, node + "|VIEW", site, 0, "", "");
    }

    private static LocationId view(String node, String path) {
        return LocationId.of(LocationKind.VIEW, "SOLR_ZK@" + node, path);
    }

    private static void awaitSize(List<String> list, int size)
            throws InterruptedException {
        awaitSize(list, size, 5000L);
    }

    private static void awaitSize(List<String> list, int size, long within)
            throws InterruptedException {
        long deadline = System.currentTimeMillis() + within;
        while (list.size() < size && System.currentTimeMillis() < deadline) {
            Thread.sleep(20L);
        }
    }

    /**
     * A thread whose event is not next waits for its turn; an interrupt
     * while it waits is the workload's to see, and the order stands; a
     * stalled slot is given up and z takes it, an event the order lacks runs
     * free, and so does everything once the prefix is used up.
     */
    @Test
    public void aThreadWhoseEventIsNotNextWaitsForItsTurn() throws Exception {
        enforce(prefix("x", "y"));
        CountDownLatch waiting = new CountDownLatch(1);
        Thread late = started(() -> {
            waiting.countDown();
            send("y");
        });
        waiting.await();
        Thread.sleep(200L);
        assertTrue("y must wait for x", written.isEmpty());
        send("x");
        joined(late);
        assertEquals(Arrays.asList("x", "y"), sites());
        progress(" 0 given up");
        assertFalse("the prefix is used up", ScheduleLog.enforcing());

        restart();
        enforce(prefix("x", "y"));
        boolean[] flagged = new boolean[1];
        Thread waiter = started(() -> {
            send("y");
            flagged[0] = Thread.currentThread().isInterrupted();
        });
        Thread.sleep(200L);
        waiter.interrupt();
        joined(waiter);
        assertTrue("the interrupt is the workload's to see", flagged[0]);
        progress(" 0 given up");
        assertTrue("the prefix still stands", ScheduleLog.enforcing());
    }

    @Test
    public void aStalledSlotIsGivenUpAndAnEventTheOrderLacksRunsFree()
            throws Exception {
        timeout(300L);
        enforce(prefix("x", "z"));
        long before = System.nanoTime();
        send("w");
        assertTrue("no slot holds w: it runs free at once",
                since(before) < 200L);
        joined(started(() -> send("z")));
        assertEquals(Arrays.asList("w", "z"), sites());
        progress(" 1 given up");
        assertFalse(ScheduleLog.enforcing());
        before = System.nanoTime();
        send("q");
        assertTrue("a free run admits at once", since(before) < 200L);
    }

    /** {@code first}, then {@code rest}. */
    private static List<ScheduleEvent> order(ScheduleEvent first,
                                             List<ScheduleEvent> rest) {
        List<ScheduleEvent> order = new ArrayList<ScheduleEvent>();
        order.add(first);
        order.addAll(rest);
        return order;
    }

    /**
     * PROGRESS IS WHAT IS NEW ({@link ScheduleLog#newKeys}, as the replay's
     * watch counts it, {@link ConcolicResultPublisher#watched}): the turns
     * of a poll loop, each its own root occurrence, doing again what the
     * first did -- its wake, its send, its write to the queue's next
     * sequential znode, a site spelled by a fresh port, session id or
     * object, a view published again at its next version (SGF7-adhoc-09: a
     * leader election failing once a minute) -- make nothing new; other
     * code, another location or another
     * node does, and so does the window's close.  Counted as steps, every
     * turn moved (PV7-38: PULL replicas polling a leader left down kept
     * replays alive until replay_timeout_s).
     */
    @Test
    public void aLoopDoingAgainWhatItDidMakesNothingNew() {
        noRequest();
        ScheduleLog.countNewEvents();
        int made = -1;
        long[] watched = null;
        for (int turn = 0; turn < 3; turn++) {
            final int n = turn;
            request("poll", () -> {
                ScheduleLog.observe(WAKE, "tick.poll");
                send("HTTP#REQUEST:replication");
                ScheduleLog.observe(WRITE,
                        "ZK:/overseer/queue/qn-000000000" + n);
                send("HTTP#REQUEST@127.0.0.1:5430" + n);
                ScheduleLog.observe(WRITE,
                        "ZK:/sessions/" + (72150482482561029L + n));
                ScheduleLog.observe(START,
                        "<S: void s()>#u1 Searcher@1a2b3c" + n);
                ScheduleLog.observe(PUBLISH,
                        "SOLR_ZK:/collections/c/state.json@" + (7 + n));
            });
            if (made < 0) {
                made = ScheduleLog.newKeys();
                watched = ConcolicResultPublisher.watched(0L);
            }
        }
        assertEquals("seven distinct events", 7, made);
        assertEquals(events().toString(), 21, events().size());
        assertEquals("turns two and three: nothing new", made,
                ScheduleLog.newKeys());
        assertTrue(Arrays.equals(watched,
                ConcolicResultPublisher.watched(0L)));
        request("poll", () -> send("HTTP#REQUEST:update"));
        assertEquals("another request", made + 1, ScheduleLog.newKeys());
        request("poll", () -> ScheduleLog.observe(WRITE,
                "ZK:/overseer/collection-queue-work/qn-0000000000"));
        assertEquals("another location", made + 2, ScheduleLog.newKeys());
        Object other = new Object();
        RuntimeTraceContext.registerSource(other, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "t/dn1", 0L));
        long elsewhere = RuntimeTraceContext.beginRequest(other, "poll");
        try {
            ScheduleLog.observe(WAKE, "tick.poll");
        } finally {
            RuntimeTraceContext.endRequest(elsewhere);
        }
        assertEquals("another node", made + 3, ScheduleLog.newKeys());
        progress((made + 3) + " distinct event(s), at most ");
        watched = ConcolicResultPublisher.watched(0L);
        RecordingWindow.close();
        assertFalse("the window's close is a step", Arrays.equals(watched,
                ConcolicResultPublisher.watched(0L)));
    }

    /** The workload closes its window: what the order still holds goes. */
    @Test(timeout = 20000L)
    public void closingTheWindowLetsTheOrderGo() throws Exception {
        timeout(30000L);
        enforce(prefix("x", "y"));
        Thread y = observer(SEND, "y");
        Thread.sleep(200L);
        assertTrue("y waits for x", y.isAlive());
        CausynthTraceRecorder.stopRecording();
        joined(y);
        assertFalse(ScheduleLog.enforcing());
        progress("2 open at the window's close");
    }

    /** A notification on a thread of its own reading {@code key}: whether a
     *  write named its work goes to {@code named}. */
    private static Thread reading(Object owner, String key,
                                  List<Boolean> named) {
        return started(() -> MessageDoors.notified("Watcher", "STORE", null,
                "NodeDataChanged", () -> {
            MessageDoors.fetched("STORE", key, owner, null);
            named.add(MessageDoors.current() != null);
        }));
    }

    /** A write ("W") or a read ("R") of /p at its turn. */
    private static void turn(String kind) {
        if (kind.equals("W")) {
            written("/p");
        } else {
            MessageDoors.reading("STORE", "/p");
        }
    }

    /**
     * A write whose slot is past the cut holds nothing of its own, but waits
     * behind the prefix's write to its location until it is made.
     */
    @Test(timeout = 30000L)
    public void aWritePastTheCutWaitsBehindThePrefixsWriteThere()
            throws Exception {
        noRequest();
        request("o", () -> written("/p"));
        request("c", () -> written("/p"));
        List<ScheduleEvent> recorded = events();
        noRequest();
        timeout(30000L);
        enforce(recorded.subList(0, 1), recorded.subList(1, 2));
        Thread c = started(() -> request("c", () -> written("/p")));
        Thread.sleep(500L);
        assertTrue("c's rest write waits for o's prefix write", c.isAlive());
        request("o", () -> written("/p"));
        joined(c);
        assertEquals(Arrays.asList(recorded.get(0).context(),
                recorded.get(1).context()), Arrays.asList(
                events().get(0).context(), events().get(1).context()));
        progress(" 0 given up");
    }

    /** A fresh run on this thread, its schedule empty, with no request
     *  standing, so the next one roots its lineage. */
    private void noRequest() {
        written.clear();
        reset();
        RuntimeTraceContext.endRequest(request);
        request = 0L;
    }

    /** One workload request {@code api}, rooting its lineage, running
     *  {@code inside}. */
    private void request(String api, Runnable inside) {
        long token = RuntimeTraceContext.beginRequest(node, api);
        try {
            inside.run();
        } finally {
            RuntimeTraceContext.endRequest(token);
        }
    }

    /** One write to the shared store at {@code location}: its bracket. */
    private static void written(String location) {
        MessageDoors.storeEnded("STORE", MessageDoors.storing("STORE",
                location));
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
        timeout(30000L);
        Object monitor = new Object();
        for (boolean opening : new boolean[] {false, true}) {
            restart();
            // Opening: the wait starts free, on the wall clock, in the set.
            if (opening) RecordingWindow.reset();
            enforce(prefix("x"));
            Thread idle = waits(monitor, WORK, 1, true).get(0);
            if (opening) Thread.sleep(100L);
            synchronized (monitor) {
                if (opening) {
                    // The opening takes the wait out of the wait set; the
                    // notify that follows reaches only its mark.
                    RecordingWindow.open();
                    TimedWaits.windowOpened();
                } else {
                    // Held past a quantum: the wait stands outside the wait
                    // set, blocked on this monitor, when the notify is sent.
                    Thread.sleep(200L);
                }
                TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
            }
            String row = opening ? "the window opened" : "a quantum ran out";
            idle.join(5000L);
            assertFalse(row + ": the notify was state the wait read",
                    idle.isAlive());
            assertTrue(row + ": and it is no event", written.isEmpty());
            progress(" 0 given up");
        }
        restart();
        enforce(prefix("x"));
        ReentrantLock lock = new ReentrantLock();
        Condition ready = lock.newCondition();
        boolean[] signalled = new boolean[1];
        CountDownLatch waiting = new CountDownLatch(1);
        Thread taker = started(() -> {
            lock.lock();
            try {
                waiting.countDown();
                signalled[0] = TimedWaits.await(ready, 60L, TimeUnit.SECONDS,
                        "<Q: java.lang.Object take()>#u8");
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            } finally {
                lock.unlock();
            }
        });
        waiting.await();
        lock.lock();
        try {
            Thread.sleep(200L);
            TimedWaits.signal(ready, "<Q: void put(java.lang.Object)>#u2");
        } finally {
            lock.unlock();
        }
        joined(taker);
        assertTrue("the signal was state the await read", signalled[0]);
        assertTrue(written.isEmpty());
    }

    /**
     * A notify ends one wait and a notifyAll every one, held or free.  An
     * untimed wait the notifyAll carrying another's notify woke goes back
     * to waiting: it ends by its own notify only.
     */
    @Test
    public void aNotifyEndsOneWaitAndANotifyAllEndsEvery() throws Exception {
        timeout(30000L);
        Object monitor = new Object();
        for (boolean held : new boolean[] {true, false}) {
            restart();
            if (held) enforce(prefix("x"));
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
            joined(first.toArray(new Thread[0]));
            List<Thread> second = waits(monitor, "<C: void loop()>#u7", 2,
                    held);
            synchronized (monitor) {
                TimedWaits.notifyAllOn(monitor, "<C: void n()>#u2");
            }
            joined(second.toArray(new Thread[0]));
            assertTrue(row, written.isEmpty());
            if (held) progress(" 0 given up");
        }
    }

    /**
     * {@code count} woven waits at {@code site} on {@code monitor}, each
     * standing in it: a minute long when {@code timed}, else untimed.
     */
    private static List<Thread> waits(Object monitor, String site, int count,
                                      boolean timed)
            throws InterruptedException {
        CountDownLatch waiting = new CountDownLatch(count);
        List<Thread> threads = new ArrayList<Thread>();
        for (int index = 0; index < count; index++) {
            threads.add(started(() -> {
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
            }));
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

    /** One event of this thread's context inside a recorded occurrence. */
    private static ScheduleEvent inOccurrence(Kind kind, String site,
                                              String occurrence) {
        return ScheduleEvent.of(0L, kind,
                ScheduleLog.contextOf(Identity.contextHere()), site, 0,
                occurrence, "");
    }

    /** A thread that makes one event, blocking for its turn; started. */
    private static Thread observer(Kind kind, String site) {
        return started(() -> ScheduleLog.observe(kind, site));
    }

    /** Holds this run to {@code prefix}, with no rest after it. */
    private static void enforce(List<ScheduleEvent> prefix) {
        enforce(prefix, Collections.<ScheduleEvent>emptyList());
    }

    /** Holds this run to {@code prefix}, then {@code rest}. */
    private static void enforce(List<ScheduleEvent> prefix,
                                List<ScheduleEvent> rest) {
        ScheduleLog.enforceForTests(prefix, rest, false);
    }

    /** A prefix of SEND events at these sites, on this thread's context. */
    private static List<ScheduleEvent> prefix(String... sites) {
        List<ScheduleEvent> events = new ArrayList<ScheduleEvent>();
        for (String site : sites) events.add(event(SEND, site));
        return events;
    }

    /** One event as this JVM's threads compute it: every one of them runs
     *  in the test's one request, so every one states the same context. */
    private static ScheduleEvent event(Kind kind, String site) {
        return inOccurrence(kind, site, "");
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

    private List<Kind> kinds() {
        List<Kind> kinds = new ArrayList<Kind>();
        for (ScheduleEvent event : events()) kinds.add(event.kind());
        return kinds;
    }

    private List<String> sites() {
        List<String> sites = new ArrayList<String>();
        for (ScheduleEvent event : events()) sites.add(event.site());
        return sites;
    }
}
