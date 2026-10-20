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
import org.junit.runner.RunWith;

@RunWith(FreshStatics.class)
public class ScheduleLogTest {
    private final List<JsonObject> written =
            Collections.synchronizedList(new ArrayList<JsonObject>());
    private final ScheduleLog.Sink writer = written::add;

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
        openRequest();
        RecordingWindow.open();
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        ScheduleLog.install(writer);
    }

    private void openRequest() {
        node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        request = RuntimeTraceContext.beginRequest(node, "schedule-test");
    }

    private void restart() {
        written.clear();
        ScheduleLog.install(writer);
    }

    @After
    public void tearDown() {
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        if (request != 0L) RuntimeTraceContext.endRequest(request);
    }

    private static void send(String site) {
        ScheduleLog.observe(SEND, site);
    }

    private static void timeout(long millis) {
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY,
                String.valueOf(millis));
    }

    private static long since(long nanos) {
        return TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - nanos);
    }

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

    private static void joined(Thread... threads) throws InterruptedException {
        for (Thread thread : threads) {
            thread.join(10000L);
            assertFalse(thread.getName() + " still runs", thread.isAlive());
        }
    }

    private static List<String> applied() {
        return Collections.synchronizedList(new ArrayList<String>());
    }

    @Test
    @FreshStatics.Rows(2)
    public void aPlantedRunHoldsTheRealizedOrder() throws Exception {
        Object other = new Object();
        RuntimeTraceContext.registerSource(other, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "t/dn1", 0L));
        String contexts = "graphchecker.test.schedule.contexts";
        if (FreshStatics.row() == 0) {
            runBoth(other, 0L);
            List<ScheduleEvent> free = events();
            assertEquals(SEND, free.get(0).kind());
            System.setProperty(contexts, free.get(0).context() + "\n"
                    + free.get(1).context());
            return;
        }
        String[] free = System.getProperty(contexts).split("\n");
        System.clearProperty(contexts);
        String ours = free[0];
        String theirs = free[1];
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
            Files.delete(plant);
        }
    }

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

    private List<String> sends() {
        List<String> sends = new ArrayList<String>();
        for (ScheduleEvent event : events()) {
            if (event.kind() == SEND) {
                sends.add(event.context() + " k=" + event.k());
            }
        }
        return sends;
    }

    @Test
    public void aViewsPublicationIsHeldAtItsPlaceByTheNodesPublisher()
            throws Exception {
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

        restart();
        String next = ScheduleEvent.published("SOLR_ZK", path, 9L);
        assertFalse("no order: in force at once", door(view, 9L,
                () -> send("inside"), next));
        assertEquals(Arrays.asList("inside", next), sites());
        assertEquals(PUBLISH, events().get(1).kind());
        assertEquals(VIEW_NODE + "|VIEW", events().get(1).context());
    }

    @Test(timeout = 30000L)
    public void aNewerVersionsDoorKeepsAnOlderOneInFlight() throws Exception {
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

    private static void held(long millis, boolean asking) {
        long until = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(millis);
        while (System.nanoTime() < until) {
            if (asking) ScheduleLog.waitsNoMore();
        }
    }

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

    /**
     * A poll that comes again while its context holds an open slot after
     * its key's last slot is past its loop's recorded count: it takes no
     * slot, so it neither passes that slot nor waits at the key's next
     * slot, a later loop's (hbase-adhoc-13 NP18: waitProcedure polled once
     * more than recorded and gave up 918 slots).  A loop left early still
     * passes its rest (hdfs-adhoc-44), and a poll whose context holds no
     * open slot in between takes the next slot.
     */
    @Test
    @FreshStatics.Rows(3)
    public void aPollPastItsLoopsCountTakesNoLaterLoopsSlot() {
        timeout(5000L);
        String[][] rows = {
            {"SEND x,WAKE w,SEND y,SEND x,WAKE w", "SEND x,WAKE w,WAKE w,"
                    + "SEND y,SEND x,WAKE w", " 0 given up in 0 stall(s)",
                    " 0 passed by", "; 1 event(s) ran free"},
            {"SEND p,WAKE w,SEND p,WAKE w,SEND a", "SEND p,WAKE w,SEND a",
                    " 0 given up in 0 stall(s)", " 1 passed by",
                    "; 0 event(s) ran free"},
            {"WAKE w,SEND y,WAKE w", "WAKE w,SEND y,WAKE w", " 3 taken",
                    " 0 passed by", "; 0 event(s) ran free"}};
        String[] row = rows[FreshStatics.row()];
        List<ScheduleEvent> recorded = new ArrayList<ScheduleEvent>();
        for (String event : row[0].split(",")) {
            String[] at = event.split(" ");
            recorded.add(event(Kind.valueOf(at[0]), at[1]));
        }
        enforce(recorded);
        List<String> made = new ArrayList<String>();
        long before = System.nanoTime();
        for (String event : row[1].split(",")) {
            String[] at = event.split(" ");
            ScheduleLog.observe(Kind.valueOf(at[0]), at[1]);
            made.add(at[1]);
        }
        assertTrue("no stall: " + ScheduleLog.progress(),
                since(before) < 1000L);
        assertEquals(made, sites());
        for (int at = 2; at < row.length; at++) progress(row[at]);
    }

    /**
     * A poll past its count whose context's next slot is not yet due waits
     * held there: it bounds no give-up of the frontier before it, another
     * context's event that comes late (hbase-adhoc-13 X191: the surplus poll
     * waited unheld and gave up 763 slots before its context's next one).
     */
    @Test
    @FreshStatics.Rows(2)
    public void aPollPastItsCountBehindAnotherContextBoundsNoGiveUp()
            throws Exception {
        Object other = new Object();
        RuntimeTraceContext.registerSource(other, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "t/dn1", 0L));
        String carried = "graphchecker.test.schedule.recorded";
        if (FreshStatics.row() == 0) {
            pollAroundTheirs(other, 0L, false);
            StringBuilder rows = new StringBuilder();
            for (ScheduleEvent event : events()) {
                rows.append(RowCodec.toLine(RowCodec.writeScheduleEvent(
                        event))).append('\n');
            }
            System.setProperty(carried, rows.toString());
            return;
        }
        List<ScheduleEvent> recorded = new ArrayList<ScheduleEvent>();
        for (String row : System.getProperty(carried).split("\n")) {
            recorded.add(RowCodec.readScheduleEvent(RowCodec.fromLine(row)));
        }
        System.clearProperty(carried);
        timeout(10000L);
        enforce(recorded);
        pollAroundTheirs(other, 3500L, true);
        assertEquals(Arrays.asList("w", "w", "f", "n", "w"), sites());
        progress(" 0 given up in 0 stall(s)");
    }

    private static void pollAroundTheirs(Object other, long late,
                                         boolean pollsAgain)
            throws Exception {
        ScheduleLog.observe(WAKE, "w");
        Thread theirs = started(() -> {
            long own = RuntimeTraceContext.beginRequest(other, "theirs");
            try {
                Thread.sleep(late);
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
            send("f");
            RuntimeTraceContext.endRequest(own);
        });
        if (pollsAgain) {
            ScheduleLog.observe(WAKE, "w");
        } else {
            theirs.join();
        }
        send("n");
        ScheduleLog.observe(WAKE, "w");
        theirs.join();
    }

    private static List<ScheduleEvent> order(ScheduleEvent first,
                                             List<ScheduleEvent> rest) {
        List<ScheduleEvent> order = new ArrayList<ScheduleEvent>();
        order.add(first);
        order.addAll(rest);
        return order;
    }

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
    }

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

    private static Thread reading(Object owner, String key,
                                  List<Boolean> named) {
        return started(() -> MessageDoors.notified("Watcher", "STORE", null,
                "NodeDataChanged", () -> {
            MessageDoors.fetched("STORE", key, owner, null);
            named.add(MessageDoors.current() != null);
        }));
    }

    private static void turn(String kind) {
        if (kind.equals("W")) {
            written("/p");
        } else {
            MessageDoors.reading("STORE", "/p");
        }
    }

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

    @Test(timeout = 60000L)
    public void aWriteWaitingOnlyBehindReadsStandsNoCeiling()
            throws Exception {
        enforceRecorded("o:R c:W", 300L, kind -> turn(kind));
        CountDownLatch written = new CountDownLatch(1);
        long before = System.nanoTime();
        Thread poller = started(() -> request("o", () -> {
            long spun = 0L;
            while (written.getCount() > 0L) spun++;
            assertTrue(spun > 0L);
        }));
        Thread write = started(() -> request("c", () -> {
            turn("W");
            written.countDown();
        }));
        write.join(30000L);
        long took = since(before);
        written.countDown();
        poller.join(30000L);
        assertFalse(write.isAlive() || poller.isAlive());
        assertTrue("a grace, not the ceiling: " + took,
                took < 3 * 300L);
    }

    private void noRequest() {
        written.clear();
        reset();
        RuntimeTraceContext.endRequest(request);
        request = 0L;
    }

    private void request(String api, Runnable inside) {
        long token = RuntimeTraceContext.beginRequest(node, api);
        try {
            inside.run();
        } finally {
            RuntimeTraceContext.endRequest(token);
        }
    }

    private static void written(String location) {
        MessageDoors.storeEnded("STORE", MessageDoors.storing("STORE",
                location));
    }

    @Test
    public void aNotifySentWhileAHeldWaitIsOutOfTheWaitSetIsNotLost()
            throws Exception {
        timeout(30000L);
        Object monitor = new Object();
        for (boolean opening : new boolean[] {false, true}) {
            restart();
            if (opening) RecordingWindow.reset();
            enforce(prefix("x"));
            Thread idle = waits(monitor, WORK, 1, true).get(0);
            if (opening) Thread.sleep(100L);
            synchronized (monitor) {
                if (opening) {
                    RecordingWindow.open();
                    TimedWaits.windowOpened();
                } else {
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

    private static ScheduleEvent inOccurrence(Kind kind, String site,
                                              String occurrence) {
        return ScheduleEvent.of(0L, kind,
                ScheduleLog.contextOf(Identity.contextHere()), site, 0,
                occurrence, "");
    }

    private static Thread observer(Kind kind, String site) {
        return started(() -> ScheduleLog.observe(kind, site));
    }

    private static void enforce(List<ScheduleEvent> prefix) {
        enforce(prefix, Collections.<ScheduleEvent>emptyList());
    }

    private static void enforce(List<ScheduleEvent> prefix,
                                List<ScheduleEvent> rest) {
        ScheduleLog.enforceForTests(prefix, rest, false);
    }

    private static List<ScheduleEvent> prefix(String... sites) {
        List<ScheduleEvent> events = new ArrayList<ScheduleEvent>();
        for (String site : sites) events.add(event(SEND, site));
        return events;
    }

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

    private void enforceRecorded(String turns, long timeout,
                                 java.util.function.Consumer<String> make) {
        noRequest();
        for (String turn : turns.split(" ")) {
            String[] at = turn.split(":", 2);
            request(at[0], () -> make.accept(at[1]));
        }
        List<ScheduleEvent> recorded = events();
        noRequest();
        timeout(timeout);
        enforce(recorded);
    }
}
