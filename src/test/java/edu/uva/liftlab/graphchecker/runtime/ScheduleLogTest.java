package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.CLAIM;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.END;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.INTERRUPT;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.PUBLISH;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.RECV;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.SEND;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.START;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.WAKE;
import static edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.WRITE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.Role;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
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
    private static final String V7 = published(7L);
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

    /** Sleeps where no InterruptedException may escape. */
    private static void nap(long millis) {
        try {
            Thread.sleep(millis);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
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

    /** Every unattributed thread shares one context, so its k would be a
     *  cross-thread counter: an event with no identity holds no place. */
    @Test
    public void anEventWithNoIdentityHoldsNoPlace() {
        RuntimeTraceContext.endRequest(request);
        request = 0L;
        assertTrue(Identity.contextHere().isLost());
        ScheduleLog.observe(START, "<A: void a()>#u1");
        send("HADOOP_IPC#REQUEST");
        assertTrue(events().toString(), written.isEmpty());
    }

    /**
     * A response stands where its request was received, whichever thread
     * sends it (a deferred RPC response's sender), not under its own.
     */
    @Test
    public void aResponseStandsWhereItsRequestWasReceived() throws Exception {
        ScheduleLog.Stance receipt = ScheduleLog.stanceHere();
        ScheduleLog.observe(RECV, "HADOOP_IPC#REQUEST");
        Object other = new Object();
        RuntimeTraceContext.registerSource(other, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "t/dn1", 0L));
        started(() -> {
            long own = RuntimeTraceContext.beginRequest(other, "sync");
            ScheduleLog.observe(START, "<A: void a()>#u1");
            ScheduleLog.observe(SEND, "HADOOP_IPC#RESPONSE",
                    "endpoint-at-receipt", receipt);
            RuntimeTraceContext.endRequest(own);
        }).join();
        List<ScheduleEvent> events = events();
        assertEquals(3, events.size());
        assertFalse("the sender has a context of its own",
                events.get(0).context().equals(events.get(1).context()));
        assertEquals(events.get(0).context(), events.get(2).context());
        assertEquals("endpoint-at-receipt", events.get(2).endpoint());
    }

    /**
     * A context's shape over this run's own senders (each anchor's SEND
     * stance, as PLAN reads the recording's; one this run never sent from
     * is unknown); a receipt's work holds a place only where this run
     * stated that SEND (hdfs-adhoc-19/35: a block report's reply cut by the
     * window's opening).
     */
    @Test
    public void aReceiptHoldsAPlaceOnlyWhereThisRunStatedItsSend() {
        ScheduleLog.observe(SEND, "HADOOP_IPC#REQUEST", "e1");
        assertEquals(Arrays.asList("HADOOP_IPC/check@t/dn0#epoch0",
                "Root:CLIENT/schedule-test"), ScheduleLog.shape(
                CausalContext.parse("Anchor:e1@HADOOP_IPC/check")));
        assertEquals(Arrays.asList(ContextShape.UNKNOWN_HOP),
                ScheduleLog.shape(CausalContext.parse(
                        "Anchor:e2@HADOOP_IPC/check")));
        List<Boolean> stood = new ArrayList<Boolean>();
        for (String producer : new String[] {"e1", "cut"}) {
            long hop = Lineage.push(NODE.key(), Role.of("HANDLER"), "check");
            Lineage.anchor(producer, "HADOOP_IPC/check");
            stood.add(ScheduleLog.stanceHere() != null);
            ScheduleLog.observe(RECV, "HADOOP_IPC#REQUEST");
            Lineage.pop(hop);
        }
        assertEquals(Arrays.asList(true, false), stood);
        assertEquals(Arrays.asList(SEND, RECV), kinds());
    }

    /**
     * A taken item's work stands in its putter's scope, whoever takes it
     * (hdfs-adhoc-46: which IPC handler took a call moved its CLAIM's
     * context), and a start's k counts per hop of the context: the putter's
     * second anchored hop counts from 0 again (hdfs-adhoc-35).
     */
    @Test
    public void aTakenItemStandsInItsPuttersScopeCountedPerHop()
            throws Exception {
        String put = "<Q: void put(java.lang.Object)>#u7";
        BlockingQueue<Object> queue = new LinkedBlockingQueue<Object>();
        List<Thread> consumers = new ArrayList<Thread>();
        for (int i = 0; i < 2; i++) {
            Thread consumer = new Thread(() -> {
                try {
                    Identity.claimItem(queue.take());
                } catch (InterruptedException stop) {
                    return;
                }
                send("x");
            });
            Identity.startWork("<S: void start()>#u5", consumer, null);
            consumer.start();
            consumers.add(consumer);
        }
        List<String> expected = new ArrayList<String>();
        for (String producer : new String[] {"e1", "e2"}) {
            ScheduleLog.observe(SEND, "HADOOP_IPC#REQUEST", producer);
            long hop = Lineage.push(NODE.key(), Role.of("HANDLER"), "check");
            Lineage.anchor(producer, "HADOOP_IPC/check");
            expected.add(ScheduleLog.contextOf(Identity.contextHere()) + "|"
                    + put + "@0");
            Object item = new Object();
            Identity.startWork(put, item, null);
            Lineage.pop(hop);
            queue.put(item);
        }
        for (Thread consumer : consumers) consumer.join(5000L);
        List<String> taken = new ArrayList<String>();
        for (ScheduleEvent event : events()) {
            if ("x".equals(event.site())) taken.add(event.context());
        }
        Collections.sort(taken);
        assertEquals(expected, taken);
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
                "HADOOP_IPC#REQUEST", 3, "occ-1");
        ScheduleEvent bare = ScheduleEvent.of(0L, WAKE, "",
                "tick.KEY_MANAGER_TICK", 0, "");
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
     * Threads started through one utility -- each call of it a level of its
     * own, so both starts are its 0th -- are told apart by the frames they
     * were made under (hdfs-adhoc-02's DataStreamer and LeaseRenewer, both
     * {@code Daemon.start}ed after one RPC returned), never by how often
     * their creator came there.
     */
    @Test
    public void threadsStartedThroughOneUtilityStateWhereTheyWereMade()
            throws Exception {
        written.clear();
        String start = "<U: void start()>#u5";
        List<String> makers = Arrays.asList("<A: void stream()>",
                "<B: void renew()>");
        for (String maker : makers) {
            long made = Identity.enterFrame(maker, null);
            Thread thread = new Thread(() -> send("HADOOP_IPC#REQUEST"));
            Identity.exitFrame(made);
            long utility = Identity.enterFrame("<U: void start()>", null);
            Identity.startWork(start, thread, null);
            Identity.exitFrame(utility);
            thread.start();
            thread.join();
        }
        String scope = ScheduleLog.contextOf(Identity.contextHere());
        assertEquals(Arrays.asList(
                scope + "|" + makers.get(0) + ">" + start + "@0 k=0",
                scope + "|" + makers.get(1) + ">" + start + "@0 k=0"),
                sends());
    }

    /**
     * A start made while a request is in hand hands that request off: its
     * site, and the start frame its work claims, name the verb, so its k
     * counts per verb (IDENTITY §3); a receipt ends the request in hand
     * (hdfs-adhoc-15: a heartbeat's hand-off to the IPC sender no longer
     * takes its block report's START and CLAIM).  A message door's fault
     * ends it as a receipt does (hdfs-17899-bug2: the SPS daemon started
     * after a faulted getBlockKeys); a demanded door's fault and a marker
     * no door names end no exchange.
     */
    @Test
    public void aStartWithARequestInHandIsThatRequestsHandOff()
            throws Exception {
        written.clear();
        String offer = "<C$Connection: void sendRpcRequest(C$Call)>#u48";
        String[] verbs = {"P.sendHeartbeat", "P.blockReceivedAndDeleted"};
        List<String> claimed = new ArrayList<String>();
        for (String verb : verbs) {
            CausynthTraceRecorder.outboundExchange("HADOOP_IPC", "c-" + verb,
                    "0", "REQUEST", null, null, verb);
            Object item = new Object();
            Identity.startWork(offer, item, null);
            started(() -> Identity.claimItem(item)).join();
        }
        CausynthTraceRecorder.inboundExchange("", "HADOOP_IPC", "c-r", "0",
                "RESPONSE", null);
        Identity.startWork(offer, new Object(), null);
        Object[][] faults = {
            {"FAULT:HADOOP_IPC:REQUEST", true},
            {"FAULT:HADOOP_IPC:REQUEST:ConnectTimeoutException", true},
            {"FAULT:HDFS_SASL:REQUEST", true},
            {"FAULT:HDFS_DATA_TRANSFER:RESPONSE:EOFException", true},
            {"FAULT:ZOOKEEPER:WRITE", true},
            {"FAULT:LOCAL_IO:WRITE", false},
            {"FAULT:NO_DOOR:REQUEST", false},
            {"a-workload-marker", false}};
        List<String> expected = new ArrayList<String>(Arrays.asList(
                offer + ":" + verbs[0] + " k=0", offer + ":" + verbs[1]
                        + " k=0", offer + " k=0"));
        for (Object[] fault : faults) {
            CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                    "c-" + fault[0], "0", "REQUEST", null, null,
                    "P.getBlockKeys");
            Identity.doorFaulted((String) fault[0]);
            Identity.startWork(offer, new Object(), null);
            expected.add(fault[0] + " " + ((Boolean) fault[1] ? offer
                    : offer + ":P.getBlockKeys"));
            CausynthTraceRecorder.inboundExchange("", "HADOOP_IPC",
                    "r-" + fault[0], "0", "RESPONSE", null);
        }
        List<String> starts = new ArrayList<String>();
        for (ScheduleEvent event : events()) {
            if (event.kind() == START) {
                int at = starts.size();
                starts.add(at < 3 ? event.site() + " k=" + event.k()
                        : faults[at - 3][0] + " " + event.site());
            } else if (event.kind() == CLAIM) {
                claimed.add(event.site());
            }
        }
        assertEquals(expected, starts);
        assertEquals(Arrays.asList(offer + ":" + verbs[0],
                offer + ":" + verbs[1]), claimed);
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
     * A DUE PUBLICATION'S TURN IS TAKEN ONCE ITS CALLBACK HAS PUBLISHED IT
     * (SGF3 snapshot-no-active: node0's v8 turn was taken at the door, and
     * the Overseer read the cluster state before constructState).  A publish
     * on the notification's thread that waits on a lock a thread waiting
     * for its turn behind it owns has its turn taken a grace in (review R2).
     */
    @Test(timeout = 30000L)
    public void aDuePublicationsTurnIsTakenOnceItIsInForce()
            throws Exception {
        List<ScheduleEvent> order = Arrays.asList(publish(VIEW_NODE, V8),
                event(SEND, "after"));
        List<String> applied = applied();
        Confirmation.resetForTests();
        enforce(order);
        boolean[] sawApplied = new boolean[1];
        Thread after = started(() -> {
            send("after");
            sawApplied[0] = applied.contains("v8");
        });
        Thread.sleep(100L);
        assertFalse("due at the door: its caller publishes", door(VIEW, 8L,
                () -> {
                    nap(300L);
                    applied.add("v8");
                }, V8));
        assertEquals("applied on the notification's thread",
                Arrays.asList("v8"), applied);
        joined(after);
        assertTrue("let go only once v8 is in force", sawApplied[0]);
        assertEquals(Arrays.asList(V8, "after"), sites());
        progress(" 0 given up");

        fresh();
        applied.clear();
        enforce(order);
        Object lock = new Object();
        CountDownLatch holding = new CountDownLatch(1);
        Thread refresh = started(() -> {
            synchronized (lock) {
                holding.countDown();
                send("after");
            }
        });
        holding.await();
        long started = System.nanoTime();
        assertFalse(door(VIEW, 8L, () -> {
            synchronized (lock) {
                applied.add("v8");
            }
        }, V8));
        assertTrue("a grace in, not the order's timeout",
                since(started) < 5000L);
        joined(refresh);
        assertEquals(Arrays.asList("v8"), applied);
        assertEquals("one PUBLISH, written when its turn was taken for it",
                Arrays.asList(V8, "after"), sites());
        progress(" 0 given up");
    }

    /**
     * THE DOOR ITSELF, in its callback ({@code MessageDoors#notified},
     * {@code #publishing}): a publication due at its door is published by
     * the caller, its turn taken when the callback ends -- one that throws
     * after its publish included, the throw going on -- and a deferred one
     * whose apply throws still takes its turn on the publisher (NIT7).
     */
    @Test(timeout = 30000L)
    public void aNotificationsTurnIsSettledWhenItsCallbackEndsAThrowIncluded()
            throws Exception {
        Confirmation.resetForTests();
        String path = "/collections/settled/state.json";
        String slot = MessageDoors.storeLocation("SOLR_ZK", path).slot();
        String v3 = ScheduleEvent.published("SOLR_ZK", slot, 3L);
        enforce(Arrays.asList(publish(NODE.key(), v3), event(SEND, "after")));
        List<String> applied = applied();
        boolean[] sawApplied = new boolean[1];
        Thread after = started(() -> {
            send("after");
            sawApplied[0] = applied.contains("v3");
        });
        Thread.sleep(100L);
        boolean[] deferred = {true};
        IllegalStateException thrown = null;
        try {
            MessageDoors.notified("Watcher", () -> {
                deferred[0] = MessageDoors.publishing("SOLR_ZK", path, 3L,
                        () -> applied.add("on the publisher"));
                nap(300L);
                applied.add("v3");
                throw new IllegalStateException("the system's own failure");
            });
        } catch (IllegalStateException system) {
            thrown = system;
        }
        assertFalse("due at its door: the caller publishes", deferred[0]);
        assertNotNull("the callback's throw goes on", thrown);
        joined(after);
        assertTrue("let go only once the callback ended", sawApplied[0]);
        assertEquals(Arrays.asList(v3, "after"), sites());
        progress(" 0 given up");

        fresh();
        applied.clear();
        String v4 = ScheduleEvent.published("SOLR_ZK", slot, 4L);
        enforce(Arrays.asList(event(SEND, "before"), publish(NODE.key(), v4),
                event(SEND, "after")));
        assertTrue("not due: handed to the publisher", door(view(NODE.key(),
                path), 4L, () -> {
                    applied.add("v4");
                    throw new IllegalStateException("thrown in the apply");
                }, v4));
        Thread next = started(() -> send("after"));
        send("before");
        joined(next);
        assertEquals(Arrays.asList("v4"), applied);
        assertEquals(Arrays.asList("before", v4, "after"), sites());
        progress(" 0 given up");
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

    /**
     * THE PUBLISHER NEVER BLOCKS ON A TURN (review B2): two views of one
     * node arrive in the reverse of their recorded order, and each applies
     * at its own turn, with nothing given up.  Blocking on X's turn, the one
     * publisher held Y's slot until the watchdog gave the run's slots up.
     */
    @Test
    public void twoViewsOfANodeApplyEachAtItsOwnTurn() throws Exception {
        Confirmation.resetForTests();
        String y = ScheduleEvent.published("SOLR_ZK", "/y.json", 3L);
        String x = ScheduleEvent.published("SOLR_ZK", "/x.json", 8L);
        enforce(Arrays.asList(event(SEND, "before"), publish(VIEW_NODE, y),
                publish(VIEW_NODE, x)));
        List<String> applied = applied();
        assertTrue(door(view(VIEW_NODE, "/x.json"), 8L,
                () -> applied.add("x"), x));
        assertTrue(door(view(VIEW_NODE, "/y.json"), 3L,
                () -> applied.add("y"), y));
        send("before");
        awaitSize(applied, 2);
        assertEquals(Arrays.asList("y", "x"), applied);
        assertEquals(Arrays.asList("before", y, x), sites());
        progress(" 0 given up");
    }

    /**
     * A VERSION A NODE NEVER PUBLISHES IS GIVEN UP AT THE NEWER ONE'S DOOR
     * (review S2, R3), by name, and what the recording made after it goes
     * without a stall: a v8 that holds no slot, in force at once, over v7's
     * turn; a callback that fetched v9 and never published v8; and the
     * system's own publication at once in a replay no pairing holds, its
     * own version's turn with them (Z3Q's seed: a 15 s stall).  A version
     * deferred on the publisher is on its way: its turn stands.
     */
    @Test(timeout = 30000L)
    public void anOlderVersionsTurnIsGivenUpWhenANewerReachesItsDoor()
            throws Exception {
        List<String> applied = applied();
        Confirmation.resetForTests();
        enforce(Arrays.asList(publish(VIEW_NODE, V7), event(SEND, "after")));
        assertFalse("v8 holds no slot: in force at once",
                door(VIEW, 8L, () -> { }, V8));
        assertNoStall(() -> send("after"));
        progress(" 1 given up");

        fresh();
        enforce(Arrays.asList(event(SEND, "before"), publish(VIEW_NODE, V8),
                event(SEND, "mid"), publish(VIEW_NODE, V9),
                event(SEND, "after")));
        assertTrue("v9's turn is not due: handed to the publisher",
                door(VIEW, 9L, () -> applied.add("v9"), V9));
        send("before");
        assertNoStall(() -> send("mid"));
        assertNoStall(() -> send("after"));
        assertEquals(Arrays.asList("v9"), applied);
        assertEquals(Arrays.asList("before", "mid", V9, "after"), sites());
        progress(" 1 given up");

        fresh();
        enforce(Arrays.asList(publish(VIEW_NODE, V8), publish(VIEW_NODE, V9),
                event(SEND, "after")));
        Confirmation.published(VIEW, 9L, null, "a forced refresh", VIEW_NODE,
                V9);
        assertNoStall(() -> send("after"));
        progress(" 2 given up");

        fresh();
        applied.clear();
        enforce(Arrays.asList(event(SEND, "before"), publish(VIEW_NODE, V8),
                publish(VIEW_NODE, V9)));
        assertTrue(door(VIEW, 8L, () -> applied.add("v8"), V8));
        assertTrue("behind v8", door(VIEW, 9L, () -> applied.add("v9"), V9));
        send("before");
        awaitSize(applied, 2);
        assertEquals(Arrays.asList("v8", "v9"), applied);
        assertEquals(Arrays.asList("before", V8, V9), sites());
        progress(" 0 given up");
    }

    /**
     * THE PUBLISHER WAITS AS THE ORDER'S WAITER (review R1): a deferred
     * publication whose predecessor never comes gives way by the watchdog,
     * named, though no other thread waits; where another thread waits
     * further on, the publisher's place bounds the give-up, so only the
     * missing predecessor is given up, not the publication's own turn.
     */
    @Test(timeout = 30000L)
    public void aPublicationsTurnWaitsWhereTheWatchdogSeesIt()
            throws Exception {
        timeout(300L);
        List<String> applied = applied();
        Confirmation.resetForTests();
        enforce(Arrays.asList(event(SEND, "never"), publish(VIEW_NODE, V8)));
        assertTrue(door(VIEW, 8L, () -> applied.add("v8"), V8));
        awaitSize(applied, 1, 10000L);
        assertEquals("given way, alone", Arrays.asList("v8"), applied);
        // The publisher states the publication once its apply has run: the
        // apply is seen first (1 in 6 runs saw no site yet).
        long stated = System.currentTimeMillis() + 10000L;
        while (sites().isEmpty() && System.currentTimeMillis() < stated) {
            Thread.sleep(20L);
        }
        assertEquals(Arrays.asList(V8), sites());
        progress(" 1 given up");

        fresh();
        applied.clear();
        enforce(Arrays.asList(event(SEND, "never"), publish(VIEW_NODE, V8),
                event(SEND, "after")));
        assertTrue(door(VIEW, 8L, () -> applied.add("v8"), V8));
        joined(started(() -> send("after")));
        assertEquals(Arrays.asList("v8"), applied);
        assertEquals(Arrays.asList(V8, "after"), sites());
        progress("the publication's own turn is not given up: ",
                " 1 given up");
    }

    /**
     * AN APPLY THAT WAITS ON A LOCK THE ORDER HOLDS (review R2): the apply
     * takes a lock owned by a thread that waits for its turn behind the
     * publication (Solr's update lock, held by a forced refresh); its turn is
     * taken a grace in, named, so the thread goes and the publication lands.
     * An apply that computes, or waits on a lock a thread the order does not
     * hold owns (R2a) -- one merely entering the order's own lock too (R2b)
     * -- holds its turn until it is in force: what comes after sees it.
     */
    @Test(timeout = 40000L)
    public void anApplyGivesItsTurnOnlyWhenTheOrderHoldsWhatItWaitsOn()
            throws Exception {
        List<String> applied = applied();
        List<ScheduleEvent> order = Arrays.asList(event(SEND, "before"),
                publish(VIEW_NODE, V8), event(SEND, "after"));
        Confirmation.resetForTests();
        enforce(order);
        Object lock = new Object();
        CountDownLatch holding = new CountDownLatch(1);
        Thread refresh = started(() -> {
            synchronized (lock) {
                holding.countDown();
                send("after");
            }
        });
        holding.await();
        assertTrue(door(VIEW, 8L, () -> {
            synchronized (lock) {
                applied.add("v8");
            }
        }, V8));
        long started = System.nanoTime();
        send("before");
        joined(refresh);
        assertTrue("a grace in, not the order's timeout",
                since(started) < 5000L);
        awaitSize(applied, 1);
        assertEquals(Arrays.asList("v8"), applied);
        assertEquals("one PUBLISH, written when its turn was taken",
                Arrays.asList("before", V8, "after"), sites());
        progress(" 0 given up");

        // A computing apply (R2a); a free thread, waiting on no turn,
        // holding the apply's lock 1.5 s; and its owner entering the
        // order's own lock meanwhile (R2b: blocked there on the watchdog,
        // which is no cycle).
        Object busy = new Object();
        for (int owner = 0; owner < 3; owner++) {
            fresh();
            applied.clear();
            enforce(order);
            boolean computing = owner == 0;
            if (!computing) {
                boolean asking = owner == 2;
                CountDownLatch entered = new CountDownLatch(1);
                started(() -> {
                    synchronized (busy) {
                        entered.countDown();
                        if (asking) {
                            held(1500L, true);
                        } else {
                            nap(1500L);
                        }
                    }
                });
                entered.await();
            }
            assertTrue(door(VIEW, 8L, () -> {
                if (computing) {
                    held(1200L, false);
                    applied.add("v8");
                } else {
                    synchronized (busy) {
                        applied.add("v8");
                    }
                }
            }, V8));
            boolean[] sawApplied = new boolean[1];
            Thread after = started(() -> {
                send("after");
                sawApplied[0] = !applied.isEmpty();
            });
            send("before");
            joined(after);
            assertTrue("owner " + owner + ": what comes after sees the "
                    + "publication", sawApplied[0]);
            if (owner == 1) {
                assertEquals(Arrays.asList("before", V8, "after"), sites());
            }
        }
    }

    /** Spins {@code millis}, asking the order between spins where
     *  {@code asking} (review R2b: blocked on the watchdog, no cycle). */
    private static void held(long millis, boolean asking) {
        long until = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(millis);
        while (System.nanoTime() < until) {
            if (asking) ScheduleLog.waitsNoMore();
        }
    }

    /** Asserts {@code event} returns without a stall. */
    private static void assertNoStall(Runnable event) {
        long started = System.nanoTime();
        event.run();
        assertTrue("no stall", since(started) < 1000L);
    }

    /**
     * A TURN-DEFERRED PUBLICATION SUPERSEDED BEFORE IT APPLIED (review S3):
     * its turn is given up by name, not left to the watchdog.
     */
    @Test
    public void aSupersededPublicationsTurnIsSettled() throws Exception {
        Confirmation.resetForTests();
        handHold(view("auto0/node9#epoch0", "/other.json"), 0L, "", "", "u");
        enforce(Arrays.asList(event(SEND, "before"), publish(VIEW_NODE, V8),
                event(SEND, "after")));
        List<String> applied = applied();
        assertTrue(door(VIEW, 8L, () -> applied.add("v8"), V8));
        // The system's own removal at once drops what was deferred.
        Confirmation.published(VIEW, -1L, null, "a removal at once",
                VIEW_NODE, null);
        send("before");
        long started = System.nanoTime();
        send("after");
        assertTrue("no stall", since(started) < 500L);
        Thread.sleep(100L);
        assertTrue(applied.toString(), applied.isEmpty());
        progress(" 1 given up");
    }

    /**
     * A HOLD AND A TURN ON ONE PUBLICATION (review S9c): held past the paired
     * version, its turn due once the SEND before it ran, it applies only
     * when the hold ends.  The paired version's own publication (S4) is in
     * force at once, its turn given up by name.
     */
    @Test
    public void aHoldWinsOverATurnAndThePairedVersionGoesAtOnce()
            throws Exception {
        Confirmation.resetForTests();
        handHold(VIEW, 7L, "auto0/node1#epoch0|Root:OVERSEER_TASK#3", "r",
                "u-reader");
        enforce(Arrays.asList(event(SEND, "before"), publish(VIEW_NODE, V7),
                publish(VIEW_NODE, V8)));
        List<String> applied = applied();
        assertFalse("the paired version: in force at once",
                door(VIEW, 7L, () -> applied.add("v7"), V7));
        assertEquals("published by its caller", Arrays.asList("v7"), applied);
        assertTrue("past it: held", door(VIEW, 8L, () -> applied.add("v8"),
                V8));
        send("before");
        Thread.sleep(200L);
        assertEquals("the hold stands", Arrays.asList("v7"), applied);
        Confirmation.exited("u-reader");
        awaitSize(applied, 2);
        assertEquals(Arrays.asList("v7", "v8"), applied);
        progress(" 1 given up");
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
        return ScheduleEvent.of(0L, PUBLISH, node + "|VIEW", site, 0, "");
    }

    private static LocationId view(String node, String path) {
        return LocationId.of(LocationKind.VIEW, "SOLR_ZK@" + node, path);
    }

    /** Hands this JVM's replay one VIEW_HOLD row (Confirmation's edges). */
    private static void handHold(LocationId view, long above,
                                 String readerContext, String reader,
                                 String until) throws java.io.IOException {
        Path worker = Files.createTempDirectory("schedule-hold");
        Files.write(worker.resolve("focused_task.jsonl"), new byte[0]);
        Files.write(worker.resolve(Confirmation.FILE), (Fixtures.json(
                "{'kind':'VIEW_HOLD','view':'" + Confirmation.viewKey(view)
                        + "','above':" + above + ",'readerContext':'"
                        + readerContext + "','reader':'" + reader
                        + "','until':'" + until + "'}") + "\n")
                .getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
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

    @Test
    public void aMonitorHoldingWaitAsksWithoutBlocking() {
        enforce(Arrays.asList(event(SEND, "x"),
                event(WAKE, "<L: void loop()>#u2")));
        ScheduleLog.Wake wake = ScheduleLog.wake("<L: void loop()>#u2");
        assertEquals(ScheduleLog.Turn.NOT_YET, ScheduleLog.turn(wake));
        send("x");
        assertEquals(ScheduleLog.Turn.ADMITTED, ScheduleLog.turn(wake));
        assertEquals(Arrays.asList("x", "<L: void loop()>#u2"), sites());
    }

    @Test
    public void aWaitBegunBeforeTheWindowConvertsWhenItOpens()
            throws Exception {
        RecordingWindow.reset();
        String site = "<L: void idle()>#u3";
        enforce(Collections.singletonList(event(WAKE, site)));
        long[] took = new long[1];
        Thread idle = started(() -> {
            long before = System.nanoTime();
            try {
                TimedWaits.sleep(1500L, site);
            } catch (InterruptedException interrupted) {
                return;
            }
            took[0] = since(before);
        });
        Thread.sleep(200L);
        assertTrue("before the window it waits on the wall clock",
                idle.isAlive());
        RecordingWindow.open();
        TimedWaits.windowOpened();
        joined(idle);
        assertTrue("its turn, and no sooner than its own 1.5 s: " + took[0],
                took[0] >= 1450L && took[0] < 5000L);
        assertEquals(Collections.singletonList(site), sites());
    }

    /**
     * A signal ends a wait with no turn, free or under a prefix it leaves
     * standing; a timeout is a turn.
     */
    @Test
    public void aSignalledWaitIsNoEventAndATimedOutOneIs() throws Exception {
        Object monitor = new Object();
        for (boolean held : new boolean[] {false, true}) {
            restart();
            if (held) enforce(prefix("x"));
            Thread woken = waits(monitor, "<C: void w()>#u1", 1, true).get(0);
            if (held) {
                Thread.sleep(200L);
                assertTrue("virtual time: the minute does not run out",
                        woken.isAlive());
            }
            synchronized (monitor) {
                monitor.notifyAll();
            }
            joined(woken);
            assertTrue("a notify ended it: no turn", written.isEmpty());
            if (held) {
                assertTrue("the prefix still stands", ScheduleLog.enforcing());
                progress(" 0 given up");
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
        timeout(300L);
        enforce(prefix("x"));
        Object monitor = new Object();
        long before = System.nanoTime();
        synchronized (monitor) {
            TimedWaits.waitOn(monitor, 1500L, WORK);
        }
        assertTrue("held, then its own deadline ended it",
                since(before) >= 1400L);
        assertEquals(Collections.singletonList(WORK), sites());
        assertTrue("nothing made x, and no one waits for it",
                ScheduleLog.enforcing());
        progress("1 of them let go");
    }

    /**
     * The WAKE of a timed-out wait the order still holds is asked for, never
     * waited for under the application's monitor: the ask answers at once,
     * and the waiter spends its hold in its own wait, so a notifier can take
     * the monitor meanwhile (hdfs-adhoc-19: a DataXceiver blocked on the IBR
     * manager while the actor's WAKE waited for its turn holding it).
     */
    @Test(timeout = 20000L)
    public void aTimedOutWakeAsksForItsTurnWithTheMonitorReleased()
            throws Exception {
        timeout(3000L);
        String site = "<C: void waitTillNextIBR(long)>#u18";
        enforce(prefix("x"));
        ScheduleLog.Wake held = ScheduleLog.wake(site);
        long asked = System.nanoTime();
        assertFalse("held at the cut: not yet", ScheduleLog.timedOut(held));
        assertTrue("one ask, no wait", since(asked) < 1000L);
        ScheduleLog.withdraw(held);
        Object monitor = new Object();
        Thread waiter = started(() -> {
            synchronized (monitor) {
                try {
                    TimedWaits.waitOn(monitor, 50L, site);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        });
        Thread.sleep(300L);
        long before = System.nanoTime();
        synchronized (monitor) {
            assertTrue("the waiter still waits for its turn",
                    waiter.isAlive());
        }
        assertTrue("the monitor was free while the WAKE was held",
                since(before) < 1000L);
        waiter.join();
        assertEquals(Collections.singletonList(site), sites());
    }

    /** A primitive's timed wait, for the table below. */
    private interface TimedWait {
        void run(String site) throws Exception;
    }

    /**
     * A wait whose recorded WAKE slot is due before its own deadline takes
     * the slot at once, so the order moves on, and returns only once its
     * deadline passed, whatever its primitive: a WAKE is a timeout, the
     * recording's wait ran its whole time (hdfs-adhoc-29: a DataNode actor
     * woken at its slot found its heartbeat not due).
     */
    @Test(timeout = 30000L)
    public void aWaitAdmittedAtItsSlotReturnsNoSoonerThanItsDeadline()
            throws Exception {
        long waitMs = 800L;
        Object monitor = new Object();
        ReentrantLock lock = new ReentrantLock();
        Condition condition = lock.newCondition();
        Map<String, TimedWait> table = new LinkedHashMap<String, TimedWait>();
        table.put("sleep", site -> TimedWaits.sleep(waitMs, site));
        table.put("monitor", site -> {
            synchronized (monitor) {
                TimedWaits.waitOn(monitor, waitMs, site);
            }
        });
        table.put("condition", site -> {
            lock.lock();
            try {
                TimedWaits.await(condition, waitMs, TimeUnit.MILLISECONDS,
                        site);
            } finally {
                lock.unlock();
            }
        });
        table.put("park", site -> TimedWaits.parkNanos(
                TimeUnit.MILLISECONDS.toNanos(waitMs), site));
        table.put("poll", site -> TimedWaits.poll(
                new LinkedBlockingQueue<Object>(), waitMs,
                TimeUnit.MILLISECONDS, site));
        for (Map.Entry<String, TimedWait> row : table.entrySet()) {
            // Each row on a fresh runtime, as each test is.
            tearDown();
            written.clear();
            reset();
            String site = "<C: void " + row.getKey() + "()>#u18";
            enforce(order(event(WAKE, site), prefix("x")));
            long began = System.nanoTime();
            long[] moved = new long[1];
            Thread next = started(() -> {
                nap(200L);
                send("x");
                moved[0] = System.nanoTime();
            });
            row.getValue().run(site);
            long returned = System.nanoTime();
            next.join();
            assertEquals(row.getKey(), Arrays.asList(site, "x"), sites());
            assertTrue(row.getKey() + ": the order moved on at its slot",
                    moved[0] - began < TimeUnit.MILLISECONDS.toNanos(waitMs));
            assertTrue(row.getKey() + ": no sooner than its deadline",
                    TimeUnit.NANOSECONDS.toMillis(returned - began)
                            >= waitMs - 50L);
        }
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
     * A wait the recording made, polled once more than recorded, goes once
     * its context's next slot is due: only its next turn makes that slot's
     * event.  A loop polling past its recorded count whose next slot is the
     * frontier owes it: it polls again with no move of the order, never held
     * to the watchdog (solr-adhoc-19 SG1: a waitForCoreNodeName loop, 66
     * stalls).
     */
    @Test(timeout = 20000L)
    public void aRecordedWaitPolledOnceMoreGoesWhenItsNextSlotIsDue()
            throws Exception {
        timeout(30000L);
        for (int polls : new int[] {2, 4}) {
            restart();
            enforce(order(event(WAKE, "tick.poll"), prefix("x")));
            long before = System.nanoTime();
            for (int poll = 0; poll < polls; poll++) {
                ScheduleLog.observe(WAKE, "tick.poll");
            }
            send("x");
            if (polls == 4) assertTrue("no stall", since(before) < 2000L);
            if (polls == 2) {
                assertEquals(Arrays.asList("tick.poll", "tick.poll", "x"),
                        sites());
                assertEquals("a WAKE is the clock's, the SEND a step", 1L,
                        ScheduleLog.steps());
            }
            progress("2 taken, 0 given up");
        }
    }

    /**
     * A wait the recording never made, held at the cut in another context
     * while the frontier stands and nothing computes, is let go a grace into
     * the stall, not a timeout: x, which no thread makes, is given up later.
     */
    @Test(timeout = 30000L)
    public void anIdleStallLetsAHeldWaitGoAGraceIn() throws Exception {
        noRequest();
        request("a", () -> send("x"));
        List<ScheduleEvent> recorded = events();
        noRequest();
        timeout(10000L);
        enforce(recorded);
        long before = System.nanoTime();
        started(() -> request("b", () -> ScheduleLog.observe(WAKE, "tick.b")))
                .join(20000L);
        long took = since(before);
        assertTrue("a grace, not the timeout: " + took,
                took >= ScheduleLog.LET_GO_GRACE_MS - 100L && took < 8000L);
        progress("1 of them let go");
    }

    /**
     * The request that makes x first sleeps a wait the recording never
     * made: held at the cut, with the run idle, it is let go before x is
     * given up, and x is taken.  The turn it let go is vacant; x's is not.
     */
    @Test(timeout = 20000L)
    public void anIdleRunLetsTheCutsWaitsGoBeforeGivingUp() throws Exception {
        timeout(1000L);
        enforce(prefix("x"));
        ScheduleLog.observe(WAKE, "tick.once");
        assertTrue("a turn let go is vacant", ScheduleLog.vacated());
        send("x");
        assertFalse("a slotted event is not", ScheduleLog.vacated());
        assertEquals(Arrays.asList("tick.once", "x"), sites());
        progress("1 taken, 0 given up");
        progress("1 of them let go");
    }

    /**
     * An event of a timed-wait loop's turn ({@code Root:WAKE/<wait>#k}: k
     * counts the loop's wakes, a timing fact) waits at the slot its key
     * found like a poll past its count: with the run idle it is let go a
     * grace in and takes that slot, and the unmade x before it is never
     * given up on its account (solr-adhoc-39 MB29s: turn #88 at recorded
     * #88's slot bounded a give-up of 4251 slots).  The same event in a
     * request is a plain waiter: the stall gives x up.
     */
    @Test(timeout = 30000L)
    public void aTimedWaitTurnsEventAtItsSlotBoundsNoGiveUp()
            throws Exception {
        for (boolean turn : new boolean[] {true, false}) {
            noRequest();
            request("a", () -> send("x"));
            List<ScheduleEvent> order = new ArrayList<ScheduleEvent>(events());
            Runnable y = () -> turnOrRequest(turn, () -> send("y"));
            y.run();
            order.add(events().get(1));
            assertEquals(turn, ScheduleLog.timedWaitTurn(order.get(1)
                    .context()));
            noRequest();
            timeout(4000L);
            enforce(order);
            long before = System.nanoTime();
            started(y).join(20000L);
            long took = since(before);
            progress(turn ? "1 taken, 0 given up" : "1 taken, 1 given up");
            if (turn) {
                assertTrue("a grace, not the timeout: " + took, took < 3500L);
                progress("1 of them let go");
            }
        }
    }

    /**
     * Let go, a timed-wait turn's WRITE still never passes an earlier held
     * write to its location: it waits behind it, and the stall gives that
     * one write up (the write rule), never taking its own slot past it.
     */
    @Test(timeout = 30000L)
    public void aLetGoTurnsWriteStillWaitsBehindTheWriteBeforeIt()
            throws Exception {
        noRequest();
        request("a", () -> written("L"));
        List<ScheduleEvent> order = new ArrayList<ScheduleEvent>(events());
        turnOrRequest(true, () -> written("L"));
        order.add(events().get(1));
        assertTrue(ScheduleLog.timedWaitTurn(order.get(1).context()));
        noRequest();
        timeout(3000L);
        enforce(order);
        started(() -> turnOrRequest(true, () -> written("L"))).join(20000L);
        progress("1 taken, 1 given up");
    }

    /** {@code inside} run in a timed-wait loop's turn on the node, else in a
     *  request of the node. */
    private void turnOrRequest(boolean turn, Runnable inside) {
        if (!turn) {
            request("b", inside);
            return;
        }
        long frame = Identity.enterFrame("<L: void loop()>#u1", node);
        long wake = RuntimeTraceContext.beginWake("L.poll");
        try {
            inside.run();
        } finally {
            RuntimeTraceContext.endWakeIfInnermost(wake);
            Identity.exitFrame(frame);
        }
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

    /**
     * A store's notification is awaited by no order, and neither is the
     * work it causes; a queue item its consumer takes is the message the
     * thread serves, as its write sent it (its key, REQUEST), the next item
     * replacing it, one no write of the window filed naming nothing.
     */
    @Test(timeout = 20000L)
    public void aStoreNotificationsWorkIsNoPartOfTheOrder() throws Exception {
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NODE);
        MessageDoors.stored("STORE", "/k@1", owner, null);
        written.clear();
        started(() -> MessageDoors.notified("Watcher", () -> {
            MessageDoors.fetched("STORE", "/k@1", owner, null);
            send("y");
        })).join(5000L);
        assertTrue(sites().toString(), sites().isEmpty());
        MessageDoors.stored("STORE", "/q/qn-1@0", owner, null);
        MessageDoors.stored("STORE", "/q/qn-2@0", owner, null);
        String[][] rows = {{"/q/qn-1@0", "/q/qn-1@0"},
                {"/q/qn-2@0", "/q/qn-2@0"}, {"/q/qn-9@0", null}};
        for (String[] row : rows) {
            MessageDoors.consumed("STORE", row[0]);
            MessageDoors.Inbound served = MessageDoors.current();
            assertEquals(row[0], row[1],
                    served == null ? null : served.correlationId);
            if (served != null) {
                assertEquals(MessageDoors.REQUEST, served.half);
            }
        }
    }

    /**
     * The store applies a write, and notifies, before its caller files the
     * version (SOLR-18413 F2's node1 state watchers): a notification reading
     * the version meanwhile waits for the write in flight at its location
     * and is named by it.  A write elsewhere holds nothing; a version no
     * other thread's write in flight files names nothing and waits for
     * nothing; a write that never files holds the read FILED_WAIT_MS at
     * most.  One FILING ({@code stored} began, 18413 Z2V: exporting the
     * document's leaves takes seconds) holds it past that bound, up to
     * FILING_WAIT_MS, and the read pairs with the write once it files.
     */
    @Test(timeout = 30000L)
    public void aNotificationWaitsForTheWriteInFlightToFileItsVersion()
            throws Exception {
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NODE);
        List<Boolean> named = Collections.synchronizedList(
                new ArrayList<Boolean>());
        long elsewhere = MessageDoors.storing("STORE", "/other");
        long store = MessageDoors.storing("STORE", "/k");
        Thread callback = reading(owner, "/k@2", named);
        Thread.sleep(300L);
        assertTrue("it waits for the write in flight", callback.isAlive());
        MessageDoors.stored("STORE", "/k@2", owner, null);
        MessageDoors.storeEnded("STORE", store);
        callback.join(5000L);
        assertEquals("and the write names its work", Arrays.asList(true),
                named);
        long own = MessageDoors.storing("STORE", "/k");
        MessageDoors.notified("Watcher", () -> {
            MessageDoors.fetched("STORE", "/k@3", owner, null);
            named.add(MessageDoors.current() != null);
        });
        MessageDoors.storeEnded("STORE", own);
        assertEquals(Arrays.asList(true, false), named);
        long hold = MessageDoors.FILED_WAIT_MS + 1500L;
        for (boolean filing : new boolean[] {false, true}) {
            named.clear();
            String location = "/q" + filing;
            long bracket = MessageDoors.storing("STORE", location);
            long filed = filing
                    ? MessageDoors.filingBegins("STORE", location) : -1L;
            long began = System.currentTimeMillis();
            Thread reader = reading(owner, location + "@1", named);
            reader.join(hold);
            assertEquals("filing " + filing + ": still waiting past "
                    + MessageDoors.FILED_WAIT_MS + " ms", filing,
                    reader.isAlive());
            MessageDoors.stored("STORE", location + "@1", owner, null);
            if (filing) MessageDoors.storeEnded("STORE", filed);
            MessageDoors.storeEnded("STORE", bracket);
            reader.join(5000L);
            long waited = System.currentTimeMillis() - began;
            assertEquals("filing " + filing + ": paired with the write",
                    Arrays.asList(filing), named);
            assertTrue("filing " + filing + ": " + waited, filing
                    ? waited >= hold : waited < hold);
        }
        MessageDoors.storeEnded("STORE", elsewhere);
    }

    /** A notification on a thread of its own reading {@code key}: whether a
     *  write named its work goes to {@code named}. */
    private static Thread reading(Object owner, String key,
                                  List<Boolean> named) {
        return started(() -> MessageDoors.notified("Watcher", () -> {
            MessageDoors.fetched("STORE", key, owner, null);
            named.add(MessageDoors.current() != null);
        }));
    }

    /**
     * A write that never files holds the read a bound, not for ever.
     */
    @Test(timeout = 20000L)
    public void aWriteThatNeverFilesHoldsTheReadABound() throws Exception {
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NODE);
        List<Boolean> named = Collections.synchronizedList(
                new ArrayList<Boolean>());
        long unfiled = MessageDoors.storing("STORE", "/k");
        long began = System.currentTimeMillis();
        reading(owner, "/k@4", named).join(10000L);
        long waited = System.currentTimeMillis() - began;
        MessageDoors.storeEnded("STORE", unfiled);
        assertEquals(Arrays.asList(false), named);
        assertTrue("a bound, not for ever: " + waited,
                waited >= MessageDoors.FILED_WAIT_MS - 100L
                        && waited < MessageDoors.FILED_WAIT_MS + 3000L);
    }

    /**
     * A WRITE takes its turn before the store's call, and never passes an
     * earlier held write to its location -- until that write is taken or
     * the watchdog gives it up: no wait is unbounded.  Per row: the writes
     * the recording made (request:location), the replay's (a request after
     * a '<' writes only once the first request's write returned: the
     * Overseer's poll for the core-admin CREATE it sent), the order they are
     * written in, and whether a slot was given up.  SOLR-18413 on
     * solr-bug-reindex (with the CREATE's write recorded, and not); a write
     * the order lacks waits for the next write at its location; one whose
     * write never comes goes after a stall; one elsewhere waits for nothing.
     */
    @Test(timeout = 60000L)
    public void aWriteNeverPassesAnEarlierWriteToItsLocationForLongerThanAStall()
            throws Exception {
        String q = "/overseer/queue/qn-";
        String[][] rows = {
            {"o:" + q + " c:" + q, "c:" + q + " o<c:" + q, "c o", "1"},
            {"o:" + q, "c:" + q + " o<c:" + q, "c o", "1"},
            {"o:/p", "c:/p o:/p", "o c", "0"},
            {"o:/p", "c:/p", "c", "1"},
            {"o:/p", "c:/q o:/p", "c o", "0"}};
        for (String[] row : rows) {
            enforceRecorded(row[0], 1000L, at -> written(at));
            CountDownLatch first = new CountDownLatch(1);
            long before = System.nanoTime();
            List<String> made = replayed(row[1], (api, at) -> {
                try {
                    if (api.endsWith("<c")) first.await();
                    written(at);
                    first.countDown();
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
            }, 20000L);
            long took = since(before);
            assertEquals(row[1], Arrays.asList(row[2].split(" ")), made);
            progress(" " + row[3] + " given up");
            assertTrue(row[1] + " a stall at most, never for ever: " + took,
                    took < (row[3].equals("1") ? 12000L : 3000L));
        }
    }

    /** A fresh run held to the recording of {@code turns} (request:at),
     *  each made by {@code make}. */
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

    /**
     * The replay's {@code turns} (request:at; a request after a '<' its
     * first letter's), each a thread of its own 300 ms after the last,
     * making it; the requests in the order their events were written.
     */
    private List<String> replayed(String turns,
            java.util.function.BiConsumer<String, String> make, long within)
            throws InterruptedException {
        Map<String, String> apis = new ConcurrentHashMap<>();
        List<Thread> threads = new ArrayList<Thread>();
        for (String turn : turns.split(" ")) {
            String[] at = turn.split(":", 2);
            String api = at[0].substring(0, 1);
            threads.add(started(() -> request(api, () -> {
                apis.put(ScheduleLog.contextOf(Identity.contextHere()), api);
                make.accept(at[0], at[1]);
            })));
            Thread.sleep(300L);
        }
        for (Thread thread : threads) thread.join(within);
        List<String> made = new ArrayList<String>();
        for (ScheduleEvent event : events()) {
            made.add(apis.get(event.context()));
        }
        return made;
    }

    /**
     * A store read takes its turn at its location as a write does (READ):
     * it waits behind the write the recording made there before it, and the
     * write the recording made after it waits behind it, so a
     * create-if-absent's check or a client's view of an alias sees what the
     * recording's read saw (solr-adhoc-39, MB23s).  Per row: the recording's
     * turns (request:W or R); the replay's; the run (a seed, cut at its
     * end; a run the model orders, cut after the write or at its end; a
     * replay no model orders, cut after the write); the order the turns are
     * made in; the account.  Past the cut of a model's order a read takes no
     * slot; a read of a location no write of the order wrote takes none.
     */
    @Test(timeout = 60000L)
    public void aReadTakesItsTurnAtItsLocation() throws Exception {
        String[][] rows = {
            {"w:W r:R", "r:R w:W", "seed", "w r", "2 taken, 0 given up"},
            {"r:R w:W", "w:W r:R", "seed", "r w", "2 taken, 0 given up"},
            {"w:W r:R", "r:R w:W", "model", "r w", "1 slot(s) (prefix 1)"},
            {"w:W r:R", "r:R w:W", "suffix", "w r", "2 taken, 0 given up"},
            {"w:W r:R", "r:R w:W", "model prefix", "w r",
                "2 taken, 0 given up"},
            {"r:R", "r:R", "seed", "r", "no order"},
            // The write never comes: the read is let go, the write's slot
            // kept; the read never comes: the write gives it up, a grace in.
            {"w:W r:R", "r:R", "seed", "r", "1 taken, 0 given up"},
            {"r:R w:W", "w:W", "seed", "w", "1 taken, 1 given up"}};
        for (String[] row : rows) {
            noRequest();
            for (String turn : row[0].split(" ")) {
                String[] at = turn.split(":", 2);
                request(at[0], () -> turn(at[1]));
            }
            List<ScheduleEvent> recorded = events();
            noRequest();
            timeout(30000L);
            int cut = row[2].equals("model") || row[2].equals("suffix")
                    ? 1 : recorded.size();
            ScheduleLog.enforceForTests(recorded.subList(0, cut),
                    recorded.subList(cut, recorded.size()), false,
                    !row[2].startsWith("model"));
            assertEquals(Arrays.toString(row), Arrays.asList(row[3].split(
                    " ")), replayed(row[1], (api, kind) -> turn(kind),
                    10000L));
            progress(row[4]);
        }
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
     * A write waiting behind the write to its location gives that one write
     * up when it stalls, never the run of other nodes' events before it: x
     * and y stay open and are taken when their threads come.
     */
    @Test(timeout = 30000L)
    public void aWriteWaitingBehindAnotherGivesUpThatWriteAlone()
            throws Exception {
        noRequest();
        request("a", () -> send("x"));
        request("b", () -> send("y"));
        request("o", () -> written("/p"));
        List<ScheduleEvent> recorded = events();
        noRequest();
        timeout(500L);
        enforce(recorded);
        joined(started(() -> request("c", () -> written("/p"))));
        progress(" 1 given up");
        request("a", () -> send("x"));
        request("b", () -> send("y"));
        progress("2 taken, 1 given up");
    }

    /**
     * The one write a conflicted waiter needs is given up once: another
     * waiter asking the watchdog before the conflicted one sees it settled
     * -- the frontier, x, standing still -- finds nothing more to do there,
     * and its own stall comes a timeout later (solr-18413 MB3: 628 stalls
     * given at one settled slot, a spin).
     */
    @Test(timeout = 30000L)
    public void aSettledConflictIsGivenUpOnceWhoeverAsks() throws Exception {
        noRequest();
        request("x", () -> send("x"));
        request("o", () -> written("/p"));
        request("y", () -> send("y"));
        String[] waiting = {"d", "e", "f", "g"};
        for (String waiter : waiting) request(waiter, () -> send("z"));
        List<ScheduleEvent> recorded = events();
        noRequest();
        timeout(100L);
        enforce(recorded);
        // x's context at work, so the stall stands to its ceiling.
        boolean[] stop = new boolean[1];
        Thread busy = started(() -> request("x", () -> {
            while (!stop[0]) {
                send("x2");
                spin(20L);
            }
        }));
        List<Thread> others = new ArrayList<Thread>();
        for (String waiter : waiting) {
            others.add(started(() -> request(waiter, () -> send("z"))));
        }
        Thread.sleep(200L);
        Thread c = started(() -> request("c", () -> written("/p")));
        c.join(10000L);
        for (Thread other : others) other.join(10000L);
        stop[0] = true;
        busy.join(10000L);
        joined(c);
        joined(others.toArray(new Thread[0]));
        progress("3 given up in 2 stall(s)");
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

    /**
     * The 18413 cycle with its poll: the Overseer's write stands first at
     * the queue's location, and the Overseer makes it only once its poll
     * sees the core-admin CREATE complete, whose write waits behind it.  The
     * poll's requests are the frontier owner at work, so the stall is
     * deferred to its ceiling, CEILING timeouts, then the Overseer's write
     * is given up and both go; never longer.
     */
    @Test(timeout = 60000L)
    public void theCycleWithAPollCostsAtMostTheStallsCeiling()
            throws Exception {
        String q = "/overseer/queue/qn-";
        enforceRecorded("o:" + q + " c:" + q, 300L, at -> written(at));
        CountDownLatch completed = new CountDownLatch(1);
        long before = System.nanoTime();
        Thread overseer = started(() -> request("o", () -> {
            try {
                while (!completed.await(50L, TimeUnit.MILLISECONDS)) {
                    send("SOLR_HTTP#REQUEST:admin.cores:REQUESTSTATUS");
                }
                written(q);
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
        }));
        Thread create = started(() -> request("c", () -> {
            written(q);
            completed.countDown();
        }));
        overseer.join(30000L);
        create.join(30000L);
        long took = since(before);
        assertFalse(overseer.isAlive() || create.isAlive());
        assertTrue("the ceiling, not for ever: " + took,
                took >= ScheduleLog.CEILING * 300L
                        && took < ScheduleLog.CEILING * 300L + 5000L);
    }

    /**
     * A leader election's node is created under its node's store session,
     * whose id differs from run to run: stated by the adapter as the node's
     * own spelling, the location keys by the node's name, so the replay's
     * creates take their recorded slots in order.  A session no adapter
     * stated keys alike in no two runs: its write takes no turn.
     */
    @Test(timeout = 20000L)
    public void anElectionPrefixKeysByItsNodeAcrossRunsWithOtherSessions()
            throws Exception {
        noRequest();
        MessageDoors.spelledAs("auto0/node0", "72088256043548677");
        MessageDoors.spelledAs("auto0/node1", "72088256043548678");
        request("a", () -> written("/elect/72088256043548677-core_node3-n_"));
        request("b", () -> written("/elect/72088256043548678-core_node6-n_"));
        List<ScheduleEvent> recorded = events();
        assertEquals(Arrays.asList("STORE:/elect/{auto0/node0}-core_node3-n_",
                "STORE:/elect/{auto0/node1}-core_node6-n_"), sites());
        noRequest();
        MessageDoors.spelledAs("auto0/node0", "72089999000000001");
        MessageDoors.spelledAs("auto0/node1", "72089999000000002");
        timeout(30000L);
        enforce(recorded);
        Thread b = started(() -> request("b", () -> written(
                "/elect/72089999000000002-core_node6-n_")));
        Thread.sleep(500L);
        assertTrue("node1's create waits for node0's", b.isAlive());
        request("a", () -> written("/elect/72089999000000001-core_node3-n_"));
        b.join(10000L);
        assertEquals(recorded.get(0).context(), events().get(0).context());
        progress("2 taken, 0 given up");
        written.clear();
        request("c", () -> written("/elect/72089999000000003-core_node9-n_"));
        assertTrue("an unstated session takes no turn: " + sites(),
                sites().isEmpty());
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

    /** A WAKE or turn the recording did not make before x waits at the cut. */
    @Test(timeout = 20000L)
    public void aWakeTheRecordingDidNotMakeSleepsThroughThePrefix()
            throws Exception {
        timeout(30000L);
        String site = "<D: void offerService()>#u4";
        enforce(prefix("x"));
        Thread daemon = started(() -> {
            try {
                TimedWaits.sleep(10L, site);
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
        });
        Thread turn = observer(WAKE, "tick.e");
        Thread.sleep(500L);
        assertTrue("its 10 ms are long past on the wall clock, and the "
                + "recording made no such WAKE before x", daemon.isAlive());
        assertTrue("nor such a turn: it waits at the cut", turn.isAlive());
        assertTrue(written.isEmpty());
        send("x");
        joined(daemon, turn);
        List<String> sites = sites();
        assertEquals(sites.toString(), 3, sites.size());
        assertEquals("x", sites.get(0));
        assertTrue(sites.toString(),
                sites.containsAll(Arrays.asList(site, "tick.e")));
    }

    /**
     * A daemon's turn, and an interrupt another thread's call made, are in
     * no later event's way: nobody waits for them, and each still takes its
     * slot when it comes (an INTERRUPT inside the prefix included).
     */
    @Test(timeout = 20000L)
    public void nobodyWaitsForALateWakeOrInterruptAndItStillTakesItsSlot()
            throws Exception {
        timeout(30000L);
        Object[][] rows = {{WAKE, "tick.d"},
                {INTERRUPT, "<S: void run()>#u12"}};
        for (Object[] row : rows) {
            Kind kind = (Kind) row[0];
            String site = (String) row[1];
            restart();
            enforce(Arrays.asList(event(kind, site), event(SEND, "x"),
                    event(SEND, "y")));
            long before = System.nanoTime();
            send("x");
            assertTrue(kind + ": x did not wait for the slot before it",
                    since(before) < 5000L);
            ScheduleLog.observe(kind, site);
            send("y");
            assertEquals(kind.name(), Arrays.asList("x", site, "y"), sites());
            progress(" 0 given up");
            assertFalse(kind + ": every slot taken", ScheduleLog.enforcing());
        }
    }

    /** A held wait, and a held poll, outlive the prefix's end. */
    @Test
    public void aHeldWaitOutlivesThePrefixOnTheWallClock() throws Exception {
        timeout(30000L);
        enforce(prefix("x"));
        Object monitor = new Object();
        Thread idle = waits(monitor, WORK, 1, true).get(0);
        BlockingQueue<Object> queue = new LinkedBlockingQueue<Object>();
        Object[] taken = new Object[1];
        Thread sender = started(() -> {
            try {
                taken[0] = TimedWaits.poll(queue, 60L, TimeUnit.SECONDS,
                        "<S: void run()>#u12");
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
        });
        Thread.sleep(200L);
        // The prefix's last event: the run is free from here.
        send("x");
        assertFalse(ScheduleLog.enforcing());
        Thread.sleep(500L);
        assertTrue("the prefix's end is no timeout of this wait",
                idle.isAlive());
        assertTrue("nor of this poll", sender.isAlive());
        synchronized (monitor) {
            TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
        }
        queue.put("call");
        joined(idle, sender);
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
     * A turn the window saw begin states its WAKE before its first event and
     * its END; the set-up's, none.  A turn that makes no event writes
     * nothing and gives its k back (hdfs-adhoc-16: an actor spinning through
     * empty turns), so the turn that acts after any number of them is #1.
     */
    @Test
    public void aTurnThatActsStatesItsWakeAndEndAndAnEmptyOneNothing() {
        RecordingWindow.reset();
        long setUp = RuntimeTraceContext.beginTick(new Object(),
                "BP_SERVICE_ACTOR");
        RecordingWindow.open();
        RuntimeTraceContext.endTick(setUp);
        assertTrue("the set-up's turn is not the window's", written.isEmpty());
        Object daemon = new Object();
        RuntimeTraceContext.registerSource(daemon, NODE);
        for (int spin = 0; spin < 3; spin++) {
            long empty = RuntimeTraceContext.beginTick(daemon,
                    "HEARTBEAT_TICK");
            // A held wait's WAKE, which only a replay computes, names none.
            ScheduleLog.wake("<D: void poll()>#u3");
            RuntimeTraceContext.endTick(empty);
        }
        assertTrue("empty turns hold no slot", written.isEmpty());
        long tick = RuntimeTraceContext.beginTick(daemon, "HEARTBEAT_TICK");
        send("HADOOP_IPC#REQUEST");
        RuntimeTraceContext.endTick(tick);
        List<ScheduleEvent> events = events();
        assertEquals(Arrays.asList(WAKE, SEND, END), kinds());
        assertTrue(events.get(0).context(),
                events.get(0).context().contains("Root:HEARTBEAT_TICK#1"));
        assertEquals("the END stands in the turn's own context",
                events.get(0).context(), events.get(2).context());
        assertEquals("tick.HEARTBEAT_TICK", events.get(2).site());
        long carrying = RuntimeTraceContext.beginTick(daemon,
                "HEARTBEAT_TICK");
        Lineage.capture();
        RuntimeTraceContext.endTick(carrying);
        long next = RuntimeTraceContext.beginTick(daemon, "HEARTBEAT_TICK");
        send("HADOOP_IPC#REQUEST");
        RuntimeTraceContext.endTick(next);
        assertTrue("work captured in a turn keeps its k: " + events(),
                events().get(3).context().contains("Root:HEARTBEAT_TICK#3"));
    }

    @Test
    public void aTurnsEndIsHeldToItsPlaceInThePrefix() throws Exception {
        // One free turn: its WAKE and END as this JVM computes them.  The
        // prefix below is a discovering run whose turn ended AFTER a send.
        Object monitor = new Object();
        daemonTurn(monitor, null).join(5000L);
        List<ScheduleEvent> free = events();
        assertEquals(END, free.get(2).kind());
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        restart();
        openRequest();
        timeout(30000L);
        enforce(Arrays.asList(free.get(0), free.get(1), event(SEND, "y"),
                free.get(2)));
        CountDownLatch ending = new CountDownLatch(1);
        Thread held = daemonTurn(monitor, ending);
        assertTrue(ending.await(5L, TimeUnit.SECONDS));
        Thread.sleep(200L);
        assertTrue("the turn's END waits for the send before it",
                held.isAlive());
        send("y");
        joined(held);
        assertEquals(Arrays.asList("tick.HEARTBEAT_TICK", "beat", "y",
                "tick.HEARTBEAT_TICK"), sites());
        progress(" 0 given up");
    }

    /**
     * JLS 17.2.4: a notify is never lost to an interrupt -- the interrupted
     * wait returns normally with its interrupt pending, or it throws and
     * the other wait is woken.  A wait the wall clock ended is out of the
     * wait set already: the notify goes to the one still in it, and the
     * clock's is a timeout, a WAKE.
     */
    @Test
    public void aWaitAWovenNotifyMarkedKeepsItThroughAnInterrupt()
            throws Exception {
        Object monitor = new Object();
        String[] outcome = new String[2];
        CountDownLatch waiting = new CountDownLatch(2);
        Thread first = untimedWaiter(monitor, outcome, 0, waiting);
        waitUntilWaiting(first);
        Thread second = untimedWaiter(monitor, outcome, 1, waiting);
        waiting.await();
        waitUntilWaiting(second);
        synchronized (monitor) {
            first.interrupt();
            Thread.sleep(200L);
            TimedWaits.notifyOn(monitor, "<C: void n()>#u1");
        }
        first.join(5000L);
        second.join(300L);
        assertTrue("the notify was lost: " + Arrays.toString(outcome),
                "normal+interrupted".equals(outcome[0])
                        || ("threw".equals(outcome[0])
                        && "normal".equals(outcome[1])));
        synchronized (monitor) {
            TimedWaits.notifyAllOn(monitor, "<C: void n()>#u1");
        }
        joined(second);

        restart();
        Arrays.fill(outcome, null);
        Thread timed = started(() -> {
            synchronized (monitor) {
                try {
                    TimedWaits.waitOn(monitor, 100L, "<C: void t()>#u2");
                    outcome[0] = "returned";
                } catch (InterruptedException interrupted) {
                    outcome[0] = "threw";
                }
            }
        });
        waitUntilWaiting(timed);
        CountDownLatch untimedWaiting = new CountDownLatch(1);
        Thread untimed = untimedWaiter(monitor, outcome, 1, untimedWaiting);
        untimedWaiting.await();
        waitUntilWaiting(untimed);
        synchronized (monitor) {
            // The timed wait's 100 ms run out while this thread holds it.
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
        // A wait at a site the identity cannot name makes no event.
        enforce(prefix("x"));
        assertTrue(ScheduleLog.enforcing());
        long before = System.nanoTime();
        TimedWaits.sleep(300L, "");
        long took = since(before);
        assertTrue("neither skipped nor spun forever: " + took,
                took >= 250L && took < 5000L);

        restart();
        timeout(30000L);
        String site = "<L: void loop()>#u9";
        enforce(prefix("x"), Collections.singletonList(event(WAKE, "tick.d")));
        send("x");
        before = System.nanoTime();
        TimedWaits.sleep(500L, site);
        took = since(before);
        assertTrue("to its own deadline, not at once: " + took, took >= 450L);
        assertTrue("and not held for the rest: " + took, took < 5000L);
        assertEquals(Arrays.asList("x", site), sites());

        // A poll(0) takes what another thread offers right now: a DataNode
        // proxy's IPC sender polls its SynchronousQueue at maxIdleTime 0.
        SynchronousQueue<String> queue = new SynchronousQueue<String>();
        Thread caller = started(() -> {
            try {
                while (!queue.offer("call", 1L, TimeUnit.SECONDS)) {
                    // As Client.Connection.sendRpcRequest does.
                }
            } catch (InterruptedException stopped) {
                Thread.currentThread().interrupt();
            }
        });
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
        timeout(30000L);
        enforce(prefix("x"));
        Object monitor = new Object();
        String[] outcome = new String[1];
        Thread waiter = started(() -> {
            synchronized (monitor) {
                try {
                    TimedWaits.waitOn(monitor, 60000L, WORK);
                    outcome[0] = "returned";
                } catch (InterruptedException interrupted) {
                    outcome[0] = "threw";
                }
            }
        });
        waitUntilWaiting(waiter);
        waiter.interrupt();
        waiter.join(5000L);
        assertEquals("the interrupt ends the held wait by throwing", "threw",
                outcome[0]);
        assertEquals(Collections.singletonList(WORK), sites());
        assertEquals(INTERRUPT, events().get(0).kind());
        String spin = "<P: void spin()>#u3";
        for (boolean held : new boolean[] {false, true}) {
            restart();
            if (held) enforce(prefix("x"));
            boolean[] flagged = new boolean[1];
            Thread parker = started(() -> {
                // JDK 8 hands a new thread a finished thread's park state
                // with its permit still set: an inherited permit would
                // return the first park at once, an unpark.
                LockSupport.parkNanos(1L);
                TimedWaits.parkNanos(TimeUnit.SECONDS.toNanos(20L), spin);
                flagged[0] = Thread.currentThread().isInterrupted();
            });
            waitUntilWaiting(parker);
            Thread.sleep(30L);
            parker.interrupt();
            joined(parker);
            assertTrue("the park leaves the flag", flagged[0]);
            assertEquals((held ? "held" : "free") + ": the interrupt that "
                    + "ended the park writes its WAKE",
                    Collections.singletonList(spin), sites());
        }
    }

    /** One wait, entered interrupted, that throws. */
    private interface Interruptible {
        void run() throws InterruptedException;
    }

    /**
     * Entered with an interrupt pending, a wait does what the JDK's does:
     * a park returns at once with no event and the flag left; sleep(0),
     * poll(0) and awaitNanos(0) throw, and so does Object.wait, turn or no
     * turn, clearing the flag.
     */
    @Test
    public void aTimedWaitEnteredInterruptedThrowsEvenWhenItsTurnIsNext()
            throws Exception {
        String site = "<L: void loop()>#u4";
        enforce(Collections.singletonList(event(WAKE, site)));
        Thread.currentThread().interrupt();
        long before = System.nanoTime();
        TimedWaits.parkNanos(TimeUnit.SECONDS.toNanos(10L),
                "<P: void spin()>#u3");
        assertTrue("a park returns at once for an interrupted thread",
                since(before) < 5000L);
        assertTrue("and leaves the flag for its caller",
                Thread.interrupted());
        assertTrue("a loop around it would spin: no event per spin",
                written.isEmpty());
        Object monitor = new Object();
        ReentrantLock lock = new ReentrantLock();
        Condition ready = lock.newCondition();
        Map<String, Interruptible> waits = new LinkedHashMap<>();
        waits.put("Thread.sleep(0)", () -> TimedWaits.sleep(0L,
                "<L: void loop()>#u9"));
        waits.put("a timed poll(0)", () -> TimedWaits.poll(
                new LinkedBlockingQueue<Object>(), 0L, TimeUnit.MILLISECONDS,
                "<S: void run()>#u12"));
        waits.put("Object.wait, turn or no turn", () -> {
            synchronized (monitor) {
                TimedWaits.waitOn(monitor, 60000L, site);
            }
        });
        waits.put("awaitNanos(0), as AQS's does", () -> {
            lock.lock();
            try {
                TimedWaits.awaitNanos(ready, 0L, "<Q: void take()>#u8");
            } finally {
                lock.unlock();
            }
        });
        for (Map.Entry<String, Interruptible> wait : waits.entrySet()) {
            Thread.currentThread().interrupt();
            boolean threw = false;
            try {
                wait.getValue().run();
            } catch (InterruptedException interrupted) {
                threw = true;
            }
            assertTrue(wait.getKey() + " throws on a pending interrupt",
                    threw);
            if (wait.getKey().startsWith("Object.wait")) {
                assertFalse("and clears the flag, as the JDK's does",
                        Thread.currentThread().isInterrupted());
            }
            Thread.interrupted();
        }
    }

    /** An untimed woven wait, started, that writes how it ended into
     *  outcome[at]. */
    private static Thread untimedWaiter(Object monitor, String[] outcome,
                                        int at, CountDownLatch waiting) {
        return started(() -> {
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

    /** One daemon turn on a thread of its own, started; counts down before
     *  its end. */
    private static Thread daemonTurn(Object owner, CountDownLatch ending) {
        return started(() -> {
            long tick = RuntimeTraceContext.beginTick(owner, "HEARTBEAT_TICK");
            send("beat");
            if (ending != null) ending.countDown();
            RuntimeTraceContext.endTick(tick);
        });
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

    /**
     * Past the prefix a timeout the rest holds waits for the events it
     * followed -- a daemon's turn and a held wait's WAKE alike.
     */
    @Test
    public void pastThePrefixATimeoutWaitsForTheEventsItFollowed()
            throws Exception {
        timeout(30000L);
        enforce(prefix("x"), Arrays.asList(event(SEND, "a"),
                event(WAKE, "tick.d"), event(WAKE, WORK)));
        long before = System.nanoTime();
        Object monitor = new Object();
        Thread idle = started(() -> {
            synchronized (monitor) {
                try {
                    TimedWaits.waitOn(monitor, 1500L, WORK);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        });
        send("x");
        assertTrue("the rest's timeouts are still to come",
                ScheduleLog.enforcing());
        Thread daemon = observer(WAKE, "tick.d");
        Thread.sleep(300L);
        assertTrue("the daemon's turn waits for what it followed",
                daemon.isAlive());
        assertTrue("and so does the held wait's timeout", idle.isAlive());
        assertEquals(Collections.singletonList("x"), sites());
        send("a");
        joined(daemon, idle);
        assertTrue("its own 1.5 s, no sooner", since(before) >= 1450L);
        assertEquals(Arrays.asList("x", "a", "tick.d", WORK), sites());
        assertFalse("no timeout of the rest is still to come",
                ScheduleLog.enforcing());
    }

    @Test
    public void pastThePrefixEverythingButTheRestsTimeoutsRunsFree() {
        timeout(30000L);
        enforce(prefix("x"), Arrays.asList(event(SEND, "a"),
                event(WAKE, "tick.d")));
        send("x");
        long before = System.nanoTime();
        send("unnamed");
        ScheduleLog.observe(WAKE, "tick.other");
        assertEquals(ScheduleLog.Turn.FREE,
                ScheduleLog.turn(ScheduleLog.wake("<L: void other()>#u1")));
        assertTrue("nothing the rest does not hold waits",
                since(before) < 200L);
        assertEquals(ScheduleLog.Turn.NOT_YET,
                ScheduleLog.turn(ScheduleLog.wake("tick.d")));
        assertEquals(Arrays.asList("x", "unnamed", "tick.other"), sites());
        assertTrue(ScheduleLog.enforcing());
    }

    /**
     * AN ORDER CUT AT ITS WITNESS ENDS THERE: its run made nothing it does
     * not list before the witness, so a WAKE it never made -- a daemon's
     * first turn -- waits until the order has drained, even in the unheld
     * order CONFIRM writes (hdfs-17967-pathC r1b: the target DataNode's
     * first actor turn ran free before the anchor and refreshed the keys the
     * witness had failed on).  Any other event it lacks runs free.
     */
    @Test(timeout = 20000L)
    public void anOrderCutAtItsWitnessHoldsAWakeItNeverMadeToItsEnd()
            throws Exception {
        timeout(30000L);
        ScheduleLog.enforceForTests(Collections.<ScheduleEvent>emptyList(),
                prefix("a", "anchor"), true);
        Thread daemon = observer(WAKE, "tick.first");
        Thread.sleep(300L);
        assertTrue("the daemon's first turn waits for the witness's order",
                daemon.isAlive());
        send("unnamed");
        send("a");
        send("anchor");
        joined(daemon);
        assertEquals(Arrays.asList("unnamed", "a", "anchor", "tick.first"),
                sites());
    }

    /**
     * A stall gives up only what came before the earliest waiting timeout,
     * past the prefix or inside it: a later timeout still waits for what it
     * followed.
     */
    @Test
    public void theRestGivesUpOnlyWhatCameBeforeTheEarliestWaitingTimeout()
            throws Exception {
        timeout(1000L);
        enforce(prefix("x"), Arrays.asList(event(SEND, "never"),
                event(WAKE, "tick.d"), event(SEND, "y"),
                event(WAKE, "tick.e")));
        send("x");
        Thread later = observer(WAKE, "tick.e");
        Thread earlier = observer(WAKE, "tick.d");
        earlier.join(10000L);
        assertFalse("the earliest waiting timeout gives up what it followed",
                earlier.isAlive());
        assertTrue("the later one still waits for y", later.isAlive());
        send("y");
        joined(later);
        assertEquals(Arrays.asList("x", "tick.d", "y", "tick.e"), sites());
        progress(" 1 given up");

        // Inside the prefix: the same give-up, and the rest still to come.
        restart();
        timeout(300L);
        enforce(Arrays.asList(event(SEND, "never"), event(WAKE, "tick.d"),
                event(SEND, "y")), Collections.singletonList(
                event(WAKE, "tick.e")));
        joined(observer(WAKE, "tick.d"));
        progress(" 1 given up");
        assertTrue("tick.e is still to come", ScheduleLog.enforcing());
        Thread other = observer(WAKE, "tick.e");
        Thread.sleep(100L);
        assertTrue("tick.e follows y", other.isAlive());
        send("y");
        joined(other);
        assertEquals(Arrays.asList("tick.d", "y", "tick.e"), sites());
        assertFalse(ScheduleLog.enforcing());
    }

    @Test
    public void aStallGivesUpOnlyTheSlotThatNeverCame() throws Exception {
        timeout(300L);
        for (int round = 0; round < 5; round++) {
            restart();
            enforce(Arrays.asList(event(SEND, "never"),
                    event(SEND, "refresh"), event(WAKE, "tick.hb")));
            // Whichever of them the watchdog wakes first, the heartbeat
            // does not jump the refresh the prefix held back.
            Thread heartbeat = observer(WAKE, "tick.hb");
            Thread refresh = observer(SEND, "refresh");
            heartbeat.join(5000L);
            refresh.join(5000L);
            assertFalse(heartbeat.isAlive() || refresh.isAlive());
            assertEquals("round " + round,
                    Arrays.asList("refresh", "tick.hb"), sites());
        }
    }

    /** A turn that found its heartbeat not due -- WAKE, then END -- settles
     *  what it did not do: the next turn waits for none of it. */
    @Test
    public void aTurnsEndSettlesWhatTheTurnDidNotDo() throws Exception {
        timeout(30000L);
        enforce(prefix("x"), Arrays.asList(event(WAKE, "tick.a"),
                event(SEND, "heartbeat"), event(START, "call"),
                event(END, "tick.a"), event(WAKE, "tick.b")));
        send("x");
        long before = System.nanoTime();
        ScheduleLog.observe(WAKE, "tick.a");
        ScheduleLog.observe(END, "tick.a");
        ScheduleLog.observe(WAKE, "tick.b");
        assertTrue(since(before) < 1000L);
        assertEquals(Arrays.asList("x", "tick.a", "tick.a", "tick.b"),
                sites());
        progress("2 settled");
    }

    @Test
    public void theRestIsLetGoAfterItsStalls() throws Exception {
        timeout(300L);
        List<ScheduleEvent> after = new ArrayList<ScheduleEvent>();
        for (int turn = 1; turn <= 4; turn++) {
            after.add(event(SEND, "never" + turn));
            after.add(event(WAKE, "tick.d" + turn));
        }
        enforce(prefix("x"), after);
        send("x");
        for (int turn = 1; turn <= ScheduleLog.REST_STALLS; turn++) {
            ScheduleLog.observe(WAKE, "tick.d" + turn);
            assertTrue("stall " + turn + " holds", ScheduleLog.enforcing());
        }
        ScheduleLog.observe(WAKE, "tick.d" + (ScheduleLog.REST_STALLS + 1));
        assertFalse("the stall after them lets the rest go",
                ScheduleLog.enforcing());
        long before = System.nanoTime();
        ScheduleLog.observe(WAKE, "tick.d4");
        assertTrue(since(before) < 200L);
    }

    /** Released by the watchdog, not by an ask gone stale. */
    @Test
    public void aWaitASignalEndedNoLongerDefersAGiveUp() throws Exception {
        timeout(400L);
        enforce(prefix("x"), Arrays.asList(event(SEND, "never"),
                event(WAKE, WORK), event(SEND, "never2"),
                event(WAKE, "tick.e")));
        send("x");
        Object monitor = new Object();
        Thread idle = waits(monitor, WORK, 1, true).get(0);
        Thread.sleep(200L);
        synchronized (monitor) {
            TimedWaits.notifyOn(monitor, "<C: boolean addCall(Call)>#u3");
        }
        joined(idle);
        long before = System.nanoTime();
        ScheduleLog.observe(WAKE, "tick.e");
        assertTrue(since(before) < 5000L);
        assertEquals(Arrays.asList("x", "tick.e"), sites());
    }

    /**
     * An occurrence's close settles the slots it held and made nothing
     * for, and only those: another occurrence's close shifts none of them.
     * A write whose slot its occurrence's close settled runs free: it is no
     * write the recording never made there, waiting behind another
     * context's next write, and a poll whose slot died is no poll past its
     * count (solr-adhoc-19 MB8s: the Overseer's state.json write waited
     * behind its own write 110 slots on).
     */
    @Test(timeout = 30000L)
    public void anOccurrencesCloseSettlesWhatItDidNotMake() throws Exception {
        timeout(30000L);
        // A send inside o1 the replay never makes (a stale connection's
        // attempt), a connection set-up, then the retry's send inside o2.
        enforce(Arrays.asList(inOccurrence(SEND, "req", "o1"),
                event(START, "conn"), inOccurrence(SEND, "req", "o2")));
        Thread setUp = observer(START, "conn");
        Thread.sleep(200L);
        assertTrue("conn waits for the slot before it", setUp.isAlive());
        long before = System.nanoTime();
        ScheduleLog.closed("o1");
        joined(setUp);
        assertTrue("no watchdog: the close settled it", since(before) < 2000L);
        send("req");
        assertEquals(Arrays.asList("conn", "req"), sites());
        assertFalse("the retry took o2's slot", ScheduleLog.enforcing());
        progress(" 1 settled by their occurrence's close");

        restart();
        enforce(Arrays.asList(inOccurrence(SEND, "req", "o1"),
                event(START, "a"), inOccurrence(SEND, "req", "o2"),
                event(START, "b")));
        ScheduleLog.closed("o2");
        send("req");
        ScheduleLog.observe(START, "a");
        before = System.nanoTime();
        ScheduleLog.observe(START, "b");
        assertTrue("o2's dead slot does not hold b", since(before) < 1000L);
        assertEquals(Arrays.asList("req", "a", "b"), sites());
        assertFalse(ScheduleLog.enforcing());

        restart();
        String here = ScheduleLog.contextOf(Identity.contextHere());
        String p = ScheduleEvent.written("STORE", "/p");
        enforce(Arrays.asList(ScheduleEvent.of(0L, WRITE, here, p, 0, "o1"),
                ScheduleEvent.of(0L, WAKE, here, "tick.w", 0, "o1"),
                event(SEND, "x"), ScheduleEvent.of(0L, WRITE, "other|Root:X",
                        p, 0, ""), event(SEND, "y")));
        ScheduleLog.closed("o1");
        send("x");
        before = System.nanoTime();
        written("/p");
        ScheduleLog.observe(WAKE, "tick.w");
        assertTrue("no wait behind the other context's write, no hold",
                since(before) < 2000L);
        progress("2 settled by their occurrence's close");
        progress("2 event(s) ran free");
    }

    /**
     * A context family whose frontier event a stall gave up has diverged:
     * its next frontier -- another turn of the same daemon, another anchor of
     * the same kind of message on the node -- stands a grace, not a timeout
     * (SG2: 69 of solr-adhoc-38's 138 give-up stalls; MB21s: 34 of 10's 58).
     */
    @Test(timeout = 60000L)
    public void aContextFamilyThatFailedAStallStandsAGraceNext()
            throws Exception {
        assertEquals("n|Root:WAKE/q.peek#*", ScheduleLog.familyOf(
                "n|Root:WAKE/q.peek#12|<a.B: void c()>#u3@0"));
        assertEquals("n|Anchor:*@SOLR_HTTP/test", ScheduleLog.familyOf(
                "n|Anchor:813cbf610082e340@SOLR_HTTP/test"));
        timeout(6000L);
        enforce(Arrays.asList(
                ScheduleEvent.of(0L, SEND, "gone|Root:G#1", "n1", 0, ""),
                event(SEND, "a"),
                ScheduleEvent.of(0L, SEND, "gone|Root:G#2", "n2", 0, ""),
                event(SEND, "b")));
        long before = System.nanoTime();
        send("a");
        long first = since(before);
        before = System.nanoTime();
        send("b");
        long second = since(before);
        assertTrue("the first stall a timeout: " + first, first >= 6000L);
        assertTrue("the failed family's next a grace: " + second,
                second >= ScheduleLog.LET_GO_GRACE_MS && second < 5000L);
        progress("2 taken, 2 given up in 2");
    }

    /**
     * A write the order lacks whose own context holds an open slot before
     * the next write to its location owes that slot: it goes at once, never
     * behind that later write, which held the order until the watchdog
     * (solr-adhoc-19 MB14s: a node's extra compare-and-set retry at its terms
     * node).  One that owes nothing before the write still waits for it.
     */
    @Test(timeout = 60000L)
    public void aWriteOwingASlotBeforeTheNextWriteThereGoes() throws Exception {
        ScheduleEvent other = ScheduleEvent.of(0L, WRITE, "other|Root:X",
                ScheduleEvent.written("STORE", "/p"), 0, "");
        ScheduleEvent far = ScheduleEvent.of(0L, SEND, "far|Root:F", "f", 0,
                "");
        Object[][] rows = {
            {"its own slot the frontier",
                Arrays.asList(event(SEND, "x"), other), true},
            {"its own slot behind another's",
                Arrays.asList(far, event(SEND, "x"), other), true},
            {"no own slot before the write",
                Arrays.asList(far, other, event(SEND, "x")), false}};
        for (Object[] row : rows) {
            restart();
            timeout(30000L);
            @SuppressWarnings("unchecked")
            List<ScheduleEvent> order = (List<ScheduleEvent>) row[1];
            enforce(order);
            Thread writer = started(() -> written("/p"));
            writer.join(2000L);
            assertEquals((String) row[0], !(Boolean) row[2],
                    writer.isAlive());
            writer.interrupt();
            writer.join(5000L);
        }
    }

    /**
     * A waiter gives up at once what its own occurrence passed: only its
     * thread could make it, and that thread waits beyond it.
     */
    @Test
    public void aWaiterGivesUpWhatItsOwnOccurrencePassed() throws Exception {
        timeout(30000L);
        Identity.occurrence(NODE.key(), "REGION.handler", true);
        String own = Identity.innermostRegionId();
        written.clear();
        enforce(Arrays.asList(inOccurrence(START, "enqueue", own),
                event(SEND, "x"), inOccurrence(SEND, "response", own)));
        Thread other = observer(SEND, "x");
        Thread.sleep(200L);
        assertTrue("x waits behind the handler's enqueue", other.isAlive());
        long before = System.nanoTime();
        send("response");
        other.join(5000L);
        assertTrue("no watchdog: the handler passed its enqueue",
                since(before) < 2000L);
        assertEquals(Arrays.asList("x", "response"), sites());
        progress(" 1 passed by their own occurrence");
    }

    /**
     * A waiter no occurrence names passes the earlier slots of its own
     * context, no occurrence naming them, at sites it made itself there: a
     * test's wall-clock poll ran fewer rounds than recorded (hdfs-adhoc-44).
     * A slot an occurrence names is not passed, nor one of a site only
     * another thread made, and a passed slot is still taken if it comes.
     */
    @Test
    public void aWaiterNoOccurrenceNamesPassesTheRestOfItsOwnLoop()
            throws Exception {
        timeout(30000L);
        enforce(Arrays.asList(event(SEND, "poll"), event(SEND, "poll"),
                event(SEND, "other"), inOccurrence(START, "named", "o1"),
                event(SEND, "after")));
        send("poll");
        Thread other = started(() -> {
            nap(300L);
            send("other");
            ScheduleLog.observe(START, "named");
        });
        long before = System.nanoTime();
        send("after");
        assertTrue("after waited for other and the named start",
                since(before) >= 250L);
        other.join(5000L);
        send("poll");
        assertEquals(Arrays.asList("poll", "other", "named", "after",
                "poll"), sites());
        progress(" 0 given up in 0 stall(s), 0 settled by their occurrence's"
                + " close, 0 settled by their turn's END, 1 passed by their"
                + " own occurrence or context (1 context(s) without an"
                + " occurrence)");
    }

    /**
     * A computing workload thread defers a stall, whichever context it last
     * stood in: which thread owes x cannot be seen between two of its events
     * (one that made w, one that made nothing yet, one whose last event was a
     * poll past its recorded count).  The engine's own threads never do: x
     * is given up after a timeout while one computes.
     */
    @Test
    public void aComputingWorkloadThreadDefersAStallAnEngineThreadDoesNot()
            throws Exception {
        timeout(700L);
        String w = "w";
        String p = "tick.poll";
        // row: what the worker made before it computes, the order's first
        // event, the worker's name, the sites written, whether x was given up.
        Object[][] rows = {
            {"made w", Arrays.asList(SEND), w, "worker",
                Arrays.asList(w, "x", "tick.d"), false},
            {"made nothing", Collections.emptyList(), w, "worker",
                Arrays.asList(w, "x", "tick.d"), false},
            {"polled once past its recorded count", Arrays.asList(WAKE, WAKE),
                p, "worker", Arrays.asList(p, p, "x", "tick.d"), false},
            {"is the engine's", Collections.emptyList(), w,
                "causynth-test-publication", Arrays.asList(w, "tick.d", "x"),
                true}};
        for (Object[] row : rows) {
            restart();
            String name = "a thread that " + row[0] + " computes";
            @SuppressWarnings("unchecked")
            List<Kind> before = (List<Kind>) row[1];
            String first = (String) row[2];
            enforce(Arrays.asList(event(first.equals(w) ? SEND : WAKE, first),
                    event(SEND, "x"), event(WAKE, "tick.d")));
            if (before.isEmpty()) send(w);
            Thread worker = new Thread(() -> {
                for (Kind kind : before) ScheduleLog.observe(kind, first);
                spin(3500L);
                send("x");
            }, (String) row[3]);
            worker.start();
            Thread daemon = observer(WAKE, "tick.d");
            worker.join(10000L);
            daemon.join(10000L);
            assertFalse(name, worker.isAlive() || daemon.isAlive());
            assertEquals(name, row[4], sites());
            progress((Boolean) row[5] ? " 1 given up" : " 0 given up");
        }
    }

    /**
     * The stall is the frontier's.  A daemon waits at tick.d behind x, which
     * x's owner makes in the test's context, while a thread in a context of
     * its own runs on elsewhere for longer than CEILING timeouts, burning
     * CPU: making events the order lacks, or taking the order's slots past x.
     * Neither moves the frontier nor defers the give-up: x is given up a
     * timeout and a CPU look after it stood (hdfs-17899-bug2 w4d1 CONFIRM).
     * x's owner seen at work in x's context defers it however little CPU it
     * gets: here a third of one.
     */
    @Test(timeout = 60000L)
    public void aThreadRunningElsewhereDefersNoStallTheFrontiersOwnerDoes()
            throws Exception {
        long timeout = 500L;
        // row: what the other thread does, its site, x's owner works.
        Object[][] rows = {
            {"runs free", "free", false},
            {"takes the slots past x", "e", false},
            {"takes the slots past x while x's owner works", "e", true}};
        for (Object[] row : rows) {
            restart();
            String name = "a thread that " + row[0];
            String site = (String) row[1];
            boolean owner = (Boolean) row[2];
            timeout(timeout);
            String[] context = new String[1];
            CountDownLatch placed = new CountDownLatch(1);
            CountDownLatch go = new CountDownLatch(1);
            boolean[] stop = new boolean[1];
            Thread elsewhere = started(() -> {
                long own = RuntimeTraceContext.beginRequest(NODE, "elsewhere",
                        true);
                context[0] = ScheduleLog.contextOf(Identity.contextHere());
                placed.countDown();
                try {
                    go.await();
                    while (!stop[0]) {
                        send(site);
                        spin(100L);
                    }
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                } finally {
                    RuntimeTraceContext.endRequest(own);
                }
            });
            placed.await();
            List<ScheduleEvent> rest = new ArrayList<ScheduleEvent>(
                    Arrays.asList(event(SEND, "x"), event(WAKE, "tick.d")));
            for (int poll = 0; poll < 200; poll++) {
                rest.add(ScheduleEvent.of(0L, SEND, context[0], "e", 0, ""));
            }
            enforce(Collections.<ScheduleEvent>emptyList(), rest);
            Thread works = new Thread(() -> {
                for (int step = 0; step < 30; step++) {
                    spin(30L);
                    nap(70L);
                    send("work");
                }
                send("x");
            });
            long before = System.nanoTime();
            go.countDown();
            if (owner) works.start();
            Thread daemon = observer(WAKE, "tick.d");
            daemon.join(15000L);
            long took = since(before);
            boolean held = daemon.isAlive();
            stop[0] = true;
            elsewhere.join(5000L);
            works.join(10000L);
            daemon.join(5000L);
            assertFalse(name + ": tick.d went while it ran", held);
            List<String> sites = sites();
            sites.retainAll(Arrays.asList("x", "tick.d"));
            if (owner) {
                assertEquals(name, Arrays.asList("x", "tick.d"), sites);
                progress(" 0 given up");
                assertTrue(name + ", held for x: " + took, took >= 2900L);
            } else {
                assertEquals(name, Collections.singletonList("tick.d"), sites);
                progress(" 1 given up");
                assertTrue(name + ", well inside the ceiling: " + took,
                        took < ScheduleLog.CEILING * timeout - 1000L);
            }
        }
    }

    /**
     * A frontier that stood with no one waiting owes its first waiter a
     * whole timeout: x, long overdue, is given up only a timeout after
     * tick.d began to wait for it.
     */
    @Test(timeout = 30000L)
    public void aStallIsTimedFromItsEarliestWaiter() throws Exception {
        timeout(1500L);
        enforce(Arrays.asList(event(SEND, "x"), event(WAKE, "tick.d")));
        Thread.sleep(2000L);
        long before = System.nanoTime();
        joined(observer(WAKE, "tick.d"));
        long took = since(before);
        assertTrue("a timeout from its arrival: " + took, took >= 1500L);
        progress(" 1 given up");
    }

    /**
     * A loop polling past its recorded count, its context's next slot due,
     * does not spin: its first poll past the count goes, and every later one
     * waits for the order to move again -- another context's event -- or for
     * the watchdog to let it go when the run idles.  A loop that reads a
     * CLOCK root waits for time only the clock brings, and is never held so.
     */
    @Test(timeout = 30000L)
    public void aPollPastItsRecordedCountWaitsForTheOrderToMove()
            throws Exception {
        String loop = "<L: boolean poll()>#u5";
        String clock = ScheduleLogTest.class.getName() + "#pollLoop";
        // A clock loop's method, as the scope map declares its CLOCK root.
        JsonObject root = Fixtures.json("{'kind':'STATIC_SCOPE_SITE','role':"
                + "'DECLARED_SITE','inputKind':'CLOCK','vmSite':"
                + "'org.a.RoutingRule#isExpired()Z'}");
        assertEquals("org.a.RoutingRule#isExpired",
                ClockLoops.clockMethod(root));
        StackTraceElement[] atTheRule = {new StackTraceElement(
                "org.a.RoutingRule", "isExpired", null, 0)};
        ClockLoops.install(Collections.singletonList(root));
        assertTrue(ClockLoops.reads(atTheRule));
        root.addProperty("inputKind", "FAULT");
        assertEquals("", ClockLoops.clockMethod(root));
        ClockLoops.install(Collections.singletonList(root));
        assertFalse(ClockLoops.reads(atTheRule));
        // row: released by, timeout, the loop reads a clock, the sites.
        Object[][] rows = {
            {"another context's event", 30000L, false,
                Arrays.asList(loop, loop, "tick.d", loop, "y")},
            {"the run idling", 300L, false,
                Arrays.asList(loop, loop, loop, "y")},
            {"nothing: its loop reads a CLOCK root", 30000L, true,
                Arrays.asList(loop, loop, loop, "y")}};
        for (Object[] row : rows) {
            restart();
            String name = "released by " + row[0];
            timeout((Long) row[1]);
            boolean reads = (Boolean) row[2];
            ClockLoops.useForTests(reads ? Collections.singleton(clock)
                    : Collections.<String>emptySet());
            enforce(Arrays.asList(event(WAKE, loop), event(WAKE, "tick.d"),
                    event(SEND, "y")));
            long before = System.nanoTime();
            Thread poller = started(() -> pollLoop(loop, 3));
            if (name.contains("event")) {
                Thread.sleep(500L);
                assertTrue(name + ": the third poll waits", poller.isAlive());
                ScheduleLog.observe(WAKE, "tick.d");
            }
            joined(poller);
            long took = since(before);
            assertEquals(name, row[3], sites());
            progress(name.contains("idling") ? "1 of them let go"
                    : "0 of them let go");
            assertTrue(name + ": " + took, reads ? took < 2000L
                    : took >= 300L);
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
        send("y");
    }

    /**
     * An event that never comes costs a timeout, then a grace after the
     * waits held without a slot are let go -- not CEILING timeouts twice
     * over while an engine thread computes.  A wait held at the cut is let
     * go once; a poll past its recorded count whose context's next slot is
     * the stalled frontier owes it and is not held at all, and it does not
     * hide that slot from the give-up y waits for: a timeout alone.  A poll
     * held at the cut bounds no give-up (solr-adhoc-13 MB6: a replica poll
     * held at the cut bounded a give-up of 4560 slots at once): with
     * nothing else waiting, the watchdog gives up nothing; once y waits, the
     * frontier's slot alone is given up and y takes its own.
     */
    @Test(timeout = 60000L)
    public void aNeverComingEventCostsATimeoutAndAGrace() throws Exception {
        String loop = "<L: boolean poll()>#u5";
        for (String row : new String[] {"a wait at the cut",
                "a poll past its count", "a poll held at the cut"}) {
            restart();
            timeout(1000L);
            ClockLoops.useForTests(Collections.<String>emptySet());
            boolean counted = row.equals("a poll past its count");
            enforce(counted ? order(event(WAKE, loop), prefix("never", "y"))
                    : prefix("never", "y"));
            boolean[] stop = new boolean[1];
            Thread busy = row.equals("a poll held at the cut") ? null
                    : new Thread(() -> {
                        while (!stop[0]) spin(50L);
                    }, "causynth-test-publication");
            if (busy != null) busy.start();
            long started = System.nanoTime();
            Thread held = row.equals("a wait at the cut")
                    ? observer(WAKE, "tick.idle") : started(() -> {
                        try {
                            while (!stop[0]) TimedWaits.sleep(50L, loop);
                        } catch (InterruptedException interrupted) {
                            Thread.currentThread().interrupt();
                        }
                    });
            String before = "";
            if (busy == null) {
                // Past a timeout and two let-go graces: a give-up was due.
                Thread.sleep(1000L + 2 * ScheduleLog.LET_GO_GRACE_MS + 500L);
                before = ScheduleLog.progress();
            }
            Thread y = observer(SEND, "y");
            y.join(20000L);
            long took = since(started);
            boolean waited = y.isAlive();
            stop[0] = true;
            if (busy != null) busy.join();
            held.join(5000L);
            y.join(5000L);
            assertFalse(row + ": y went while the loop still polled", waited);
            assertFalse(row, y.isAlive() || held.isAlive());
            List<String> sites = sites();
            assertTrue(row + ": " + sites, sites.contains("y"));
            progress(" 1 given up");
            if (busy == null) {
                assertTrue(before, before.contains(" 0 given up"));
                continue;
            }
            assertTrue(row + ", a timeout, then any let-go's grace: " + took,
                    took >= 1000L + (counted ? 0L
                            : ScheduleLog.LET_GO_GRACE_MS));
            assertTrue(row + ", well inside the ceiling: " + took,
                    took < ScheduleLog.CEILING * 1000L - 500L);
            assertEquals(row + ": " + sites, counted ? loop : "tick.idle",
                    sites.get(0));
            progress(counted ? " of them let go" : "1 of them let go");
        }
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
        timeout(30000L);
        String site = "<D: void run()>#u29";
        enforce(Arrays.asList(event(INTERRUPT, site), event(SEND, "x")));
        boolean[] threw = new boolean[1];
        Thread daemon = started(() -> {
            try {
                TimedWaits.sleep(60000L, site);
            } catch (InterruptedException interrupted) {
                threw[0] = true;
            }
        });
        Thread.sleep(300L);
        assertTrue("no WAKE slot: virtual time does not end it",
                daemon.isAlive());
        daemon.interrupt();
        daemon.join(5000L);
        assertTrue(threw[0]);
        assertEquals(INTERRUPT, events().get(0).kind());
        assertTrue("x still holds the order", ScheduleLog.enforcing());
        send("x");
        progress(": 2 taken");
    }

    /**
     * A replay holds a taker at a startup step to the order its recording
     * completed it in (hdfs-adhoc-01/43: DataNodes added in another order
     * placed every pipeline elsewhere), whatever either run's window; a
     * taker the order does not mark and one whose predecessor never comes
     * go on.
     */
    @Test
    public void aReplayTakesTheStepInItsRecordingsOrder() throws Exception {
        RecordingWindow.reset();
        Path order = Files.createTempFile("startup", ".jsonl");
        RowCodec.writeJsonl(order, Arrays.asList(
                RowCodec.writeScheduleStartup("register", "dn1"),
                RowCodec.writeScheduleStartup("register", "dn0")));
        System.setProperty(ScheduleLog.PREFIX_PROPERTY, order.toString());
        timeout(30000L);
        try {
            List<String> took = Collections.synchronizedList(
                    new ArrayList<String>());
            Thread dn0 = started(() -> take("dn0", took));
            Thread.sleep(200L);
            assertTrue("dn0 waits for dn1, marked before it", dn0.isAlive());
            take("dn1", took);
            dn0.join(5000L);
            assertEquals(Arrays.asList("dn1", "dn0"), took);
            for (String row : new String[] {"never comes", "unmarked",
                    "in the window"}) {
                StartupOrder.resetForTests();
                timeout(300L);
                if (row.equals("in the window")) RecordingWindow.open();
                long before = System.nanoTime();
                take(row.equals("unmarked") ? "dn9" : "dn0", took);
                assertEquals("a predecessor that " + row, !row.equals(
                        "unmarked"), since(before) >= 250L);
            }
        } finally {
            System.clearProperty(ScheduleLog.PREFIX_PROPERTY);
            Files.delete(order);
        }
    }

    private static void take(String node, List<String> took) {
        String[] pass = StartupOrder.begin("register", node);
        took.add(node);
        StartupOrder.done(pass);
    }

    /** One event of this thread's context inside a recorded occurrence. */
    private static ScheduleEvent inOccurrence(Kind kind, String site,
                                              String occurrence) {
        return ScheduleEvent.of(0L, kind,
                ScheduleLog.contextOf(Identity.contextHere()), site, 0,
                occurrence);
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
