package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * THE attribution rule, one case per rule: an explicit scope, then the
 * innermost registered receiver on the stack, then the starter by reference
 * (its node by the same rules, its inherited node included) -- and nothing
 * when all fail; what a node's startup starts or creates is the node's; the
 * scope and window index a thread inherits.
 */
public class AttributionTest {
    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "t/nn0", 0L);
    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private static final SourceRef RESTARTED =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 1L);
    private static final SourceRef CLIENT =
            new SourceRef("EXTERNAL_APP", "DFS_CLIENT", "t/client0", 0L);

    @Before
    @After
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        ScheduleLog.resetForTests();
        Lineage.resetForTests();
        RecordingWindow.reset();
    }

    private static String key(SourceRef resolved) {
        return resolved == null ? "" : resolved.key();
    }

    @Test
    public void anExplicitScopeOutranksTheFrames() {
        Object server = new Object();
        Object datanode = new Object();
        RuntimeTraceContext.registerSource(server, NN);
        RuntimeTraceContext.registerSource(datanode, DN);
        long frame = Identity.enterFrame("<a.Server: void call()>", server);
        long request = RuntimeTraceContext.beginRequest(datanode, "refresh");
        assertEquals(DN.key(), Attribution.resolve(null).key());
        RuntimeTraceContext.endRequest(request);
        assertEquals("a closed scope names nothing any more", NN.key(),
                Attribution.resolve(null).key());
        Identity.exitFrame(frame);
    }

    /**
     * A request the workload began in a traced call that returned stands
     * until its end, the calls it began under nested or not, and its end
     * puts back what stood before (SG1, solr-adhoc-31: a test's request
     * begun in its traced createServers).
     */
    @Test
    public void aRequestOutlivesTheCallsItBeganIn() {
        Object client = new Object();
        RuntimeTraceContext.registerSource(client,
                new SourceRef("EXTERNAL_APP", "SOLR_CLIENT", "t/client0", 0L));
        RuntimeTraceContext.View outer = RuntimeTraceContext.enterRoot(null);
        RuntimeTraceContext.View inner = RuntimeTraceContext.enterRoot(null);
        long request = RuntimeTraceContext.beginRequest(client, "test");
        String test = RuntimeTraceContext.current().requestKey;
        RuntimeTraceContext.exitRoot(inner.spanId);
        assertEquals(test, RuntimeTraceContext.current().requestKey);
        RuntimeTraceContext.exitRoot(outer.spanId);
        assertEquals(test, RuntimeTraceContext.current().requestKey);
        assertFalse(RuntimeTraceContext.outboundHeader(null, null).isEmpty());
        RuntimeTraceContext.endRequest(request);
        assertEquals("", RuntimeTraceContext.current().requestKey);
    }

    /** A NameNode handler serving Server.call is the RPC server's, on
     *  whatever pool thread it runs; with all three rules failing, nothing
     *  names the node and the planner counts it unregistered. */
    @Test
    public void theInnermostRegisteredReceiverOnTheStackAnswers() {
        Object server = new Object();
        RuntimeTraceContext.registerSource(server, NN);
        long handler = Identity.enterFrame("<a.Server$Handler: void run()>",
                new Object());
        long call = Identity.enterFrame("<a.Server: void call()>", server);
        long convert = Identity.enterFrame("<a.BlockManager: void convert()>",
                new Object());
        assertEquals(NN.key(), Attribution.resolve(null).key());
        assertEquals(NN.key(),
                RuntimeTraceContext.activationSource(null).key());
        Identity.exitFrame(convert);
        Identity.exitFrame(call);
        Identity.exitFrame(handler);
        reset();
        Identity.enterFrame("<a.Orphan: void run()>", new Object());
        assertNull(Attribution.resolve(null));
        assertEquals(RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                RuntimeTraceContext.activationSource(null).key());
    }

    /** A DataNode's server thread started before the node registers:
     *  nothing names it until then, the reference resolves once it is. */
    @Test
    public void aStarterRegisteredAfterTheStartStillAttributesTheWork()
            throws Exception {
        Object datanode = new Object();
        Object xceiverServer = new Object();
        long frame = Identity.enterFrame("<a.DataNode: void start()>",
                datanode);
        CountDownLatch registered = new CountDownLatch(1);
        List<String> named = Collections.synchronizedList(new ArrayList<>());
        Thread server = new Thread(() -> {
            Identity.enterFrame("<a.DataXceiverServer: void run()>",
                    xceiverServer);
            named.add(key(Attribution.resolve(null)));
            try {
                registered.await();
            } catch (InterruptedException interrupted) {
                return;
            }
            named.add(key(Attribution.resolve(null)));
        });
        Identity.startWork("<a.DataNode: void start()>#u7", server, null);
        server.start();
        Identity.exitFrame(frame);
        Thread.sleep(100L);
        RuntimeTraceContext.registerSource(datanode, DN);
        registered.countDown();
        server.join(5000L);
        assertEquals(java.util.Arrays.asList("", DN.key()), named);
    }

    /**
     * A thread a node's startup created under no request is that node by
     * rule 3 alone; the work it hands a shared consumer names that node too,
     * before the node registers (hdfs-adhoc-53: a DataNode actor's IPC
     * sends, claimed by Hadoop's one sender pool).
     */
    @Test
    public void aStartersInheritedNodeTravelsWithWhatItStarts()
            throws Exception {
        BlockingQueue<Object> queue = new ArrayBlockingQueue<>(1);
        AtomicReference<String> claimed = new AtomicReference<>("");
        Thread consumer = new Thread(() -> {
            try {
                Identity.claimItem(queue.take());
            } catch (InterruptedException interrupted) {
                return;
            }
            claimed.set(key(Attribution.resolve(null)));
        });
        consumer.start();
        long startup = RuntimeTraceContext.beginNodeStartup(DN);
        Thread actor = new Thread(() -> {
            // A tick whose owner the run has not registered yet.
            long tick = RuntimeTraceContext.beginTick(new Object(),
                    "BP_SERVICE_ACTOR");
            Object item = new Object();
            Identity.startWork("<a.Connection: void send()>#u1", item, null);
            queue.add(item);
            RuntimeTraceContext.endTick(tick);
        });
        RuntimeTraceContext.endNodeStartup(startup);
        actor.start();
        actor.join(5000L);
        consumer.join(5000L);
        assertEquals(DN.key(), claimed.get());
    }

    /**
     * What a node's startup starts or creates is the node's, though the
     * test's request stands where it runs: a thread started under a hop
     * (rule 4) and one created with no start (rule 3).  A construction names
     * its node before it is registered; a registered node's start that node,
     * a restart's its next epoch.  The thread running the startup is the
     * node's while it stands, the test's client once it ends; outside a
     * startup all are the client's.
     */
    @Test
    public void whatAStartupStartsOrCreatesIsTheNodes() throws Exception {
        Object[][] table = {
            {"CONSTRUCTION", DN}, {"START", DN}, {"RESTART", RESTARTED},
            {"NONE", CLIENT}};
        for (Object[] row : table) {
            for (boolean started : new boolean[] {true, false}) {
                reset();
                assertEquals(row[0] + " started=" + started,
                        ((SourceRef) row[1]).key(),
                        attributed((String) row[0], started));
            }
        }
    }

    /** The test's thread, in its request, starts or creates one of a
     *  node's threads in a startup or not; the node that thread's work is
     *  attributed to. */
    private static String attributed(String startup, boolean started)
            throws InterruptedException {
        Object client = new Object();
        Object slot = new Object();
        RuntimeTraceContext.registerSource(client, CLIENT);
        if (startup.equals("START") || startup.equals("RESTART")) {
            RuntimeTraceContext.registerSource(slot, DN);
        }
        if (startup.equals("RESTART")) {
            RuntimeTraceContext.restartSource(slot, RESTARTED);
        }
        long request = RuntimeTraceContext.beginRequest(client, "test");
        long token = startup.equals("CONSTRUCTION")
                ? RuntimeTraceContext.beginNodeStartup(DN)
                : startup.equals("NONE") ? 0L
                : RuntimeTraceContext.beginNodeStartup(
                        RuntimeTraceContext.sourceFor(slot));
        assertEquals("the thread running the startup is the node's",
                startup.equals("NONE") ? CLIENT.key()
                        : startup.equals("RESTART") ? RESTARTED.key()
                        : DN.key(), Attribution.resolve(null).key());
        AtomicReference<String> node = new AtomicReference<>("");
        Thread thread = new Thread(() -> node.set(key(
                Attribution.resolve(null))));
        if (started) {
            Identity.startWork("<a.Cluster: void startup()>#u3", thread, null);
        }
        thread.start();
        thread.join(5000L);
        RuntimeTraceContext.endNodeStartup(token);
        assertEquals("the startup over, the thread is the test's client",
                CLIENT.key(), Attribution.resolve(null).key());
        RuntimeTraceContext.endRequest(request);
        return node.get();
    }

    /**
     * A construction is the test's own work and a daemon's turn a root of
     * its own: each ends the exchange the thread served (HG4, hdfs-adhoc-22:
     * a node stood under the last response's anchor), and the turn outlives
     * the end the next message gives that exchange (HG5A, hdfs-adhoc-21).
     */
    @Test
    public void aStartupOrATurnEndsTheExchangeItsThreadServed() {
        for (boolean turn : new boolean[] {false, true}) {
            reset();
            Object owner = new Object();
            RuntimeTraceContext.registerSource(owner, CLIENT);
            Object dataNode = new Object();
            RuntimeTraceContext.registerSource(dataNode, DN);
            RecordingWindow.open();
            long request = RuntimeTraceContext.beginRequest(CLIENT, "test");
            String root = Identity.contextHere().render();
            String header = CausynthTraceRecorder.outboundExchange(
                    "HADOOP_IPC", "corr-1", "0", "RESPONSE", owner, null, "");
            MessageDoors.inbound(header, "", "HADOOP_IPC", "corr-1", "0",
                    "RESPONSE", owner, false);
            assertTrue(Identity.contextHere().render(),
                    Identity.contextHere().render().startsWith("Anchor:"));
            long opened = turn ? MessageDoors.beginTick(dataNode, "ACTOR")
                    : MessageDoors.beginNodeStartup("CLUSTER_NODE",
                            "DATANODE", "t/dn0");
            String expected = turn ? "Root:ACTOR#1" : root;
            assertEquals("turn=" + turn, expected,
                    Identity.contextHere().render());
            assertTrue("turn=" + turn + ": the served exchange ended",
                    MessageDoors.current() == null);
            MessageDoors.endInbound();
            assertEquals("turn=" + turn + " outlives the next message",
                    expected, Identity.contextHere().render());
            if (turn) {
                MessageDoors.endTick(opened);
            } else {
                MessageDoors.endNodeStartup(opened);
            }
            RuntimeTraceContext.endRequest(request);
        }
    }

    /**
     * A startup names the node's live epoch, one naming a dead epoch is
     * refused by name; it is construction work, so a timed wait inside it
     * is a pause that opens no turn (HG2: a NameNode format's wait made
     * every IPC handler its constructor started serve in that one turn).
     */
    @Test
    public void aStartupNamingADeadEpochIsRefused() {
        Object slot = new Object();
        RuntimeTraceContext.registerSource(slot, DN);
        RuntimeTraceContext.restartSource(slot, RESTARTED);
        try {
            RuntimeTraceContext.beginNodeStartup(DN);
            fail("a startup of the dead epoch opened");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains(RESTARTED.key()));
        }
        RecordingWindow.open();
        long token = RuntimeTraceContext.beginNodeStartup(
                RuntimeTraceContext.sourceFor(slot));
        assertEquals(RESTARTED.key(), Attribution.resolve(null).key());
        assertEquals("a pause in a construction", 0L,
                RuntimeTraceContext.beginWake(
                        "FSEditLogAsync$SyncEdit.logSyncWait"));
        RuntimeTraceContext.endNodeStartup(token);
    }

    /**
     * A thread starts in its creator's scope, a pool's worker does not (the
     * pool creates it while one caller submits, and it outlives that task);
     * a child inherits the engine's state from its creator in Thread.init,
     * on the creator, which keeps its own.
     */
    @Test
    public void aThreadInheritsItsCreatorsScopeAndAPoolsWorkerDoesNot()
            throws Exception {
        long token = Lineage.pushRoot("t/n0#epoch0", Role.of("OVERSEER_TASK"),
                "");
        try {
            AtomicBoolean thread = new AtomicBoolean();
            Thread plain = new Thread(() -> thread.set(Lineage.named()));
            plain.start();
            plain.join(5000L);
            assertTrue("a plain thread starts in its creator's scope",
                    thread.get());
            AtomicBoolean worker = new AtomicBoolean(true);
            ExecutorService pool = Executors.newSingleThreadExecutor();
            try {
                pool.submit(() -> worker.set(Lineage.named()))
                        .get(5, TimeUnit.SECONDS);
            } finally {
                pool.shutdownNow();
            }
            assertFalse("the worker the submit created starts in no scope",
                    worker.get());
        } finally {
            Lineage.pop(token);
        }

        List<String> ranOn = Collections.synchronizedList(new ArrayList<>());
        InheritedState<String> scope = new InheritedState<String>() {
            @Override
            protected String initialValue() {
                return "root";
            }

            @Override
            protected String inherit(String parent) {
                ranOn.add(Thread.currentThread().getName());
                return parent + "/child";
            }
        };
        scope.set("creator");
        String[] seen = new String[1];
        Thread child = new Thread(() -> seen[0] = scope.get(), "child");
        child.start();
        child.join();
        assertEquals("creator/child", seen[0]);
        assertEquals("inherit runs in Thread.init, on the creator",
                Collections.singletonList(Thread.currentThread().getName()),
                ranOn);
        assertEquals("creator", scope.get());
        assertFalse("a stock JDK has no propagation to pause",
                ConcolicVmBroker.pauseEngineWork());
    }

    /** A TURN begun before the recording window is the set-up's and stands
     *  at 0 inside it; a request opened before its window keeps its k. */
    @Test
    public void aTurnBegunBeforeTheWindowIsNotTheWindowsFirstTurn() {
        Role actor = Role.of("BP_SERVICE_ACTOR");
        long before = Lineage.pushRoot("hdfs/dn0", actor, "");
        assertEquals("the loop's first turn", 1, Lineage.rootWindowIndex());
        RecordingWindow.open();
        assertEquals("the set-up's turn", 0, Lineage.rootWindowIndex());
        Lineage.pop(before);
        long first = Lineage.pushRoot("hdfs/dn0", actor, "");
        assertEquals("the window's own first turn", 1,
                Lineage.rootWindowIndex());
        Lineage.pop(first);
        long request = Lineage.push("hdfs/balancer", Role.CLIENT,
                "balance-block");
        RecordingWindow.open();
        assertEquals("a request keeps its k", 1, Lineage.rootWindowIndex());
        Lineage.pop(request);
    }
}
