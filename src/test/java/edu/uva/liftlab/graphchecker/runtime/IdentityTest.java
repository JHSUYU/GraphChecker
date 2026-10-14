package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.ActivationRow.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import org.junit.Before;
import org.junit.Test;

/**
 * Where work stands ({@link Identity}): a claimed start, the frames a task
 * runs on, a hop's scope root, the window's counts, and the occurrence
 * unnamed work opens.
 */
public class IdentityTest {
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "SOLR_NODE", "t/node0", 0L);
    private static final SourceRef OTHER =
            new SourceRef("CLUSTER_NODE", "SOLR_NODE", "t/node1", 0L);
    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "t/nn0", 0L);
    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private static final String ADD =
            "<a.Sync: void processRequest(a.Request)>#u4";
    private static final String ACCEPT = "<a.Acceptor: void run()>#u5";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        Lineage.resetForTests();
        ScheduleLog.resetForTests();
        RecordingWindow.reset();
    }

    /** Runs {@code work} on a thread of its own and waits for it. */
    private static void on(Runnable work) throws InterruptedException {
        Thread thread = new Thread(work);
        thread.start();
        thread.join(5000L);
    }

    /** {@code work}'s answer on a new thread claiming {@code carrier}. */
    private static <T> T claimed(Object carrier, Function<Object, T> work)
            throws InterruptedException {
        List<T> result = new ArrayList<T>();
        on(() -> {
            Identity.claimStart(carrier);
            result.add(work.apply(carrier));
        });
        return result.get(0);
    }

    /** One task as the weave runs it: claim, its frame, and back. */
    private static String runTask(Object carrier, String entry) {
        long claim = Identity.claimStart(carrier);
        long frame = Identity.enterFrame(entry, null);
        String chain = Identity.handoffs();
        Identity.exitFrame(frame);
        Identity.endClaim(claim);
        return chain;
    }

    /** How many frames a chain of handoffs renders ({@code site@k}). */
    private static int hops(String chain) {
        return chain.split("@\\d+", -1).length - 1;
    }

    /**
     * A work entry's claim ends when the work returns: tasks run in sequence
     * on a pool never nest, a task its starter runs itself stands on the
     * starter's frames once, an event loop's callbacks on none of the last
     * task's; a claim an exception left ends with the work around it.
     */
    @Test
    public void aClaimEndsWithItsMethod() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        long request = RuntimeTraceContext.beginRequest(node, "update");
        Object[] wrappers = {new Object(), new Object()};
        Object[] callables = {new Object(), new Object()};
        for (int task = 0; task < 2; task++) {
            Identity.startWork("<a.Shards: void submit(a.Req)>#u7",
                    callables[task], null);
            Identity.startWork("<a.Pool: void execute(java.lang.Runnable)>"
                    + "#u58", wrappers[task], null);
        }
        RuntimeTraceContext.endRequest(request);
        String[] pooled = new String[2];
        on(() -> {
            for (int task = 0; task < 2; task++) {
                // A FutureTask inside an executor's wrapper.
                long claim = Identity.claimStart(wrappers[task]);
                long wrapper = Identity.enterFrame(
                        "<a.Pool: void lambda$execute$0()>#u3", null);
                pooled[task] = runTask(callables[task],
                        "<a.Shards: java.lang.Object call()>#u1");
                Identity.exitFrame(wrapper);
                Identity.endClaim(claim);
            }
        });
        assertEquals("the second task nests in no finished one: " + pooled[1],
                hops(pooled[0]), hops(pooled[1]));

        String send = "<a.Conn: void sendRequest(a.Call)>#u5";
        request = RuntimeTraceContext.beginRequest(node, "put");
        Object first = new Object();
        Identity.startWork(send, first, null);
        RuntimeTraceContext.endRequest(request);
        String[] looped = new String[4];
        on(() -> {
            looped[0] = runTask(first, "<a.Conn$1: void run()>");
            for (int at = 1; at < looped.length; at++) {
                // A response's callback, under its own hop and no claim,
                // sends the next call, which this loop runs at once.
                long response = RuntimeTraceContext.beginRequest(node,
                        "response");
                long callback = Identity.enterFrame(
                        "<a.Registry$1: void accept(java.lang.Object)>", null);
                Object next = new Object();
                Identity.startWork(send, next, null);
                looped[at] = runTask(next, "<a.Conn$1: void run()>");
                Identity.exitFrame(callback);
                RuntimeTraceContext.endRequest(response);
            }
        });
        for (String chain : looped) {
            assertEquals("its start frame alone, on no task before it: "
                    + chain, 1, hops(chain));
        }

        long outer = Identity.claimStart(new Object());
        long inner = Identity.claimStart(new Object());
        Identity.endClaim(outer);
        Identity.endClaim(inner);
        assertNull("no claim stands", Identity.claimedStart());
    }

    /** A queue item carries its putter's scope to whichever consumer takes
     *  it: one sender serves every node's calls. */
    @Test
    public void aSharedConsumerCarriesEachPuttersScope() throws Exception {
        Object putter = new Object();
        Object sender = new Object();
        RuntimeTraceContext.registerSource(putter, NODE);
        RuntimeTraceContext.registerSource(sender, OTHER);
        Object call = new Object();
        long request = RuntimeTraceContext.beginRequest(putter, "heartbeat");
        Identity.startWork("<a.Chunks: void putBack(a.Chunk)>#u13", call,
                null);
        RuntimeTraceContext.endRequest(request);
        Object[] seen = new Object[1];
        on(() -> {
            long work = Identity.enterFrame("<a.Sender: void run()>", sender);
            Identity.claimItem(call);
            seen[0] = RuntimeTraceContext.explicitSource();
            Identity.exitFrame(work);
        });
        assertEquals(NODE, seen[0]);
    }

    /**
     * A consumer claiming one queue item after another runs each under its
     * claimed start, not the thread (the program order {@code
     * ActivationRow#threadKey} states); work under no claim keeps none.
     */
    @Test
    public void twoItemsOnOneConsumerAreTwoProgramOrders() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        Object[] items = {new Object(), new Object()};
        for (Object item : items) {
            long request = RuntimeTraceContext.beginRequest(node, "getData");
            Identity.startWork(ADD, item, null);
            RuntimeTraceContext.endRequest(request);
        }
        String[] keys = new String[3];
        on(() -> {
            keys[2] = Identity.claimedStart();
            for (int item = 0; item < 2; item++) {
                Identity.claimItem(items[item]);
                keys[item] = Identity.claimedStart();
            }
        });
        assertNull("no claim, no start: the thread orders it", keys[2]);
        assertNotNull(keys[0]);
        assertNotEquals("each item is its own program order", keys[0],
                keys[1]);
    }

    /**
     * A claim states what its work is: a task an executor hands to a worker
     * of its own (a ThreadPoolExecutor on a SynchronousQueue: an Overseer's
     * pool), a task a worker takes off a queue (single-thread, full bounded,
     * no ThreadPoolExecutor at all), a task its starter runs itself, a queue
     * item, or no claim.  Only the first is held where it runs.
     */
    @Test
    public void aClaimStatesItsExecutorsHandOff() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        ThreadPoolExecutor handOff = new ThreadPoolExecutor(0, 4, 1L,
                TimeUnit.SECONDS, new SynchronousQueue<Runnable>());
        ThreadPoolExecutor single = new ThreadPoolExecutor(1, 1, 1L,
                TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
        // No worker started: the queue stays full.
        ThreadPoolExecutor full = new ThreadPoolExecutor(1, 1, 1L,
                TimeUnit.SECONDS, new ArrayBlockingQueue<Runnable>(1));
        full.getQueue().add(() -> { });
        ExecutorService wrapped = Executors.newSingleThreadExecutor();
        ScheduledThreadPoolExecutor scheduled =
                new ScheduledThreadPoolExecutor(1);
        Object[][] table = {
            // submitted to, claimed as, its claim's kind
            {handOff, "task", ClaimKind.HANDOFF_TASK},
            {handOff, "task run here", ClaimKind.QUEUED_TASK},
            {single, "task", ClaimKind.QUEUED_TASK},
            {full, "task", ClaimKind.QUEUED_TASK},
            {wrapped, "task", ClaimKind.QUEUED_TASK},
            {ForkJoinPool.commonPool(), "task", ClaimKind.QUEUED_TASK},
            {scheduled, "task", ClaimKind.QUEUED_TASK},
            {null, "task", ClaimKind.QUEUED_TASK},
            {new Object(), "item", ClaimKind.ITEM}};
        try {
            for (Object[] row : table) {
                Object work = new Object();
                ClaimKind[] kinds = new ClaimKind[2];
                String as = (String) row[1];
                Runnable claim = () -> {
                    kinds[0] = Identity.claimKind();
                    if ("item".equals(as)) {
                        Identity.claimItem(work);
                        kinds[1] = Identity.claimKind();
                    } else {
                        long claimed = Identity.claimStart(work);
                        kinds[1] = Identity.claimKind();
                        Identity.endClaim(claimed);
                    }
                };
                long request = RuntimeTraceContext.beginRequest(node,
                        "submit");
                Identity.startWork(ADD, work, row[0]);
                if ("task run here".equals(as)) claim.run();
                RuntimeTraceContext.endRequest(request);
                if (!"task run here".equals(as)) on(claim);
                assertEquals("no claim yet", ClaimKind.NONE, kinds[0]);
                assertEquals(row[0] + " " + as, row[2], kinds[1]);
            }
            assertEquals("no task took other work", Collections.emptySet(),
                    Identity.servingTasks());
        } finally {
            for (ExecutorService pool : Arrays.asList(handOff, single, full,
                    wrapped, scheduled)) {
                pool.shutdownNow();
            }
        }
    }

    /**
     * A hand-off task that takes queue items on its thread (a
     * ConcurrentUpdate client's Runner polling its queue, the take inside a
     * callee) serves a queue: its rows still state HANDOFF_TASK and the run
     * states it at its close (Identity#servingTasks); so does one whose
     * items no named start filed.  One that takes nothing serves none.
     */
    @Test
    public void aHandOffTaskThatTakesItemsServesAQueue() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        ThreadPoolExecutor handOff = new ThreadPoolExecutor(0, 4, 1L,
                TimeUnit.SECONDS, new SynchronousQueue<Runnable>());
        try {
            Set<String> serving = new TreeSet<String>();
            // its items offered by a named start, under no hop, never filed;
            // or no item at all
            for (String offered : new String[] {"named", "unnamed",
                    "unfiled", "none"}) {
                Object runner = new Object();
                Object[] updates = {new Object(), new Object()};
                long request = RuntimeTraceContext.beginRequest(node,
                        "update");
                Identity.startWork(ADD, runner, handOff);
                for (Object update : updates) {
                    if ("named".equals(offered)) {
                        Identity.startWork(ADD, update,
                                new LinkedBlockingQueue<>());
                    }
                }
                RuntimeTraceContext.endRequest(request);
                for (Object update : updates) {
                    if ("unnamed".equals(offered)) {
                        Identity.startWork(ADD, update,
                                new LinkedBlockingQueue<>());
                    }
                }
                String[] key = new String[2];
                ClaimKind[] kind = new ClaimKind[1];
                on(() -> {
                    long claimed = Identity.claimStart(runner);
                    key[0] = Identity.claimedStart();
                    for (Object update : "none".equals(offered)
                            ? new Object[0] : updates) {
                        long poll = Identity.enterFrame(
                                "<a.Queue: java.lang.Object poll()>#u1", null);
                        Identity.claimItem(update);
                        key[1] = Identity.claimedStart();
                        Identity.exitFrame(poll);
                    }
                    kind[0] = Identity.claimKind();
                    Identity.endClaim(claimed);
                });
                assertNotNull(offered, key[0]);
                assertEquals("only a named start opens the item's claim: "
                        + offered, "named".equals(offered),
                        key[1] != null && !key[1].equals(key[0]));
                assertEquals(offered + ": the row's kind is the entry's",
                        ClaimKind.HANDOFF_TASK, kind[0]);
                if (!"none".equals(offered)) serving.add(key[0]);
                assertEquals(offered, serving, Identity.servingTasks());
            }
        } finally {
            handOff.shutdownNow();
        }
    }

    /**
     * An occurrence's events count under the root hop it was opened under,
     * whatever root hop opens inside it: each turn's send in one occurrence
     * has an index of its own (HG5A, hdfs-adhoc-21: three heartbeats at one
     * producer endpoint).  Where no occurrence runs, each turn counts afresh.
     */
    @Test
    public void aTurnInsideAnOccurrenceRestartsNoCount() {
        String loop = "<a.Actor: void offerService()>#u3";
        String send = "<a.Actor: void sendHeartBeat()>#u5";
        String site = "HADOOP_IPC#REQUEST";
        Object[][] table = {
            {true, Arrays.asList(loop + "@0/" + send + "@0/" + site + "@0",
                    loop + "@0/" + send + "@1/" + site + "@0",
                    loop + "@0/" + send + "@2/" + site + "@0")},
            {false, Collections.nCopies(3, send + "@0/" + site + "@0")}};
        for (Object[] row : table) {
            reset();
            boolean running = (Boolean) row[0];
            Object actor = new Object();
            RuntimeTraceContext.registerSource(actor, DN);
            long request = RuntimeTraceContext.beginRequest(actor, "test");
            long run = Identity.enterFrame("<a.Actor: void run()>#u1", null);
            if (running) Identity.occurrence(DN.key(), "REGION.run", true);
            long loopFrame = Identity.enterFrame(loop, null);
            List<String> indexes = new ArrayList<String>();
            Set<String> producers = new LinkedHashSet<String>();
            for (int turn = 0; turn < 3; turn++) {
                long tick = RuntimeTraceContext.beginTick(actor, "ACTOR");
                long sendFrame = Identity.enterFrame(send, null);
                Endpoint sent = Identity.endpointAt(
                        Identity.currentOccurrence(DN.key()), site, 0);
                indexes.add(sent.siteIndex().render());
                producers.add(sent.id());
                Identity.exitFrame(sendFrame);
                RuntimeTraceContext.endTick(tick);
            }
            assertEquals("occurrence running=" + running, row[1], indexes);
            assertEquals("one producer per turn: " + producers, 3,
                    producers.size());
            Identity.exitFrame(loopFrame);
            if (running) Identity.regionExit(null);
            Identity.exitFrame(run);
            RuntimeTraceContext.endRequest(request);
        }
    }

    /**
     * A served message's endpoints are indexed from its own scope root:
     * which pool thread served it, and what it did before, are no part of
     * its identity; after it the thread's own root and frames stand again.
     */
    @Test
    public void theThreadsOwnFramesStandAgainAfterAServedMessage()
            throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NN);
        long restart = RuntimeTraceContext.beginRequest(node, "restart");
        Object message = RuntimeTraceContext.captureScope();
        RuntimeTraceContext.endRequest(restart);
        String[] rendered = new String[2];
        for (int handler = 0; handler < 2; handler++) {
            int which = handler;
            on(() -> {
                // The handler's own history: one frame deep, then two.
                long base = Identity.enterFrame(
                        "<a.Server: void start()>#u31", null);
                long more = which == 1 ? Identity.enterFrame(
                        "<a.Server$Handler: void run()>#u2", null) : 0L;
                long scope = RuntimeTraceContext.enterCarriedScope(message,
                        "IPC_HANDLER", null);
                rendered[which] = Identity.endpointAt(Identity.roleOccurrence(
                        NN.key(), Role.of("IPC_HANDLER")),
                        "HADOOP_IPC#RESPONSE", 0).siteIndex().render();
                RuntimeTraceContext.exitCarriedScope(scope);
                if (which == 1) Identity.exitFrame(more);
                Identity.exitFrame(base);
            });
        }
        assertEquals("indexed from its scope root, whichever thread served it",
                rendered[0], rendered[1]);
        assertFalse("the handler's own frames are below that root: "
                + rendered[0], rendered[0].contains("#u31"));

        long request = RuntimeTraceContext.beginRequest(node, "poll");
        Object carried = RuntimeTraceContext.captureScope();
        RuntimeTraceContext.endRequest(request);
        String[] later = new String[1];
        on(() -> {
            long base = Identity.enterFrame("<a.Poller: void run()>#u1", null);
            long served = RuntimeTraceContext.enterCarriedScope(carried,
                    "IPC_HANDLER", null);
            RuntimeTraceContext.exitCarriedScope(served);
            long call = Identity.enterFrame("<a.Client: Object call()>#u2",
                    null);
            later[0] = Identity.atScope().render();
            Identity.exitFrame(call);
            Identity.exitFrame(base);
        });
        assertEquals("<a.Poller: void run()>#u1@0/<a.Client: Object call()>"
                + "#u2@0", later[0]);
    }

    /**
     * Counts restarted at the window's opening start at 1 for a site the
     * level reached before it ({@code Identity.Counters#reopened}), so a
     * call the window opens in names its entries as one it opened before
     * does.  SL1, hdfs-adhoc-39: a blockReport handler queued two storage
     * reports through {@code runBlockOp}, the first before the window, and
     * both stood at {@code runBlockOp@0}.
     */
    @Test
    public void eachQueuedReportStandsApartWhereverTheWindowOpened()
            throws Exception {
        String handler = "<a.Rpc: java.lang.Object blockReport(a.Report[])>";
        String runOp = "<a.Blocks: java.lang.Object runBlockOp("
                + "java.util.concurrent.Callable)>";
        String enqueue = "<a.Queue: void enqueue(java.lang.Runnable)>#u3";
        // where the window opens: before the handler; inside it, before
        // the first report; during the first report; after it
        for (String window : new String[] {"BEFORE", "IN_HANDLER", "DURING",
                "AFTER"}) {
            reset();
            Object node = new Object();
            RuntimeTraceContext.registerSource(node, NN);
            if (window.equals("BEFORE")) RecordingWindow.open();
            long request = RuntimeTraceContext.beginRequest(node, "report");
            long call = Identity.enterFrame(handler, null);
            if (window.equals("IN_HANDLER")) RecordingWindow.open();
            Object[] items = {new Object(), new Object()};
            for (int report = 0; report < items.length; report++) {
                long op = Identity.enterFrame(runOp, null);
                Identity.startWork(enqueue, items[report], null);
                if (report == 0 && window.equals("DURING")) {
                    RecordingWindow.open();
                }
                Identity.exitFrame(op);
                if (report == 0 && window.equals("AFTER")) {
                    RecordingWindow.open();
                }
            }
            Identity.exitFrame(call);
            RuntimeTraceContext.endRequest(request);
            String[] ran = new String[items.length];
            on(() -> {
                for (int report = 0; report < items.length; report++) {
                    long claim = Identity.claimStart(items[report]);
                    ran[report] = Identity.atScope().render();
                    Identity.endClaim(claim);
                }
            });
            assertEquals(window + ": the first report at 0, the second at 1",
                    Arrays.asList(handler + "@0/" + runOp + "@0/" + enqueue
                            + "@0", handler + "@0/" + runOp + "@1/" + enqueue
                            + "@0"), Arrays.asList(ran));
        }
    }

    /**
     * The k of a start is an ordinal of the level that makes it within one
     * root hop; a thread under no root hop would count for its whole life,
     * so its starts file no frame, and a message its unnamed work sends
     * files no producer endpoint (HG2: every IPC handler's response shared
     * one anchor).  Under a hop whose context still renders Lost the start
     * files its frame, and the same send files one.
     */
    @Test
    public void aStartWithNoIdentityFilesNoFrame() throws Exception {
        assertTrue(Identity.contextHere().isLost());
        Object first = new Object();
        Object second = new Object();
        Identity.startWork(ACCEPT, first, null);
        Identity.startWork(ACCEPT, second, null);
        assertEquals("", claimed(first, carrier -> Identity.innermostFrame()));
        assertEquals("", claimed(second, carrier ->
                Identity.innermostFrame()));
        assertEquals(null, Identity.messageSent(DN.key(), "IPC", "c1",
                "RESPONSE", "IPC#RESPONSE", null));
        assertEquals("", Interactions.sender("IPC", "c1", "RESPONSE"));

        long hop = Lineage.push(DN.key(), Role.UNKNOWN, "accept");
        try {
            assertTrue(Identity.contextHere().isLost());
            Object filed = new Object();
            Identity.startWork(ACCEPT, filed, null);
            assertEquals(ACCEPT, claimed(filed,
                    carrier -> Identity.innermostFrame()));
            assertNotNull(Identity.messageSent(DN.key(), "IPC", "c2",
                    "RESPONSE", "IPC#RESPONSE", null));
        } finally {
            Lineage.pop(hop);
            Interactions.resetForTests();
        }
        // On a pool's thread an unnamed task ends at the next claim there
        // once its work is over, so the next task's entry opens one.
        Object unnamed = new Object();
        Identity.startWork(ACCEPT, unnamed, null);
        String[] tasks = claimed(unnamed, carrier -> {
            String task = opened("REGION.task");
            Identity.regionExit(null);
            Identity.claimStart(new Object());
            String next = opened("REGION.task");
            Identity.regionExit(null);
            return new String[] {task, next};
        });
        assertEquals("none", tasks[0]);
        assertEquals("Lost:UNKNOWN", tasks[1]);
    }

    /**
     * A daemon whose service loop's one entry no hop named: what it enters
     * opens no occurrence until a hop names its work; then the outermost
     * unnamed region opens one under the hop, for as long as the hop
     * stands, decisions counting from 1 and entries folding into it.  The
     * region's exit ends it too.  A start made under a scope names its work.
     */
    @Test
    public void unnamedWorkOpensNoOccurrenceUntilAHopNamesIt()
            throws Exception {
        Object daemon = new Object();
        Identity.startWork(ACCEPT, daemon, null);
        List<String> seen = claimed(daemon, carrier -> {
            List<String> said = new ArrayList<String>();
            said.add(opened("REGION.loop"));
            said.add(opened("REGION.step"));
            said.add("ordinal " + Identity.nextBranchOrdinal("loop#u3"));
            for (String turn : new String[] {"turn", "turn"}) {
                long hop = RuntimeTraceContext.beginRequest(DN, turn);
                said.add(Identity.currentOccurrence(DN.key()).render());
                said.add(opened("REGION.inner"));
                said.add("ordinals " + Identity.nextBranchOrdinal("loop#u3")
                        + "," + Identity.nextBranchOrdinal("loop#u3"));
                Identity.regionExit(null);
                RuntimeTraceContext.endRequest(hop);
                said.add(Identity.currentOccurrence(DN.key()).regionId());
            }
            Identity.regionExit(null);
            long hop = RuntimeTraceContext.beginRequest(DN, "last");
            Identity.regionExit(null);
            said.add(Identity.currentOccurrence(DN.key()).regionId());
            RuntimeTraceContext.endRequest(hop);
            return said;
        });
        String turn = DN.key() + "/region/REGION.loop/ctx:Root:CLIENT/turn#";
        assertEquals(Arrays.asList("none", "none", "ordinal 0",
                turn + "1/idx:", "none", "ordinals 1,2", "ROLE.UNKNOWN",
                turn + "2/idx:", "none", "ordinals 1,2", "ROLE.UNKNOWN",
                "ROLE.CLIENT"), seen);

        long request = RuntimeTraceContext.beginRequest(DN, "accept");
        Object named = new Object();
        Identity.startWork(ACCEPT, named, null);
        RuntimeTraceContext.endRequest(request);
        assertEquals("Root:CLIENT/accept#1", claimed(named, carrier -> {
            String first = opened("REGION.handshake");
            Identity.regionExit(null);
            return first;
        }));
    }

    /** What one region entry opened: its context, or "none". */
    private static String opened(String region) {
        OccurrenceAddress address = Identity.occurrence(DN.key(), region,
                true);
        return Identity.openedNone() ? "none" : address.context().render();
    }
}
