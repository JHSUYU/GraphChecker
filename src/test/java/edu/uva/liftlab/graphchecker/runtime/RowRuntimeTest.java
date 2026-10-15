package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.call;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Validity;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import org.apache.hadoop.ipc.CausynthMessagePropagation;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * The runtime half of the contract: the lineage an activation is addressed by,
 * and the rows one session publishes.
 */
public class RowRuntimeTest {
    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs-17899/nn0", 0);
    private static final String ATOMIC =
            "java.util.concurrent.atomic.AtomicInteger";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void clear() {
        // A test's exchange and levels are its own: left standing, the
        // thread's next test sent in them.
        MessageDoors.endInbound();
        Identity.resetForTests();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        Fixtures.set(ConcolicTaskPlan.class, "plan", null);
        Fixtures.set(MessageDoors.class, "chain", null);
    }

    private void openSession() throws Exception {
        Fixtures.openSession(iteration.getRoot().toPath());
    }

    private SessionDir session() {
        return Fixtures.session(iteration.getRoot().toPath());
    }

    private List<GapRow> gaps() throws Exception {
        return Fixtures.gaps(iteration.getRoot().toPath());
    }

    /** Starts {@code thread} and waits for it. */
    private static void run(Thread thread) {
        thread.start();
        try {
            thread.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
    }

    /** A thread a pool created before any scope existed. */
    private static Thread poolThreadCreatedOutsideAnyScope(Runnable work) {
        AtomicReference<Thread> created = new AtomicReference<>();
        run(new Thread(() -> created.set(new Thread(work))));
        return created.get();
    }

    private static OccurrenceAddress address(String nodeKey, String regionId,
                                             CausalContext context,
                                             ExecutionIndex index) {
        return OccurrenceAddress.of(NodeId.parse(nodeKey), regionId, context,
                index);
    }

    /** The occurrence every row of the codec cases stands in. */
    private static OccurrenceAddress targetDn() {
        return address("hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
    }

    /** A VM read-out is read for the members asked, the rest skipped: a
     *  page's header behind its records, a summary's three members. */
    @Test
    public void aReadOutIsReadForTheMembersAsked() {
        assertEquals(json("{'complete':false,'nextAfterEventId':7}"),
                ConcolicRegionRuntime.members("{\"locations\":[{\"a\":1}],"
                        + "\"complete\":false,\"nextAfterEventId\":7,"
                        + "\"vmExpressionTable\":{}}", "complete",
                        "nextAfterEventId"));
        assertEquals(new JsonObject(), ConcolicRegionRuntime.members(" ",
                "aborted"));
        assertNull(ConcolicRegionRuntime.members("[1]", "aborted"));
        assertNull(ConcolicRegionRuntime.members("{\"modelGaps\":",
                "aborted"));
    }

    /**
     * A scope reaches the work, not the thread: a thread started inside a
     * request and a task submitted to a pool created before it both carry
     * the lineage they were made in, asserted on the ADDRESS the scope
     * produces (IDENTITY §2): the root role and window index, the innermost
     * role beside them.
     */
    @Test
    public void aCarriedScopeReachesTheThreadThatRunsTheWork()
            throws Exception {
        RuntimeTraceContext.registerSource(new Object(), NN);
        long request = RuntimeTraceContext.beginRequest(NN, "balance-block");
        // The api the k was counted under is part of the context.
        assertEquals("Root:CLIENT/balance-block#1", rootContext());
        assertEquals(Role.CLIENT, Lineage.role());
        // The IPC Server.Call queue: captured at enqueue, restored at
        // dequeue on a handler that never saw the request.
        Object carried = RuntimeTraceContext.captureScope();
        AtomicReference<String> onHandler = new AtomicReference<>("");
        run(poolThreadCreatedOutsideAnyScope(() -> {
            long scope = RuntimeTraceContext.enterCarriedScope(carried,
                    "IPC_HANDLER", "balance-block");
            onHandler.set(rootContext() + "/" + Lineage.role());
            RuntimeTraceContext.exitCarriedScope(scope);
        }));
        assertEquals("Root:CLIENT/balance-block#1/IPC_HANDLER",
                onHandler.get());
        // An executor submission: captured by the START hook, taken back
        // where the work CLAIMS it.
        Object task = new Object();
        Identity.startWork("<a.Pool: void submit()>#u1", task, null);
        AtomicReference<String> onWorker = new AtomicReference<>("");
        run(poolThreadCreatedOutsideAnyScope(() -> {
            Identity.claimStart(task);
            onWorker.set(rootContext() + "/" + Lineage.role());
            RuntimeTraceContext.releaseCarried();
        }));
        assertEquals("Root:CLIENT/balance-block#1/EXECUTOR_TASK",
                onWorker.get());
        RuntimeTraceContext.endRequest(request);
        assertFalse("the request's scope ended with it", Lineage.named());
    }

    /**
     * An occurrence that drains a queue closes at the depth it opened: the
     * task it claimed ends with it (BlockManager's processQueue left its last
     * task's start level standing, FRAME_UNBALANCED) -- while an entry
     * folded into it, which shares its base, closes nothing.
     */
    @Test
    public void anOccurrenceClosesTheWorkItClaimed() throws Exception {
        RuntimeTraceContext.registerSource(new Object(), NN);
        long request = RuntimeTraceContext.beginRequest(NN, "block-report");
        Object task = new Object();
        Identity.startWork("<a.Queue: void enqueue(Runnable)>#u3", task, null);
        int[] depths = new int[3];
        run(poolThreadCreatedOutsideAnyScope(() -> {
            depths[0] = Identity.depth();
            Identity.occurrence(NN.key(), "REGION.queue", true);
            Identity.claimStart(task);
            int claimed = Identity.depth();
            Identity.occurrence(NN.key(), "REGION.accessor", true);
            Identity.regionExit(null);
            depths[1] = Identity.depth() - claimed;
            Identity.regionExit(null);
            depths[2] = Identity.depth();
        }));
        assertEquals("a folded entry's exit leaves the claimed work", 0,
                depths[1]);
        assertEquals(depths[0], depths[2]);
        RuntimeTraceContext.endRequest(request);
    }

    /**
     * A closed session is written no more (hdfs-17899-bug1 r1: attaches
     * refused in a VM session opened after the close), and a withdrawn one
     * stays withdrawn (hdfs-11741 v85: a killed replay's last table rewrite
     * brought back a directory holding only its expression table).
     */
    @Test
    public void aClosedSessionIsNotWrittenAgain() throws Exception {
        GapRow late = GapRow.of("s", GapKind.UNSTATED_VALUE,
                GapClass.BLOCKING, "late", "filed after the run ended");
        SessionDir ended = SessionDir.of(iteration.getRoot().toPath(),
                "ended");
        SessionPublisher closed = SessionPublisher.at(ended);
        closed.close();
        closed.gap(late);
        assertEquals(0L, Files.size(ended.gaps()));
        SessionDir layout = SessionDir.of(iteration.getRoot().toPath(),
                "withdrawn");
        SessionPublisher session = SessionPublisher.at(layout);
        Files.move(layout.dir(), iteration.getRoot().toPath().resolve("aside"));
        session.gap(late);
        assertFalse(Files.exists(layout.dir()));
    }

    /**
     * A capture keeps each node's view by identity across the captures of
     * one store: a subtree two predicates share is viewed once, and each
     * capture reads as a fresh one does.
     */
    @Test
    public void aSharedSubtreeIsViewedOnceAcrossCaptures() {
        JsonObject shared = json("{'_type':'X','a':1,'gone':null}");
        JsonObject first = new JsonObject();
        first.add("_left", shared);
        first.add("_right", json("{'k':2}"));
        JsonObject second = new JsonObject();
        second.add("_left", shared);
        Map<JsonElement, JsonElement> views =
                new java.util.IdentityHashMap<JsonElement, JsonElement>();
        JsonObject a = edu.uva.liftlab.graphchecker.plan.BranchWitness
                .immutablePredicate(first, views).toImmutableJsonView();
        JsonObject b = edu.uva.liftlab.graphchecker.plan.BranchWitness
                .immutablePredicate(second, views).toImmutableJsonView();
        assertSame(a.getAsJsonObject("sourceSatisfiedPredicate").get("_left"),
                b.getAsJsonObject("sourceSatisfiedPredicate").get("_left"));
        assertEquals(edu.uva.liftlab.graphchecker.plan.BranchWitness
                .immutablePredicate(second,
                        new java.util.IdentityHashMap<JsonElement,
                                JsonElement>()).toImmutableJsonView()
                .toString(), b.toString());
        assertFalse(b.toString().contains("gone"));
    }

    /**
     * A read-out page is decoded on its own thread, beside the publications:
     * a publication runs while a page decodes (on the one publication thread
     * it waited), and a read-out's publication reads it once every page it
     * handed on is decoded, refusals included.
     */
    @Test(timeout = 60000L)
    public void aReadOutDecodesBesideThePublications() throws Exception {
        java.util.concurrent.CountDownLatch decoding =
                new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch release =
                new java.util.concurrent.CountDownLatch(1);
        String[] ran = new String[1];
        assertTrue(ConcolicResultPublisher.decodeBeforePublication(1L, () -> {
            ran[0] = Thread.currentThread().getName();
            decoding.countDown();
            try {
                release.await();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
        }));
        decoding.await();
        java.util.concurrent.CountDownLatch published =
                new java.util.concurrent.CountDownLatch(1);
        ((java.util.concurrent.Executor) Fixtures.get(
                ConcolicResultPublisher.class,
                "RESULT_PUBLICATION_EXECUTOR")).execute(published::countDown);
        assertTrue(published.await(30L, TimeUnit.SECONDS));
        release.countDown();
        assertTrue(ran[0], ran[0].startsWith("causynth-read-out-decode-"));
        SharedStateCapture.SharedStateReadOut readOut =
                new SharedStateCapture.SharedStateReadOut();
        assertTrue((Boolean) call(readOut, "decodeLater", new Class<?>[] {
                String.class, ActiveRegion.class}, "{}", null));
        readOut.awaitDecoded();
        assertEquals(1, ((List<?>) Fixtures.get(readOut, "refusals")).size());
    }

    /**
     * A row is written whole, as its codec spells it, under the session's
     * lock -- spelled before it, since every thread stating a row takes it,
     * so it is held only while lines are written: a row stated while
     * another thread holds the lock lands once that thread lets go.
     */
    @Test(timeout = 60000L)
    public void aRowIsWrittenWholeUnderTheSessionLock() throws Exception {
        GapRow row = GapRow.of("s", GapKind.UNSTATED_VALUE,
                GapClass.DIAGNOSTIC, "held", "stated while the lock is held");
        SessionDir layout = SessionDir.of(iteration.getRoot().toPath(),
                "locked");
        SessionPublisher session = SessionPublisher.at(layout);
        Thread stating = new Thread(() -> session.gap(row));
        synchronized (Fixtures.get(SessionPublisher.class, "LOCK")) {
            stating.start();
            while (stating.getState() != Thread.State.BLOCKED) {
                Thread.yield();
            }
            assertEquals(0L, Files.size(layout.gaps()));
        }
        stating.join();
        assertEquals(RowCodec.toLine(RowCodec.writeGap(row))
                        + System.lineSeparator(),
                new String(Files.readAllBytes(layout.gaps()),
                        StandardCharsets.UTF_8));
    }

    /**
     * An occurrence opened Lost folds what is entered still Lost; a hop that
     * gives the thread a context names its region for the hop's life, and
     * what is entered under it folds into that occurrence (a DataXceiver
     * before and during its connection's message).  The hop's end leaves the
     * region Lost again.
     */
    @Test
    public void aHopNamesTheRegionALostOccurrenceStandsIn()
            throws Exception {
        RuntimeTraceContext.registerSource(new Object(), NN);
        long request = RuntimeTraceContext.beginRequest(NN, "write-block");
        Object carried = RuntimeTraceContext.captureScope();
        RuntimeTraceContext.endRequest(request);
        boolean[] folded = new boolean[2];
        String[] opened = new String[3];
        run(poolThreadCreatedOutsideAnyScope(() -> {
            opened[0] = Identity.occurrence(NN.key(), "REGION.run", true)
                    .render();
            Identity.occurrence(NN.key(), "REGION.handshake", true);
            folded[0] = Identity.openedNone();
            Identity.regionExit(null);
            long scope = RuntimeTraceContext.enterCarriedScope(carried,
                    "DATA_XCEIVER", "write-block");
            opened[1] = Identity.currentOccurrence(NN.key()).render();
            Identity.occurrence(NN.key(), "REGION.check", true);
            folded[1] = Identity.openedNone();
            Identity.regionExit(null);
            RuntimeTraceContext.exitCarriedScope(scope);
            opened[2] = Identity.currentOccurrence(NN.key()).render();
            Identity.regionExit(null);
        }));
        assertTrue(opened[0], opened[0].contains("/ctx:Lost"));
        assertTrue("entered still Lost, it folds", folded[0]);
        assertTrue(opened[1], opened[1].contains("REGION.run")
                && !opened[1].contains("/ctx:Lost"));
        assertTrue("entered under the hop, it folds into its name",
                folded[1]);
        assertEquals(opened[0], opened[2]);
    }

    /**
     * Unnamed work opens no occurrence (IDENTITY §1), and is never silent:
     * each region a node's unnamed work entered is one LINEAGE_LOST row, and
     * the manifest counts every entry.  So is a declared source read where
     * its occurrence ran concretely (the first reading at each occurrence,
     * nothing for a value the hook could not spell), the roots found
     * derived, the run-only spellings, and the hand-off tasks that took
     * queue items on their thread (none in a manifest from before that
     * field); a schema-1 manifest is refused.
     */
    @Test
    public void theRunsEndStatesUnnamedEntriesAndConcreteReadings()
            throws Exception {
        AtomicReference<String> runnerKey = new AtomicReference<>();
        openSession();
        RecordingWindow.open();
        try {
            Object connection = new Object();
            Identity.startWork("<a.Acceptor: void run()>#u5", connection,
                    null);
            List<OccurrenceAddress> opened = new ArrayList<>();
            run(new Thread(() -> {
                Identity.claimStart(connection);
                for (String region : new String[] {"REGION.handshake",
                        "REGION.handshake", "REGION.wrap"}) {
                    opened.add(Identity.occurrence(NN.key(), region, true));
                    Identity.regionExit(null);
                }
            }));
            assertEquals(Arrays.asList(null, null, null), opened);
            RowRuntime.concreteReading("ROOT.SERIAL", "occ#1", "119528");
            RowRuntime.concreteReading("ROOT.SERIAL", "occ#1", "119529");
            RowRuntime.concreteReading("ROOT.SERIAL", "occ#2", "119529");
            RowRuntime.concreteReading("ROOT.SERIAL", "occ#3", "");
            RowRuntime.derivedRoot("ROOT.EXPIRY");
            RunNames.spelled("auto0/node1", "10.0.0.1:8983_solr");
            // A Runner on a SynchronousQueue pool polling its update queue,
            // its run() entering no frame: the take replaces its claim.
            RuntimeTraceContext.registerSource(new Object(), NN);
            ThreadPoolExecutor scheduler = new ThreadPoolExecutor(0, 1, 1L,
                    TimeUnit.SECONDS, new SynchronousQueue<Runnable>());
            Object runner = new Object();
            Object update = new Object();
            long request = RuntimeTraceContext.beginRequest(NN, "update");
            Identity.startWork("<a.Client: void request()>#u3", runner,
                    scheduler);
            Identity.startWork("<a.Client: void request()>#u7", update,
                    new LinkedBlockingQueue<Object>());
            RuntimeTraceContext.endRequest(request);
            run(new Thread(() -> {
                long claimed = Identity.claimStart(runner);
                runnerKey.set(ActivationRow.CLAIMED + Identity.claimedStart());
                Identity.claimItem(update);
                Identity.endClaim(claimed);
            }));
            scheduler.shutdownNow();
            RowRuntime.closeSession();
        } finally {
            RecordingWindow.reset();
            RunNames.resetForTests();
        }
        List<String> named = new ArrayList<>();
        for (GapRow gap : gaps()) {
            if (gap.kind() == GapKind.LINEAGE_LOST) named.add(gap.subject());
        }
        String node = NN.key() + "/region/";
        assertEquals(Arrays.asList(node + "REGION.handshake",
                node + "REGION.wrap"), named);
        SessionManifest manifest = RowCodec.readManifest(session().manifest());
        JsonObject counted = new JsonObject();
        counted.addProperty(node + "REGION.handshake", 2);
        counted.addProperty(node + "REGION.wrap", 1);
        assertEquals(counted, manifest.toJson().getAsJsonObject(
                "unnamedEntries"));
        Map<String, String> read = new HashMap<>();
        read.put("occ#1", "119528");
        read.put("occ#2", "119529");
        assertEquals(Collections.singletonMap("ROOT.SERIAL", read),
                manifest.concreteReadings());
        assertEquals(Collections.singleton("ROOT.EXPIRY"),
                manifest.derivedRoots());
        Map<String, String> spelled = new HashMap<>();
        spelled.put("10.0.0.1:8983_solr", "auto0/node1");
        spelled.put("10.0.0.1:8983", "auto0/node1");
        assertEquals(spelled, manifest.runSpellings().asMap());
        assertEquals(Collections.singleton(runnerKey.get()),
                manifest.servingTasks());
        JsonObject before = manifest.toJson();
        before.remove("servingTasks");
        assertEquals(Collections.<String>emptySet(),
                SessionManifest.fromJson(before).servingTasks());
        JsonObject older = manifest.toJson();
        older.addProperty("schemaVersion", 1);
        try {
            SessionManifest.fromJson(older);
            fail("a schema-1 manifest is read");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("schema 1"));
        }
    }

    /**
     * A response's endpoint is its request's: the request's scope and the
     * response site -- not the region a pool handler opened before the
     * request came (the NameNode's {@code doAs}), nor what the handler sent
     * before.  Two requests served in one such region answer from two
     * endpoints; one request from one endpoint whatever its handler served
     * first.
     */
    @Test
    public void aResponseEndpointIsItsRequestsWhateverTheHandlerDidBefore()
            throws Exception {
        SourceRef client = new SourceRef("CLUSTER_NODE", "CLIENT",
                "hdfs-17899/client0", 0);
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, client);
        long calling = RuntimeTraceContext.beginRequest(client, "append");
        String first = CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                "corr-1", "0", "REQUEST", owner, null, "");
        String second = CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                "corr-2", "0", "REQUEST", owner, null, "");
        RuntimeTraceContext.endRequest(calling);
        List<String> both = answered(new String[][] {{"corr-1", first},
                {"corr-2", second}});
        assertFalse("two requests, two responses",
                both.get(0).equals(both.get(1)));
        assertEquals("the second request's response, served first",
                both.get(1), answered(new String[][] {{"corr-2", second}})
                        .get(0));
    }

    /** The response endpoints a pooled handler mints for these requests
     *  ({correlation, header}), in one region it opened before any came. */
    private static List<String> answered(String[][] requests) {
        List<String> ids = new ArrayList<>();
        run(poolThreadCreatedOutsideAnyScope(() -> {
            Identity.occurrence(NN.key(), "REGION.doAs", true);
            for (String[] request : requests) {
                long inbound = RuntimeTraceContext.enterInbound(request[1],
                        "HADOOP_IPC", request[0], "0", "REQUEST", null, "");
                ids.add(Identity.responseEndpoint(NN.key(), "HADOOP_IPC",
                        "RESPONSE").id());
                RuntimeTraceContext.exitInbound(inbound);
            }
            Identity.regionExit(null);
        }));
        return ids;
    }

    /**
     * A request whose door names the operation it asks for is that
     * operation's (IDENTITY §4): its site states the verb and its k counts
     * that operation's requests, so a block report is its turn's first
     * report whether or not the turn sent a heartbeat before it
     * (hdfs-adhoc-15).  A door naming none keeps {@code <transport>#<half>}.
     */
    @Test
    public void aRequestNamingItsOperationIsThatOperationsKth()
            throws Exception {
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "hdfs-adhoc-15/dn0", 0));
        String heartbeat = "DatanodeProtocol.sendHeartbeat";
        String report = "DatanodeProtocol.blockReceivedAndDeleted";
        String[][] turns = {{heartbeat, report}, {report}};
        List<Endpoint> reports = new ArrayList<>();
        for (int turn = 0; turn < turns.length; turn++) {
            long tick = RuntimeTraceContext.beginTick(owner,
                    "BP_SERVICE_ACTOR");
            for (String verb : turns[turn]) {
                String correlation = "corr-" + turn + "-" + verb;
                CausynthMessagePropagation.outboundRequest("HADOOP_IPC",
                        correlation, "0", owner, null, new RpcProtobufRequest(
                                "org.apache.hadoop.hdfs.server.protocol."
                                        + verb));
                Endpoint producer = Interactions.producer(Interactions.sender(
                        "HADOOP_IPC", correlation, "REQUEST"));
                assertEquals("HADOOP_IPC#REQUEST:" + verb, producer.site());
                if (verb.equals(report)) reports.add(producer);
            }
            RuntimeTraceContext.endTick(tick);
        }
        assertEquals("the report is its turn's first report either way",
                reports.get(1).siteIndex(), reports.get(0).siteIndex());
        assertEquals("HADOOP_IPC#REQUEST",
                Endpoint.messageSite("HADOOP_IPC", "REQUEST", ""));
    }

    /**
     * A request is its verb's k-th (IDENTITY §3): it opens a level of its
     * own at its message site when it starts at its RPC engine's invoke
     * point, counted per verb, so a request of another verb inserted before
     * it renames none (hdfs-adhoc-52 SL1-3); the client's call inside it,
     * and any frame after it, stay plain; a retry is its original's k at a
     * site naming its attempt, one whose original this level did not count
     * counted there.  Starting, it ends a RESPONSE its thread received, so
     * it stands in the thread's own context, as a client's call does; a
     * REQUEST the thread serves stands.
     */
    @Test
    public void aRequestIsItsVerbsKthInItsThreadsOwnContext()
            throws Exception {
        String call = "<org.apache.hadoop.ipc.Client: org.apache.hadoop.io."
                + "Writable call(org.apache.hadoop.ipc.Client$Call)>";
        String list = "ClientProtocol.getListing";
        String stat = "ClientProtocol.getFileInfo";
        String site = "HADOOP_IPC#REQUEST:";
        // Each run's requests (verb, attempt); the expected level of each,
        // "" for one inserted that the others need not match.
        Object[][][] runs = {
            {{list, 0, site + list + "@0"}, {stat, 0, site + stat + "@0"},
                {list, 0, site + list + "@1"}},
            {{list, 0, site + list + "@0"},
                {"ClientProtocol.renewLease", 0, ""},
                {stat, 0, site + stat + "@0"}, {list, 0, site + list + "@1"}},
            {{list, 0, site + list + "@0"},
                {list, 1, site + list + "#retry1@0"},
                {stat, 0, site + stat + "@0"}, {list, 0, site + list + "@1"}}};
        SourceRef client = new SourceRef("EXTERNAL_APP", "DFS_CLIENT",
                "t/client0", 0L);
        for (Object[][] requests : runs) {
            reset();
            Identity.resetForTests();
            Object owner = new Object();
            RuntimeTraceContext.registerSource(owner, client);
            RecordingWindow.open();
            long test = RuntimeTraceContext.beginRequest(client, "test");
            String own = Identity.contextHere().render();
            int ordinal = 0;
            for (Object[] request : requests) {
                String verb = (String) request[0];
                // The response to the request before it, received here.
                received(owner, "corr-" + ordinal++);
                long started = CausynthMessagePropagation.requestStarting(
                        new RpcProtobufRequest("org.apache.hadoop.hdfs."
                                + "protocol." + verb), (Integer) request[1]);
                assertEquals(verb + ": the request is the thread's own",
                        own, Identity.contextHere().render());
                List<Frame> frames = framesIn(call);
                CausynthMessagePropagation.requestEnded(started);
                assertEquals("the client's call in it is plain", call + "@0",
                        frames.get(frames.size() - 1).render());
                if (!((String) request[2]).isEmpty()) {
                    assertEquals(Arrays.toString(request), request[2],
                            frames.get(frames.size() - 2).render());
                }
            }
            List<Frame> later = framesIn(call);
            assertEquals("a frame after the requests is plain", call + "@0",
                    later.get(later.size() - 1).render());
            received(owner, "corr-last");
            MessageDoors.callStarting();
            assertEquals("a client's call is the thread's own", own,
                    Identity.contextHere().render());
            RuntimeTraceContext.endRequest(test);
            RecordingWindow.reset();
        }
        // A retry whose original another thread made: counted at its retry
        // site, two of them two levels.
        List<String> retries = new ArrayList<>();
        for (int retry = 0; retry < 2; retry++) {
            long started = CausynthMessagePropagation.requestStarting(
                    new RpcProtobufRequest("org.apache.hadoop.hdfs.protocol."
                            + list), 1);
            List<Frame> frames = Identity.atScope().frames();
            retries.add(frames.get(frames.size() - 1).render());
            CausynthMessagePropagation.requestEnded(started);
        }
        assertEquals(Arrays.asList(site + list + "#retry1@0",
                site + list + "#retry1@1"), retries);
        // A handler's nested call: the REQUEST it serves stands.
        reset();
        Identity.resetForTests();
        Object handler = new Object();
        RuntimeTraceContext.registerSource(handler, client);
        RecordingWindow.open();
        long test = RuntimeTraceContext.beginRequest(client, "test");
        String header = CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                "corr-served", "0", "REQUEST", handler, null, list);
        MessageDoors.inbound(header, "", "HADOOP_IPC", "corr-served", "0",
                "REQUEST", handler, false);
        String serving = Identity.contextHere().render();
        assertTrue(serving, serving.startsWith("Anchor:"));
        long nested = CausynthMessagePropagation.requestStarting(
                new RpcProtobufRequest("org.apache.hadoop.hdfs.protocol."
                        + stat), 0);
        assertEquals("a served request stands under its nested call",
                serving, Identity.contextHere().render());
        CausynthMessagePropagation.requestEnded(nested);
        RuntimeTraceContext.endRequest(test);
        RecordingWindow.reset();
    }

    /** A RESPONSE of {@code correlation} received on this thread. */
    private static void received(Object owner, String correlation) {
        String header = CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                correlation, "0", "RESPONSE", owner, null, "");
        MessageDoors.inbound(header, "", "HADOOP_IPC", correlation, "0",
                "RESPONSE", owner, false);
    }

    /** The frames this thread stands on inside {@code method}. */
    private static List<Frame> framesIn(String method) {
        long entered = Identity.enterFrame(method, null);
        List<Frame> frames = Identity.atScope().frames();
        Identity.exitFrame(entered);
        return frames;
    }

    /**
     * A received call handed to the handlers' queue is named by its request
     * (IDENTITY §3): the Reader's START is the call's, standing on none of
     * the Reader's own frames, so a call one run handed off and the other
     * did not renames none of the rest (hdfs-adhoc-21, TM13); a call whose
     * sender this run did not file is a plain start.
     */
    @Test
    public void aReceivedCallHandedOffIsNamedByItsRequest() throws Exception {
        String queue = "<org.apache.hadoop.ipc.Server: void internalQueueCall("
                + "org.apache.hadoop.ipc.Server$Call,boolean)>#u5";
        // Each run's calls, by the api of the client root that sent each.
        String[][] runs = {{"a", "b", "c"}, {"a", "extra", "b", "c"}};
        byte[] clientId = {7, 7};
        List<Map<String, String>> named = new ArrayList<>();
        for (String[] calls : runs) {
            reset();
            Identity.resetForTests();
            Interactions.resetForTests();
            ScheduleLog.resetForTests();
            List<JsonObject> rows = new ArrayList<>();
            ScheduleLog.install(rows::add);
            RecordingWindow.open();
            Object client = new Object();
            RuntimeTraceContext.registerSource(client, new SourceRef(
                    "EXTERNAL_APP", "DFS_CLIENT", "t/client0", 0L));
            Object server = new Object();
            RuntimeTraceContext.registerSource(server, NN);
            for (int call = 0; call < calls.length; call++) {
                long sending = RuntimeTraceContext.beginRequest(client,
                        calls[call]);
                CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                        CausynthMessagePropagation.rpcCorrelation(clientId,
                                call), "0", "REQUEST", client, null, "");
                RuntimeTraceContext.endRequest(sending);
            }
            // One Reader hands every call off, then one no client sent.
            long reader = RuntimeTraceContext.beginRequest(server, "reader");
            for (int call = 0; call <= calls.length; call++) {
                Object handoff = CausynthMessagePropagation.handingOff(
                        clientId, call);
                Identity.startWork(queue, new Object(), null);
                CausynthMessagePropagation.handedOff(handoff);
            }
            RuntimeTraceContext.endRequest(reader);
            Map<String, String> starts = new LinkedHashMap<>();
            for (JsonObject row : rows) {
                if (!row.has("kind")) continue;
                ScheduleEvent event = RowCodec.readScheduleEvent(row);
                if (event.kind() != ScheduleEvent.Kind.START) continue;
                starts.put(starts.size() < calls.length ? calls[starts.size()]
                        : "unsent", event.context() + " " + event.site() + "#"
                        + event.k());
            }
            named.add(starts);
            ScheduleLog.resetForTests();
            RecordingWindow.reset();
        }
        for (String api : runs[0]) {
            assertEquals(api + ": its hand-off's name is its request's",
                    named.get(0).get(api), named.get(1).get(api));
            assertTrue(named.get(0).get(api), named.get(0).get(api)
                    .contains(queue + ":HADOOP_IPC."));
        }
        assertEquals("three calls, three names", 3, new HashSet<>(
                Arrays.asList(named.get(0).get("a"), named.get(0).get("b"),
                        named.get(0).get("c"))).size());
        assertTrue("a call no client sent is a plain start: "
                + named.get(0).get("unsent"), named.get(0).get("unsent")
                .endsWith(" " + queue + "#0"));
    }

    /** Named as Hadoop's protobuf RPC request is, which names itself by
     *  its header's protocol and method. */
    static final class RpcProtobufRequest {
        private final String named;

        RpcProtobufRequest(String named) {
            this.named = named;
        }

        @Override
        public String toString() {
            return named;
        }
    }

    /**
     * A response is produced by its request's role scope, which no region
     * opened and so no activation states: its send states it, naming the
     * client's send its anchor answers, so a chain through the response
     * goes on to the client.
     */
    @Test
    public void aResponseStatesTheRoleScopeThatAnswersAndTheSendItAnswers()
            throws Exception {
        openSession();
        SourceRef client = new SourceRef("CLUSTER_NODE", "CLIENT",
                "hdfs-17899/client0", 0);
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, client);
        long calling = RuntimeTraceContext.beginRequest(client, "append");
        String header = CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                "corr-1", "0", "REQUEST", owner, null, "");
        RuntimeTraceContext.endRequest(calling);
        AtomicReference<Endpoint> response = new AtomicReference<>();
        run(poolThreadCreatedOutsideAnyScope(() -> {
            long inbound = RuntimeTraceContext.enterInbound(header,
                    "HADOOP_IPC", "corr-1", "0", "REQUEST", null, "");
            response.set(Identity.messageSent(NN.key(), "HADOOP_IPC",
                    "corr-1", "RESPONSE", "HADOOP_IPC#RESPONSE",
                    Identity.responseEndpoint(NN.key(), "HADOOP_IPC",
                            "RESPONSE")));
            RuntimeTraceContext.exitInbound(inbound);
        }));
        RowRuntime.closeSession();
        OccurrenceAddress scope = response.get().occurrence();
        ActivationRow stated = null;
        for (ActivationRow row : SessionReader.read(session()).activations()) {
            if (row.occurrence().equals(scope)) stated = row;
        }
        assertNotNull("the role scope that answered is stated", stated);
        assertFalse("and was no instrumented region", stated.instrumented());
        assertNotNull("with the client's send its anchor answers",
                stated.anchorProducer());
        assertEquals(((CausalContext.Anchor) scope.context())
                .producerEndpointId(), stated.anchorProducer().id());
        assertTrue("which the client occurrence ran", stated.anchorProducer()
                .occurrence().node().render().contains("client0"));
    }

    /** The causal context the calling thread's root hop states. */
    private static String rootContext() {
        return CausalContext.of(Lineage.rootRole(), Lineage.rootApi(),
                Lineage.rootWindowIndex()).render();
    }

    /**
     * A daemon tick is a root of its own: the NameNode's key rotation is
     * addressed by its role and the k-th tick of the window; an
     * unattributable scope degrades rather than disappearing; a node this
     * run cannot name addresses nothing.  And the execution index, which is
     * not an ordinal: an identity that moves when an unrelated call is
     * inserted elsewhere is not an identity.
     */
    @Test
    public void aDaemonTickIsAddressedByItsRoleAndItsWindowLocalK() {
        Object anchor = new Object();
        RuntimeTraceContext.registerSource(anchor, NN);
        List<OccurrenceAddress> addresses = new ArrayList<>();
        for (int tick = 0; tick < 2; tick++) {
            long token = CausynthTraceRecorder.beginDaemonTick(anchor,
                    "HEARTBEAT_TICK");
            addresses.add(address("hdfs-17899/nn0#epoch0", "REGION.aaa1cfd7",
                    CausalContext.of(Role.of("HEARTBEAT_TICK"), "",
                            Lineage.rootWindowIndex()),
                    ExecutionIndex.empty()));
            CausynthTraceRecorder.endDaemonTick(token);
        }
        assertEquals("Root:HEARTBEAT_TICK#1",
                addresses.get(0).context().render());
        assertEquals("Root:HEARTBEAT_TICK#2",
                addresses.get(1).context().render());
        assertFalse(addresses.get(0).id().equals(addresses.get(1).id()));
        OccurrenceAddress lost = Identity.roleOccurrence(
                "hdfs-17899/nn0#epoch0", Role.of("KEY_MANAGER_TICK"));
        assertTrue(lost.lineageLost());
        assertEquals("ROLE.KEY_MANAGER_TICK", lost.regionId());
        assertNull(Identity.occurrence("", "REGION.aaa1cfd7", false));
        executionIndexIsStableUnderUnrelatedCalls();
    }

    /**
     * Counts start again at the window: hdfs-11741's balancer opens its
     * request before the window and sends a varying number of set-up RPCs
     * under it; the first send inside the window is one endpoint whatever
     * the set-up sent.  A site reached before the window starts again at 1,
     * so a call the window opened in names its entries as one it opened
     * before (hdfs-adhoc-39), and an iteration counted before it stands at 0
     * (hdfs-17899-bug1's DataXceivers inherit {@code instantiateDataNode@k}).
     */
    @Test
    public void aCountTakenBeforeTheWindowDoesNotReachIntoIt() {
        OccurrenceAddress at = address("hdfs-11741/balancer#epoch0",
                "ROLE.CLIENT", CausalContext.of(Role.CLIENT, "", 1),
                ExecutionIndex.empty());
        List<Endpoint> firstInWindow = new ArrayList<>();
        for (int setUpSends : new int[] {1, 3}) {
            RuntimeTraceContext.resetForTests();
            Identity.resetForTests();
            Lineage.resetForTests();
            Object anchor = new Object();
            RuntimeTraceContext.registerSource(anchor, NN);
            long request = RuntimeTraceContext.beginRequest(anchor,
                    "balance-block");
            for (int send = 0; send < setUpSends; send++) {
                Identity.endpointAt(at, "HADOOP_IPC#REQUEST", 0);
            }
            RecordingWindow.open();
            firstInWindow.add(Identity.endpointAt(at, "HADOOP_IPC#REQUEST",
                    0));
            assertFalse("inside the window the count goes on", Identity
                    .endpointAt(at, "HADOOP_IPC#REQUEST", 0).id().equals(
                            firstInWindow.get(firstInWindow.size() - 1)
                                    .id()));
            RuntimeTraceContext.endRequest(request);
        }
        assertEquals(firstInWindow.get(0).id(), firstInWindow.get(1).id());
        assertTrue(firstInWindow.get(0).siteIndex().render(),
                firstInWindow.get(0).siteIndex().render()
                        .endsWith("HADOOP_IPC#REQUEST@1"));
        Identity.resetForTests();
        String start = "Cluster.startDataNodes()#u1";
        Identity.exitFrame(Identity.enterFrame(start, null));
        long second = Identity.enterFrame(start, null);
        assertEquals(start + "@1", Identity.siteIndex().render());
        RecordingWindow.open();
        assertEquals("set-up history is not part of the address",
                start + "@0", Identity.siteIndex().render());
        Identity.exitFrame(second);
        long third = Identity.enterFrame(start, null);
        assertEquals("the window's first entry is the one after those that "
                + "stand at 0", start + "@1", Identity.siteIndex().render());
        Identity.exitFrame(third);
        long fourth = Identity.enterFrame(start, null);
        assertEquals("inside the window the count goes on", start + "@2",
                Identity.siteIndex().render());
        Identity.exitFrame(fourth);
    }

    /**
     * The entry rule: a delivery with no selected region still mints, and
     * the row pairs it to the producer the run staged the value from.
     */
    @Test
    public void anUnselectedAttachMintsAndPairsToItsExportByHandle()
            throws Exception {
        openSession();
        OccurrenceAddress producer = address("hdfs-17899/nn0#epoch0",
                "REGION.2392e4b7", CausalContext.of(Role.of("HEARTBEAT_TICK"),
                        "", 3),
                ExecutionIndex.parse("PBHelper.convert()#u2@0"));
        Endpoint exported = RowRuntime.exported(producer, 61L,
                "XCH.resp.block-key-id", 4242L, 0, null, "J", "119981");
        assertNotNull(exported);
        OccurrenceAddress consumer = RowRuntime.occurrenceHere(
                "hdfs-17899/target-dn#epoch0", "XCH.resp.block-key-id");
        assertTrue(consumer.lineageLost());
        Endpoint attached = RowRuntime.attachedAt(
                RowRuntime.nextEndpoint(consumer, "XCH.resp.block-key-id", 0),
                62L, "XCH.resp.block-key-id", 4242L, "hadoop-ipc-7",
                MessageDoors.RESPONSE, "HOFF.5e10236f", "J", "119981", false,
                "");
        RowRuntime.closeSession();
        List<AttachRow> rows = SessionReader.read(session()).attaches();
        assertEquals(1, rows.size());
        AttachRow row = rows.get(0);
        assertEquals(attached, row.endpoint());
        assertEquals(exported, row.producer());
        assertFalse(row.interaction().producer().occurrence().lineageLost());
        assertTrue(row.endpoint().occurrence().lineageLost());
        assertEquals("the handle is the strongest evidence there is",
                "HANDLE", Interactions.pairing("XCH.resp.other", 4242L, "",
                        "").key());
    }

    /**
     * WIRE pairing is the run's own RECORDED evidence and nothing else: the
     * handle the VM handed out, or the message the attach received -- its
     * correlation and half -- with the port, for an element that message
     * carried, filed at its outbound door.  hdfs-adhoc-07 (HG5A): a
     * JournalNode's own export answered the request's attaches of a segment
     * the client forwarded without exporting it: 855 self-pairings.  Per
     * row: the port, the element's handle (-1 absent), the received
     * message's correlation and half, the producer that answers (- none) by
     * which key.  A queue item its consumer takes is the message it serves,
     * its element paired with the writer's export by the item and the port.
     */
    @Test
    public void aCorrelationPairingIsTheSendingSideOfTheMessageReceived()
            throws Exception {
        openSession();
        Endpoint client = RowRuntime.exported(address("q/client#epoch0",
                "REGION.c", CausalContext.of(Role.of("CLIENT"), "", 1),
                ExecutionIndex.parse("C.send()#u1@0")), 1L, "XCH.seg", 0L, 0,
                null, "J", "3");
        Endpoint server = RowRuntime.exported(address("q/jn0#epoch0",
                "REGION.s", CausalContext.of(Role.of("SERVER"), "", 1),
                ExecutionIndex.parse("S.getSegmentInfo()#u1@0")), 2L,
                "XCH.seg", 77L, 0, null, "J", "4");
        // The client's request c-1 carries its concrete export; the server,
        // serving c-1, stages its own for the response.
        assertTrue(SymbolicMessageEnvelope.stage("XCH.seg", 0L, client));
        CausynthTraceRecorder.outboundExchange("HADOOP_IPC", "c-1", "0",
                "REQUEST", null, null, "");
        SymbolicMessageEnvelope.takeOutbound();
        assertTrue(SymbolicMessageEnvelope.stage("XCH.seg", 77L, server));
        CausynthTraceRecorder.outboundExchange("HADOOP_IPC", "c-1", "0",
                "RESPONSE", null, null, "");
        SymbolicMessageEnvelope.takeOutbound();
        Map<String, Endpoint> producers = new LinkedHashMap<>();
        producers.put("client", client);
        producers.put("server", server);
        String[][] rows = {
            {"XCH.seg", "0", "c-1", "REQUEST", "client", "CORRELATION_PORT"},
            {"XCH.seg", "0", "c-1", "request", "client", "CORRELATION_PORT"},
            {"XCH.seg", "0", "c-1", "RESPONSE", "server", "CORRELATION_PORT"},
            {"XCH.seg", "-1", "c-1", "REQUEST", "-", ""},
            {"XCH.seg", "77", "c-1", "REQUEST", "server", "HANDLE"},
            {"XCH.seg", "77", "", "", "server", "HANDLE"},
            {"XCH.other", "0", "c-1", "REQUEST", "-", ""},
            {"XCH.seg", "0", "c-2", "REQUEST", "-", ""},
            {"XCH.seg", "0", "", "REQUEST", "-", ""}};
        for (String[] row : rows) {
            Interactions.Pairing pairing = Interactions.pairing(row[0],
                    Long.parseLong(row[1]), row[2], row[3]);
            assertEquals(String.join(" ", row), producers.get(row[4]),
                    pairing.producer());
            assertEquals(String.join(" ", row), row[5], pairing.key());
        }

        RecordingWindow.open();
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NN);
        long request = RuntimeTraceContext.beginRequest(owner, "offer");
        Endpoint writer = RowRuntime.exported(address("q/node0#epoch0",
                "REGION.w", CausalContext.of(Role.of("NODE"), "", 1),
                ExecutionIndex.parse("W.offer()#u1@0")), 3L, "XCH.item", 0L,
                0, null, "J", "3");
        assertTrue(SymbolicMessageEnvelope.stage("XCH.item", 0L, writer));
        MessageDoors.stored("STORE", "/q/qn-1@0", owner, null);
        RuntimeTraceContext.endRequest(request);
        MessageDoors.consumed("STORE", "/q/qn-1@0");
        MessageDoors.Inbound item = MessageDoors.current();
        Interactions.Pairing pairing = Interactions.pairing("XCH.item", 0L,
                item.correlationId, item.half);
        assertEquals("CORRELATION_PORT", pairing.key());
        assertEquals(writer, pairing.producer());
        RowRuntime.closeSession();
    }

    /** The VIEW (or STORE) write rows of this session, each as {@code
     *  render}. */
    private List<String> writes(LocationKind kind,
            java.util.function.Function<WriteRow, String> render)
            throws Exception {
        List<String> found = new ArrayList<String>();
        for (WriteRow write : SessionReader.read(session()).writes()) {
            if (write.location().kind() == kind) found.add(render.apply(write));
        }
        return found;
    }

    /**
     * A node's view takes one write per version it decodes: a second parse
     * of a version the node decoded before, or of one a read of the view
     * already observed, re-points nothing (Z2K: every view read of version 0
     * met a re-decode after it, TOPOLOGY_DIVERGENCE).  The version decoded
     * before any row was stated is the view's INITIAL (M4).  A decode on a
     * thread no registered node owns re-points no view and states nothing
     * (solr-sg3 SP2-10: it threw an NPE into the workload).
     */
    @Test
    public void aNodesViewTakesOneWritePerVersionItDecodes() throws Exception {
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NN);
        long request = RuntimeTraceContext.beginRequest(owner, "watch");
        MessageDoors.decoded("STORE", "/views/once.json@0", new Object());
        openSession();
        RecordingWindow.open();
        MessageDoors.decoded("STORE", "/views/once.json@0", new Object());
        MessageDoors.decoded("STORE", "/views/once.json@1", new Object());
        // A version a read of the view observed before any parse of it
        // stated a row is held already.
        OccurrenceAddress here = Identity.currentOccurrence(NN.key());
        RowRuntime.viewRead(here, new RowOrder.Position(0L, 0),
                "STORE#VIEWED:|views|once.json#VIEW",
                MessageDoors.viewOf(MessageDoors.storeLocation("STORE",
                        "/views/once.json"), here), 2L);
        MessageDoors.decoded("STORE", "/views/once.json@2", new Object());
        RuntimeTraceContext.endRequest(request);
        Identity.occurrence(OccurrenceBinding.UNREGISTERED_SOURCE_KEY,
                "REGION.before", true);
        MessageDoors.decoded("SOLR_ZK", "/views/nobody.json@0", new Object());
        Identity.regionExit(null);
        RowRuntime.closeSession();
        assertEquals(Arrays.asList("INITIAL 0", "1"), writes(LocationKind.VIEW,
                write -> (write.initial() ? "INITIAL " : "")
                        + write.version()));
        for (GapRow gap : SessionReader.read(session()).gaps()) {
            assertFalse("the unregistered decode names nothing: " + gap,
                    gap.subject().contains("nobody")
                            || gap.detail().contains("nobody"));
        }
    }

    /**
     * Every row the engine states of a store or a node's view stands after
     * every VM event so far (IDENTITY §7.2): a decode and a read of the view
     * at one VM event are ordered write first, by their ties (Z2L: 78
     * BLOCKING TOPOLOGY_DIVERGENCE rows; B3); a store's write stands after
     * its writer's last event, so a closure that cuts a writer before its
     * write keeps the writer's door fault; a path created again after its
     * delete is its next life, {@code <path>#<n>} (design Z §1).
     */
    @Test
    public void aDecodeAndAReadAtOneVmEventStandWriteFirst() throws Exception {
        openSession();
        RecordingWindow.open();
        Identity.clock(() -> 41L);
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NN);
        Identity.occurrence(NN.key(), "REGION.view", true);
        org.example.decoded.Decoded.Slice slice =
                new org.example.decoded.Decoded.Slice("shard1", "active");
        MessageDoors.decoded("SOLR_ZK", "/views/one-event.json@3", slice);
        MessageDoors.viewed("SOLR_ZK", "/views/one-event.json", slice);
        MessageDoors.stored("SOLR_ZK", "/collections/t/state.json@3", owner,
                null);
        for (String version : new String[] {"0", "1", "0", "1", "0"}) {
            MessageDoors.stored("SOLR_ZK", "/m5/life@" + version, owner, null);
        }
        Identity.regionExit(null);
        RowRuntime.closeSession();
        SessionReader rows = SessionReader.read(session());
        List<String> seqs = new ArrayList<>();
        WriteRow decode = null;
        for (WriteRow write : rows.writes()) {
            if (write.location().kind() == LocationKind.VIEW) {
                seqs.add("write " + write.seq() + "/" + write.tie());
                decode = write;
            }
        }
        ReadRow viewRead = null;
        for (ReadRow read : rows.reads()) {
            LocationKind kind = read.location().kind();
            if (kind == LocationKind.VIEW || kind == LocationKind.STORE) {
                seqs.add(kind + " read " + read.seq() + "/" + read.tie());
                if (kind == LocationKind.VIEW) viewRead = read;
            }
        }
        assertEquals(Arrays.asList("write 42/1", "STORE read 42/2",
                "VIEW read 42/3"), seqs);
        assertTrue(RowOrder.before(decode, viewRead));
        assertFalse(RowOrder.before(viewRead, decode));
        assertEquals("one past the writer's last event, 41", Arrays.asList(
                "42 /collections/t/state.json@3", "42 /m5/life@0",
                "42 /m5/life@1", "42 /m5/life#2@0", "42 /m5/life#2@1",
                "42 /m5/life#3@0"), writes(LocationKind.STORE, write ->
                write.seq() + " " + write.location().slot() + "@"
                        + write.version()));
    }

    /**
     * A replay states a read at the store's call -- the version it
     * returned, under the store's READ site -- only where the composition
     * reads it: in a planned occurrence that runs tracked, of a path on the
     * ZooKeeper chain or by an occurrence on it (the chain's growth).  A
     * role's poll, a doors-only occurrence, a path neither touches, a
     * getChildren's children version and a read of no node state nothing,
     * and no activation.
     */
    @Test
    public void aStoreCallsReadIsARowOnlyOnTheChainOfAPlannedOccurrence()
            throws Exception {
        openSession();
        RecordingWindow.open();
        Identity.clock(() -> 41L);
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NN);
        String planned = NN.key() + "/region/REGION.reads/ctx:Root:CLIENT#1"
                + "/idx:";
        String chained = NN.key() + "/region/REGION.chained/ctx:Root:CLIENT#1"
                + "/idx:";
        JsonObject path = json("{'kind':'ZK_CHAIN_PATH','transport':"
                + "'SOLR_ZK','location':'/live/one','slot':'/live/one'}");
        JsonObject occurrence = json("{'kind':'ZK_CHAIN_OCCURRENCE',"
                + "'occurrenceId':'" + OccurrenceAddress.parse(chained)
                .render() + "'}");
        Fixtures.set(MessageDoors.class, "chain",
                ZkChain.of(Arrays.asList(path, occurrence)));
        // the running occurrence (none: a role), doors-only, the read
        Object[][] table = {
                {null, false, "/live/one@2", "getData"},
                {planned, false, "/live/one@3", "exists"},
                {planned, true, "/live/one@4", "getData"},
                {planned, false, "/live/two@5", "getData"},
                {chained, false, "/live/three@6", "exists"},
                {planned, false, "/live/one@-1", "exists"},
                {planned, false, "/live@7", "getChildren"}};
        long token = 960000L;
        for (Object[] row : table) {
            if (row[0] != null) {
                ActiveRegion active = Fixtures.region(++token,
                        Fixtures.taskRow(NN.key(), (String) row[0],
                                "<a.Reader: void read()>", true,
                                "'doorsOnly':" + row[1]));
                active.d3Address = OccurrenceAddress.parse((String) row[0]);
                Fixtures.pushed(active);
            }
            MessageDoors.storeRead("SOLR_ZK", (String) row[2],
                    (String) row[3], owner);
            Fixtures.release();
        }
        RowRuntime.closeSession();
        List<String> reads = new ArrayList<String>();
        for (ReadRow read : SessionReader.read(session()).reads()) {
            reads.add(read.endpoint().occurrence().regionId() + " "
                    + read.endpoint().site() + "@" + read.observedVersion());
        }
        assertEquals(Arrays.asList("REGION.reads SOLR_ZK#READ:.live.one@3",
                "REGION.chained SOLR_ZK#READ:.live.three@6"), reads);
        assertTrue(SessionReader.read(session()).activations().isEmpty());
    }

    /**
     * A store document crosses symbolically only at or under the content
     * keys of the occurrence that writes or parses it (a plan row's
     * {@code contentKeys}): there a leaf is exported or minted -- no VM runs
     * here, so each one tried is named unread or unminted -- and every
     * other leaf a writer exports as its value, a constant, and a reader
     * takes as parsed, no attach.  No keys: no leaf, no export.
     */
    @Test
    public void aDocumentCrossesSymbolicallyOnlyUnderItsContentKeys()
            throws Exception {
        openSession();
        RecordingWindow.open();
        Identity.clock(() -> 41L);
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, NN);
        Identity.occurrence(NN.key(), "REGION.keys", true);
        // the location, its content keys
        Object[][] table = {
                {"/collections/a/state.json", Collections.emptyList()},
                {"/collections/b/state.json",
                        Collections.singletonList("|c|shards|s1|state")}};
        for (Object[] row : table) {
            Map<String, Object> shard = new LinkedHashMap<String, Object>();
            shard.put("state", "active");
            shard.put("leader", "n1");
            Map<String, Object> collection =
                    new LinkedHashMap<String, Object>();
            collection.put("shards", Collections.singletonMap("s1", shard));
            collection.put("router", "compositeId");
            Map<String, Object> tree = Collections.<String, Object>
                    singletonMap("c", collection);
            @SuppressWarnings("unchecked")
            List<String> keys = (List<String>) row[1];
            String key = row[0] + "@3";
            StoreContent.export("SOLR_ZK", key, tree, keys);
            StoreContent.attach("SOLR_ZK", key, null, tree, keys);
        }
        Identity.regionExit(null);
        RowRuntime.closeSession();
        Map<String, List<String>> tried = new TreeMap<String, List<String>>();
        for (GapRow gap : gaps()) {
            String how = gap.detail().startsWith("the leaf's expression")
                    ? "export" : gap.detail().startsWith("the parsed leaf")
                    ? "mint" : null;
            if (how == null) continue;
            tried.computeIfAbsent(how, any -> new ArrayList<String>())
                    .add(gap.subject().substring(gap.subject()
                            .indexOf("#CONTENT:") + 9));
        }
        for (List<String> each : tried.values()) Collections.sort(each);
        List<String> keyed = Collections.singletonList(
                "|collections|b|state.json#|c|shards|s1|state");
        assertEquals("export", keyed, tried.get("export"));
        assertEquals("mint", keyed, tried.get("mint"));
        List<String> constants = new ArrayList<String>();
        for (ExportRow export : SessionReader.read(session()).exports()) {
            constants.add(export.endpoint().site().substring(export
                    .endpoint().site().indexOf("#CONTENT:") + 9) + "="
                    + export.recordedValue() + " " + export.javaType());
        }
        Collections.sort(constants);
        assertEquals(Arrays.asList(
                "|collections|b|state.json#|c|router=compositeId"
                        + " java/lang/String",
                "|collections|b|state.json#|c|shards|s1|leader=n1"
                        + " java/lang/String"), constants);
    }

    /**
     * Never silent: an export or attach the VM refused, and a receipt whose
     * sender this run does not hold, each name the occurrence they ran in.
     * An attach no activation ran is the closure's to admit: an
     * ADMISSION_GAP beside the unselected activation it names (SOLR-18413
     * s45: a watcher callback's refused attach left no row and no gap).
     */
    @Test
    public void aRefusedWireStepNamesTheOccurrenceItRanIn() throws Exception {
        JsonObject row;
        try (Reader plan = new InputStreamReader(getClass().getClassLoader()
                .getResourceAsStream(
                        "plans/hdfs-17899-bug3-loop-body-producer.json"),
                StandardCharsets.UTF_8)) {
            row = JsonParser.parseReader(plan).getAsJsonObject();
        }
        // The row's two OUT ports, the first declared IN instead.
        JsonArray ports = row.getAsJsonArray("communicationHandoffs");
        String out = ports.get(1).getAsJsonObject().get("portId")
                .getAsString();
        String in = ports.get(0).getAsJsonObject().get("portId")
                .getAsString();
        ports.get(0).getAsJsonObject().addProperty("side", "IN");
        Fixtures.set(ConcolicTaskPlan.class, "plan", new ConcolicTaskPlan(
                null, Collections.singletonList(Fixtures.runtimeTask(row))));
        openSession();
        long request = RuntimeTraceContext.beginRequest(NN, "refused-wire");
        OccurrenceAddress here;
        try {
            // No concolic VM runs these tests: the broker refuses both steps.
            WireExport.exportLeaf(out,
                    new ConcolicRegionRuntime.HandoffLeafCarrier(), "j", "J",
                    null);
            assertTrue(SymbolicMessageEnvelope.stage(in, 41L, null));
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());
            WireExport.attachLeaf(in,
                    new ConcolicRegionRuntime.HandoffLeafCarrier(), "i", "I",
                    null);
            here = RowRuntime.occurrenceHere(NN.key(), in);
            RuntimeTraceContext.exitInbound(RuntimeTraceContext.enterInbound(
                    RuntimeTraceContext.outboundHeader(null, null),
                    "HADOOP_IPC", "never-sent", "0", "REQUEST", null, ""));
        } finally {
            RuntimeTraceContext.endRequest(request);
            SymbolicMessageEnvelope.clear();
        }
        RowRuntime.closeSession();
        Map<GapKind, GapRow> named = new EnumMap<>(GapKind.class);
        for (GapRow gap : gaps()) named.put(gap.kind(), gap);
        GapRow attach = named.get(GapKind.ADMISSION_GAP);
        assertEquals(here.render(), attach.subject());
        assertEquals(GapClass.DIAGNOSTIC, attach.cls());
        assertTrue(attach.detail(), attach.detail().contains(
                "attach of handle 41 at " + in + " (INVOCATION_FAILED)"));
        GapRow export = named.get(GapKind.UNSTATED_VALUE);
        assertEquals(here.render(), export.subject());
        assertTrue(export.detail(), export.detail().contains(
                "export at " + out + " (INVOCATION_FAILED)"));
        GapRow receipt = named.get(GapKind.LINEAGE_LOST);
        assertTrue(receipt.detail(), receipt.detail().contains(
                "HADOOP_IPC REQUEST received at HADOOP_IPC/refused-wire"
                        + " names no sender this run holds"));
        List<ActivationRow> activations =
                SessionReader.read(session()).activations();
        assertEquals("the activation to admit is stated, unselected",
                here, activations.get(0).occurrence());
        assertFalse(activations.get(0).instrumented());
    }

    /**
     * AN EXPORT NO TASK PLANS NAMES THE REGION IT RAN IN: every export is
     * woven (RuntimeRegionPlanner#exportSites), so one that runs under no
     * admitted activation states its endpoint at the occurrence its
     * skeleton's entry opened -- a region the closure can grow -- never a
     * ROLE, and no plan declares its port (hdfs-adhoc-12 HG9L: the
     * NameNode's HA status txid).
     */
    @Test
    public void anUnplannedExportNamesTheRegionItRanIn() throws Exception {
        Fixtures.set(ConcolicTaskPlan.class, "plan", new ConcolicTaskPlan(
                null, Collections.<ConcolicTaskPlan.RuntimeTask>emptyList()));
        openSession();
        Identity.resetForTests();
        Lineage.resetForTests();
        Object nameNode = new Object();
        RuntimeTraceContext.registerSource(nameNode, NN);
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        String convert = "<o.a.h.PBHelper: o.a.h.NNHAStatusHeartbeatProto"
                + " convert(o.a.h.NNHAStatusHeartbeat)>";
        long frame = Identity.enterFrame(convert + "#u0", null);
        long entry = ConcolicRegionRuntime.enterRegionEntry(
                "REGION.b9bd09cd", convert, nameNode);
        OccurrenceAddress here;
        try {
            here = Identity.currentOccurrence(NN.key());
            WireExport.exportLeaf("XCH.53d59f95-3ee5-385f-a674-a07d58f5b75b"
                    + ".wire.auto:NNHAStatusHeartbeatProto.Txid",
                    new ConcolicRegionRuntime.HandoffLeafCarrier(), "j", "J",
                    null);
        } finally {
            ConcolicRegionRuntime.exitRegionEntry(entry);
            Identity.exitFrame(frame);
        }
        RowRuntime.closeSession();
        assertEquals("REGION.b9bd09cd", here.regionId());
        assertFalse("a region, which the closure can grow", here.role());
        GapRow refused = null;
        for (GapRow gap : gaps()) {
            assertTrue("no plan declares an export: " + gap.detail(),
                    gap.kind() != GapKind.DECLARATION_MISSING);
            if (gap.kind() == GapKind.UNSTATED_VALUE) refused = gap;
        }
        assertNotNull("the refused export is named", refused);
        assertEquals("at the occurrence it ran in", here.render(),
                refused.subject());
        List<ActivationRow> activations =
                SessionReader.read(session()).activations();
        assertEquals("that occurrence is stated, unselected", here,
                activations.get(0).occurrence());
        assertFalse(activations.get(0).instrumented());
    }

    /**
     * Every row kind round-trips through the codec it is written with, and
     * what each row states: a decision states the jump's predicate and the
     * arm (17960's marker: {@code marker == false}, outcome false), one with
     * no VM event id seq 0 and no term (a high-water mark once decided
     * whether it sat inside a prefix); a class the JVM mints per run
     * (reflection accessors, lambda proxies) is no identity (11741 campaign
     * #3: 8 of 11 owed worlds differed by GeneratedMethodAccessor23 against
     * 22 alone); a write's site and java type (an RMW's operands', a
     * String method's String, a null's reference); the tool's own wait set
     * and a generated builder state no row; a declared region input is a
     * READ of the location the write log spells, joining the last real write
     * before the mint, once per mint store; a gap whose caller named nothing
     * is a row, never a throw into the workload; an over-pop of the region
     * stack is BLOCKING; the read-out keeps the site and activation of every
     * event.
     */
    @Test
    public void theSessionRoundTripsEveryRowKind() throws Exception {
        openSession();
        OccurrenceAddress occurrence = targetDn();
        Endpoint endpoint = RowRuntime.nextEndpoint(occurrence, "XCH.port", 0);
        JsonObject expression = json("{'_type':'SymbolExpression','_exp':"
                + "'M_J_serial'}");
        RowRuntime.decision(occurrence, 12L, "Klass.m()#u8", 1, true,
                expression);
        RowRuntime.decision(occurrence, 13L, "SnapshotManager.delete()#u7", 1,
                false, compared("M_Z_marker", "Z", "==", "Y_Z_0"));
        RowRuntime.decision(occurrence, 0L, "Klass.beforeRecording()#u2", 1,
                true, null);
        RowRuntime.exported(occurrence, 4L, "XCH.port", 7L, 0, expression,
                "J", "1");
        RowRuntime.attachedAt(endpoint, 9L, "XCH.port", 7L, "c1",
                MessageDoors.REQUEST, "v_H", "J", "1", true, "2");
        String invoke = "(Ljava/lang/Object;[Ljava/lang/Object;)"
                + "Ljava/lang/Object;";
        String inflatedOnce = LoggedEventSites.site(loggedAt(
                "sun/reflect/GeneratedMethodAccessor23", "invoke", invoke, 56),
                "L", -1L, true);
        assertEquals("the accessor's inflation number is not where the write"
                + " happened", inflatedOnce, LoggedEventSites.site(loggedAt(
                "sun/reflect/GeneratedMethodAccessor7", "invoke", invoke, 56),
                "L", -1L, true));
        assertTrue(inflatedOnce, inflatedOnce.startsWith(
                "sun.reflect.GeneratedMethodAccessor#invoke"));
        String apply = "(Ljava/lang/Object;)Ljava/lang/Object;";
        String proxied = LoggedEventSites.site(loggedAt(
                "example/Keys$$Lambda$14/1234567890", "apply", apply, 3), "L",
                -1L, false);
        assertEquals("nor is a lambda proxy's", proxied, LoggedEventSites.site(
                loggedAt("example/Keys$$Lambda$3/987654321", "apply", apply,
                        3), "L", -1L, false));
        assertTrue(proxied, proxied.startsWith("example.Keys$$Lambda#apply"));
        assertTrue("a name the PROGRAM chose is untouched", LoggedEventSites
                .site(loggedAt("org/apache/hadoop/hdfs/security/token/block/"
                        + "BlockTokenSecretManager", "addKeys", "()V", 21),
                        "L", -1L, true).startsWith("org.apache.hadoop.hdfs"
                        + ".security.token.block.BlockTokenSecretManager"
                        + "#addKeys"));
        // The endpoint mint puts the site and the innermost frame of its
        // index in that ONE spelling.
        assertEquals("sun.reflect.GeneratedMethodAccessor#invoke()V#56:WRITE",
                RowRuntime.nextEndpoint(occurrence, Endpoint.stateSite(
                        "sun.reflect.GeneratedMethodAccessor23", "invoke",
                        "()V", 56, true), 0).site());
        LocationId location = LocationId.of(LocationKind.INSTANCE, "22", "24");
        String body = "Caller.body()#u9@1";
        RowRuntime.write(occurrence, 10L, Endpoint.stateSite(ATOMIC,
                "getAndIncrement", "()I", 12, true), location, 125L,
                rmwExpression(), "", body, null, null, false);
        // A String method's result is a String (f4 visible-gs).
        JsonObject concat = json("{'_type':'OpStrExpression','_name':"
                + "'concat'}");
        JsonArray operands = new JsonArray();
        operands.add(rmwExpression());
        concat.add("_param_list", operands);
        RowRuntime.write(occurrence, 13L, Endpoint.stateSite("java.io.File",
                "<init>", "(Ljava/lang/String;)V", 4, true),
                LocationId.of(LocationKind.INSTANCE, "49", "32"), 127L, concat,
                "", body, null, null, false);
        // A null stored into a tracked reference field (17960 v64).
        RowRuntime.write(occurrence, 12L, Endpoint.stateSite("Diff",
                "setPosterior", "(LDiff;)V", 2, true),
                LocationId.of(LocationKind.INSTANCE, "6", "40"), 126L,
                json("{'_type':'SymbolExpression','_java_type':'','_exp':"
                        + "'N'}"), "", body, null, null, false);
        RowRuntime.read(occurrence, 14L, Endpoint.stateSite(ATOMIC, "get",
                "()I", 2, false), location, 125L, "s", "J", "9", "",
                ReadRow.UNKNOWN_VERSION);
        String waits = Endpoint.stateSite(TimedWaits.class.getName(), "send",
                "(Ljava/lang/Object;Z)Z", 34, true);
        LocationId waitSet = LocationId.of(LocationKind.INSTANCE, "350", "24");
        RowRuntime.write(occurrence, 16L, waits, waitSet, 6254L,
                rmwExpression(), "", body, null, null, false);
        RowRuntime.read(occurrence, 16L, waits, waitSet, 6253L, "w", "I", "1",
                "", ReadRow.UNKNOWN_VERSION);
        RowRuntime.write(occurrence, 17L, Endpoint.stateSite(
                com.google.protobuf.Field.Builder.class.getName(), "setNumber",
                "(I)Lcom/google/protobuf/Field$Builder;", 2, true),
                LocationId.of(LocationKind.INSTANCE, "351", "16"), 6255L,
                rmwExpression(), "", body, null, null, false);
        RowRuntime.rootMint(occurrence, 11L, "HDFS.BLOCK_KEY.SERIAL_NO",
                "M_I_1", RootKind.INTEGRAL, RootCategory.HOOK, "3", "3", "6",
                Validity.ANY, true, null, 0L);
        RowRuntime.rootMint(occurrence, 13L,
                "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED", "M_Z_marker",
                RootKind.MARKER, RootCategory.HOOK, "true", "", "",
                Validity.ANY, true, null, 0L);
        RowRuntime.target(occurrence, 15L, "Klass.m()#u8", expression, true,
                true, true);
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, "s", "d");
        RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, "   ",
                "a caller that named no subject");
        String cell = "INSTANCE_FIELD/22#28";
        placeholder(occurrence, placeholderRow("a", vmRead(125L)),
                "M_I_placeholder", null);
        placeholder(occurrence, placeholderRow("b", null), "M_I_unversioned",
                null);
        // A reference mint of an int cell: the sorts disagree, no row.
        placeholder(occurrence, placeholderRow("f", null),
                "P_L'org/apache/hadoop/hdfs/server/namenode/snapshot/"
                        + "Snapshot'_", null);
        // The mint's shadow store is no write: it joins version 125.
        placeholder(occurrence, placeholderRow("c", null), "M_I_installed",
                new String[] {cell, "126", "125"});
        // A second declared port of the SAME cell: another read event.
        JsonObject second = placeholderRow("g", null);
        second.addProperty("eventSeq", 19L);
        placeholder(occurrence, second, "M_I_second",
                new String[] {cell, "127", "125"});
        // The SAME read event reached again states no second row.
        placeholder(occurrence, placeholderRow("c", null), "M_I_installed",
                new String[] {cell, "126", "125"});
        // A mint with no write before it states -1 and pins the decimal.
        placeholder(occurrence, placeholderRow("e", null), "M_I_unwritten",
                new String[] {"INSTANCE_FIELD/22#32", "126", "-1"});
        // An over-pop of the region stack is a named refusal.
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Loader.loadEditRecords()#u4", null);
        Identity.occurrence(NN.key(), "REGION.loader", true);
        long nested = ConcolicRegionRuntime.enterRegionEntry("REGION.apply",
                "<a.Loader: long applyEditLogOp()>", null);
        Identity.regionExit(null);
        ConcolicRegionRuntime.exitRegionEntry(nested);
        RowRuntime.closeSession();

        SessionDir dir = session();
        SessionReader read = SessionReader.read(dir);
        List<DecisionRow> decisions = read.decisions();
        assertEquals(3, decisions.size());
        assertEquals(occurrence, decisions.get(0).occurrence());
        assertTrue(decisions.get(0).term().startsWith("EXPR."));
        assertEquals("a decision with no VM event id states 0", 0L,
                decisions.get(2).seq());
        assertEquals("and no term", "", decisions.get(2).term());
        assertFalse("a clockless decision adds no conjunct",
                Arms.predicate(Arms.conjunct(decisions.get(2))));
        List<ExportRow> exports = read.exports();
        assertEquals(1, exports.size());
        assertEquals(7L, exports.get(0).handle());
        assertEquals(4L, exports.get(0).seq());
        assertEquals("J", exports.get(0).javaType());
        List<AttachRow> attaches = read.attaches();
        assertTrue(attaches.get(0).answered());
        assertEquals("2", attaches.get(0).answeredValue());
        List<WriteRow> writes = read.writes();
        assertEquals("neither the tool's wait set nor a builder is a write",
                3, writes.size());
        assertEquals(125L, writes.get(0).version());
        assertEquals(10L, writes.get(0).seq());
        assertEquals(ATOMIC + "#getAndIncrement()I#12:WRITE",
                writes.get(0).endpoint().site());
        assertEquals(body, writes.get(0).endpoint().siteIndex().render());
        assertEquals("an int RMW is no Object", "I", writes.get(0).javaType());
        assertEquals("a written null is a reference", "L",
                writes.get(2).javaType());
        assertEquals("a String method's result is a String",
                "Ljava/lang/String;", writes.get(1).javaType());
        List<ReadRow> reads = read.reads();
        assertEquals(125L, reads.get(0).observedVersion());
        assertEquals(14L, reads.get(0).seq());
        assertEquals("the placeholder reads the location the write wrote",
                writes.get(0).location(), reads.get(1).location());
        assertEquals(writes.get(0).version(), reads.get(1).observedVersion());
        assertEquals("M_I_placeholder", reads.get(1).symbol());
        for (ReadRow row : reads) {
            assertFalse("no row names a location the VM did not state",
                    LocationId.of(LocationKind.INSTANCE, ATOMIC, "value")
                            .equals(row.location()));
        }
        assertEquals(LocationKind.INSTANCE, reads.get(2).location().kind());
        assertEquals(125L, reads.get(2).observedVersion());
        assertEquals("2", reads.get(2).concreteValue());
        ReadRow unwritten = null;
        for (ReadRow row : reads) {
            if ("M_I_unwritten".equals(row.symbol())) unwritten = row;
        }
        assertNotNull(unwritten);
        // CONTRACT v2.4: the version its own mint published, beside the
        // last real write it observed.
        assertEquals(126L, unwritten.mintVersion());
        assertEquals(ReadRow.UNKNOWN_VERSION, reads.get(0).mintVersion());
        assertEquals(ReadRow.UNKNOWN_VERSION, unwritten.observedVersion());
        assertEquals("2", unwritten.concreteValue());
        assertEquals("no row for a reference-sorted mint or one with no VM "
                + "location; one per mint store", 5, reads.size());
        List<RootMintRow> roots = RowCodec.readAll(dir.roots(),
                RowCodec::readRootMint);
        // A decision over declared roots alone holds exactly when its arm
        // says it does: "the term held", not "the jump was taken".
        Map<String, String> recorded = new HashMap<>();
        for (RootMintRow root : roots) {
            recorded.put(root.symbol(), root.recordedValue());
        }
        Map<String, JsonObject> table = read.expressions().expressions();
        int checked = 0;
        for (DecisionRow row : decisions) {
            Boolean held = holdsAtRoots(table.get(row.term()), recorded);
            if (held == null) continue;
            assertEquals("the conjunct of " + row.siteId() + " is satisfied",
                    held, row.outcome());
            checked++;
        }
        assertEquals("one decision is over declared roots only", 1, checked);
        assertEquals(RootKind.INTEGRAL, roots.get(0).kind());
        assertEquals(11L, roots.get(0).seq());
        assertTrue("the declared root is domained", roots.get(0).domainMin()
                != null || roots.get(0).domainMax() != null);
        // The kind is read off the declaration (a configured boolean is a
        // MARKER); ONE ROOT PER SYMBOL, the mint that made it (11741's
        // expiry hooks reused the clock's: six BLOCKING refusals).
        JsonObject configured = json("{'sourceId':'HDFS.CONFIG.SNAPSHOT_"
                + "DELETION_ORDERED','recordedValue':'true','category':'HOOK',"
                + "'expression':{'_type':'SymbolExpression','_java_type':'Z',"
                + "'_exp':'M_Z_field_SRC.50c885b3_a/Manager'}}");
        Class<?>[] row = {JsonObject.class};
        assertEquals(RootKind.MARKER, call(RowPlaceholderMint.class, "kindOf",
                row, configured));
        assertEquals(RootKind.INTEGRAL, call(RowPlaceholderMint.class,
                "kindOf", row, placeholderRow("d", null)));
        assertEquals(true, call(RowPlaceholderMint.class, "minted", row,
                configured));
        assertEquals("a read that reused one is no root", false,
                call(RowPlaceholderMint.class, "minted", row, json(
                        "{'sourceId':'HDFS.BLOCK_KEY.EXPIRY_DATE.RETIRED',"
                                + "'recordedValue':'1789616343508',"
                                + "'expression':{'_type':'BinaryExpression',"
                                + "'_exp':'+','_left':{'_type':"
                                + "'SymbolExpression','_java_type':'J','_exp':"
                                + "'M_J_field_REGION.aaa1cfd7.in.fa630d59.occ"
                                + ".23886999_java/lang/Long'}},"
                                + "'reused':true}")));
        assertTrue(RowCodec.readAll(dir.targets(), RowCodec::readTarget)
                .get(0).observedFatal());
        List<GapRow> gaps = RowCodec.readAll(dir.gaps(), RowCodec::readGap);
        assertTrue(gaps.get(0).blocking());
        boolean unnamedSubject = false;
        boolean unstatedLocation = false;
        for (GapRow gap : gaps) {
            if (gap.detail().startsWith("this LINEAGE_LOST names no subject")) {
                unnamedSubject = true;
                assertEquals("the session that met it is what is left to "
                        + "name", gap.sessionId(), gap.subject());
            }
            unstatedLocation |= gap.kind() == GapKind.DECLARATION_MISSING
                    && gap.detail().contains("states no VM location");
        }
        assertTrue("a gap whose caller named nothing is a row",
                unnamedSubject);
        assertTrue("the location-less declared input is named",
                unstatedLocation);
        GapRow unbalanced = gaps.get(gaps.size() - 1);
        assertEquals(GapKind.FRAME_UNBALANCED, unbalanced.kind());
        assertTrue("an over-pop is BLOCKING", unbalanced.blocking());
        assertTrue(unbalanced.detail(), unbalanced.detail().contains(
                "closed with 0 region(s) open and opened with 1"));
        assertTrue(unbalanced.detail(), unbalanced.detail().contains(
                "a region it did not open was closed under it"));
        // What the read-out keeps of the VM's envelope: the site and the
        // activation of each event, and the whole read log.
        JsonObject envelope = SharedStateCapture.writeLogRecord(
                "INSTANCE_FIELD/2#24", vmEnvelopeRecord().getAsJsonObject(
                        "envelope")).getAsJsonObject("envelope");
        JsonObject version = envelope.getAsJsonArray("versions").get(0)
                .getAsJsonObject();
        assertEquals(41L, version.get("regionEnterEventId").getAsLong());
        assertEquals("getAndIncrement", version.getAsJsonObject("site")
                .get("methodName").getAsString());
        JsonObject logged = envelope.getAsJsonArray("reads").get(0)
                .getAsJsonObject();
        assertEquals(76L, logged.get("readEventId").getAsLong());
        assertEquals(41L, logged.get("regionEnterEventId").getAsLong());
        assertEquals("()I", logged.getAsJsonObject("site")
                .get("methodDescriptor").getAsString());
        assertEquals(50L, VmRows.recordedVersion(logged));
        assertEquals("RMW", logged.getAsJsonObject("observedVersion")
                .get("versionKind").getAsString());
        assertTrue(Files.exists(dir.expressions()));
        assertTrue(read.expressions().refs().contains(
                exports.get(0).expressionRef()));
    }

    /**
     * A version names the region that wrote it wholly, or -- a store
     * outside every region -- not at all; half a writer is a malformed
     * envelope (commit-gs v73).  A reference write's container state, or
     * why none is stated, rides on a WRITE or RMW only: at most one of the
     * two, a state naming an older MAP_STATE version.
     */
    @Test
    public void aVersionNamesItsWritingRegionWhollyOrNotAtAll()
            throws Exception {
        Class<?>[] fault = {JsonObject.class, boolean.class, Set.class};
        for (Object[] each : new Object[][] {
                {41L, "REGION.a", "TASK.a", 7L, true},
                {0L, "", "", 0L, true},
                {41L, "", "TASK.a", 7L, false}}) {
            JsonObject version = json("{'fieldVersionId':50,'versionKind':"
                    + "'WRITE','regionEnterEventId':" + each[0] + ",'regionId':"
                    + "'" + each[1] + "','taskId':'" + each[2] + "',"
                    + "'writerContextId':" + each[3] + "}");
            String said = (String) call(SharedStateCapture.class,
                    "versionFault", fault, version, false, new HashSet<>());
            assertEquals(Arrays.toString(each), each[4],
                    !said.contains("names no writer case"));
        }
        JsonObject older = referent(49L);
        for (Object[] each : new Object[][] {
                {"WRITE", false, older, null, true},
                {"RMW", false, null, "RESIZING", true},
                {"WRITE", false, referent(50L), null, false},
                {"WRITE", false, older, "RESIZING", false},
                {"WRITE", false, null, " ", false},
                {"INITIAL", false, older, null, false},
                {"STATE_PUT", true, older, null, false}}) {
            JsonObject version = json("{'fieldVersionId':50,'versionKind':'"
                    + each[0] + "'}");
            version.add("pathGuard", JsonNull.INSTANCE);
            version.add("expression", rmwExpression());
            if (each[2] != null) {
                version.add("referentState", (JsonObject) each[2]);
            }
            if (each[3] != null) {
                version.addProperty("referentStateRefused", (String) each[3]);
            }
            String said = (String) call(SharedStateCapture.class,
                    "versionFault", fault, version, each[1], new HashSet<>());
            assertEquals(Arrays.toString(each) + ": " + said, each[4],
                    !said.contains("referent"));
        }
    }

    /**
     * A referent's version is a write row, or the write says why not: the
     * read-out refused its log, or the log holds it as no row (stored
     * outside every region) or no longer; a log the read-out did not select
     * is an earlier activation's to publish.
     */
    @Test
    public void aReferentWhoseStateIsNoRowIsRefusedByName() {
        String key = "MAP_STATE/1234#-3";
        JsonObject version = new JsonObject();
        version.add("referentState", referent(49L));
        for (Object[] each : new Object[][] {
                {"refused", "CONTAINER_BASE_UNSTATED: no walker"},
                {"rowed", ""}, {"outside", "VERSION_NOT_ROWED"},
                {"evicted", "VERSION_NOT_RETAINED"}, {"unselected", ""}}) {
            Map<String, String> refusals = new HashMap<String, String>();
            Map<String, SharedStateCapture.Filed> records = new HashMap<>();
            if ("refused".equals(each[0])) {
                refusals.put(key, (String) each[1]);
            } else if (!"unselected".equals(each[0])) {
                records.put(key, new SharedStateCapture.Filed("", json(
                        "{'envelope':{'versions':[{'fieldVersionId':"
                                + ("evicted".equals(each[0]) ? 51 : 49)
                                + ",'versionKind':'INITIAL',"
                                + "'regionEnterEventId':"
                                + ("outside".equals(each[0]) ? 0 : 40)
                                + "}]}}"), "", 0));
            }
            assertEquals(Arrays.toString(each), each[1],
                    RowPublication.unrowedReferent(refusals, records, version,
                            Collections.<String, String>emptyMap()));
        }
    }

    /** A MAP_STATE version as a reference version names it. */
    private static JsonObject referent(long version) {
        return json("{'ownerSymRid':1234,'slot':-3,'locationKind':"
                + "'MAP_STATE','fieldVersionId':" + version + "}");
    }

    /** One tracked location, as the VM's read-out states it. */
    private static JsonObject vmEnvelopeRecord() {
        String site = "{'className':'java/util/concurrent/atomic/"
                + "AtomicInteger','methodName':'getAndIncrement',"
                + "'methodDescriptor':'()I','bci':12}";
        JsonObject record = json("{'locationKey':'INSTANCE_FIELD/2#24',"
                + "'envelope':{'kind':'SHARED_FIELD_VERSIONS','schemaVersion':"
                + "2,'versions':[{'fieldVersionId':50,'versionKind':'RMW',"
                + "'regionEnterEventId':41,'writerContextId':7,'site':" + site
                + "}],'reads':[{'readEventId':76,'regionEnterEventId':41,"
                + "'readerContextId':7,'site':" + site + ",'observedVersion':"
                + "{'fieldVersionId':50,'versionKind':'RMW'},'observedExact':"
                + "true,'writerSetComplete':true,'_java_type':'I'}],"
                + "'readLogTruncated':false}}");
        record.getAsJsonObject("envelope").getAsJsonArray("versions").get(0)
                .getAsJsonObject().add("expression", rmwExpression());
        return record;
    }

    /** {@code <symbol> <op> <literal>} over a field read, as the VM
     *  publishes a compared read. */
    private static JsonObject compared(String symbol, String javaType,
                                       String operator, String literal) {
        return json("{'_type':'BinaryExpression','_left':{'_type':"
                + "'ConsumerBoundaryExpression','boundaryKind':'FIELD_READ',"
                + "'_java_type':'" + javaType + "','expression':{'_type':"
                + "'SymbolExpression','_java_type':'" + javaType + "','_exp':'"
                + symbol + "'}},'_op':'" + operator + "','_right':{'_type':"
                + "'ConstExpr','_java_type':'" + javaType + "','_exp':'"
                + literal + "'}}");
    }

    /**
     * Whether one term holds at the roots the session recorded, or null when
     * it is not an (in)equality over declared roots and literals alone:
     * {@code Y_<sort>_<value>} is the VM's literal and a root's {@code
     * recordedValue} what the run read.
     */
    private static Boolean holdsAtRoots(JsonObject term,
                                        Map<String, String> roots) {
        if (term == null || !"BinaryExpression".equals(text(term, "_type"))) {
            return null;
        }
        String operator = text(term, "_op");
        if (!"==".equals(operator) && !"!=".equals(operator)) return null;
        String left = valueAtRoots(term.get("_left"), roots);
        String right = valueAtRoots(term.get("_right"), roots);
        if (left == null || right == null) return null;
        return "==".equals(operator) == left.equals(right);
    }

    private static String valueAtRoots(JsonElement node,
                                       Map<String, String> roots) {
        if (node == null || !node.isJsonObject()) return null;
        JsonObject object = node.getAsJsonObject();
        String symbol = text(object, "_exp");
        if (roots.containsKey(symbol)) return normalized(roots.get(symbol));
        if (symbol.startsWith("Y_")) {
            return normalized(symbol.substring(symbol.lastIndexOf('_') + 1));
        }
        return valueAtRoots(object.get("expression"), roots);
    }

    /** {@code true}/{@code 1} and {@code false}/{@code 0} are one value. */
    private static String normalized(String value) {
        String stated = value == null ? "" : value.trim();
        return "true".equals(stated) ? "1" : "false".equals(stated) ? "0"
                : stated;
    }

    private static String text(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                ? value.getAsString() : "";
    }

    /** One logged event's node, carrying only the site the VM states for it
     *  (its class in the VM's own form, with slashes). */
    private static JsonObject loggedAt(String className, String method,
                                       String descriptor, int bci) {
        return json("{'site':{'className':'" + className + "','methodName':'"
                + method + "','methodDescriptor':'" + descriptor + "','bci':"
                + bci + "}}");
    }

    /** {@code Y_I_0 + Y_I_1}, as the VM publishes a linearized RMW. */
    private static JsonObject rmwExpression() {
        return json("{'_type':'BinaryExpression','_left':{'_type':"
                + "'ConstExpr','_java_type':'I','_exp':'Y_I_0'},'_op':'+',"
                + "'_right':{'_type':'ConstExpr','_java_type':'I','_exp':"
                + "'Y_I_1'}}");
    }

    /** One manual mint row, as {@code recordManualSymbolization} writes it. */
    private static JsonObject placeholderRow(String port, JsonObject read) {
        JsonObject row = json("{'portId':'REGION.f0132fca.in." + port + "',"
                + "'occurrenceId':'hdfs-17960/nn0#epoch1/region/REGION.f0132fca"
                + "#1','rawSymbol':'" + (read == null ? "M_I_unversioned"
                : "M_I_placeholder") + "','javaType':'int','fieldSignature':"
                + "'<" + ATOMIC + ": int value>','observedValue':'2',"
                + "'recordedValue':'2','eventSeq':16}");
        if (read != null) row.add("expression", read);
        return row;
    }

    /** The VM's read of a tracked location, as it spells one. */
    private static JsonObject vmRead(long version) {
        return json("{'_type':'ReadFromExpression','_exp':'M_I_placeholder',"
                + "'_java_type':'I','location':{'locationKind':"
                + "'INSTANCE_FIELD','ownerSymRid':22,'slot':24},"
                + "'observedVersion':{'fieldVersionId':" + version + "}}");
    }

    /** The placeholder read of ONE mint store ({@code installed}: the
     *  cell, the mint's version, the last real write's; or null). */
    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    String[] installed) throws Exception {
        call(RowPlaceholderMint.class, "placeholder", new Class<?>[] {
                OccurrenceAddress.class, JsonObject.class, String.class,
                String[].class, boolean.class}, occurrence, row, symbol,
                installed, false);
    }

    /**
     * The anchor's phi is published in the FATAL polarity whichever arm the
     * run took, so no reader downstream negates it a second time; a concrete
     * fatal condition states the constant of the arm it took (SOLR-18413
     * r9), an anchor the run did not reach none.
     */
    @Test
    public void phiIsPublishedInTheFatalPolarityForBothObservedArms()
            throws Exception {
        openSession();
        OccurrenceAddress occurrence = targetDn();
        JsonObject condition = json("{'_type':'BinaryExpression','_exp':"
                + "'allKeys.get(id) == null'}");
        String site = "retrieveDataEncryptionKey#u8";
        RowRuntime.target(occurrence, 8L, site, condition, true, true, true);
        RowRuntime.target(occurrence, 9L, site, condition, false, false, true);
        RowRuntime.target(occurrence, 10L, site, null, true, true, true);
        RowRuntime.target(occurrence, 11L, site, null, false, false, true);
        RowRuntime.target(occurrence, 0L, site, null, false, false, false);
        RowRuntime.closeSession();
        List<TargetRow> rows = RowCodec.readAll(session().targets(),
                RowCodec::readTarget);
        assertEquals(5, rows.size());
        String ref = rows.get(0).phiTerm();
        assertTrue(ref.startsWith("EXPR."));
        assertTrue(rows.get(0).observedFatal());
        assertEquals("(not " + ref + ")", rows.get(1).phiTerm());
        assertFalse(rows.get(1).observedFatal());
        assertEquals("true", rows.get(2).phiTerm());
        assertEquals("false", rows.get(3).phiTerm());
        assertEquals("", rows.get(4).phiTerm());
    }

    /**
     * I4: a decision row carries exactly the clock cells its term names.
     * The readings were a JVM-WIDE map of every clock the process minted --
     * one MiniDFSCluster is one JVM: on hdfs-11741 14 of 17 {@code
     * removeExpiredKeys#u15} rows lacked their own cell and 15 of 17 listed
     * other NODES' cells.
     */
    @Test
    public void aDecisionCarriesTheClockCellsItsTermNames() throws Exception {
        openSession();
        OccurrenceAddress occurrence = address("hdfs-11741/nn0#epoch0",
                "REGION.aaa1cfd7", CausalContext.of(Role.of(
                        "KEY_MANAGER_TICK"), "updateKeys", 1),
                ExecutionIndex.parse("KeyManager.updateKeys()#u3@0"));
        RowRuntime.rootMint(occurrence, 3L, "HDFS.KEY.NOW@nn0", "M_J_now_nn0",
                RootKind.CLOCK, RootCategory.CLOCK, "1789358344655", "", "",
                Validity.ANY, true, Clock.of(1_000_000L, Clock.WALL), 0L);
        RowRuntime.rootMint(occurrence, 4L, "HDFS.KEY.NOW@dn1", "M_J_now_dn1",
                RootKind.CLOCK, RootCategory.CLOCK, "1789358344999", "", "",
                Validity.ANY, true, Clock.of(1_000_000L, Clock.WALL), 0L);
        RowRuntime.rootMint(occurrence, 5L, "HDFS.BLOCK_KEY.SERIAL_NO",
                "M_I_serial", RootKind.INTEGRAL, RootCategory.HOOK, "3", "3",
                "6", Validity.ANY, true, null, 0L);
        RowRuntime.decision(occurrence, 12L, "<a.BlockTokenSecretManager: "
                + "void removeExpiredKeys()>#u15", 1, true, compared(
                "M_J_now_nn0", "J", "<", "Y_J_0"));
        RowRuntime.decision(occurrence, 13L, "<a.KeyManager: void"
                + " updateKeys()>#u9", 1, false, compared("M_I_serial", "I",
                "<", "Y_I_0"));
        RowRuntime.decision(occurrence, 0L, "<a.KeyManager: void"
                + " updateKeys()>#u2", 1, true, null);
        RowRuntime.closeSession();
        List<DecisionRow> decisions = SessionReader.read(session()).decisions();
        assertEquals(3, decisions.size());
        assertEquals("the cell this term reads, at what its mint recorded",
                Collections.singletonMap("HDFS.KEY.NOW@nn0", 1789358344655L),
                decisions.get(0).clockReadings());
        assertEquals("not the other node's", Collections.emptyMap(),
                decisions.get(1).clockReadings());
        assertEquals("a decision with no term names no cell",
                Collections.emptyMap(), decisions.get(2).clockReadings());
    }

    /**
     * I1: the enclosing occurrence wins.  A declared region method called
     * synchronously inside another region's occurrence opens NO occurrence
     * of its own (paper SS3.1.2): on hdfs-11741 dn1 {@code addKeys} calling
     * {@code removeExpiredKeys} once opened a nested occurrence that took
     * every decision, read and mint of the call with it.  Neither pass
     * records an activation for a folded entry (IDENTITY §1); a declared
     * region on a thread running no occurrence opens its own.
     */
    @Test
    public void aNestedDeclaredRegionFoldsIntoTheRunningOccurrence()
            throws Exception {
        Identity.resetForTests();
        Lineage.resetForTests();
        RuntimeTraceContext.resetForTests();
        Object keyManager = new Object();
        RuntimeTraceContext.registerSource(keyManager, NN);
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        String addKeysMethod = "<a.BlockTokenSecretManager: void addKeys()>";
        String expiry = "<a.BlockTokenSecretManager: void removeExpiredKeys()>";
        Identity.enterFrame(addKeysMethod + "#u1", null);
        OccurrenceAddress addKeys = Identity.occurrence(NN.key(),
                "REGION.ba3902cd", true);
        assertNotNull(addKeys);
        String opened = addKeys.render();
        long nestedFrame = Identity.enterFrame(expiry + "#u7", null);
        long entry = ConcolicRegionRuntime.enterRegionEntry("REGION.094a8e3d",
                expiry, keyManager);
        assertEquals("the entry opens none of its own", addKeys,
                Identity.currentOccurrence(NN.key()));
        assertEquals("both entries stand on the region stack", 2,
                Identity.regionDepth());
        assertEquals(opened, addKeys.render());
        // A site below the fold is indexed from the entry that OPENED it.
        long deeper = Identity.enterFrame("<a.Key: long getExpiryDate()>#u2",
                null);
        assertEquals(expiry + "#u7@0/<a.Key: long getExpiryDate()>#u2@0",
                Identity.siteIndex().render());
        Identity.exitFrame(deeper);
        ConcolicRegionRuntime.exitRegionEntry(entry);
        Identity.exitFrame(nestedFrame);
        assertEquals("the folded region's exit closes nothing", 1,
                Identity.regionDepth());
        assertEquals(addKeys, Identity.currentOccurrence(NN.key()));

        Identity.resetForTests();
        Lineage.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame(addKeysMethod + "#u1", null);
        assertFalse("nothing runs here: this entry opens an occurrence",
                recordedAddress("REGION.ba3902cd").isEmpty());
        assertFalse(Identity.openedNone());
        Identity.enterFrame(expiry + "#u7", null);
        assertEquals("the nested entry folds: no address, no activation", "",
                recordedAddress("REGION.094a8e3d"));
        assertTrue(Identity.openedNone());
        Identity.regionExit(null);
        Identity.regionExit(null);
        assertFalse(Identity.openedNone());

        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame(expiry + "#u7", null);
        OccurrenceAddress alone = Identity.occurrence(NN.key(),
                "REGION.094a8e3d", true);
        assertNotNull("no occurrence was running, so this entry opens one",
                alone);
        assertEquals("REGION.094a8e3d", alone.regionId());
        assertEquals(1, Identity.regionDepth());
        assertEquals(alone, Identity.currentOccurrence(NN.key()));
    }

    /** What the RECORDING writes onto this entry's trace row, through the
     *  recorder's own door, so the fold is asserted where PLAN reads it. */
    private static String recordedAddress(String regionId) throws Exception {
        return (String) call(CausynthTraceRecorder.class, "occurrenceAddress",
                new Class<?>[] {String.class, String.class}, NN.key(),
                regionId);
    }

    private void executionIndexIsStableUnderUnrelatedCalls() {
        // A scope opened inside a call that RETURNS is rooted at the deepest
        // level the scope start and the point share: the four
        // PBHelper.convert activations of one refresh answered one address.
        Identity.resetForTests();
        Identity.enterFrame("Server.processRpcRequest()#u3", null);
        long inbound = Identity.enterFrame("Propagation.inbound()#u7", null);
        Identity.scopeStart(Identity.Hop.ANCHOR);
        Identity.exitFrame(inbound);
        long converting = Identity.enterFrame("PBHelper.convert()#u9", null);
        assertEquals("PBHelper.convert()#u9@0", Identity.atScope().render());
        Identity.exitFrame(converting);
        Identity.enterFrame("PBHelper.convert()#u9", null);
        assertEquals("the k-th call at one site under one occurrence",
                "PBHelper.convert()#u9@1", Identity.atScope().render());
        // The frames ABOVE the inbound scope are the carrier thread's: which
        // pooled handler serves is scheduling (hdfs-17960 planned handler 3
        // and ran handler 0: 14 tasks refused at Server.start()#u31).
        Object served = new Object();
        RuntimeTraceContext.registerSource(served, NN);
        long serving = RuntimeTraceContext.beginRequest(NN,
                "checkpoint-namespace");
        String header = RuntimeTraceContext.outboundHeader(served, null);
        RuntimeTraceContext.endRequest(serving);
        String recorded = anchoredActivationIndex(header, 3);
        assertEquals("the served api is frame 0",
                "NameNodeRpcServer.saveNamespace()#u40@0", recorded);
        assertEquals("whichever handler was scheduled", recorded,
                anchoredActivationIndex(header, 0));
        // A tick IS the started work: its index begins at the start frame it
        // claimed (IDENTITY §3).
        Identity.resetForTests();
        Lineage.resetForTests();
        Object updating = new Object();
        RuntimeTraceContext.registerSource(updating, NN);
        assertEquals("KeyManager.startBlockKeyUpdater()#u5@0"
                + "/BlockKeyUpdater.run()#u6@0"
                + "/KeyManager.updateBlockKeys()#u2@0",
                daemonTickIndex(updating));
        // Counts live in the LEVEL, one set per ROOT HOP it was live under:
        // a tick inside a request cannot move the request's counts (the
        // balancer's two runOneIteration calls once shared an endpoint).
        Identity.resetForTests();
        Lineage.resetForTests();
        Object ticking = new Object();
        RuntimeTraceContext.registerSource(ticking, NN);
        long request = RuntimeTraceContext.beginRequest(NN, "balance-block");
        String iterate = "Balancer.runOneIteration()#u1";
        Identity.exitFrame(Identity.enterFrame(iterate, null));
        long tick = CausynthTraceRecorder.beginDaemonTick(ticking,
                "KEY_MANAGER_TICK");
        Identity.exitFrame(Identity.enterFrame(
                "KeyManager.updateBlockKeys()#u2", null));
        CausynthTraceRecorder.endDaemonTick(tick);
        Identity.enterFrame(iterate, null);
        assertEquals(iterate + "@1", Identity.atScope().render());
        RuntimeTraceContext.endRequest(request);
        // Keyed by the live context, a standing response's anchor once made
        // one producer endpoint of six create-snapshots RPCs (hdfs-17960
        // #6: 158 OCCURRENCE_ADDRESS_SHARED rows).
        Object client = new Object();
        RuntimeTraceContext.registerSource(client, NN);
        List<Endpoint> standing = clientRequestSends(client, true);
        List<Endpoint> quiet = clientRequestSends(client, false);
        Set<String> ids = new LinkedHashSet<String>();
        for (Endpoint send : standing) ids.add(send.id());
        assertEquals("six sends at one site are six endpoints", 6,
                ids.size());
        assertEquals("Client.call()#u12@5/Client.call()#u13@0"
                + "/Connection.sendRpcRequest()#u9@0"
                + "/Propagation.outbound()#u4@0/HADOOP_IPC#REQUEST@0",
                standing.get(5).siteIndex().render());
        for (int send = 0; send < standing.size(); send++) {
            assertEquals("the standing hop moves no send's endpoint",
                    quiet.get(send).id(), standing.get(send).id());
        }

        Identity.resetForTests();
        Lineage.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Caller.run()#u3", null);
        Identity.enterFrame("Caller.step()#u7", null);
        ExecutionIndex inner = Identity.atScope();
        assertEquals("Caller.run()#u3@0/Caller.step()#u7@0", inner.render());
        Identity.exitFrame(Identity.enterFrame("Other.helper()#u1", null));
        assertEquals("an unrelated call moves nothing", inner,
                Identity.atScope());
        Identity.exitFrame(Identity.enterFrame("Caller.body()#u9", null));
        Identity.enterFrame("Caller.body()#u9", null);
        assertEquals("re-entering one site is the next iteration",
                "Caller.run()#u3@0/Caller.step()#u7@0/Caller.body()#u9@1",
                Identity.atScope().render());
        // A region entry re-bases the index.
        ExecutionIndex atEntry = Identity.regionEnter();
        assertEquals(3, atEntry.frames().size());
        assertTrue(Identity.siteIndex().frames().isEmpty());
        Identity.enterFrame("Region.port()#u2", null);
        assertEquals("Region.port()#u2@0", Identity.siteIndex().render());

        // The frame journal: a VM-logged event takes the frames the thread
        // stood on when the VM's event clock was below its id.
        Identity.resetForTests();
        long[] clock = {41L};
        Identity.clock(() -> clock[0]);
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.occurrence(NN.key(), "REGION.save", true);
        Identity.regionKey(41L);
        Identity.enterFrame("Saver.save()#u1", null);
        clock[0] = 44L;
        long counting = Identity.enterFrame("Manager.count()#u2", null);
        clock[0] = 48L;
        String both = "Saver.save()#u1@0/Manager.count()#u2@0";
        assertEquals(both, FrameJournal.framesAt(41L, 45L).render());
        assertEquals(both, FrameJournal.framesAt(41L, 48L).render());
        assertEquals("one frame shallower before count() was entered",
                "Saver.save()#u1@0", FrameJournal.framesAt(41L, 43L)
                        .render());
        Identity.exitFrame(counting);
        Identity.enterFrame("Manager.count()#u2", null);
        assertEquals("Saver.save()#u1@0/Manager.count()#u2@1",
                FrameJournal.framesAt(41L, 49L).render());
        assertNull(FrameJournal.framesAt(99L, 49L));
        assertNull(FrameJournal.framesAt(41L, 41L));
        // One key, two answers: the frames, and the occurrence that
        // performed the event, as the VM names it on the record.
        OccurrenceAddress performer = address("hdfs-17960/nn0#epoch1",
                "REGION.9492ec77", CausalContext.of(Role.CLIENT, "", 1),
                ExecutionIndex.parse("Manager.delete()#u3@0"));
        RowRuntime.journalRegion(41L, performer);
        assertEquals(performer, RowRuntime.occurrenceAt(41L));
        assertNull(RowRuntime.occurrenceAt(99L));

        // The thread-start handover (P2h): the child's stack GAINS the frame
        // of the start that created it, so two siblings started from one
        // site (hdfs-17960's two FSImageSaver threads) differ by that
        // start's iteration alone; the next activation of the starter is
        // another occurrence, its starts at 0 again.
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Object starter = new Object();
        RuntimeTraceContext.registerSource(starter, NN);
        long starting = RuntimeTraceContext.beginRequest(starter, "checkpoint");
        String save = "FSImage.saveFSImageInAllDirs()#u12";
        String start = "FSImage.saveFSImageInAllDirs()#u40";
        long saving = Identity.enterFrame(save, null);
        assertEquals(save + "@0/" + start + "@0/FSImageSaver.run()#u1@0",
                startedWorkIndex(start));
        assertEquals(save + "@0/" + start + "@1/FSImageSaver.run()#u1@0",
                startedWorkIndex(start));
        Identity.exitFrame(saving);
        Identity.enterFrame(save, null);
        assertEquals(save + "@1/" + start + "@0/FSImageSaver.run()#u1@0",
                startedWorkIndex(start));
        RuntimeTraceContext.endRequest(starting);

        // TWO stacks, one balance rule: a nested region opened and closed
        // leaves the enclosing counts alone; a stray region pop touches no
        // count (17960 #3: 13 tasks refused at applyEditLogOp), only the
        // frame the site index is measured from.
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Loader.loadEditRecords()#u4", null);
        Identity.occurrence(NN.key(), "REGION.loader", true);
        assertEquals(1, Identity.regionDepth());
        String applyOp = "Loader.applyEditLogOp()#u115";
        for (int record = 0; record < 3; record++) {
            long applying = Identity.enterFrame(applyOp, null);
            Identity.occurrence(NN.key(), "REGION.apply", true);
            Identity.regionExit(null);
            Identity.exitFrame(applying);
        }
        assertEquals(1, Identity.regionDepth());
        long applied = Identity.enterFrame(applyOp, null);
        assertEquals("Loader.loadEditRecords()#u4@0/" + applyOp + "@3",
                Identity.atScope().render());
        assertTrue(Identity.innermostRegion().contains("REGION.loader"));
        Identity.exitFrame(applied);
        int frames = Identity.depth();
        Identity.regionExit(null);
        assertEquals("the frames are untouched by a region pop", frames,
                Identity.depth());
        assertEquals(0, Identity.regionDepth());
        Identity.enterFrame(applyOp, null);
        assertEquals("the fifth entry is still the fifth",
                "Loader.loadEditRecords()#u4@0/" + applyOp + "@4",
                Identity.atScope().render());

        // A pool thread created before the work: the start filed for each
        // TASK is claimed on its object and ends with it (11741 r3: the
        // balancer's two move tasks shared one address).
        Identity.resetForTests();
        List<String> ran = Collections.synchronizedList(new ArrayList<>());
        Object[] tasks = {new Object(), new Object()};
        Thread worker = poolThreadCreatedOutsideAnyScope(() -> {
            for (Object task : tasks) {
                long claim = Identity.claimStart(task);
                long running = Identity.enterFrame("Task.run()#u1", null);
                ran.add(Identity.atScope().render());
                Identity.exitFrame(running);
                Identity.endClaim(claim);
            }
        });
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Object submitter = new Object();
        RuntimeTraceContext.registerSource(submitter, NN);
        long submitting = RuntimeTraceContext.beginRequest(submitter,
                "submit");
        for (Object task : tasks) {
            long submitOne = Identity.enterFrame("Pool.submitOne()#u5", null);
            Identity.startWork("Pool.submitOne()#u9", task, null);
            Identity.exitFrame(submitOne);
        }
        run(worker);
        RuntimeTraceContext.endRequest(submitting);
        assertEquals(Arrays.asList(
                "Pool.submitOne()#u5@0/Pool.submitOne()#u9@0/Task.run()#u1@0",
                "Pool.submitOne()#u5@1/Pool.submitOne()#u9@0/Task.run()#u1@0"),
                ran);
        // Push and pop are paired, recursion included; a stale token closes
        // nothing.
        int depthAtOpen = Identity.depth();
        long outer = Identity.enterFrame("Recursive.m()#u1", null);
        long innerRecursion = Identity.enterFrame("Recursive.m()#u1", null);
        assertEquals(depthAtOpen + 2, Identity.depth());
        assertEquals("Recursive.m()#u1", Identity.innermostFrame());
        Identity.exitFrame(innerRecursion);
        assertEquals(depthAtOpen + 1, Identity.depth());
        Identity.exitFrame(outer);
        assertEquals(depthAtOpen, Identity.depth());
        Identity.exitFrame(innerRecursion);
        assertEquals(depthAtOpen, Identity.depth());

        // The three causal contexts: a ROOT names the api its k counts
        // (IDENTITY §2), a tick declares none.
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Caller.run()#u3", null);
        assertEquals("Root:HEARTBEAT_TICK#4", Identity.context("", "",
                Role.of("HEARTBEAT_TICK"), "", 4).render());
        assertEquals("Root:CLIENT/balance-block#1", Identity.context("", "",
                Role.CLIENT, "balance-block", 1).render());
        assertEquals("Anchor:abc123@HADOOP_IPC#heartbeat", Identity.context(
                "abc123", "HADOOP_IPC#heartbeat", Role.of("IPC_HANDLER"), "",
                2).render());
        assertEquals("Lost:DATA_XCEIVER", Identity.context("", "",
                Role.of("DATA_XCEIVER"), "", 0).render());
    }

    /**
     * The index of one anchored activation as a pass that scheduled the
     * {@code scheduled}-th of four handlers computes it: hdfs-17960's
     * NameNode RPC, whose inbound opens the served scope inside a call that
     * hands control straight back to the handler.
     */
    private static String anchoredActivationIndex(String header,
                                                  int scheduled) {
        Identity.resetForTests();
        Lineage.resetForTests();
        AtomicReference<String> onHandler = new AtomicReference<>("");
        Thread[] pool = new Thread[4];
        for (int handler = 0; handler < pool.length; handler++) {
            pool[handler] = new Thread(handler != scheduled ? () -> { }
                    : () -> {
                        Identity.enterFrame("Server$Handler.run()#u32", null);
                        Identity.enterFrame("Server$RpcCall.run()#u33", null);
                        long propagating = Identity.enterFrame(
                                "Propagation.inbound()#u7", null);
                        long inbound = RuntimeTraceContext.enterInbound(header,
                                "HADOOP_IPC", "corr-1", "attempt-0", "REQUEST",
                                null, "");
                        Identity.exitFrame(propagating);
                        Identity.enterFrame(
                                "NameNodeRpcServer.saveNamespace()#u40", null);
                        onHandler.set(Identity.atScope().render());
                        RuntimeTraceContext.exitInbound(inbound);
                    });
            Identity.startWork("Server.start()#u31", pool[handler], null);
        }
        run(pool[scheduled]);
        return onHandler.get();
    }

    /**
     * The producer endpoints of six RPCs one client request sends, as
     * hdfs-17960's client does: {@code Client.call} entered from an unwoven
     * caller, {@code sendRpcRequest} closing whatever inbound hop stands,
     * and {@code getRpcResponse} leaving the response's scope standing when
     * {@code installResponses}.
     */
    private static List<Endpoint> clientRequestSends(Object client,
                                                     boolean installResponses) {
        Identity.resetForTests();
        Lineage.resetForTests();
        Interactions.resetForTests();
        List<Endpoint> sent = new ArrayList<Endpoint>();
        long request = RuntimeTraceContext.beginRequest(NN,
                "create-snapshots");
        String header = RuntimeTraceContext.outboundHeader(client, null);
        long response = 0L;
        for (int rpc = 0; rpc < 6; rpc++) {
            long call = Identity.enterFrame("Client.call()#u12", null);
            long retrying = Identity.enterFrame("Client.call()#u13", null);
            long sending = Identity.enterFrame(
                    "Connection.sendRpcRequest()#u9", null);
            if (response > 0L) RuntimeTraceContext.exitInbound(response);
            long outbound = Identity.enterFrame("Propagation.outbound()#u4",
                    null);
            sent.add(Identity.messageSent(NN.key(), "HADOOP_IPC",
                    "corr-" + rpc, "REQUEST", "HADOOP_IPC#REQUEST", null));
            Identity.exitFrame(outbound);
            Identity.exitFrame(sending);
            response = installResponses ? RuntimeTraceContext.enterInbound(
                    header, "HADOOP_IPC", "corr-" + rpc, "0", "RESPONSE",
                    client, "") : 0L;
            Identity.exitFrame(retrying);
            Identity.exitFrame(call);
        }
        if (response > 0L) RuntimeTraceContext.exitInbound(response);
        RuntimeTraceContext.endRequest(request);
        return sent;
    }

    /** The index one daemon tick of an updater thread stands on, started
     *  inside the balancer's own request. */
    private static String daemonTickIndex(Object owner) {
        AtomicReference<String> onUpdater = new AtomicReference<>("");
        Thread updater = new Thread(() -> {
            Identity.enterFrame("BlockKeyUpdater.run()#u6", null);
            long tick = CausynthTraceRecorder.beginDaemonTick(owner,
                    "KEY_MANAGER_TICK");
            Identity.enterFrame("KeyManager.updateBlockKeys()#u2", null);
            onUpdater.set(Identity.atScope().render());
            CausynthTraceRecorder.endDaemonTick(tick);
        });
        long starting = RuntimeTraceContext.beginRequest(owner, "balance");
        Identity.startWork("KeyManager.startBlockKeyUpdater()#u5", updater,
                null);
        RuntimeTraceContext.endRequest(starting);
        run(updater);
        return onUpdater.get();
    }

    /** The index of the work one start site started, on its own thread,
     *  CONSTRUCTED before the start is filed, as {@code new Thread(saver)}
     *  then {@code start()} is. */
    private static String startedWorkIndex(String startSite) {
        AtomicReference<String> onChild = new AtomicReference<>("");
        Thread child = new Thread(() -> {
            Identity.enterFrame("FSImageSaver.run()#u1", null);
            onChild.set(Identity.atScope().render());
        });
        Identity.startWork(startSite, child, null);
        run(child);
        return onChild.get();
    }

    /**
     * What the runtime reads out of an expression -- a mint's symbol, the
     * read under wrappers, a written value's java type, a branch's witness
     * -- is read once per node and to its end: a chain naming the one below
     * twice is 2^64 paths as a tree, and one 100000 deep passed the walks'
     * cuts or overflowed a recursion on the workload's own thread.
     */
    @Test(timeout = 120_000L)
    public void aDeepSharedChainIsReadToItsEnd() throws Exception {
        openSession();
        JsonObject deepest = json("{'_type':'SymbolExpression','_exp':"
                + "'M_J_deepest','_java_type':'J'}");
        JsonObject untyped = json("{'_type':'ConstExpr','_exp':'Y_J_1'}");
        long version = 200L;
        for (int depth : new int[] {64, 100_000}) {
            JsonObject chain = deepest;
            JsonObject read = vmRead(version);
            JsonObject wrapped = read;
            for (int level = 0; level < depth; level++) {
                JsonObject sum = json("{'_type':'BinaryExpression','_op':"
                        + "'+'}");
                sum.add("_left", chain);
                sum.add("_right", depth == 64 ? chain : untyped);
                // A null member, so the witness copies every node.
                sum.add("_guard", JsonNull.INSTANCE);
                chain = sum;
                JsonObject boundary = json("{'_type':"
                        + "'ConsumerBoundaryExpression'}");
                boundary.add("expression", wrapped);
                wrapped = boundary;
            }
            JsonObject row = new JsonObject();
            row.add("expression", chain);
            assertEquals(depth + " levels", "M_J_deepest",
                    RowPlaceholderMint.vmSymbol(row));
            assertTrue(depth + " levels",
                    RowPublication.nestedRead(wrapped) == read);
            JsonObject witness = edu.uva.liftlab.graphchecker.plan
                    .BranchWitness.immutablePredicate(chain,
                            new java.util.IdentityHashMap<JsonElement,
                                    JsonElement>())
                    .toImmutableJsonView()
                    .getAsJsonObject("sourceSatisfiedPredicate");
            assertFalse(witness.has("_guard"));
            assertEquals(depth == 64, witness.get("_left")
                    == witness.get("_right"));
            Set<String> symbols = new HashSet<String>();
            Arms.symbolsIn(witness, symbols);
            assertTrue(depth + " levels: " + symbols,
                    symbols.contains("M_J_deepest"));
            // One occurrence per chain: two writes at one site of one
            // occurrence are two events on the same frames.
            RowRuntime.write(address("hdfs-17899/target-dn#epoch0",
                    "REGION.deep", CausalContext.of(Role.of("DEEP"), "",
                            depth), ExecutionIndex.parse(
                            "DataXceiver.run()#u9@0")), version,
                    Endpoint.stateSite(ATOMIC, "getAndIncrement", "()I", 12,
                            true), LocationId.of(LocationKind.INSTANCE, "22",
                            "24"), version++, chain, "", "Caller.body()#u9@1",
                    null, null, false);
        }
        RowRuntime.closeSession();
        List<WriteRow> writes = SessionReader.read(session()).writes();
        assertEquals(2, writes.size());
        for (WriteRow write : writes) {
            assertEquals("the deepest node states the type", "J",
                    write.javaType());
        }
    }

    /**
     * A version reads observed and no write row of the session states is
     * named at the close, once per location and version, with where its
     * store ran when the VM stated it outside every region: never a silent
     * skip (hdfs-adhoc-39 OA4).  A version a row wrote, and a placeholder's
     * mint store, are no such version.  A read the VM named nothing is named
     * in its own session: two diverged replays hold two objects under one
     * rid and version.
     */
    @Test
    public void aReadOfAVersionNoRowWroteIsNamedAtTheClose() throws Exception {
        assertFalse(RowPublication.versionSymbol("s1", "INSTANCE_FIELD/203#24",
                "v927").equals(RowPublication.versionSymbol("s2",
                "INSTANCE_FIELD/203#24", "v927")));
        openSession();
        OccurrenceAddress occurrence = address("hdfs/nn0#epoch0",
                "REGION.53092d3e", CausalContext.of("producer-endpoint-id",
                        "HADOOP_IPC/test"),
                ExecutionIndex.parse("Server.run()#u9@0"));
        String reads = Endpoint.stateSite("a.BlockInfo", "getBlockUCState",
                "()I", 48, false);
        LocationId written = LocationId.of(LocationKind.INSTANCE, "22", "24");
        LocationId lost = LocationId.of(LocationKind.INSTANCE, "23", "24");
        LocationId outside = LocationId.of(LocationKind.INSTANCE, "152", "80");
        LocationId minted = LocationId.of(LocationKind.INSTANCE, "24", "24");
        RowRuntime.write(occurrence, 10L, Endpoint.stateSite("a.BlockInfo",
                "set", "()V", 3, true), written, 5L, rmwExpression(), "",
                "Caller.body()#u9@1", null, null, false);
        RowRuntime.storedOutside(outside, 9L,
                "a.BlockInfo#convertToCompleteBlock()V#214:WRITE");
        Object[][] observed = {{11L, written, 5L, "s", -1L},
                {12L, lost, 7L, "t", -1L}, {13L, outside, 9L, "u", -1L},
                {14L, outside, 9L, "u", -1L}, {15L, minted, 11L, "v", 11L}};
        for (Object[] read : observed) {
            RowRuntime.read(occurrence, (Long) read[0], reads,
                    (LocationId) read[1], (Long) read[2], (String) read[3],
                    "J", "9", "", (Long) read[4] == -1L
                            ? ReadRow.UNKNOWN_VERSION : (Long) read[4]);
        }
        RowRuntime.closeSession();
        List<String> named = new ArrayList<String>();
        for (GapRow gap : gaps()) {
            if (gap.kind() != GapKind.UNATTRIBUTED_STORE) continue;
            assertFalse(gap.blocking());
            named.add(gap.subject() + " " + gap.detail());
        }
        Collections.sort(named);
        assertEquals(named.toString(), 2, named.size());
        assertTrue(named.get(0), named.get(0).startsWith("INSTANCE/152#80@9 2"
                + " read(s)") && named.get(0).endsWith("its store ran outside"
                + " every activation, at a.BlockInfo#convertToCompleteBlock()"
                + "V#214:WRITE"));
        assertTrue(named.get(1), named.get(1).startsWith("INSTANCE/23#24@7 1"
                + " read(s)") && named.get(1).endsWith("no read-out of this"
                + " run states its store"));
    }

    /**
     * {@code if (a || b || c) throw}: every test jumps to the throw, so phi
     * is the OR of their fatal arms as one evaluation decided them, from the
     * target branch on (adhoc reader-chunk's first-chunk offset check); an
     * evaluation that skipped the recording's first test reaches the target
     * at the test it did decide (SOLR-18406's second disjunct).
     */
    @Test
    public void aDisjunctiveGuardIsTheOrOfItsTestsFatalArms() {
        JsonObject a = predicate("a");
        JsonObject c = predicate("c");
        String refA = RowRuntime.expressionRef(a);
        String refC = RowRuntime.expressionRef(c);
        Map<String, Boolean> guards = new LinkedHashMap<>();
        guards.put("G#u1", true);
        guards.put("G#u2", true);
        guards.put("G#u3", false);
        Object[][] rows = {
            // All healthy: a symbolic, b concrete, c symbolic.
            {decided("G#u1", false, a), decided("G#u2", false, null),
                decided("G#u3", true, c), false,
                Arrays.asList("(not " + refA + ")", "(not " + refC + ")")},
            // b took its fatal arm concretely: the constant of that arm.
            {decided("G#u1", false, a), decided("G#u2", true, null), null,
                true, Collections.singletonList("true")},
            // a took it symbolically: its predicate is the arm.
            {decided("G#u1", true, a), null, null, true,
                Collections.singletonList(refA)}};
        for (Object[] row : rows) {
            List<JsonObject> mappings = new ArrayList<>();
            // An earlier evaluation of a test is not this one.
            mappings.add(decided("G#u2", true, null));
            mappings.get(0).addProperty("occurrence", 0);
            for (int index = 0; index < 3; index++) {
                if (row[index] != null) mappings.add((JsonObject) row[index]);
            }
            List<String> arms = new ArrayList<>();
            assertEquals(row[3], RowPublication.disjunction(mappings, guards,
                    "G#u1", 1, arms));
            assertEquals(row[4], arms);
        }
        List<String> arms = new ArrayList<>();
        assertTrue(RowPublication.disjunction(Collections.singletonList(
                decided("G#u3", false, c)), guards, "G#u3", 1, arms));
        assertEquals(Collections.singletonList(refC), arms);
    }

    /**
     * A target testing a helper's return is decided by the latest decision
     * in the helper's method before it, when that is a decider's
     * (causynth.BooleanReturns): {@code ite(the decision as it held, the arm
     * it took, the other arm)}, an arm its verdict or, open and taken, the
     * guard's own condition; a concrete decision tests a nested helper's
     * return, whose deciders give its condition (hdfs-adhoc-40: {@code
     * isSufficientlyReplicated}'s concrete test of {@code hasMinStorage}).
     * Where the other arm is open and never ran, the result names it, with
     * the decision whose flip runs it.  None where the constant arm taken is
     * not what the guard observed or the latest decision is no decider's:
     * never an earlier call's, nor one after the target.  phi puts the
     * condition in the fatal polarity, and leaves the run's own where an arm
     * is open.
     */
    @Test
    public void aHelpersReturnIsDecidedByTheLatestArmInItsMethod() {
        String helper = "<a.H: boolean sufficient(int)>";
        String nested = "<a.H: boolean hasMin(int)>";
        List<StaticScopeMap.Guard> none = Collections.emptyList();
        List<StaticScopeMap.Guard> hasMin = Arrays.asList(
                new StaticScopeMap.Guard(nested + "#u1", true, true, none,
                        helper),
                new StaticScopeMap.Guard(nested + "#u1", false, false, none,
                        helper));
        List<StaticScopeMap.Guard> deciders = Arrays.asList(
                new StaticScopeMap.Guard(helper + "#u2", true, null, hasMin,
                        ""),
                new StaticScopeMap.Guard(helper + "#u2", false, true, hasMin,
                        ""),
                new StaticScopeMap.Guard(helper + "#u4", true, false, none,
                        ""),
                new StaticScopeMap.Guard(helper + "#u4", false, true, none,
                        ""));
        JsonObject m = predicate("m");
        JsonObject h = predicate("h");
        String refM = RowRuntime.expressionRef(m);
        String refH = RowRuntime.expressionRef(h);
        String refO = RowRuntime.expressionRef(predicate("o"));
        String open = helper + "#u2#2=true asked at ";
        Object[][] rows = {
            // the decisions before the target at 12 (site, event, outcome,
            // predicate, ordinal), what the guard observed, and the
            // condition with the event it stands at, or the open arm named
            {"two constant arms: the decision at the arm it took",
                new Object[][] {{helper + "#u4", 11L, true, h, 1}}, false,
                "(not " + refH + ")", 11L},
            {"the constant arm taken must be what the guard observed",
                new Object[][] {{helper + "#u4", 11L, true, h, 1}}, true,
                null, null},
            {"an open arm taken is the guard's own condition",
                new Object[][] {{helper + "#u2", 11L, true, m, 1}}, true,
                "(ite " + refM + " " + refO + " true)", 11L},
            {"a constant arm beside an open one that never ran names it",
                new Object[][] {{helper + "#u2", 11L, false, m, 2}}, true,
                "open " + open + helper + "#u2#2", null},
            {"under a concrete decision, asked at the nested one",
                new Object[][] {{nested + "#u1", 10L, false, m, 3},
                    {helper + "#u2", 11L, false, null, 2}}, true,
                "open " + open + nested + "#u1#3", null},
            {"concrete, the nested helper's comparison decides it",
                new Object[][] {{nested + "#u1", 10L, true, m, 1},
                    {helper + "#u2", 11L, true, null, 1}}, true,
                "(ite " + refM + " " + refO + " true)", 10L},
            {"never an earlier call's",
                new Object[][] {{helper + "#u4", 5L, true, h, 1},
                    {helper + "#u4", 11L, false, null, 2}}, true, null, null},
            {"nor one after the target",
                new Object[][] {{helper + "#u4", 13L, true, h, 1}}, false,
                null, null}};
        for (Object[] row : rows) {
            RowPublication.Decided found = RowPublication.decided(
                    mappings((Object[][]) row[1]), deciders, 12L, refO,
                    (Boolean) row[2]);
            assertEquals((String) row[0], row[3], found == null ? null
                    : found.open != null ? "open " + found.open
                    : found.condition);
            assertEquals((String) row[0], row[4], found == null
                    || found.open != null ? null : Long.valueOf(found.at));
        }
        Object[][] phis = {
            // the decisions, the arm the guard took, the fatal arm, phi, its
            // event, the open arm
            {new Object[][] {{helper + "#u4", 11L, true, h, 1}}, false, true,
                "(not " + refH + ")", 11L, null},
            {new Object[][] {{helper + "#u4", 11L, true, h, 1}}, false, false,
                refH, 11L, null},
            {new Object[][] {{helper + "#u2", 11L, false, m, 2}}, true, true,
                "true", 12L, open + helper + "#u2#2"},
            {new Object[][] {{helper + "#u2", 11L, false, m, 2}}, true, false,
                "false", 12L, open + helper + "#u2#2"},
            {new Object[][] {}, false, true, "false", 12L, null}};
        for (Object[] row : phis) {
            RowPublication.Phi phi = RowPublication.phi(
                    mappings((Object[][]) row[0]), deciders, null,
                    (Boolean) row[1], (Boolean) row[2], 12L);
            String what = Arrays.deepToString((Object[][]) row[0])
                    + " took=" + row[1] + " fatal=" + row[2];
            assertEquals(what, row[3], phi.phi);
            assertEquals(what, row[4], Long.valueOf(phi.at));
            assertEquals(what, row[5], phi.openArm == null ? null
                    : phi.openArm.toString());
        }
    }

    /** Decision mappings as the VM publishes them: (site, event, outcome,
     *  satisfied predicate or null, ordinal). */
    private static List<JsonObject> mappings(Object[][] decisions) {
        List<JsonObject> mappings = new ArrayList<>();
        for (Object[] each : decisions) {
            JsonObject mapping = decided((String) each[0],
                    (Boolean) each[2], (JsonObject) each[3]);
            mapping.addProperty("vmEventId", (Long) each[1]);
            mapping.addProperty("occurrence", (Integer) each[4]);
            mappings.add(mapping);
        }
        return mappings;
    }

    private static JsonObject predicate(String name) {
        return json("{'_exp':'" + name + "'}");
    }

    private static JsonObject decided(String site, boolean outcome,
                                      JsonObject satisfied) {
        JsonObject mapping = json("{'siteId':'" + site + "','occurrence':1,"
                + "'outcome':" + outcome + ",'witness':{}}");
        if (satisfied != null) {
            mapping.getAsJsonObject("witness").add("sourceSatisfiedPredicate",
                    satisfied);
        }
        return mapping;
    }
}
