package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SharedExpressionTable;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The runtime half of the contract: the lineage an activation is addressed by,
 * and the rows one session publishes.
 */
public class RowRuntimeTest {
    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs-17899/nn0", 0);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void clear() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    /**
     * A scope reaches the work, not the thread: a thread started inside a
     * request and a task submitted to a pool created before it both carry
     * the lineage they were made in.
     *
     * <p>Asserted on the ADDRESS the scope produces rather than on a
     * rendered chain: what an occurrence is addressed by is its causal
     * context (IDENTITY-V3 SS4), so the root role and the window index the
     * carried scope hands the worker are what "the scope reached the work"
     * means -- the innermost role beside them says which hop is running.</p>
     */
    @Test
    public void aCarriedScopeReachesTheThreadThatRunsTheWork()
            throws Exception {
        Object anchor = new Object();
        RuntimeTraceContext.registerSource(anchor, NN);
        long request = RuntimeTraceContext.beginRequest(NN, "balance-block");
        // The api the k was counted under is part of the context: two
        // declared apis of one node are not one root (G11).
        assertEquals("Root:CLIENT/balance-block#1", rootContext());
        assertEquals(Role.CLIENT, Lineage.role());

        // The IPC Server.Call queue: captured at enqueue on this thread,
        // restored at dequeue on a handler that never saw the request.
        final Object carried = RuntimeTraceContext.captureScope();
        final AtomicReference<String> onHandler = new AtomicReference<>("");
        Thread handler = poolThreadCreatedOutsideAnyScope(new Runnable() {
            @Override
            public void run() {
                long scope = RuntimeTraceContext.enterCarriedScope(carried,
                        "IPC_HANDLER", "balance-block");
                onHandler.set(rootContext() + "/" + Lineage.role());
                RuntimeTraceContext.exitCarriedScope(scope);
            }
        });
        handler.start();
        handler.join();
        assertEquals("Root:CLIENT/balance-block#1/IPC_HANDLER",
                onHandler.get());

        // An executor submission: the same carry, captured by the START hook
        // (both passes weave it) and taken back where the work CLAIMS it.
        final Object task = new Object();
        Identity.startWork("<a.Pool: void submit()>#u1", task);
        final AtomicReference<String> onWorker = new AtomicReference<>("");
        Thread worker = poolThreadCreatedOutsideAnyScope(new Runnable() {
            @Override
            public void run() {
                Identity.claimStart(task);
                onWorker.set(rootContext() + "/" + Lineage.role());
                RuntimeTraceContext.releaseCarried();
            }
        });
        worker.start();
        worker.join();
        assertEquals("Root:CLIENT/balance-block#1/EXECUTOR_TASK",
                onWorker.get());
        RuntimeTraceContext.endRequest(request);
        assertFalse("the request's scope ended with it", Lineage.named());
    }

    /**
     * An occurrence that drains a queue closes at the depth it opened: the
     * task it claimed ends with it, not at the next claim (BlockManager's
     * processQueue left its last task's start level standing,
     * FRAME_UNBALANCED) -- while an entry folded into it, which shares its
     * base, closes nothing (the accessor its loop condition calls).
     */
    @Test
    public void anOccurrenceClosesTheWorkItClaimed() throws Exception {
        Object anchor = new Object();
        RuntimeTraceContext.registerSource(anchor, NN);
        long request = RuntimeTraceContext.beginRequest(NN, "block-report");
        final Object task = new Object();
        Identity.startWork("<a.Queue: void enqueue(Runnable)>#u3", task);
        final int[] depths = new int[3];
        Thread drainer = poolThreadCreatedOutsideAnyScope(() -> {
            depths[0] = Identity.depth();
            Identity.occurrence(NN.key(), "REGION.queue", true);
            Identity.claimStart(task);
            int claimed = Identity.depth();
            Identity.occurrence(NN.key(), "REGION.accessor", true);
            Identity.regionExit();
            depths[1] = Identity.depth() - claimed;
            Identity.regionExit();
            depths[2] = Identity.depth();
        });
        drainer.start();
        drainer.join();
        assertEquals("a folded entry's exit leaves the claimed work", 0,
                depths[1]);
        assertEquals(depths[0], depths[2]);
        RuntimeTraceContext.endRequest(request);
    }

    /**
     * A session the campaign withdrew stays withdrawn: a replay killed at its
     * bound still shuts down, and its last table rewrite brought back a
     * directory holding only expressions.json (hdfs-11741 v85, IMPORT).
     */
    @Test
    public void aWithdrawnSessionIsNotWrittenBack() throws Exception {
        SessionDir layout = SessionDir.of(iteration.getRoot().toPath(),
                "withdrawn");
        SessionPublisher session = SessionPublisher.at(layout,
                new SharedExpressionTable.Codec());
        Files.move(layout.dir(), iteration.getRoot().toPath().resolve("aside"));
        session.close();
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_exp", "C_I_1");
        session.expression("EXPR.0000000000000001", constant);
        assertFalse(Files.exists(layout.dir()));
    }

    /**
     * An occurrence opened Lost folds only what is entered still Lost: once
     * the thread has a context a declared region opens its own (a
     * DataXceiver before and after its connection's first message).
     */
    @Test
    public void aLostOccurrenceFoldsNothingEnteredUnderAContext()
            throws Exception {
        Object anchor = new Object();
        RuntimeTraceContext.registerSource(anchor, NN);
        long request = RuntimeTraceContext.beginRequest(NN, "write-block");
        final Object carried = RuntimeTraceContext.captureScope();
        RuntimeTraceContext.endRequest(request);
        final boolean[] folded = new boolean[2];
        final String[] opened = new String[2];
        Thread connection = poolThreadCreatedOutsideAnyScope(() -> {
            opened[0] = Identity.occurrence(NN.key(), "REGION.run", true)
                    .render();
            Identity.occurrence(NN.key(), "REGION.handshake", true);
            folded[0] = Identity.foldedEntry();
            Identity.regionExit();
            long scope = RuntimeTraceContext.enterCarriedScope(carried,
                    "DATA_XCEIVER", "write-block");
            opened[1] = Identity.occurrence(NN.key(), "REGION.check", true)
                    .render();
            folded[1] = Identity.foldedEntry();
            Identity.regionExit();
            RuntimeTraceContext.exitCarriedScope(scope);
            Identity.regionExit();
        });
        connection.start();
        connection.join();
        assertTrue(opened[0], opened[0].contains("/ctx:Lost"));
        assertTrue("entered still Lost, it folds", folded[0]);
        assertFalse("entered under a context, it opens its own", folded[1]);
        assertTrue(opened[1], opened[1].contains("REGION.check")
                && !opened[1].contains("/ctx:Lost"));
    }

    /**
     * A response's endpoint is its request's: the request's scope and the
     * response site -- not the region a pool handler opened before the
     * request came (the NameNode's {@code doAs}, whose index counts that
     * handler's calls), nor what the handler sent before.  Two requests
     * served in one such region answer from two endpoints (the HA token
     * cases' client responses shared one, and the k-th receipt named the
     * wrong call); one request answers from one endpoint whatever its
     * handler served first.
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
                "corr-1", "0", "REQUEST", owner, null);
        String second = CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                "corr-2", "0", "REQUEST", owner, null);
        RuntimeTraceContext.endRequest(calling);
        List<String> both = answered(new String[][]{{"corr-1", first},
                {"corr-2", second}});
        assertFalse("two requests, two responses",
                both.get(0).equals(both.get(1)));
        assertEquals("the second request's response, served first",
                both.get(1), answered(new String[][]{{"corr-2", second}})
                        .get(0));
    }

    /**
     * A response is produced by its request's role scope, which no region
     * opened and so no activation states: its send states it, naming the
     * client's send its anchor answers, so a chain through the response
     * goes on to the client (a NameNode handler's STATE alternatives rest on
     * that chain).
     */
    @Test
    public void aResponseStatesTheRoleScopeThatAnswersAndTheSendItAnswers()
            throws Exception {
        RowRuntime.configure(sessionFile());
        SourceRef client = new SourceRef("CLUSTER_NODE", "CLIENT",
                "hdfs-17899/client0", 0);
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, client);
        long calling = RuntimeTraceContext.beginRequest(client, "append");
        String header = CausynthTraceRecorder.outboundExchange("HADOOP_IPC",
                "corr-1", "0", "REQUEST", owner, null);
        RuntimeTraceContext.endRequest(calling);
        AtomicReference<Endpoint> response = new AtomicReference<>();
        Thread handler = poolThreadCreatedOutsideAnyScope(() -> {
            long inbound = RuntimeTraceContext.enterInbound(header,
                    "HADOOP_IPC", "corr-1", "0", "REQUEST", null, "");
            response.set(Identity.messageSent(NN.key(), "HADOOP_IPC",
                    "corr-1", "RESPONSE", Identity.responseEndpoint(NN.key(),
                            "HADOOP_IPC", "RESPONSE")));
            RuntimeTraceContext.exitInbound(inbound);
        });
        handler.start();
        handler.join();
        RowRuntime.closeSession();

        OccurrenceAddress scope = response.get().occurrence();
        ActivationRow stated = null;
        for (ActivationRow row : RowCodec.readAll(session().activations(),
                RowCodec::readActivation)) {
            if (row.occurrence().equals(scope)) stated = row;
        }
        assertNotNull("the role scope that answered is stated", stated);
        assertFalse("and was no instrumented region", stated.instrumented());
        assertNotNull("with the client's send its anchor answers",
                stated.anchorProducer());
        assertEquals(((CausalContext.Anchor) scope.context())
                .producerEndpointId(), stated.anchorProducer().id());
        assertTrue("which the client occurrence ran",
                stated.anchorProducer().occurrence().node().render()
                        .contains("client0"));
    }

    /** The response endpoints a pooled handler mints for these requests
     *  ({correlation, header}), in one region it opened before any came. */
    private static List<String> answered(String[][] requests)
            throws InterruptedException {
        List<String> ids = new ArrayList<>();
        Thread handler = poolThreadCreatedOutsideAnyScope(() -> {
            Identity.occurrence(NN.key(), "REGION.doAs", true);
            for (String[] request : requests) {
                long inbound = RuntimeTraceContext.enterInbound(request[1],
                        "HADOOP_IPC", request[0], "0", "REQUEST", null, "");
                ids.add(Identity.responseEndpoint(NN.key(), "HADOOP_IPC",
                        "RESPONSE").id());
                RuntimeTraceContext.exitInbound(inbound);
            }
            Identity.regionExit();
        });
        handler.start();
        handler.join();
        return ids;
    }

    /** The causal context the calling thread's root hop states. */
    private static String rootContext() {
        return CausalContext.of(Lineage.rootRole(), Lineage.rootApi(),
                Lineage.rootWindowIndex()).render();
    }

    /** One address, by the contract constructor the runtime calls. */
    private static OccurrenceAddress address(String nodeKey, String regionId,
                                             CausalContext context,
                                             ExecutionIndex index) {
        return OccurrenceAddress.of(NodeId.parse(nodeKey), regionId, context,
                index);
    }

    /**
     * A daemon tick is a root of its own: the NameNode's key rotation is
     * addressed by its role and the k-th tick of the window, where before
     * it was addressed by nothing at all.
     */
    @Test
    public void aDaemonTickIsAddressedByItsRoleAndItsWindowLocalK() {
        Object anchor = new Object();
        RuntimeTraceContext.registerSource(anchor, NN);
        List<OccurrenceAddress> addresses = new ArrayList<>();
        for (int tick = 0; tick < 2; tick++) {
            long token = CausynthTraceRecorder.beginDaemonTick(anchor,
                    "HEARTBEAT_TICK");
            addresses.add(address("hdfs-17899/nn0#epoch0",
                    "REGION.aaa1cfd7",
                    CausalContext.of(Role.of("HEARTBEAT_TICK"), "",
                            Lineage.rootWindowIndex()),
                    ExecutionIndex.empty()));
            CausynthTraceRecorder.endDaemonTick(token);
        }
        assertEquals("Root:HEARTBEAT_TICK#1",
                addresses.get(0).context().render());
        assertEquals("Root:HEARTBEAT_TICK#2",
                addresses.get(1).context().render());
        // Two ticks, two identities: the window index is the tick's own
        // ordinal, which is inherent to the role.
        assertFalse(addresses.get(0).id().equals(addresses.get(1).id()));

        // An unattributable scope degrades rather than disappearing.
        OccurrenceAddress lost = Identity.roleOccurrence(
                "hdfs-17899/nn0#epoch0", Role.of("KEY_MANAGER_TICK"));
        assertTrue(lost.lineageLost());
        assertEquals("ROLE.KEY_MANAGER_TICK", lost.regionId());
        // A node this run cannot name addresses nothing: a guessed node is
        // a wrong causal chain.
        assertNull(Identity.occurrence("", "REGION.aaa1cfd7", false));
        executionIndexIsStableUnderUnrelatedCalls();
    }

    /**
     * Counts start at the window.  hdfs-11741's balancer opens its request
     * before the window and sends a varying number of set-up RPCs under it;
     * the first send inside the window must be the same endpoint whatever
     * the set-up sent, or its anchor -- and every context downstream of it
     * -- differs between the recording and the replay.
     *
     * <p>Frames too: an iteration counted before the window stands at 0 in
     * an address made inside it.  hdfs-17899-bug1's DataXceiver threads
     * inherit {@code instantiateDataNode@k} for the k-th DataNode started,
     * and which started node plays the case's target was random -- @0 in the
     * recording, @1 in the replay.</p>
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
            Endpoint second = Identity.endpointAt(at, "HADOOP_IPC#REQUEST",
                    0);
            assertFalse("inside the window the count goes on",
                    second.id().equals(firstInWindow.get(
                            firstInWindow.size() - 1).id()));
            RuntimeTraceContext.endRequest(request);
        }
        assertEquals(firstInWindow.get(0).id(), firstInWindow.get(1).id());
        assertTrue(firstInWindow.get(0).siteIndex().render(),
                firstInWindow.get(0).siteIndex().render()
                        .endsWith("HADOOP_IPC#REQUEST@0"));

        Identity.resetForTests();
        long first = Identity.enterFrame("Cluster.startDataNodes()#u1", null);
        Identity.exitFrame(first);
        long second = Identity.enterFrame("Cluster.startDataNodes()#u1",
                null);
        assertEquals("Cluster.startDataNodes()#u1@1",
                Identity.siteIndex().render());
        RecordingWindow.open();
        assertEquals("set-up history is not part of the address",
                "Cluster.startDataNodes()#u1@0",
                Identity.siteIndex().render());
        Identity.exitFrame(second);
        long third = Identity.enterFrame("Cluster.startDataNodes()#u1", null);
        Identity.exitFrame(third);
        long fourth = Identity.enterFrame("Cluster.startDataNodes()#u1",
                null);
        assertEquals("inside the window the count stands",
                "Cluster.startDataNodes()#u1@1",
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
        RowRuntime.configure(sessionFile());
        OccurrenceAddress producer = address(
                "hdfs-17899/nn0#epoch0", "REGION.2392e4b7",
                CausalContext.of(Role.of("HEARTBEAT_TICK"), "", 3),
                ExecutionIndex.parse("PBHelper.convert()#u2@0"));
        Endpoint exported = RowRuntime.exported(producer, 61L,
                "XCH.resp.block-key-id", 4242L, "hadoop-ipc-7", 0, null, "J",
                "119981");
        assertNotNull(exported);

        OccurrenceAddress consumer = RowRuntime.occurrenceHere(
                "hdfs-17899/target-dn#epoch0", "XCH.resp.block-key-id");
        assertTrue(consumer.lineageLost());
        Endpoint attached = RowRuntime.attachedAt(
                RowRuntime.nextEndpoint(consumer, "XCH.resp.block-key-id", 0),
                62L, "XCH.resp.block-key-id", 4242L, "hadoop-ipc-7",
                "HOFF.5e10236f", "J", "119981", false, "");
        RowRuntime.closeSession();

        List<AttachRow> rows = RowCodec.readAll(
                session().attaches(), RowCodec::readAttach);
        assertEquals(1, rows.size());
        AttachRow row = rows.get(0);
        assertEquals(attached, row.endpoint());
        assertEquals(exported, row.producer());
        assertFalse(row.interaction().producer().occurrence().lineageLost());
        assertTrue(row.endpoint().occurrence().lineageLost());
        // Pairing is the run's own RECORDED evidence and nothing else: the
        // handle the VM handed out, or the correlation the workload named
        // with the port.  A delivery on the same port that carries neither
        // pairs to nothing -- it used to take the port's last producer,
        // which states a chain nobody made -- and another port's delivery
        // takes no producer from this one either.
        assertNull("no handle and no correlation is no pairing",
                Interactions.pairing(
                        "XCH.resp.block-key-id", 0L, "").producer());
        assertNull("another port is another interaction",
                Interactions.pairing(
                        "XCH.resp.other", 0L, "hadoop-ipc-7").producer());
        assertEquals("the handle is the strongest evidence there is",
                exported,
                Interactions.pairing("XCH.resp.other", 4242L, "").producer());
        // And the pairing states WHICH of the two keys answered, so a row
        // paired on the message rather than on the staged expression is not
        // read as the stronger fact.
        assertEquals("HANDLE",
                Interactions.pairing("XCH.resp.other", 4242L, "").key());
        assertEquals("", Interactions.pairing(
                "XCH.resp.block-key-id", 0L, "").key());
    }

    /** Every row kind round-trips through the codec it is written with. */
    @Test
    public void theSessionRoundTripsEveryRowKind() throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress occurrence = address(
                "hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
        Endpoint endpoint = RowRuntime.nextEndpoint(occurrence, "XCH.port", 0);
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_exp", "M_J_serial");

        RowRuntime.decision(occurrence, 12L, "Klass.m()#u8", 1, true,
                expression);
        // hdfs-17960's marker decision: the source reads
        // `if marker == 0 goto`, the run had marker true so the jump fell
        // through, and the VM published the constraint it SATISFIED,
        // `marker != false`.  The row states the JUMP's predicate --
        // `marker == false`, the one spelling of this site that does not
        // move between arms or replays -- and outcome=false, the arm.  The
        // conjunct a consumer forms, `(not term)`, is the satisfied
        // constraint back again; the flipped replay states the same term
        // with outcome=true, which is what lets a flip be seen at all.
        RowRuntime.decision(occurrence, 13L, "SnapshotManager.delete()#u7", 1,
                false, markerJumpCondition("M_Z_marker"));
        // A decision the VM gave no event id: taken before path recording
        // opened, so it captured no site condition and states no term.  Its
        // seq used to be the session's HIGH-WATER MARK -- "no VM clock" and
        // "the latest VM event" came out as one integer, and Arms
        // #pathCondition keeps every decision seq < before, so whether this
        // row sat inside a prefix was decided by where the mark stood.  On
        // the 17960 corpus 46/46/52 decision rows per session share a seq
        // with another row and exactly one of each group owns it.
        RowRuntime.decision(occurrence, 0L, "Klass.beforeRecording()#u2", 1,
                true, null);
        RowRuntime.exported(occurrence, 4L, "XCH.port", 7L, "c1", 0,
                expression, "J", "1");
        RowRuntime.attachedAt(endpoint, 9L, "XCH.port", 7L, "c1", "v_H", "J",
                "1", true, "2");
        // A CLASS THE JVM MINTS PER RUN IS NOT AN IDENTITY.  The site of a
        // state event carries the class the event stood in, and two of
        // those are named by the runtime with a counter that starts over in
        // every JVM: the reflection accessors, inflated on the k-th
        // reflective call this JVM happened to make, and the lambda
        // proxies.  Two recordings of ONE write then state two sites, and
        // downstream that is two worlds: on the hdfs-11741 campaign #3
        // corpus 75 of wave 2's 187 affected (task, session) pairs, and 8
        // of the 11 worlds the witness arm was owed in, were
        // GeneratedMethodAccessor23 against GeneratedMethodAccessor22 in
        // one write site and nothing else.  The number goes at the mint --
        // here, where the VM's name is converted -- so a row already
        // written keeps its own spelling and the contract stays a codec.
        String inflatedOnce = LoggedEventSites.site(loggedAt(
                "sun/reflect/GeneratedMethodAccessor23", "invoke",
                "(Ljava/lang/Object;[Ljava/lang/Object;)"
                        + "Ljava/lang/Object;", 56), "L", -1L, true);
        assertEquals("the accessor's inflation number is not part of where "
                        + "the write happened",
                inflatedOnce, LoggedEventSites.site(loggedAt(
                        "sun/reflect/GeneratedMethodAccessor7", "invoke",
                        "(Ljava/lang/Object;[Ljava/lang/Object;)"
                                + "Ljava/lang/Object;", 56), "L", -1L, true));
        assertTrue("and what is left names the accessor: " + inflatedOnce,
                inflatedOnce.startsWith(
                        "sun.reflect.GeneratedMethodAccessor#invoke"));
        String proxied = LoggedEventSites.site(loggedAt(
                "example/Keys$$Lambda$14/1234567890", "apply",
                "(Ljava/lang/Object;)Ljava/lang/Object;", 3), "L", -1L, false);
        assertEquals("nor is a lambda proxy's", proxied,
                LoggedEventSites.site(loggedAt(
                        "example/Keys$$Lambda$3/987654321", "apply",
                        "(Ljava/lang/Object;)Ljava/lang/Object;", 3),
                        "L", -1L, false));
        assertTrue("and what is left names the lambda's outer class: "
                + proxied, proxied.startsWith("example.Keys$$Lambda#apply"));
        // A name the PROGRAM chose is untouched, counter or no counter.
        assertTrue(LoggedEventSites.site(loggedAt(
                "org/apache/hadoop/hdfs/security/token/block/"
                        + "BlockTokenSecretManager", "addKeys", "()V", 21),
                "L", -1L, true).startsWith("org.apache.hadoop.hdfs.security"
                + ".token.block.BlockTokenSecretManager#addKeys"));
        // And the endpoint mint puts the site and the innermost frame of
        // its index in that ONE spelling, so the two cannot disagree.
        assertEquals("sun.reflect.GeneratedMethodAccessor#invoke()V#56:WRITE",
                RowRuntime.nextEndpoint(occurrence, Endpoint.stateSite(
                        "sun.reflect.GeneratedMethodAccessor23", "invoke",
                        "()V", 56, true), 0).site());

        LocationId location = LocationId.of(LocationKind.INSTANCE, "22", "24");
        // The site is spelled once, by the contract's renderer, from what the
        // VM's log states about the event -- including the descriptor, so two
        // overloads of one name are two sites.
        RowRuntime.write(occurrence, 10L,
                Endpoint.stateSite("java.util.concurrent.atomic.AtomicInteger",
                        "getAndIncrement", "()I", 12, true),
                location, 125L, rmwExpression(), "",
                "Caller.body()#u9@1");
        // A String method's result states no type of its own, and its
        // operands' are not its own: a concat is a String (f4 visible-gs:
        // java.io.File.path's version published no row, and the path that
        // read it was refused).
        JsonObject concat = new JsonObject();
        concat.addProperty("_type", "OpStrExpression");
        concat.addProperty("_name", "concat");
        com.google.gson.JsonArray operands = new com.google.gson.JsonArray();
        operands.add(rmwExpression());
        concat.add("_param_list", operands);
        RowRuntime.write(occurrence, 13L,
                Endpoint.stateSite("java.io.File", "<init>",
                        "(Ljava/lang/String;)V", 4, true),
                LocationId.of(LocationKind.INSTANCE, "49", "32"), 127L,
                concat, "", "Caller.body()#u9@1");
        // A null stored into a tracked reference field states no class, and
        // is a reference write all the same (17960 v64: a diff's cleared
        // posteriorDiff published no row, and the path reading it was
        // refused).
        RowRuntime.write(occurrence, 12L,
                Endpoint.stateSite("Diff", "setPosterior", "(LDiff;)V", 2,
                        true),
                LocationId.of(LocationKind.INSTANCE, "6", "40"), 126L,
                nullExpression(), "",
                "Caller.body()#u9@1");
        RowRuntime.read(occurrence, 14L,
                Endpoint.stateSite("java.util.concurrent.atomic.AtomicInteger",
                        "get", "()I", 2, false),
                location, 125L, "s", "J", "9", "", ReadRow.UNKNOWN_VERSION);
        // The tool's own wait set states no row, read or written.
        String waits = Endpoint.stateSite(TimedWaits.class.getName(), "send",
                "(Ljava/lang/Object;Z)Z", 34, true);
        RowRuntime.write(occurrence, 16L, waits,
                LocationId.of(LocationKind.INSTANCE, "350", "24"), 6254L,
                rmwExpression(), "", "Caller.body()#u9@1");
        RowRuntime.read(occurrence, 16L, waits,
                LocationId.of(LocationKind.INSTANCE, "350", "24"), 6253L, "w",
                "I", "1", "", ReadRow.UNKNOWN_VERSION);
        RowRuntime.rootMint(occurrence, 11L, "HDFS.BLOCK_KEY.SERIAL_NO",
                "M_I_1", RootKind.INTEGRAL, "3", "3", "6", true, 0L);
        RowRuntime.rootMint(occurrence, 13L,
                "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED", "M_Z_marker",
                RootKind.MARKER, "true", "", "", true, 0L);
        RowRuntime.target(occurrence, 15L, "Klass.m()#u8", expression, true,
                true, true);
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, "s", "d");
        // THE DOOR NEVER THROWS INTO THE WORKLOAD.  GapRow.of puts subject
        // through Fields.text, which refuses a blank one -- correctly, a
        // refusal that reports a category is not evidence -- and that
        // refusal would leave a woven hook and change the execution the
        // rows describe.  An unnamed subject is answered by the session
        // that met it, and the detail says the caller named nothing.
        RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, "   ",
                "a caller that named no subject");
        // A declared region input is a READ of the location it stands for,
        // spelled the way the write log spells it, so the placeholder joins
        // the write above rather than naming a second location nobody wrote.
        placeholder(occurrence, placeholderRow("a", vmRead(125L)), "M_I_placeholder",
                Collections.<String, String[]>emptyMap());
        placeholder(occurrence, placeholderRow("b", null), "M_I_unversioned",
                Collections.<String, String[]>emptyMap());
        // The mint symbolized the object, not the int cell: the sorts
        // disagree (L against I), so the row states neither.  A reference
        // mint for a reference cell agrees and does publish (P2l).
        placeholder(occurrence, placeholderRow("f", null),
                "P_L'org/apache/hadoop/hdfs/server/namenode/snapshot/"
                        + "Snapshot'_",
                Collections.<String, String[]>emptyMap());
        // The mint's own shadow store is not a write, so the version this
        // read OBSERVED is the last real write before it -- version 125,
        // which the WriteRow above states -- and the row is the anchor's
        // join to that writer.
        placeholder(occurrence, placeholderRow("c", null), "M_I_installed",
                Collections.singletonMap("M_I_installed",
                        new String[]{"INSTANCE_FIELD/22#28", "126", "125"}));
        // A second declared port of the SAME cell is a second read event
        // and states its own row: two calls of a declared accessor in one
        // occurrence are two values.
        placeholder(occurrence, secondPortRow(), "M_I_second",
                Collections.singletonMap("M_I_second",
                        new String[]{"INSTANCE_FIELD/22#28", "127", "125"}));
        // The SAME read event reached again -- the same mint row, from an
        // activation the read also ran inside -- states no second row.
        placeholder(occurrence, placeholderRow("c", null), "M_I_installed",
                Collections.singletonMap("M_I_installed",
                        new String[]{"INSTANCE_FIELD/22#28", "126", "125"}));
        // A mint with no write before it states -1 and pins the decimal.
        placeholder(occurrence, placeholderRow("e", null), "M_I_unwritten",
                Collections.singletonMap("M_I_unwritten",
                        new String[]{"INSTANCE_FIELD/22#32", "126", "-1"}));
        // An over-pop of the region stack is a named refusal.  The entry
        // hook is the one push and #closeRegionEntry the one pop; a second
        // pop under an open activation closes a region that activation
        // never opened, and the only balance check there was compared frame
        // depth, which such a pop does not move.
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Loader.loadEditRecords()#u4", null);
        Identity.occurrence(NN.key(), "REGION.loader", true);
        long nested = ConcolicRegionRuntime.enterRegionEntry("REGION.apply",
                "<a.Loader: long applyEditLogOp()>", null);
        Identity.regionExit();
        ConcolicRegionRuntime.exitRegionEntry(nested);

        RowRuntime.closeSession();

        SessionDir dir = session();
        List<DecisionRow> decisions = RowCodec.readAll(dir.decisions(),
                RowCodec::readDecision);
        assertEquals(3, decisions.size());
        assertEquals(occurrence, decisions.get(0).occurrence());
        assertTrue(decisions.get(0).term().startsWith("EXPR."));
        // seq == 0 IS the statement "this row carries no VM clock", and it
        // never borrows an order it does not have.
        assertEquals("a decision with no VM event id states 0", 0L,
                decisions.get(2).seq());
        assertEquals("and no term, so it is in no path condition either",
                "", decisions.get(2).term());
        assertFalse("a clockless decision adds no conjunct at any prefix",
                Arms.predicate(Arms.conjunct(decisions.get(2))));
        List<ExportRow> exports = RowCodec.readAll(dir.exports(),
                RowCodec::readExport);
        assertEquals(1, exports.size());
        assertEquals(7L, exports.get(0).handle());
        assertEquals(4L, exports.get(0).seq());
        assertEquals("J", exports.get(0).javaType());
        List<AttachRow> attaches = RowCodec.readAll(dir.attaches(),
                RowCodec::readAttach);
        assertTrue(attaches.get(0).answered());
        assertEquals("2", attaches.get(0).answeredValue());
        List<WriteRow> writes = RowCodec.readAll(dir.writes(),
                RowCodec::readWrite);
        assertEquals("the tool's own wait set is no write", 3, writes.size());
        assertEquals(125L, writes.get(0).version());
        assertEquals(10L, writes.get(0).seq());
        assertEquals("java.util.concurrent.atomic.AtomicInteger"
                        + "#getAndIncrement()I#12:WRITE",
                writes.get(0).endpoint().site());
        assertEquals("Caller.body()#u9@1",
                writes.get(0).endpoint().siteIndex().render());
        // An operator node states no type of its own; the run states the
        // operands', so an int RMW is not published as an Object.
        assertEquals("I", writes.get(0).javaType());
        assertEquals("a written null is a reference", "L",
                writes.get(2).javaType());
        assertEquals("a String method's result is a String",
                "Ljava/lang/String;", writes.get(1).javaType());
        List<ReadRow> reads = RowCodec.readAll(dir.reads(),
                RowCodec::readRead);
        assertEquals(125L, reads.get(0).observedVersion());
        assertEquals(14L, reads.get(0).seq());
        assertEquals("the placeholder reads the location the write wrote",
                writes.get(0).location(), reads.get(1).location());
        assertEquals("at the version the write states",
                writes.get(0).version(), reads.get(1).observedVersion());
        assertEquals("M_I_placeholder", reads.get(1).symbol());
        // A declared input the VM numbered no location for states NO row:
        // the location used to be built out of the Java field signature --
        // INSTANCE/<declaring class>#<field name> -- which is a location the
        // VM never stated and which no write of the same storage spells, so
        // the composer joined reads on a location nothing wrote.
        for (ReadRow read : reads) {
            assertFalse("no row names a location the VM did not state",
                    LocationId.of(LocationKind.INSTANCE,
                            "java.util.concurrent.atomic.AtomicInteger",
                            "value").equals(read.location()));
        }
        // The mint is not a write -- no WriteRow states its version -- so
        // the row names the VM's location and the LAST REAL WRITE before
        // the mint: the placeholder read is the anchor's JOIN to the
        // occurrence that wrote the cell.
        assertEquals(LocationKind.INSTANCE, reads.get(2).location().kind());
        assertEquals(125L, reads.get(2).observedVersion());
        assertEquals("2", reads.get(2).concreteValue());
        ReadRow unwritten = null;
        for (ReadRow read : reads) {
            if ("M_I_unwritten".equals(read.symbol())) unwritten = read;
        }
        assertNotNull("the unwritten mint states a row", unwritten);
        // CONTRACT v2.4: the placeholder states the version its own mint
        // published, which is what a term's ReadFrom names, beside the last
        // real write it observed, which is the join to the writer.
        assertEquals(126L, unwritten.mintVersion());
        assertEquals(ReadRow.UNKNOWN_VERSION,
                reads.get(0).mintVersion());
        assertEquals("no write precedes the mint: -1 and the decimal",
                ReadRow.UNKNOWN_VERSION, unwritten.observedVersion());
        assertEquals("2", unwritten.concreteValue());
        assertEquals("a reference-sorted mint states no row; a mint with no"
                        + " VM location states no row; a second mint of one"
                        + " cell (version 127) is a second mint and states"
                        + " one; the SAME mint reached twice states one row,"
                        + " whatever occurrence or read event reached it",
                5, reads.size());
        List<RootMintRow> roots = RowCodec.readAll(dir.roots(),
                RowCodec::readRootMint);
        // The corpus invariant: a decision whose term is over declared root
        // symbols only holds exactly when the row says its outcome does.
        // This is what tells "the term held" apart from "the jump was
        // taken", and the two differ at every fall-through branch.
        Map<String, String> recorded = new java.util.HashMap<>();
        for (RootMintRow root : roots) {
            recorded.put(root.symbol(), root.recordedValue());
        }
        Map<String, JsonObject> table =
                RowCodec.readExpressions(dir.expressions()).expressions();
        int checked = 0;
        for (DecisionRow row : decisions) {
            Boolean held = holdsAtRoots(table.get(row.term()), recorded,
                    table);
            if (held == null) continue;
            // `outcome ? term : (not term)` is the constraint the run
            // satisfied, so a term over declared roots alone holds exactly
            // when the row's arm says it does.
            assertEquals("the conjunct of " + row.siteId() + " is satisfied",
                    held, Boolean.valueOf(row.outcome()));
            checked++;
        }
        assertEquals("one decision is over declared roots only", 1, checked);
        assertEquals(RootKind.INTEGRAL, roots.get(0).kind());
        assertEquals(11L, roots.get(0).seq());
        assertFalse(roots.get(0).pinned());
        // The kind is read off the declaration: a configured source states
        // no javaType of its own and carries it on the symbol it minted, so
        // a declared boolean root is a MARKER and not an INTEGRAL with a
        // range of two.
        assertEquals(RootKind.MARKER, kindOf(booleanConfiguredSourceRow()));
        assertEquals(RootKind.INTEGRAL, kindOf(placeholderRow("d", null)));
        // ONE ROOT PER SYMBOL, and it is the mint that MADE the symbol.  A
        // declared read whose field already carried a propagated expression
        // minted nothing and says so, so the only name vmSymbol can give it
        // is the first leaf of what it read back -- another mint's symbol.
        // 11741's three expiry hooks in nn0 updateKeys read back
        // timer.now() + k*keyUpdateInterval + tokenLifetime over that
        // region's declared clock cell and each published a root row
        // carrying the CLOCK's symbol with the EXPIRY's value: six BLOCKING
        // "one solver name for 2 roots" refusals out of COMPOSE.
        assertTrue("a mint that made its symbol is a root",
                minted(booleanConfiguredSourceRow()));
        assertFalse("a read that reused one is not",
                minted(reusedConfiguredSourceRow()));
        List<TargetRow> targets = RowCodec.readAll(dir.targets(),
                RowCodec::readTarget);
        assertTrue(targets.get(0).observedFatal());
        List<GapRow> gaps = RowCodec.readAll(dir.gaps(), RowCodec::readGap);
        assertTrue(gaps.get(0).blocking());
        boolean unnamedSubject = false;
        for (GapRow gap : gaps) {
            if (!gap.detail().startsWith("this LINEAGE_LOST names no"
                    + " subject")) {
                continue;
            }
            unnamedSubject = true;
            assertEquals("the session that met it is what is left to name",
                    gap.sessionId(), gap.subject());
        }
        assertTrue("a gap whose caller named nothing is a row, not a throw",
                unnamedSubject);
        // And the refusal of the location-less mint is a row of its own, so
        // "this input read nothing the run can name" is stated rather than
        // replaced by a fabricated location.
        boolean unstatedLocation = false;
        for (GapRow gap : gaps) {
            if (gap.kind() == GapKind.DECLARATION_MISSING
                    && gap.detail().contains("states no VM location")) {
                unstatedLocation = true;
            }
        }
        assertTrue("the location-less declared input is named", 
                unstatedLocation);
        GapRow unbalanced = gaps.get(gaps.size() - 1);
        assertEquals(GapKind.FRAME_UNBALANCED, unbalanced.kind());
        assertTrue("an over-pop is BLOCKING, not a renumbered anchor",
                unbalanced.blocking());
        assertTrue(unbalanced.detail(), unbalanced.detail().contains(
                "closed with 0 region(s) open and opened with 1"));
        assertTrue(unbalanced.detail(), unbalanced.detail().contains(
                "a region it did not open was closed under it"));
        // What the read-out keeps of the VM's envelope is what a write or
        // read endpoint can be built from: the bytecode site the event stood
        // at and the activation that ran it.  The reduction used to drop
        // both and the whole read log, which is why every write endpoint
        // carried its location as a site and the empty index.
        JsonObject reduced = SharedStateCapture.writeLogRecord(
                "INSTANCE_FIELD/2#24",
                vmEnvelopeRecord().getAsJsonObject("envelope"));
        JsonObject envelope = reduced.getAsJsonObject("envelope");
        JsonObject version = envelope.getAsJsonArray("versions").get(0)
                .getAsJsonObject();
        assertEquals(41L, version.get("regionEnterEventId").getAsLong());
        assertEquals("getAndIncrement", version.getAsJsonObject("site")
                .get("methodName").getAsString());
        JsonObject read = envelope.getAsJsonArray("reads").get(0)
                .getAsJsonObject();
        assertEquals(76L, read.get("readEventId").getAsLong());
        assertEquals(41L, read.get("regionEnterEventId").getAsLong());
        assertEquals("()I", read.getAsJsonObject("site")
                .get("methodDescriptor").getAsString());
        // The expressions the refs name are in the session's own table.
        assertTrue(Files.exists(dir.expressions()));
        assertTrue(RowCodec.readExpressions(dir.expressions())
                .refs().contains(exports.get(0).expressionRef()));
    }

    /**
     * A version names the region that wrote it wholly, or -- a store
     * outside every region (VM 22f2707a1) -- not at all; half a writer is a
     * malformed envelope.  Refusing the whole-less one dropped the location
     * and every read of it (commit-gs v73: the GS reads at both later
     * targets).
     */
    @Test
    public void aVersionNamesItsWritingRegionWhollyOrNotAtAll()
            throws Exception {
        java.lang.reflect.Method fault = SharedStateCapture.class
                .getDeclaredMethod("versionFault", JsonObject.class,
                        boolean.class, java.util.Set.class);
        fault.setAccessible(true);
        for (Object[] each : new Object[][]{
                {41L, "REGION.a", "TASK.a", 7L, true},
                {0L, "", "", 0L, true},
                {41L, "", "TASK.a", 7L, false}}) {
            JsonObject version = new JsonObject();
            version.addProperty("fieldVersionId", 50L);
            version.addProperty("versionKind", "WRITE");
            version.addProperty("regionEnterEventId", (Long) each[0]);
            version.addProperty("regionId", (String) each[1]);
            version.addProperty("taskId", (String) each[2]);
            version.addProperty("writerContextId", (Long) each[3]);
            String said = (String) fault.invoke(null, version, false,
                    new java.util.HashSet<Object>());
            assertEquals(Arrays.toString(each), each[4],
                    !said.contains("names no writer case"));
        }
    }

    /** One tracked location, as the VM's read-out states it. */
    private static JsonObject vmEnvelopeRecord() {
        JsonObject site = new JsonObject();
        site.addProperty("className",
                "java/util/concurrent/atomic/AtomicInteger");
        site.addProperty("methodName", "getAndIncrement");
        site.addProperty("methodDescriptor", "()I");
        site.addProperty("bci", 12);
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 50L);
        version.addProperty("versionKind", "RMW");
        version.addProperty("regionEnterEventId", 41L);
        version.addProperty("writerContextId", 7L);
        version.add("site", site);
        version.add("expression", rmwExpression());
        JsonObject read = new JsonObject();
        read.addProperty("readEventId", 76L);
        read.addProperty("regionEnterEventId", 41L);
        read.addProperty("readerContextId", 7L);
        read.add("site", site);
        JsonArray versions = new JsonArray();
        versions.add(version);
        JsonArray reads = new JsonArray();
        reads.add(read);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind", "SHARED_FIELD_VERSIONS");
        envelope.addProperty("schemaVersion", 1);
        envelope.add("versions", versions);
        envelope.add("reads", reads);
        envelope.addProperty("readLogTruncated", false);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", "INSTANCE_FIELD/2#24");
        record.add("envelope", envelope);
        return record;
    }

    /** {@code marker == false}, the predicate the jump is taken under. */
    private static JsonObject markerJumpCondition(String symbol) {
        JsonObject marker = new JsonObject();
        marker.addProperty("_type", "SymbolExpression");
        marker.addProperty("_java_type", "Z");
        marker.addProperty("_exp", symbol);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ConsumerBoundaryExpression");
        read.addProperty("boundaryKind", "FIELD_READ");
        read.addProperty("_java_type", "Z");
        read.add("expression", marker);
        JsonObject literal = new JsonObject();
        literal.addProperty("_type", "ConstExpr");
        literal.addProperty("_java_type", "Z");
        literal.addProperty("_exp", "Y_Z_0");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.add("_left", read);
        predicate.addProperty("_op", "==");
        predicate.add("_right", literal);
        return predicate;
    }

    /**
     * Whether one term holds at the roots the session recorded, or null when
     * it is not a comparison over declared roots and literals alone.
     *
     * <p>Deliberately small: {@code Y_<sort>_<value>} is the VM's spelling
     * of a literal and a root's {@code recordedValue} is what the run read,
     * so an equality over the two is decidable from the rows without a
     * solver.  Anything else is not this invariant's business.</p>
     */
    private static Boolean holdsAtRoots(JsonObject term,
                                        Map<String, String> roots,
                                        Map<String, JsonObject> table) {
        if (term == null
                || !"BinaryExpression".equals(text(term, "_type"))) {
            return null;
        }
        String operator = text(term, "_op");
        if (!"==".equals(operator) && !"!=".equals(operator)) return null;
        String left = valueAtRoots(term.get("_left"), roots, table);
        String right = valueAtRoots(term.get("_right"), roots, table);
        if (left == null || right == null) return null;
        return Boolean.valueOf("==".equals(operator)
                ? left.equals(right) : !left.equals(right));
    }

    private static String valueAtRoots(com.google.gson.JsonElement node,
                                       Map<String, String> roots,
                                       Map<String, JsonObject> table) {
        if (node == null || !node.isJsonObject()) return null;
        JsonObject object = node.getAsJsonObject();
        String symbol = text(object, "_exp");
        if (roots.containsKey(symbol)) return normalized(roots.get(symbol));
        if (symbol.startsWith("Y_")) {
            int mark = symbol.lastIndexOf('_');
            return mark < 0 ? null : normalized(symbol.substring(mark + 1));
        }
        com.google.gson.JsonElement nested = object.get("expression");
        return nested == null ? null : valueAtRoots(nested, roots, table);
    }

    /** {@code true}/{@code 1} and {@code false}/{@code 0} are one value. */
    private static String normalized(String value) {
        String stated = value == null ? "" : value.trim();
        if ("true".equals(stated)) return "1";
        if ("false".equals(stated)) return "0";
        return stated;
    }

    private static String text(JsonObject object, String field) {
        com.google.gson.JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                ? value.getAsString() : "";
    }

    /**
     * One logged event's node, carrying only the site the VM states for it.
     *
     * <p>The class is in the VM's own form, with slashes: converting it is
     * what {@code LoggedEventSites#site} does, and it is the one place a
     * per-run name is taken out of an identity.</p>
     */
    private static JsonObject loggedAt(String className, String method,
                                       String descriptor, int bci) {
        JsonObject site = new JsonObject();
        site.addProperty("className", className);
        site.addProperty("methodName", method);
        site.addProperty("methodDescriptor", descriptor);
        site.addProperty("bci", bci);
        JsonObject node = new JsonObject();
        node.add("site", site);
        return node;
    }

    /** {@code Y_I_0 + Y_I_1}, as the VM publishes a linearized RMW. */
    /** The VM's null symbol, which states no class. */
    private static JsonObject nullExpression() {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "");
        expression.addProperty("_exp", "N");
        return expression;
    }

    private static JsonObject rmwExpression() {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "ConstExpr");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "Y_I_0");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_1");
        JsonObject binary = new JsonObject();
        binary.addProperty("_type", "BinaryExpression");
        binary.add("_left", left);
        binary.addProperty("_op", "+");
        binary.add("_right", right);
        return binary;
    }

    /** A second declared port of one cell: another read, another event. */
    private static JsonObject secondPortRow() {
        JsonObject row = placeholderRow("g", null);
        row.addProperty("eventSeq", 19L);
        return row;
    }

    /** One manual mint row, as {@code recordManualSymbolization} writes it. */
    private static JsonObject placeholderRow(String port, JsonObject read) {
        JsonObject row = new JsonObject();
        row.addProperty("portId", "REGION.f0132fca.in." + port);
        row.addProperty("occurrenceId", "hdfs-17960/nn0#epoch1/region/"
                + "REGION.f0132fca#1");
        row.addProperty("rawSymbol", read == null
                ? "M_I_unversioned" : "M_I_placeholder");
        row.addProperty("javaType", "int");
        row.addProperty("fieldSignature",
                "<java.util.concurrent.atomic.AtomicInteger: int value>");
        row.addProperty("observedValue", "2");
        row.addProperty("recordedValue", "2");
        row.addProperty("eventSeq", 16L);
        if (read != null) row.add("expression", read);
        return row;
    }

    /** The VM's read of a tracked location, as it spells one. */
    private static JsonObject vmRead(long version) {
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "INSTANCE_FIELD");
        location.addProperty("ownerSymRid", 22);
        location.addProperty("slot", 24);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty("_exp", "M_I_placeholder");
        read.addProperty("_java_type", "I");
        read.add("location", location);
        read.addProperty("observedVersion", version);
        return read;
    }

    /** A configured source mints through the VM's label and states no type. */
    private static JsonObject booleanConfiguredSourceRow() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "Z");
        symbol.addProperty("_exp", "M_Z_field_SRC.50c885b3_a/Manager");
        JsonObject row = new JsonObject();
        row.addProperty("sourceId", "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED");
        row.addProperty("recordedValue", "true");
        row.add("expression", symbol);
        return row;
    }

    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    java.util.Map<String, String[]> installed)
            throws Exception {
        placeholder(occurrence, row, symbol, installed, false);
    }

    /**
     * The same mint, as one that also publishes a RootMintRow.
     *
     * <p>{@code placeholder} is of ONE mint store, not of a symbol's whole
     * table: a symbol minted twice has two stores and owes a row for each,
     * so the caller picks which one this row is of.  These helpers keep
     * taking the table and hand over the symbol's first store, which is what
     * a single-mint session has.</p>
     */
    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    java.util.Map<String, String[]> installed,
                                    boolean declaredRoot)
            throws Exception {
        java.lang.reflect.Method publish = RowPlaceholderMint.class
                .getDeclaredMethod("placeholder", OccurrenceAddress.class,
                        JsonObject.class, String.class, String[].class,
                        boolean.class);
        publish.setAccessible(true);
        publish.invoke(null, occurrence, row, symbol,
                installed == null ? null : installed.get(symbol),
                Boolean.valueOf(declaredRoot));
    }

    /** The same declaration, met where the field was already symbolic. */
    private static JsonObject reusedConfiguredSourceRow() {
        JsonObject clock = new JsonObject();
        clock.addProperty("_type", "SymbolExpression");
        clock.addProperty("_java_type", "J");
        clock.addProperty("_exp",
                "M_J_field_REGION.aaa1cfd7.in.fa630d59.occ.23886999_java/lang/Long");
        JsonObject sum = new JsonObject();
        sum.addProperty("_type", "BinaryExpression");
        sum.addProperty("_exp", "+");
        sum.add("_left", clock);
        JsonObject row = new JsonObject();
        row.addProperty("sourceId", "HDFS.BLOCK_KEY.EXPIRY_DATE.RETIRED");
        row.addProperty("recordedValue", "1789616343508");
        row.add("expression", sum);
        row.addProperty("reused", true);
        return row;
    }

    private static boolean minted(JsonObject row) throws Exception {
        java.lang.reflect.Method decision = RowPlaceholderMint.class
                .getDeclaredMethod("minted", JsonObject.class);
        decision.setAccessible(true);
        return ((Boolean) decision.invoke(null, row)).booleanValue();
    }

    private static RootKind kindOf(JsonObject row) throws Exception {
        java.lang.reflect.Method kind = RowPlaceholderMint.class
                .getDeclaredMethod("kindOf", JsonObject.class);
        kind.setAccessible(true);
        return (RootKind) kind.invoke(null, row);
    }

    /**
     * The anchor's phi is published in the FATAL polarity whichever arm the
     * run took, so no reader downstream negates it a second time.
     */
    @Test
    public void phiIsPublishedInTheFatalPolarityForBothObservedArms()
            throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress occurrence = address(
                "hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.addProperty("_exp", "allKeys.get(id) == null");

        // The run that took the fatal arm, and the run that took the
        // healthy one, state the same predicate about the same anchor.
        RowRuntime.target(occurrence, 8L, "retrieveDataEncryptionKey#u8",
                condition, true, true, true);
        RowRuntime.target(occurrence, 9L, "retrieveDataEncryptionKey#u8",
                condition, false, false, true);
        RowRuntime.closeSession();

        List<TargetRow> rows = RowCodec.readAll(session().targets(),
                RowCodec::readTarget);
        assertEquals(2, rows.size());
        String ref = rows.get(0).phiTerm();
        assertTrue(ref.startsWith("EXPR."));
        assertTrue(rows.get(0).observedFatal());
        assertEquals("(not " + ref + ")", rows.get(1).phiTerm());
        assertFalse(rows.get(1).observedFatal());
    }

    /**
     * I4: a decision row carries exactly the clock cells its term names.
     *
     * <p>The readings were a JVM-WIDE map of every clock the process had
     * ever minted, snapshotted into every decision row -- and one
     * MiniDFSCluster is one JVM, so on hdfs-11741 14 of 17 {@code
     * removeExpiredKeys#u15} rows lack the cell their own term reads and 15
     * of 17 list other NODES' cells.  Membership is what the downstream
     * stages read as "this session's decision read this cell" ({@code
     * explore.Corpus#index}, {@code compose.ClaimPolicy#movedRoots} and
     * {@code #clockNecessary}), so the row has to state the cells the term
     * names and nothing else.</p>
     */
    @Test
    public void aDecisionCarriesTheClockCellsItsTermNames() throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress occurrence = address(
                "hdfs-11741/nn0#epoch0", "REGION.aaa1cfd7",
                CausalContext.of(Role.of("KEY_MANAGER_TICK"),
                        "updateKeys", 1),
                ExecutionIndex.parse("KeyManager.updateKeys()#u3@0"));
        // Two clocks of one JVM -- the cluster's nodes run in one process --
        // and one root that is not a clock at all.
        RowRuntime.rootMint(occurrence, 3L, "HDFS.KEY.NOW@nn0", "M_J_now_nn0",
                RootKind.CLOCK, "1789358344655", "", "", true, 1_000_000L);
        RowRuntime.rootMint(occurrence, 4L, "HDFS.KEY.NOW@dn1", "M_J_now_dn1",
                RootKind.CLOCK, "1789358344999", "", "", true, 1_000_000L);
        RowRuntime.rootMint(occurrence, 5L, "HDFS.BLOCK_KEY.SERIAL_NO",
                "M_I_serial", RootKind.INTEGRAL, "3", "3", "6", true, 0L);

        // `key.getExpiryDate() < now`, over nn0's clock alone.
        RowRuntime.decision(occurrence, 12L,
                "<a.BlockTokenSecretManager: void removeExpiredKeys()>#u15",
                1, true, comparison("M_J_now_nn0", "J"));
        // A decision over a root that is no clock states no cell.
        RowRuntime.decision(occurrence, 13L, "<a.KeyManager: void"
                + " updateKeys()>#u9", 1, false,
                comparison("M_I_serial", "I"));
        // And a concrete decision names nothing at all.
        RowRuntime.decision(occurrence, 0L, "<a.KeyManager: void"
                + " updateKeys()>#u2", 1, true, null);
        RowRuntime.closeSession();

        List<DecisionRow> decisions = RowCodec.readAll(session().decisions(),
                RowCodec::readDecision);
        assertEquals(3, decisions.size());
        assertEquals("the cell this term reads, at what its mint recorded",
                Collections.singletonMap("HDFS.KEY.NOW@nn0",
                        Long.valueOf(1789358344655L)),
                decisions.get(0).clockReadings());
        assertEquals("and not the other node's, which this decision never"
                        + " read", Collections.emptyMap(),
                decisions.get(1).clockReadings());
        assertEquals("a decision with no term names no cell",
                Collections.emptyMap(), decisions.get(2).clockReadings());
    }

    /** {@code <symbol> < 0}, as the VM publishes a compared read. */
    private static JsonObject comparison(String symbol, String javaType) {
        JsonObject read = new JsonObject();
        read.addProperty("_type", "SymbolExpression");
        read.addProperty("_java_type", javaType);
        read.addProperty("_exp", symbol);
        JsonObject boundary = new JsonObject();
        boundary.addProperty("_type", "ConsumerBoundaryExpression");
        boundary.addProperty("boundaryKind", "FIELD_READ");
        boundary.addProperty("_java_type", javaType);
        boundary.add("expression", read);
        JsonObject literal = new JsonObject();
        literal.addProperty("_type", "ConstExpr");
        literal.addProperty("_java_type", javaType);
        literal.addProperty("_exp", "Y_" + javaType + "_0");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.add("_left", boundary);
        predicate.addProperty("_op", "<");
        predicate.add("_right", literal);
        return predicate;
    }

    /**
     * I1: the enclosing occurrence wins.
     *
     * <p>A declared region method called synchronously inside another
     * region's occurrence opens NO occurrence of its own -- sites connected
     * by synchronous calls are one region, and an occurrence ends only when
     * execution crosses a thread or process boundary (paper SS3.1.2).  On
     * hdfs-11741 dn1 that is {@code addKeys} (REGION.ba3902cd) calling
     * {@code removeExpiredKeys} (REGION.094a8e3d), which used to open the
     * nested occurrence {@code 845fa3841a35af67} and take every decision,
     * read and mint of the call with it.</p>
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

        Identity.enterFrame("<a.BlockTokenSecretManager: void addKeys()>#u1", null);
        OccurrenceAddress addKeys = Identity.occurrence(NN.key(),
                "REGION.ba3902cd", true);
        assertNotNull(addKeys);
        String opened = addKeys.render();

        // The synchronous call into the nested declared region, through the
        // woven entry hook itself.
        long nestedFrame = Identity.enterFrame(
                "<a.BlockTokenSecretManager: void removeExpiredKeys()>#u7", null);
        long entry = ConcolicRegionRuntime.enterRegionEntry(
                "REGION.094a8e3d",
                "<a.BlockTokenSecretManager: void removeExpiredKeys()>",
                keyManager);
        assertEquals("the entry is an event of the occurrence already"
                        + " running, so it opens none of its own",
                addKeys, Identity.currentOccurrence(NN.key()));
        assertEquals("both entries stand on the region stack: the folded one"
                        + " pushed the marker its own exit pops", 2,
                Identity.regionDepth());
        assertEquals("and the enclosing occurrence's address never moved",
                opened, addKeys.render());

        // A site below the fold is indexed from the entry that OPENED the
        // occurrence, so its idx: frames carry the folded region's own
        // method -- the call path is what the index is for.
        long deeper = Identity.enterFrame("<a.Key: long getExpiryDate()>#u2", null);
        assertEquals("<a.BlockTokenSecretManager: void"
                        + " removeExpiredKeys()>#u7@0"
                        + "/<a.Key: long getExpiryDate()>#u2@0",
                Identity.siteIndex().render());
        Identity.exitFrame(deeper);

        // The folded region's exit closes nothing.
        ConcolicRegionRuntime.exitRegionEntry(entry);
        Identity.exitFrame(nestedFrame);
        assertEquals("one region open: the one that opened the occurrence",
                1, Identity.regionDepth());
        assertEquals("and it is still the occurrence this thread runs",
                addKeys, Identity.currentOccurrence(NN.key()));

        // F1: A FOLDED ENTRY IS NOT AN ENTRY OF AN OCCURRENCE.  Neither pass
        // records an activation for it -- the recording states no occurrence
        // address on its trace row, so PLAN builds one activation per
        // occurrence and a SHARED_ADDRESS_ROOT_CALLS row keeps meaning a
        // real identity failure.
        Identity.resetForTests();
        Lineage.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("<a.BlockTokenSecretManager: void addKeys()>#u1", null);
        assertFalse("nothing is running here, so this entry opens an"
                        + " occurrence and the recording states its address",
                recordedAddress("REGION.ba3902cd").isEmpty());
        assertFalse("it is no fold", Identity.foldedEntry());

        Identity.enterFrame(
                "<a.BlockTokenSecretManager: void removeExpiredKeys()>#u7", null);
        assertEquals("the nested entry folds, so the recording states no"
                        + " address for it and PLAN records no activation",
                "", recordedAddress("REGION.094a8e3d"));
        assertTrue("and while the fold stands, no activation starts here",
                Identity.foldedEntry());
        Identity.regionExit();
        Identity.regionExit();
        assertFalse("and the enclosing occurrence is no fold",
                Identity.foldedEntry());

        // A declared region on a thread running no occurrence opens its own.
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame(
                "<a.BlockTokenSecretManager: void removeExpiredKeys()>#u7", null);
        OccurrenceAddress alone = Identity.occurrence(NN.key(),
                "REGION.094a8e3d", true);
        assertNotNull("no occurrence was running, so this entry opens one",
                alone);
        assertEquals("REGION.094a8e3d", alone.regionId());
        assertEquals(1, Identity.regionDepth());
        assertEquals(alone, Identity.currentOccurrence(NN.key()));
    }

    /**
     * The execution index, and why it is not an ordinal.
     *
     * <p>Folded into the daemon-tick case because it is the same question:
     * an identity that moves when an unrelated call is inserted elsewhere
     * is not an identity.</p>
     */
    private void executionIndexIsStableUnderUnrelatedCalls() {
        // A scope opened inside a call that RETURNS is rooted at the
        // deepest level the scope start and the point still share.  The
        // scope of a served message is opened by
        // CausynthMessagePropagation.inbound, which hands control back to
        // the handler, so an index measured from the level that opened it
        // is empty once that level is gone -- and the four
        // PBHelper.convert activations of one refresh then answered one
        // address (G11).
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

        // And the frames ABOVE the inbound scope are the carrier thread's,
        // not the request's: which of N pooled handlers serves a request is
        // scheduling, and the anchor already identifies the request.  Two
        // passes that schedule different handlers of one pool compute ONE
        // index for the served activation -- hdfs-17960 planned handler 3
        // and ran handler 0, and REPLAY refused 14 tasks at frame 0,
        // <org.apache.hadoop.ipc.Server: void start()>#u31.
        Object served = new Object();
        RuntimeTraceContext.registerSource(served, NN);
        long serving = RuntimeTraceContext.beginRequest(NN,
                "checkpoint-namespace");
        String header = RuntimeTraceContext.outboundHeader(served, null);
        RuntimeTraceContext.endRequest(serving);
        String recorded = anchoredActivationIndex(header, 3);
        String replayed = anchoredActivationIndex(header, 0);
        assertEquals("the served api is frame 0; no Server.start, no "
                        + "Handler.run, no RpcCall.run",
                "NameNodeRpcServer.saveNamespace()#u40@0", recorded);
        assertEquals("the same index whichever handler was scheduled",
                recorded, replayed);

        // A tick is the other arm of the one rule: it IS the started work,
        // so its index begins at the start frame it claimed rather than at
        // the point the tick was opened -- the start site and its iteration
        // are what tell two started siblings apart (G10/G11).
        Identity.resetForTests();
        Lineage.resetForTests();
        Object updating = new Object();
        RuntimeTraceContext.registerSource(updating, NN);
        assertEquals("KeyManager.startBlockKeyUpdater()#u5@0"
                        + "/BlockKeyUpdater.run()#u6@0"
                        + "/KeyManager.updateBlockKeys()#u2@0",
                daemonTickIndex(updating));

        // Those counts live in the LEVEL that made them, one set per ROOT
        // HOP that level has been live under: a tick opened and closed
        // inside a request is its own root, its turns cannot move the
        // request's counts, and the request's own counts continue after it.
        // Keyed by the innermost SCOPE frame's token instead, the
        // balancer's two Balancer.runOneIteration calls of one request both
        // stood at iteration 0 and shared a producer endpoint -- a scope
        // token moves at every request main sends, a root hop does not.
        Identity.resetForTests();
        Lineage.resetForTests();
        Object ticking = new Object();
        RuntimeTraceContext.registerSource(ticking, NN);
        long request = RuntimeTraceContext.beginRequest(NN, "balance-block");
        Identity.exitFrame(Identity.enterFrame("Balancer.runOneIteration()#u1", null));
        long tick = CausynthTraceRecorder.beginDaemonTick(ticking,
                "KEY_MANAGER_TICK");
        Identity.exitFrame(Identity.enterFrame("KeyManager.updateBlockKeys()#u2", null));
        CausynthTraceRecorder.endDaemonTick(tick);
        Identity.enterFrame("Balancer.runOneIteration()#u1", null);
        assertEquals("Balancer.runOneIteration()#u1@1",
                Identity.atScope().render());
        RuntimeTraceContext.endRequest(request);

        // And keyed by the enclosing occurrence's CONTEXT -- which is what
        // stood here -- the k of the SEND could not advance at all, because
        // the context is read live and a client thread's context moves
        // between two sends of one request: Client.getRpcResponse installs
        // the response's scope on the CALLING thread and nothing on that
        // path closes it, so the next Client.call frame was counted under
        // the PREVIOUS response's anchor, restarted at iteration 0, and
        // hdfs-17960 verification #6 minted ONE producer endpoint
        // (98ad5650d0490b91) for the six create-snapshots RPCs main sent in
        // one request -- 46 sends over 28 ids, and 158 downstream
        // OCCURRENCE_ADDRESS_SHARED rows.  Keyed by (level, root hop, site)
        // the standing hop moves nothing, and the two shapes are the SAME
        // six endpoints.
        Object client = new Object();
        RuntimeTraceContext.registerSource(client, NN);
        List<Endpoint> standing = clientRequestSends(client, true);
        List<Endpoint> quiet = clientRequestSends(client, false);
        List<String> ids = new ArrayList<String>();
        for (Endpoint send : standing) ids.add(send.id());
        assertEquals("six sends of one occurrence at one site are six"
                        + " endpoints", 6,
                new java.util.LinkedHashSet<String>(ids).size());
        assertEquals("the sixth is the sixth call of an unwoven caller, and"
                        + " the k of each send is 0 in its own frame",
                "Client.call()#u12@5/Client.call()#u13@0"
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

        // An unrelated call, entered and left, moves nothing.
        Identity.exitFrame(Identity.enterFrame("Other.helper()#u1", null));
        assertEquals(inner, Identity.atScope());

        // Re-entering one site under one frame IS the next iteration --
        // the rule that makes a loop body's turns distinct, computed the
        // same way in the recording and in the replay.
        Identity.exitFrame(Identity.enterFrame("Caller.body()#u9", null));
        Identity.enterFrame("Caller.body()#u9", null);
        assertEquals("Caller.run()#u3@0/Caller.step()#u7@0"
                + "/Caller.body()#u9@1", Identity.atScope().render());

        // A region entry re-bases the index: an endpoint inside it is
        // addressed from the region, not from the thread's whole stack.
        ExecutionIndex atEntry = Identity.regionEnter();
        assertEquals(3, atEntry.frames().size());
        assertTrue(Identity.siteIndex().frames().isEmpty());
        Identity.enterFrame("Region.port()#u2", null);
        assertEquals("Region.port()#u2@0", Identity.siteIndex().render());

        // The frame journal: a VM-logged event takes the frames the thread
        // stood on when the VM's event clock was below its id.  The clock is
        // the VM's; the frames are this stack's; nothing is an ordinal.
        Identity.resetForTests();
        // The region-enter event is the newest when the region opens.
        final long[] clock = {41L};
        Identity.clock(new FrameJournal.Clock() {
            @Override
            public long now() {
                return clock[0];
            }
        });
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.regionEnter();
        Identity.regionKey(41L);
        // No event between the region entry and this call, so the entry the
        // clock stood at is replaced rather than duplicated.
        Identity.enterFrame("Saver.save()#u1", null);
        clock[0] = 44L;
        long counting = Identity.enterFrame("Manager.count()#u2", null);
        clock[0] = 48L;
        // Event 45..48 happened inside count(): the last entry below it is
        // the one the clock read when count() was entered.
        assertEquals("Saver.save()#u1@0/Manager.count()#u2@0",
                FrameJournal.framesAt(41L, 45L).render());
        assertEquals("Saver.save()#u1@0/Manager.count()#u2@0",
                FrameJournal.framesAt(41L, 48L).render());
        // Event 42..44 happened after save() was entered and before count()
        // was, so it stands one frame shallower.
        assertEquals("Saver.save()#u1@0",
                FrameJournal.framesAt(41L, 43L).render());
        // Entered and left with no event in between: the interval holds
        // nothing, so the collapsed entry is the one that stood at 48.
        Identity.exitFrame(counting);
        Identity.enterFrame("Manager.count()#u2", null);
        assertEquals("Saver.save()#u1@0/Manager.count()#u2@1",
                FrameJournal.framesAt(41L, 49L).render());
        // Not this activation's journal, and below the region entry: unplaced
        // rather than answered with someone else's frames.
        assertNull(FrameJournal.framesAt(99L, 49L));
        assertNull(FrameJournal.framesAt(41L, 41L));
        // One key, two answers of the same activation: the frames a logged
        // event stood on, and the occurrence that performed it.  A row of a
        // read belongs to the activation the VM names on the record, not to
        // whichever activation's read-out found the location's log first.
        OccurrenceAddress performer = address(
                "hdfs-17960/nn0#epoch1", "REGION.9492ec77",
                CausalContext.of(Role.CLIENT, "", 1),
                ExecutionIndex.parse("Manager.delete()#u3@0"));
        RowRuntime.journalRegion(41L, performer);
        assertEquals(performer, RowRuntime.occurrenceAt(41L));
        assertNull("an event of no activation of this session names none",
                RowRuntime.occurrenceAt(99L));
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Caller.run()#u3", null);
        Identity.enterFrame("Caller.step()#u7", null);
        Identity.enterFrame("Caller.body()#u9", null);

        // The thread-start handover (P2h): the child's inherited stack
        // GAINS the frame of the start that created it, and two siblings
        // started from one site inside one starter frame -- hdfs-17960's two
        // FSImageSaver threads -- differ by that start's iteration and by
        // nothing else.  No thread id, no address, no session counter.
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        // Both savers are started inside the ONE served request, as the
        // checkpoint handler starts them: a start made by a thread under no
        // root hop files no frame (AStartWithNoIdentityFilesNoFrameTest).
        Object starter = new Object();
        RuntimeTraceContext.registerSource(starter, NN);
        long starting = RuntimeTraceContext.beginRequest(starter, "checkpoint");
        long saving = Identity.enterFrame("FSImage.saveFSImageInAllDirs()#u12", null);
        String first = startedWorkIndex("FSImage.saveFSImageInAllDirs()#u40");
        String second = startedWorkIndex("FSImage.saveFSImageInAllDirs()#u40");
        assertEquals("FSImage.saveFSImageInAllDirs()#u12@0"
                + "/FSImage.saveFSImageInAllDirs()#u40@0"
                + "/FSImageSaver.run()#u1@0", first);
        assertEquals("FSImage.saveFSImageInAllDirs()#u12@0"
                + "/FSImage.saveFSImageInAllDirs()#u40@1"
                + "/FSImageSaver.run()#u1@0", second);
        // The count is the occurrence's own (Identity.State#nextSiteEvent),
        // and outside every region the occurrence is the role occurrence at
        // the path this thread stands on: the next activation of the starter
        // stands on a different path, so it is a different occurrence and its
        // starts begin at 0 again -- exactly as a loop iteration count does.
        Identity.exitFrame(saving);
        Identity.enterFrame("FSImage.saveFSImageInAllDirs()#u12", null);
        assertEquals("FSImage.saveFSImageInAllDirs()#u12@1"
                + "/FSImage.saveFSImageInAllDirs()#u40@0"
                + "/FSImageSaver.run()#u1@0",
                startedWorkIndex("FSImage.saveFSImageInAllDirs()#u40"));

        // The index has TWO stacks and one balance rule.  A nested region
        // opened and closed leaves the enclosing occurrence's site counts
        // alone, so the k-th entry of a site inside a loop keeps counting.
        // A region popped without a push no longer touches a count at all
        // -- the counts are the LEVEL's, and a region holds none -- which
        // is what renumbered the 10 applyEditLogOp entries of one
        // loadEditRecords on hdfs-17960 verification #3 (0, then 0..8) and
        // refused 13 tasks at that one frame, when the counter was keyed by
        // the open region's serial.  What the stray pop still moves is the
        // frame the site index is measured FROM, and that is why the region
        // depth is balance-checked exactly as the frames are.
        RuntimeTraceContext.endRequest(starting);
        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Loader.loadEditRecords()#u4", null);
        Identity.occurrence(NN.key(), "REGION.loader", true);
        assertEquals("one region open, pushed by the entry", 1,
                Identity.regionDepth());
        for (int record = 0; record < 3; record++) {
            long applying = Identity.enterFrame("Loader.applyEditLogOp()#u115", null);
            // One nested activation, opened and closed as the entry hook
            // pairs them.
            Identity.occurrence(NN.key(), "REGION.apply", true);
            Identity.regionExit();
            Identity.exitFrame(applying);
        }
        assertEquals("the pair left the enclosing region standing", 1,
                Identity.regionDepth());
        long applied = Identity.enterFrame("Loader.applyEditLogOp()#u115", null);
        assertEquals("the k-th entry of one site inside one occurrence",
                "Loader.loadEditRecords()#u4@0/Loader.applyEditLogOp()#u115@3",
                Identity.atScope().render());
        assertTrue("and the enclosing occurrence is the one open region",
                Identity.innermostRegion().contains("REGION.loader"));
        Identity.exitFrame(applied);

        // One pop too many, and the counts stand: the fifth entry of the
        // site is the fifth.  The frame depth says nothing is wrong and
        // neither does the index, so the region depth is the only thing
        // that can name it.
        int frames = Identity.depth();
        Identity.regionExit();
        assertEquals("the frames are untouched by a region pop", frames,
                Identity.depth());
        assertEquals("but no region is open any more", 0,
                Identity.regionDepth());
        Identity.enterFrame("Loader.applyEditLogOp()#u115", null);
        assertEquals("the fifth entry is still the fifth",
                "Loader.loadEditRecords()#u4@0/Loader.applyEditLogOp()#u115@4",
                Identity.atScope().render());

        // A pool thread was created before the work it runs, so it inherits
        // nothing from the submission: the start filed for the TASK is
        // claimed on the object the region is entered on, and the next task
        // replaces that frame instead of nesting under it.
        Identity.resetForTests();
        final List<String> ran =
                Collections.synchronizedList(new ArrayList<String>());
        final Object[] tasks = {new Object(), new Object()};
        Thread worker = poolThreadCreatedOutsideAnyScope(new Runnable() {
            @Override
            public void run() {
                for (Object task : tasks) {
                    Identity.claimStart(task);
                    long running = Identity.enterFrame("Task.run()#u1", null);
                    ran.add(Identity.atScope().render());
                    Identity.exitFrame(running);
                }
            }
        });
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        // The batch is submitted inside a request, as a pool's work is: a
        // start made by a thread under no root hop files no frame
        // (AStartWithNoIdentityFilesNoFrameTest).
        Object submitter = new Object();
        RuntimeTraceContext.registerSource(submitter, NN);
        long submitting = RuntimeTraceContext.beginRequest(submitter, "submit");
        Identity.enterFrame("Pool.submitAll()#u5", null);
        Identity.startWork("Pool.submitAll()#u9", tasks[0]);
        Identity.startWork("Pool.submitAll()#u9", tasks[1]);
        worker.start();
        try {
            worker.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        RuntimeTraceContext.endRequest(submitting);
        assertEquals("Pool.submitAll()#u9@0/Task.run()#u1@0", ran.get(0));
        assertEquals("Pool.submitAll()#u9@1/Task.run()#u1@0", ran.get(1));

        // An activation's push and its pop are paired, recursion included:
        // the frames an occurrence stands on ARE its identity, so a frame
        // left standing moves the address of everything after it.  Every
        // entry of one method has its own depth, and an unbalanced one is
        // visible as a depth that did not come back.
        int depthAtOpen = Identity.depth();
        long outer = Identity.enterFrame("Recursive.m()#u1", null);
        long innerRecursion = Identity.enterFrame("Recursive.m()#u1", null);
        assertEquals(depthAtOpen + 2, Identity.depth());
        assertEquals("Recursive.m()#u1", Identity.innermostFrame());
        // Each entry closes the level ITS OWN token owns, so an exit of the
        // inner one cannot take the outer one's level with it.
        Identity.exitFrame(innerRecursion);
        assertEquals(depthAtOpen + 1, Identity.depth());
        Identity.exitFrame(outer);
        assertEquals(depthAtOpen, Identity.depth());
        // A level nothing opened is closed by nothing: a stale token is not
        // an excuse to pop whatever is innermost.
        Identity.exitFrame(innerRecursion);
        assertEquals(depthAtOpen, Identity.depth());

        Identity.resetForTests();
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.enterFrame("Caller.run()#u3", null);

        // The three causal contexts, and the one that is not an ordinal.
        // A ROOT names the api its k was counted under, because that is
        // what the k counts (G11): two declared apis of one node are two
        // roots, and a tick declares none.
        assertEquals("Root:HEARTBEAT_TICK#4", Identity.context("", "",
                Role.of("HEARTBEAT_TICK"), "", 4).render());
        assertEquals("Root:CLIENT/balance-block#1", Identity.context("", "",
                Role.CLIENT, "balance-block", 1).render());
        assertEquals("Anchor:abc123@HADOOP_IPC#heartbeat",
                Identity.context("abc123", "HADOOP_IPC#heartbeat",
                        Role.of("IPC_HANDLER"), "", 2).render());
        assertEquals("Lost:DATA_XCEIVER",
                Identity.context("", "", Role.of("DATA_XCEIVER"), "", 0)
                        .render());
    }

    /**
     * The index of one anchored activation, as a pass that scheduled the
     * {@code scheduled}-th handler of the pool computes it.
     *
     * <p>The real shape of hdfs-17960's NameNode RPC: {@code Server.start}
     * starts N handler threads, one of them takes the call, and
     * {@code CausynthMessagePropagation.inbound} opens the served scope
     * inside a call that hands control straight back to the handler.</p>
     */
    private static String anchoredActivationIndex(final String header,
                                                  int scheduled) {
        Identity.resetForTests();
        Lineage.resetForTests();
        final AtomicReference<String> onHandler = new AtomicReference<>("");
        Runnable handling = new Runnable() {
            @Override
            public void run() {
                Identity.enterFrame("Server$Handler.run()#u32", null);
                Identity.enterFrame("Server$RpcCall.run()#u33", null);
                long propagating = Identity.enterFrame("Propagation.inbound()#u7", null);
                long inbound = RuntimeTraceContext.enterInbound(header,
                        "HADOOP_IPC", "corr-1", "attempt-0", "REQUEST", null, "");
                Identity.exitFrame(propagating);
                Identity.enterFrame("NameNodeRpcServer.saveNamespace()#u40", null);
                onHandler.set(Identity.atScope().render());
                RuntimeTraceContext.exitInbound(inbound);
            }
        };
        Thread[] pool = new Thread[4];
        for (int handler = 0; handler < pool.length; handler++) {
            pool[handler] = new Thread(handler == scheduled ? handling
                    : new Runnable() {
                        @Override
                        public void run() {
                        }
                    });
            Identity.startWork("Server.start()#u31", pool[handler]);
        }
        pool[scheduled].start();
        try {
            pool[scheduled].join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        return onHandler.get();
    }

    /**
     * The producer endpoints of six RPCs one client request sends.
     *
     * <p>The real shape of hdfs-17960's client: {@code Client.call} is
     * entered from a caller the weave does not reach, {@code
     * Connection.sendRpcRequest} closes whatever inbound hop is standing
     * before it writes the request ({@code
     * CausynthMessagePropagation.endInbound}), and {@code
     * Client.getRpcResponse} installs the response's scope on this same
     * thread and leaves it standing for the next call to close.</p>
     *
     * @param installResponses whether the responses come back at all
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
            long outbound = Identity.enterFrame("Propagation.outbound()#u4", null);
            sent.add(Identity.messageSent(NN.key(), "HADOOP_IPC",
                    "corr-" + rpc, "REQUEST", null));
            Identity.exitFrame(outbound);
            Identity.exitFrame(sending);
            response = installResponses
                    ? RuntimeTraceContext.enterInbound(header, "HADOOP_IPC",
                            "corr-" + rpc, "0", "RESPONSE", client, "")
                    : 0L;
            Identity.exitFrame(retrying);
            Identity.exitFrame(call);
        }
        if (response > 0L) RuntimeTraceContext.exitInbound(response);
        RuntimeTraceContext.endRequest(request);
        return sent;
    }

    /** The index one daemon tick of a started updater thread stands on. */
    private static String daemonTickIndex(final Object owner) {
        final AtomicReference<String> onUpdater = new AtomicReference<>("");
        Thread updater = new Thread(new Runnable() {
            @Override
            public void run() {
                Identity.enterFrame("BlockKeyUpdater.run()#u6", null);
                long tick = CausynthTraceRecorder.beginDaemonTick(owner,
                        "KEY_MANAGER_TICK");
                Identity.enterFrame("KeyManager.updateBlockKeys()#u2", null);
                onUpdater.set(Identity.atScope().render());
                CausynthTraceRecorder.endDaemonTick(tick);
            }
        });
        // Started inside the balancer's own request, as the KeyManager's
        // updater is: a start made by a thread under no root hop files no
        // frame (AStartWithNoIdentityFilesNoFrameTest).
        long starting = RuntimeTraceContext.beginRequest(owner, "balance");
        Identity.startWork("KeyManager.startBlockKeyUpdater()#u5", updater);
        RuntimeTraceContext.endRequest(starting);
        updater.start();
        try {
            updater.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        return onUpdater.get();
    }

    /**
     * The index of the work one start site started, on its own thread.
     *
     * <p>The child is CONSTRUCTED before the start is filed, which is the
     * real order -- {@code new Thread(saver)} then {@code start()} -- and the
     * reason the frame cannot travel by inheritance.</p>
     */
    private static String startedWorkIndex(String startSite) {
        final AtomicReference<String> onChild = new AtomicReference<>("");
        Thread child = new Thread(new Runnable() {
            @Override
            public void run() {
                Identity.enterFrame("FSImageSaver.run()#u1", null);
                onChild.set(Identity.atScope().render());
            }
        });
        Identity.startWork(startSite, child);
        child.start();
        try {
            child.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        return onChild.get();
    }

    /** A thread a pool created before any scope existed. */
    private static Thread poolThreadCreatedOutsideAnyScope(Runnable work) {
        final AtomicReference<Thread> created = new AtomicReference<>();
        Thread factory = new Thread(new Runnable() {
            @Override
            public void run() {
                created.set(new Thread(work));
            }
        });
        factory.start();
        try {
            factory.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
        return created.get();
    }

    /**
     * What the RECORDING writes onto this entry's trace row: the one
     * function both passes compute an occurrence with, through the
     * recorder's own door, so the fold is asserted where PLAN reads it.
     */
    private static String recordedAddress(String regionId) throws Exception {
        java.lang.reflect.Method address = CausynthTraceRecorder.class
                .getDeclaredMethod("occurrenceAddress", String.class,
                        String.class);
        address.setAccessible(true);
        return (String) address.invoke(null, NN.key(), regionId);
    }

    private Path sessionFile() throws Exception {
        Path results = iteration.getRoot().toPath()
                .resolve("iteration-0000").resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        return results;
    }

    private SessionDir session() {
        return SessionDir.of(iteration.getRoot().toPath()
                .resolve("iteration-0000"), RowRuntime.sessionId());
    }


    /**
     * {@code if (a || b || c) throw}: every test jumps to the throw, so phi
     * is the OR of their fatal arms as one evaluation decided them, from the
     * target branch on (adhoc reader-chunk's first-chunk offset check).
     */
    @Test
    public void aReadTheVmNamedNothingIsNamedInItsOwnSession() {
        // Two replays that diverged hold two objects under one rid and
        // version; one corpus-wide name would give them one sort.
        assertFalse(RowPublication.versionSymbol("s1", "INSTANCE_FIELD/203#24",
                "v927").equals(RowPublication.versionSymbol("s2",
                "INSTANCE_FIELD/203#24", "v927")));
    }

    @Test
    public void aDisjunctiveGuardIsTheOrOfItsTestsFatalArms() {
        JsonObject a = predicate("a"), c = predicate("c");
        String refA = RowRuntime.expressionRef(a);
        String refC = RowRuntime.expressionRef(c);
        java.util.LinkedHashMap<String, Boolean> guards =
                new java.util.LinkedHashMap<>();
        guards.put("G#u1", true);
        guards.put("G#u2", true);
        guards.put("G#u3", false);
        Object[][] rows = {
                // All healthy: a symbolic, b concrete, c symbolic.
                {decided("G#u1", false, a), decided("G#u2", false, null),
                        decided("G#u3", true, c), false,
                        Arrays.asList("(not " + refA + ")",
                                "(not " + refC + ")")},
                // b took its fatal arm concretely: fatal, and no arm stated.
                {decided("G#u1", false, a), decided("G#u2", true, null),
                        null, true, Collections.emptyList()},
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
    }

    private static JsonObject predicate(String name) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_exp", name);
        return expression;
    }

    private static JsonObject decided(String site, boolean outcome,
                                      JsonObject satisfied) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("outcome", outcome);
        JsonObject witness = new JsonObject();
        if (satisfied != null) {
            witness.add("sourceSatisfiedPredicate", satisfied);
        }
        mapping.add("witness", witness);
        return mapping;
    }
}
