package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

public class RuntimeTraceContextTest {
    @Before
    public void setUp() {
        RuntimeTraceContext.resetForTests();
    }

    @Test
    public void sourceRefHasStableLogicalAndEpochIdentity() {
        SourceRef source = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 3L);

        assertEquals("CLUSTER_NODE", source.kind());
        assertEquals("NAMENODE", source.role());
        assertEquals("cluster0/nn0", source.id());
        assertEquals(3L, source.epoch());
        assertEquals("cluster0/nn0#epoch3", source.key());
    }

    @Test
    public void requestScopeOverridesActiveRootAndRestoresItsSource() {
        Object testAnchor = new Object();
        Object clientAnchor = new Object();
        SourceRef test = new SourceRef(
                "TEST_DRIVER", "JUNIT", "test/driver", 0L);
        SourceRef client = new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "app/client0", 0L);
        RuntimeTraceContext.registerSource(testAnchor, test);
        RuntimeTraceContext.registerSource(clientAnchor, client);

        RuntimeTraceContext.View root =
                RuntimeTraceContext.enterRoot(testAnchor);
        assertEquals(test, root.source);

        long request = RuntimeTraceContext.beginRequest(clientAnchor);
        assertEquals(client, RuntimeTraceContext.currentSource());
        RuntimeTraceContext.endRequest(request);

        assertEquals(test, RuntimeTraceContext.currentSource());
        assertEquals(2, RuntimeTraceContext.sourceEventsForTests().size());
        assertEquals(RuntimeTraceContext.SourceEventKind.REQUEST_BEGIN,
                RuntimeTraceContext.sourceEventsForTests().get(0).kind);
        assertEquals(RuntimeTraceContext.SourceEventKind.REQUEST_END,
                RuntimeTraceContext.sourceEventsForTests().get(1).kind);
    }

    @Test
    public void restartMovesStableAnchorButKeepsOldRuntimeAliasInOldEpoch() {
        Object stableSlot = new Object();
        Object oldNameNode = new Object();
        Object newNameNode = new Object();
        SourceRef before = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 0L);
        SourceRef after = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 1L);
        RuntimeTraceContext.registerSource(stableSlot, before);
        RuntimeTraceContext.registerSourceAlias(oldNameNode, stableSlot);

        RuntimeTraceContext.restartSource(stableSlot, after);
        RuntimeTraceContext.registerSourceAlias(newNameNode, stableSlot);

        assertEquals(before, RuntimeTraceContext.sourceFor(oldNameNode));
        assertEquals(after, RuntimeTraceContext.sourceFor(stableSlot));
        assertEquals(after, RuntimeTraceContext.sourceFor(newNameNode));
        RuntimeTraceContext.SourceEvent restart =
                RuntimeTraceContext.sourceEventsForTests().get(0);
        assertEquals(RuntimeTraceContext.SourceEventKind.RESTART,
                restart.kind);
        assertEquals(before, restart.source);
        assertEquals(after, restart.relatedSource);
    }

    @After
    public void tearDown() {
        RuntimeTraceContext.resetForTests();
    }

    @Test
    public void spawnedThreadInheritsOwnerAndParentSpanButGetsNewLane()
            throws Exception {
        Object owner = new Object();
        RuntimeTraceContext.registerOwner(owner, "node");
        RuntimeTraceContext.View parent = RuntimeTraceContext.enterRoot(owner);
        Thread child = new Thread(() -> { });
        RuntimeTraceContext.captureAsync(child);
        AtomicReference<RuntimeTraceContext.View> observed =
                new AtomicReference<>();
        Thread actual = new Thread(() -> observed.set(
                RuntimeTraceContext.enterRoot(Thread.currentThread())));
        // Capture the object that is actually started, as the Soot start hook
        // does in production.
        RuntimeTraceContext.captureAsync(actual);
        actual.start();
        actual.join();

        assertEquals(parent.ownerId, observed.get().ownerId);
        assertEquals(parent.spanId, observed.get().parentSpanId);
        assertNotEquals(parent.laneId, observed.get().laneId);
    }

    @Test
    public void spawnedThreadAlsoInheritsStableSource() throws Exception {
        Object node = new Object();
        SourceRef source = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "cluster0/dn0", 0L);
        RuntimeTraceContext.registerSource(node, source);
        RuntimeTraceContext.View parent = RuntimeTraceContext.enterRoot(node);
        AtomicReference<RuntimeTraceContext.View> observed =
                new AtomicReference<>();
        Thread child = new Thread(() -> observed.set(
                RuntimeTraceContext.enterRoot(Thread.currentThread())));

        RuntimeTraceContext.captureAsync(child);
        child.start();
        child.join();

        assertEquals(source, observed.get().source);
        assertEquals(parent.ownerId, observed.get().ownerId);
        assertEquals(parent.spanId, observed.get().parentSpanId);
        assertNotEquals(parent.laneId, observed.get().laneId);
    }

    @Test
    public void newThreadCarriesSourceAndRequestWithoutTraceHooks()
            throws Exception {
        Object client = new Object();
        SourceRef source = new SourceRef(
                "EXTERNAL_APP", "CLIENT", "app/client0", 0L);
        RuntimeTraceContext.registerSource(client, source);
        long request = RuntimeTraceContext.beginRequest(client, "api");
        String requestKey = RuntimeTraceContext.current().requestKey;
        AtomicReference<RuntimeTraceContext.View> observed =
                new AtomicReference<>();

        Thread child = new Thread(() -> observed.set(
                RuntimeTraceContext.current()));
        child.start();
        child.join();
        RuntimeTraceContext.endRequest(request);

        assertEquals(source, observed.get().source);
        assertEquals(requestKey, observed.get().requestKey);
    }

    @Test
    public void distinctOwnersRemainDistinctForTheSameRegionTemplate() {
        Object first = new Object();
        Object second = new Object();
        RuntimeTraceContext.View one = RuntimeTraceContext.enterRoot(first);
        RuntimeTraceContext.exitRoot(one.spanId);
        RuntimeTraceContext.View two = RuntimeTraceContext.enterRoot(second);

        assertNotEquals(one.ownerId, two.ownerId);
    }

    @Test
    public void rpcReceiveCarriesCallerAsRemoteParent() throws Exception {
        Object client = new Object();
        RuntimeTraceContext.View caller = RuntimeTraceContext.enterRoot(client);
        RuntimeTraceContext.rpc("SEND", "RPC", "call-1", null);

        AtomicReference<RuntimeTraceContext.View> receive =
                new AtomicReference<>();
        Thread server = new Thread(() -> {
            RuntimeTraceContext.enterRoot(new Object());
            receive.set(RuntimeTraceContext.rpc("RECEIVE", "RPC", "call-1",
                    new Object()));
        });
        server.start();
        server.join();

        assertEquals(caller.spanId, receive.get().remoteParentSpanId);
        assertTrue(receive.get().ownerId > 0L);
        assertNotEquals(caller.ownerId, receive.get().ownerId);
    }

    @Test
    public void rpcReceiveSwitchesToRegisteredServerSource() throws Exception {
        Object client = new Object();
        Object nameNode = new Object();
        SourceRef clientSource = new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "app/client0", 0L);
        SourceRef serverSource = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 1L);
        RuntimeTraceContext.registerSource(client, clientSource);
        RuntimeTraceContext.registerSource(nameNode, serverSource);
        RuntimeTraceContext.View caller = RuntimeTraceContext.enterRoot(client);
        RuntimeTraceContext.rpc("SEND", "RPC", "call-source", null);

        AtomicReference<RuntimeTraceContext.View> receive =
                new AtomicReference<>();
        Thread server = new Thread(() -> receive.set(
                RuntimeTraceContext.rpc("RECEIVE", "RPC", "call-source",
                        nameNode)));
        server.start();
        server.join();

        assertEquals(serverSource, receive.get().source);
        assertEquals(caller.spanId, receive.get().remoteParentSpanId);
        assertNotEquals(caller.ownerId, receive.get().ownerId);
        assertEquals(clientSource, RuntimeTraceContext.currentSource());
    }

    @Test
    public void rpcReceiveBeforeSelectedRootSeedsThatRoot() throws Exception {
        RuntimeTraceContext.View caller = RuntimeTraceContext.enterRoot(
                new Object());
        RuntimeTraceContext.rpc("SEND", "RPC", "call-before-root", null);

        AtomicReference<RuntimeTraceContext.View> root =
                new AtomicReference<>();
        Thread server = new Thread(() -> {
            Object owner = new Object();
            RuntimeTraceContext.rpc("RECEIVE", "RPC", "call-before-root",
                    owner);
            root.set(RuntimeTraceContext.enterRoot(owner));
        });
        server.start();
        server.join();

        assertEquals(caller.spanId, root.get().remoteParentSpanId);
    }

    @Test
    public void adapterRootCannotConsumeRemoteParentBeforeHandlerRoot()
            throws Exception {
        RuntimeTraceContext.View caller = RuntimeTraceContext.enterRoot(
                new Object());
        RuntimeTraceContext.rpc("SEND", "RPC", "call-through-adapter", null);

        AtomicReference<RuntimeTraceContext.View> handler =
                new AtomicReference<>();
        Thread server = new Thread(() -> {
            RuntimeTraceContext.rpc("RECEIVE", "RPC",
                    "call-through-adapter", new Object());
            RuntimeTraceContext.View adapter =
                    RuntimeTraceContext.enterRoot(new Object());
            RuntimeTraceContext.exitRoot(adapter.spanId);
            handler.set(RuntimeTraceContext.enterRoot(new Object()));
        });
        server.start();
        server.join();

        assertEquals(caller.spanId, handler.get().remoteParentSpanId);
    }
}
