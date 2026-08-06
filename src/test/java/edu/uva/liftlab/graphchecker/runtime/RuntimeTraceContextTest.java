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
