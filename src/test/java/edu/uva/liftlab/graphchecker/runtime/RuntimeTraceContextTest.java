package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

public class RuntimeTraceContextTest {
    @Before
    public void setUp() {
        RuntimeTraceContext.resetForTests();
    }

    @After
    public void tearDown() {
        RuntimeTraceContext.resetForTests();
    }

    /** A replay epoch may change, but the logical node may not. */
    @Test
    public void sourceIdentityIsStableAcrossFreshReplayEpochs() {
        SourceRef epoch0 = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "cluster0/dn0", 0L);
        RuntimeTraceContext.registerSource(new Object(), epoch0);
        assertEquals(true,
                RuntimeTraceContext.sourceIdentityRegistered(
                        "cluster0/dn0#epoch0"));
        assertEquals(true,
                RuntimeTraceContext.sourceIdentityRegistered(
                        "cluster0/dn0#epoch7"));
        assertEquals(false,
                RuntimeTraceContext.sourceIdentityRegistered(
                        "cluster0/dn1#epoch0"));
    }

    /**
     * A receiver that names its own source outranks the source of whoever
     * started its thread.
     *
     * <p>This is the in-process cluster shape and no fixture that opens a
     * request scope reproduces it: the driver constructs and starts every
     * node's threads, so each one inherits the driver's source through the
     * async seed, while the node itself binds its own receivers at start-up.
     * Preferring the seed filed a whole node's activations under the driver -
     * which put a producer and its target on different owners and epochs, and
     * made one exchange's delivery look like it was recorded by two
     * occurrences of one source.  The receiver's registration is what the
     * application actually stated, so it wins.</p>
     */
    @Test
    public void aRegisteredReceiverOutranksTheThreadThatStartedIt() {
        Object driver = new Object();
        Object dataNode = new Object();
        Object secretManager = new Object();
        SourceRef driverSource = new SourceRef(
                "EXTERNAL_APP", "TEST_DRIVER", "cluster0/driver0", 0L);
        SourceRef nodeSource = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "cluster0/dn0", 1L);
        RuntimeTraceContext.registerSource(driver, driverSource);
        RuntimeTraceContext.registerSource(dataNode, nodeSource);
        RuntimeTraceContext.registerSourceAlias(secretManager, dataNode);

        // The driver is current and submits the node's work, exactly as an
        // in-process cluster start does.
        RuntimeTraceContext.beginRequest(driverSource, "workload");
        // The seed a submitted thread would carry: the driver's source.
        RuntimeTraceContext.captureAsync(Thread.currentThread());

        // The activation runs on a receiver the node registered.
        RuntimeTraceContext.View attributed =
                RuntimeTraceContext.enterRoot(secretManager);
        assertEquals(nodeSource.key(), attributed.source.key());

        // A receiver that registered nothing still gets the ambient stamp -
        // there is no other answer - and that is the only remaining path.
        RuntimeTraceContext.View ambient =
                RuntimeTraceContext.enterRoot(new Object());
        assertEquals(nodeSource.key(), ambient.source.key());
    }

    /**
     * A submitted Runnable may carry an exact source seed without being a
     * source alias itself. Region admission accepts that entry context, but
     * never lets it override a receiver explicitly registered to another
     * source.
     */
    @Test
    public void exactEntryContextAdmitsUnregisteredRunnableOnlyForItsSource() {
        Object sourceAnchor = new Object();
        Object runnable = new Object();
        SourceRef balancer = new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "cluster0/balancer0", 0L);
        RuntimeTraceContext.registerSource(sourceAnchor, balancer);
        RuntimeTraceContext.beginRequest(balancer, "balancerIteration");

        assertEquals(null, RuntimeTraceContext.sourceFor(runnable));
        assertEquals(true, ConcolicRegionRuntime.exactEntrySourceForTests(
                runnable, balancer.key()));
        assertEquals(false, ConcolicRegionRuntime.exactEntrySourceForTests(
                runnable, "cluster0/driver0#epoch0"));

        SourceRef other = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "cluster0/dn0", 1L);
        RuntimeTraceContext.registerSource(runnable, other);
        assertEquals(false, ConcolicRegionRuntime.exactEntrySourceForTests(
                runnable, balancer.key()));
        assertEquals(true, ConcolicRegionRuntime.exactEntrySourceForTests(
                runnable, other.key()));
    }

    /** A REGISTERED_SOURCE root requires an exact receiver lifecycle key. */
    @Test
    public void registeredSourceRejectsMissingWrongAndStaleReceiverAlias() {
        Object driver = new Object();
        Object receiver = new Object();
        SourceRef driverSource = new SourceRef(
                "EXTERNAL_APP", "TEST_DRIVER", "cluster0/driver0", 0L);
        RuntimeTraceContext.registerSource(driver, driverSource);
        RuntimeTraceContext.beginRequest(driverSource, "workload");

        assertEquals(null, RuntimeTraceContext.sourceFor(receiver));
        assertEquals(false,
                ConcolicRegionRuntime.plannedEntrySourceForTests(
                        receiver, "cluster0/nn0#epoch1"));

        SourceRef dataNode = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "cluster0/dn0", 1L);
        RuntimeTraceContext.registerSource(receiver, dataNode);
        assertEquals(false,
                ConcolicRegionRuntime.plannedEntrySourceForTests(
                        receiver, "cluster0/nn0#epoch1"));
        assertEquals(true,
                ConcolicRegionRuntime.plannedEntrySourceForTests(
                        receiver, dataNode.key()));
        assertEquals(false,
                ConcolicRegionRuntime.plannedEntrySourceForTests(
                        receiver, "cluster0/dn0#epoch99"));
    }

    /**
     * A source is a stable logical identity plus an epoch, and every span the
     * workload opens is attributed to one: a restart advances the epoch
     * without rewriting what the old runtime object already reported, a
     * spawned thread inherits its parent's source on a lane of its own, and
     * an RPC receive switches to the registered server source while carrying
     * the caller as its remote parent.
     */
    @Test
    public void everySpanIsAttributedToOneSourceEpoch() throws Exception {
        SourceRef source = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 3L);
        assertEquals("CLUSTER_NODE", source.kind());
        assertEquals("NAMENODE", source.role());
        assertEquals("cluster0/nn0", source.id());
        assertEquals(3L, source.epoch());
        assertEquals("cluster0/nn0#epoch3", source.key());

        // A restart moves the stable anchor to the next epoch.  The runtime
        // object the old epoch used keeps answering for that old epoch, so
        // nothing already recorded is silently re-attributed.
        RuntimeTraceContext.resetForTests();
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

        // A thread the workload spawns inherits the parent span and the
        // parent's source, on a lane of its own.
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        SourceRef dataNode = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "cluster0/dn0", 0L);
        RuntimeTraceContext.registerSource(node, dataNode);
        RuntimeTraceContext.View parent = RuntimeTraceContext.enterRoot(node);
        final AtomicReference<RuntimeTraceContext.View> spawned =
                new AtomicReference<>();
        Thread child = new Thread(() -> spawned.set(
                RuntimeTraceContext.enterRoot(Thread.currentThread())));
        RuntimeTraceContext.captureAsync(child);
        child.start();
        child.join();
        assertEquals(dataNode, spawned.get().source);
        assertEquals(parent.spanId, spawned.get().parentSpanId);
        assertNotEquals(parent.laneId, spawned.get().laneId);

        // An RPC receive runs on the server's source, keeps the caller as its
        // remote parent, and leaves the caller's own source untouched.
        RuntimeTraceContext.resetForTests();
        Object client = new Object();
        Object nameNode = new Object();
        SourceRef clientSource = new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "app/client0", 0L);
        SourceRef serverSource = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 1L);
        RuntimeTraceContext.registerSource(client, clientSource);
        RuntimeTraceContext.registerSource(nameNode, serverSource);
        RuntimeTraceContext.View caller = RuntimeTraceContext.enterRoot(client);
        RuntimeTraceContext.rpc("SEND", "RPC", "call-source", "REQUEST",
                null);
        final AtomicReference<RuntimeTraceContext.View> receive =
                new AtomicReference<>();
        Thread server = new Thread(() -> receive.set(
                RuntimeTraceContext.rpc("RECEIVE", "RPC", "call-source",
                        "REQUEST", nameNode)));
        server.start();
        server.join();
        assertEquals(serverSource, receive.get().source);
        assertEquals(caller.spanId, receive.get().remoteParentSpanId);
        assertEquals(clientSource, RuntimeTraceContext.currentSource());
    }
}
