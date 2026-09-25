package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.Before;
import org.junit.Test;

/**
 * THE attribution rule, one case per rule: an explicit scope, then the
 * innermost registered receiver on the stack, then the starter by reference
 * -- and nothing when all three fail.
 */
public class AttributionTest {
    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "t/nn0", 0L);
    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        ScheduleLog.resetForTests();
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
        // The scope is a frame: closed, it names nothing any more.
        assertEquals(NN.key(), Attribution.resolve(null).key());
        Identity.exitFrame(frame);
    }

    @Test
    public void theInnermostRegisteredReceiverOnTheStackAnswers() {
        Object handler = new Object();
        Object server = new Object();
        Object blockManager = new Object();
        RuntimeTraceContext.registerSource(server, NN);
        Identity.enterFrame("<a.Server$Handler: void run()>", handler);
        Identity.enterFrame("<a.Server: void call()>", server);
        Identity.enterFrame("<a.BlockManager: void convert()>",
                blockManager);
        // A NameNode handler serving Server.call is the RPC server's, on
        // whatever pool thread it runs.
        assertEquals(NN.key(), Attribution.resolve(null).key());
        assertEquals(NN.key(),
                RuntimeTraceContext.activationSource(null).key());
    }

    @Test
    public void aStarterRegisteredAfterTheStartStillAttributesTheWork()
            throws Exception {
        final Object datanode = new Object();
        final Object xceiverServer = new Object();
        // DataNode start-up, before the workload registers the node: the
        // server thread is started from the DataNode's own frame.
        long frame = Identity.enterFrame("<a.DataNode: void start()>",
                datanode);
        final CountDownLatch registered = new CountDownLatch(1);
        final AtomicReference<String> before = new AtomicReference<>();
        final AtomicReference<String> after = new AtomicReference<>();
        Thread server = new Thread(new Runnable() {
            @Override
            public void run() {
                Identity.enterFrame("<a.DataXceiverServer: void run()>",
                        xceiverServer);
                SourceRef unnamed = Attribution.resolve(null);
                before.set(unnamed == null ? "" : unnamed.key());
                try {
                    registered.await();
                } catch (InterruptedException interrupted) {
                    return;
                }
                SourceRef named = Attribution.resolve(null);
                after.set(named == null ? "" : named.key());
            }
        });
        Identity.startWork("<a.DataNode: void start()>#u7", server);
        server.start();
        Identity.exitFrame(frame);
        Thread.sleep(100L);
        RuntimeTraceContext.registerSource(datanode, DN);
        registered.countDown();
        server.join(5000L);
        assertEquals("nothing names the node before it is registered", "",
                before.get());
        assertEquals("the reference resolves once it is", DN.key(),
                after.get());
    }

    @Test
    public void allThreeFailingNamesNoNode() {
        Identity.enterFrame("<a.Orphan: void run()>", new Object());
        assertNull(Attribution.resolve(null));
        assertEquals("the planner's unregistered population",
                RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                RuntimeTraceContext.activationSource(null).key());
    }
}
