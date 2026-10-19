package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

/**
 * THE attribution rule, one case per rule: an explicit scope, then the
 * innermost registered receiver on the stack, then the starter by reference
 * (its node by the same rules, its inherited node included) -- and nothing
 * when all fail; what a node's startup starts or creates is the node's; the
 * scope and window index a thread inherits.
 */
@RunWith(FreshStatics.class)
public class AttributionTest {
    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "t/nn0", 0L);
    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);

    @Before
    @After
    public void reset() {
        RuntimeTraceContext.resetForTests();
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
}
