package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import java.util.concurrent.atomic.AtomicReference;
import org.junit.Before;
import org.junit.Test;

/**
 * What a node's startup starts or creates is the node's, though the test's
 * request stands where it runs ({@link RuntimeTraceContext#beginNodeStartup}):
 * a thread started under a hop (rule 4, its start's carried node) and one
 * created with no start (rule 3, its creator's).  A construction names its
 * node from its first moment, before the node is built and registered; the
 * start of a registered node's thread names that node, and a restart's (the
 * node's slot moved to its next epoch first) that epoch.  The thread running
 * the startup keeps its own node.  Outside a startup both are the test's
 * client, as before.
 */
public class ANodesStartupIsTheNodesTest {
    private static final SourceRef CLIENT =
            new SourceRef("EXTERNAL_APP", "DFS_CLIENT", "t/client0", 0L);
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private static final SourceRef RESTARTED =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 1L);

    private enum Startup { CONSTRUCTION, START, RESTART, NONE }

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        ScheduleLog.resetForTests();
    }

    @Test
    public void whatAStartupStartsOrCreatesIsTheNodes() throws Exception {
        Object[][] table = {
            // a construction, named before the node is registered
            {Startup.CONSTRUCTION, true, NODE},
            {Startup.CONSTRUCTION, false, NODE},
            // the start of a registered node's thread
            {Startup.START, true, NODE},
            {Startup.START, false, NODE},
            // a restart: the node's next epoch
            {Startup.RESTART, true, RESTARTED},
            {Startup.RESTART, false, RESTARTED},
            // no startup: the test's request carries its client
            {Startup.NONE, true, CLIENT},
            {Startup.NONE, false, CLIENT},
        };
        for (Object[] row : table) {
            reset();
            Startup startup = (Startup) row[0];
            boolean started = (Boolean) row[1];
            assertEquals(startup + " started=" + started,
                    ((SourceRef) row[2]).key(), attributed(startup, started));
        }
    }

    /**
     * The test's thread, in its request, starts or creates one of a node's
     * threads, in a startup or not.
     *
     * @return the node that thread's work is attributed to, asked while the
     *         node is still unregistered unless the startup is a START or a
     *         RESTART
     */
    private static String attributed(Startup startup, boolean started)
            throws InterruptedException {
        Object client = new Object();
        Object slot = new Object();
        RuntimeTraceContext.registerSource(client, CLIENT);
        if (startup == Startup.START || startup == Startup.RESTART) {
            RuntimeTraceContext.registerSource(slot, NODE);
        }
        if (startup == Startup.RESTART) {
            RuntimeTraceContext.restartSource(slot, RESTARTED);
        }
        long request = RuntimeTraceContext.beginRequest(client, "test");
        long token = startup == Startup.CONSTRUCTION
                ? RuntimeTraceContext.beginNodeStartup(NODE)
                : startup == Startup.NONE ? 0L
                : RuntimeTraceContext.beginNodeStartup(
                        RuntimeTraceContext.sourceFor(slot));
        assertEquals("the thread running the startup keeps its node",
                CLIENT.key(), Attribution.resolve(null).key());
        AtomicReference<String> node = new AtomicReference<>("");
        Thread thread = new Thread(() -> {
            SourceRef resolved = Attribution.resolve(null);
            node.set(resolved == null ? "" : resolved.key());
        });
        if (started) {
            Identity.startWork("<a.Cluster: void startup()>#u3", thread);
        }
        thread.start();
        thread.join(5000L);
        RuntimeTraceContext.endNodeStartup(token);
        RuntimeTraceContext.endRequest(request);
        return node.get();
    }
}
