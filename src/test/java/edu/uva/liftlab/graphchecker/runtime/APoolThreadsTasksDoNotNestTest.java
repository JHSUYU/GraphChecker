package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * A pool thread runs one task after another, and a task may run a task of
 * its own (a FutureTask inside an executor's wrapper).  When the nested one
 * ends, the task that ran it still stands, and when that one ends the next
 * task starts from the thread's base: tasks run in sequence never nest.
 */
public class APoolThreadsTasksDoNotNestTest {
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "SOLR_NODE", "t/node0", 0L);
    private static final String SUBMIT = "<a.Shards: void submit(a.Req)>#u7";
    private static final String EXECUTE = "<a.Pool: void execute(java.lang.Runnable)>#u58";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
    }

    @Test
    public void eachTaskOnAPoolThreadStartsFromItsBase() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        long request = RuntimeTraceContext.beginRequest(node, "update");
        final Object[] wrappers = {new Object(), new Object()};
        final Object[] callables = {new Object(), new Object()};
        for (int task = 0; task < 2; task++) {
            Identity.startWork(SUBMIT, callables[task]);
            Identity.startWork(EXECUTE, wrappers[task]);
        }
        RuntimeTraceContext.endRequest(request);

        final String[] chains = new String[2];
        Thread pool = new Thread(() -> {
            for (int task = 0; task < 2; task++) {
                Identity.claimStart(wrappers[task]);
                long wrapper = Identity.enterFrame(
                        "<a.Pool: void lambda$execute$0()>#u3", null);
                Identity.claimStart(callables[task]);
                long call = Identity.enterFrame(
                        "<a.Shards: java.lang.Object call()>#u1", null);
                chains[task] = Identity.handoffs();
                Identity.exitFrame(call);
                Identity.exitFrame(wrapper);
            }
        });
        pool.start();
        pool.join(5000L);
        assertEquals("the second task nests in no finished one: " + chains[1],
                hops(chains[0]), hops(chains[1]));
    }

    private static int hops(String chain) {
        return chain.isEmpty() ? 0 : chain.split(">").length;
    }
}
