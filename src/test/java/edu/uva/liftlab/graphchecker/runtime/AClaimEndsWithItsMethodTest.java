package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

/**
 * A work entry's claim ends when the work returns, as the weave brackets
 * every work entry ({@code Identity#claimStart}, {@code #endClaim}): tasks
 * run in sequence never nest, a task its starter runs itself stands on the
 * starter's frames once, and an event loop's callbacks run on none of the
 * last task's frames.  A queue item carries its putter's scope to
 * whichever consumer takes it.
 */
public class AClaimEndsWithItsMethodTest {
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "SOLR_NODE", "t/node0", 0L);
    private static final SourceRef OTHER =
            new SourceRef("CLUSTER_NODE", "SOLR_NODE", "t/node1", 0L);
    private static final String SUBMIT = "<a.Shards: void submit(a.Req)>#u7";
    private static final String EXECUTE =
            "<a.Pool: void execute(java.lang.Runnable)>#u58";
    private static final String SEND =
            "<a.Conn: void sendRequest(a.Call)>#u5";
    private static final String PUT_BACK =
            "<a.Chunks: void putBack(a.Chunk)>#u13";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
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
                // A FutureTask inside an executor's wrapper: the nested
                // task stands on the wrapper while it runs.
                long claim = Identity.claimStart(wrappers[task]);
                long wrapper = Identity.enterFrame(
                        "<a.Pool: void lambda$execute$0()>#u3", null);
                chains[task] = runTask(callables[task],
                        "<a.Shards: java.lang.Object call()>#u1");
                Identity.exitFrame(wrapper);
                Identity.endClaim(claim);
            }
        });
        pool.start();
        pool.join(5000L);
        assertEquals("the second task nests in no finished one: " + chains[1],
                hops(chains[0]), hops(chains[1]));
    }

    @Test
    public void aLoopsCallbacksStandOnNoFinishedTask() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        long request = RuntimeTraceContext.beginRequest(node, "put");
        Object first = new Object();
        Identity.startWork(SEND, first);
        RuntimeTraceContext.endRequest(request);
        final String[] chains = new String[4];
        Thread loop = new Thread(() -> {
            chains[0] = runTask(first, "<a.Conn$1: void run()>");
            for (int send = 1; send < chains.length; send++) {
                // A response's callback, under its own hop and no claim,
                // sends the next call, which this loop runs at once.
                long response = RuntimeTraceContext.beginRequest(node,
                        "response");
                long callback = Identity.enterFrame(
                        "<a.Registry$1: void accept(java.lang.Object)>", null);
                Object next = new Object();
                Identity.startWork(SEND, next);
                chains[send] = runTask(next, "<a.Conn$1: void run()>");
                Identity.exitFrame(callback);
                RuntimeTraceContext.endRequest(response);
            }
        });
        loop.start();
        loop.join(5000L);
        assertEquals("the queued task: its starter's start", 1,
                hops(chains[0]));
        for (int send = 1; send < chains.length; send++) {
            assertEquals("a task its starter runs itself adds its start "
                    + "frame alone, on no task before it: " + chains[send],
                    1, hops(chains[send]));
        }
    }

    @Test
    public void aSharedConsumerCarriesEachPuttersScope() throws Exception {
        Object putter = new Object();
        Object sender = new Object();
        RuntimeTraceContext.registerSource(putter, NODE);
        RuntimeTraceContext.registerSource(sender, OTHER);
        Object call = new Object();
        long request = RuntimeTraceContext.beginRequest(putter, "heartbeat");
        Identity.startWork(PUT_BACK, call);
        RuntimeTraceContext.endRequest(request);
        final Object[] seen = new Object[1];
        Thread consumer = new Thread(() -> {
            long work = Identity.enterFrame("<a.Sender: void run()>", sender);
            Identity.claimItem(call);
            seen[0] = RuntimeTraceContext.explicitSource();
            Identity.exitFrame(work);
        });
        consumer.start();
        consumer.join(5000L);
        assertEquals("one sender serves every node's calls, each in its "
                + "putter's scope", NODE, seen[0]);
    }

    @Test
    public void aClaimAnExceptionLeftEndsWithTheWorkAroundIt() {
        long outer = Identity.claimStart(new Object());
        long inner = Identity.claimStart(new Object());
        Identity.endClaim(outer);
        Identity.endClaim(inner);
        assertNull("no claim stands", Identity.claimedStart());
    }

    /** How many frames a chain of handoffs renders ({@code site@k}). */
    private static int hops(String chain) {
        return chain.split("@\\d+", -1).length - 1;
    }
}
