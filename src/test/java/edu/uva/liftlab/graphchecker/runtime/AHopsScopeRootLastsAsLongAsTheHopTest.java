package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * A served message opens a scope root for its own occurrence; when the
 * message's scope ends, the thread's own root is back, and the frames that
 * name the thread stand in every later occurrence of it.
 */
public class AHopsScopeRootLastsAsLongAsTheHopTest {
    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "t/nn0", 0L);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
    }

    @Test
    public void theThreadsOwnFramesStandAgainAfterAServedMessage()
            throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NN);
        long request = RuntimeTraceContext.beginRequest(node, "poll");
        final Object carried = RuntimeTraceContext.captureScope();
        RuntimeTraceContext.endRequest(request);
        final String[] later = new String[1];
        Thread poller = new Thread(new Runnable() {
            @Override
            public void run() {
                long base = Identity.enterFrame(
                        "<a.Poller: void run()>#u1", null);
                long served = RuntimeTraceContext.enterCarriedScope(
                        carried, "IPC_HANDLER", null);
                RuntimeTraceContext.exitCarriedScope(served);
                long call = Identity.enterFrame(
                        "<a.Client: Object call()>#u2", null);
                later[0] = Identity.atScope().render();
                Identity.exitFrame(call);
                Identity.exitFrame(base);
            }
        });
        poller.start();
        poller.join(5000L);
        assertEquals("<a.Poller: void run()>#u1@0/<a.Client: Object call()>#u2@0",
                later[0]);
    }
}
