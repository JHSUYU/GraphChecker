package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * A served message opens a scope root for its own occurrence, and its
 * endpoints are indexed from that root: the pool thread that happened to
 * serve it, and what that thread did before, are no part of the message's
 * identity.  When the message's scope ends, the thread's own root is back,
 * and the frames that name the thread stand in every later occurrence of it.
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
        long restart = RuntimeTraceContext.beginRequest(node, "restart");
        final Object message = RuntimeTraceContext.captureScope();
        RuntimeTraceContext.endRequest(restart);
        final String[] rendered = new String[2];
        for (int handler = 0; handler < 2; handler++) {
            final int which = handler;
            Thread pool = new Thread(new Runnable() {
                @Override
                public void run() {
                    // The handler's own history before the message: one
                    // frame deep on the first, two on the second.
                    long base = Identity.enterFrame(
                            "<a.Server: void start()>#u31", null);
                    long more = which == 1 ? Identity.enterFrame(
                            "<a.Server$Handler: void run()>#u2", null) : 0L;
                    long scope = RuntimeTraceContext.enterCarriedScope(
                            message, "IPC_HANDLER", null);
                    Endpoint sent = Identity.endpointAt(
                            Identity.roleOccurrence(NN.key(),
                                    Role.of("IPC_HANDLER")),
                            "HADOOP_IPC#RESPONSE", 0);
                    rendered[which] = sent.siteIndex().render();
                    RuntimeTraceContext.exitCarriedScope(scope);
                    if (which == 1) Identity.exitFrame(more);
                    Identity.exitFrame(base);
                }
            });
            pool.start();
            pool.join(5000L);
        }
        assertEquals("the message's send is indexed from its scope root, "
                + "whichever thread served it", rendered[0], rendered[1]);
        assertFalse("the handler's own frames are below that root: "
                + rendered[0], rendered[0].contains("#u31"));

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
