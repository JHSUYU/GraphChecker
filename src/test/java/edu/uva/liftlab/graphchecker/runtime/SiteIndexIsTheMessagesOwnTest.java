package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * A served message's endpoints are indexed from the message's own scope
 * root: the pool thread that happened to serve it, and what that thread did
 * before, are no part of the message's identity.
 */
public class SiteIndexIsTheMessagesOwnTest {
    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "t/nn0", 0L);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
    }

    @Test
    public void twoPoolThreadsServingOneMessageIndexItsSendAlike()
            throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NN);
        long request = RuntimeTraceContext.beginRequest(node, "restart");
        final Object carried = RuntimeTraceContext.captureScope();
        RuntimeTraceContext.endRequest(request);
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
                            carried, "IPC_HANDLER", null);
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
    }
}
