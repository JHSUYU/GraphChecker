package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

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

    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private static final String LOOP = "<a.Actor: void offerService()>#u3";
    private static final String SEND = "<a.Actor: void sendHeartBeat()>#u5";
    private static final String SITE = "HADOOP_IPC#REQUEST";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        Lineage.resetForTests();
        ScheduleLog.resetForTests();
    }

    /**
     * An occurrence's events count under the root hop it was opened under,
     * whatever root hop opens inside it: a daemon's region entered under a
     * request (a startup window) runs every turn inside one occurrence, whose
     * address names no turn, so each turn's send has an index of its own
     * (round HG5A, hdfs-adhoc-21: three heartbeats at one producer
     * endpoint).  Where no occurrence runs, each turn counts afresh: its
     * context, the turn's root, tells its sends apart.
     */
    @Test
    public void aTurnInsideAnOccurrenceRestartsNoCount() {
        Object[][] table = {
            {true, Arrays.asList(LOOP + "@0/" + SEND + "@0/" + SITE + "@0",
                    LOOP + "@0/" + SEND + "@1/" + SITE + "@0",
                    LOOP + "@0/" + SEND + "@2/" + SITE + "@0")},
            {false, Arrays.asList(SEND + "@0/" + SITE + "@0",
                    SEND + "@0/" + SITE + "@0", SEND + "@0/" + SITE + "@0")},
        };
        for (Object[] row : table) {
            reset();
            boolean running = (Boolean) row[0];
            Object actor = new Object();
            RuntimeTraceContext.registerSource(actor, DN);
            long request = RuntimeTraceContext.beginRequest(actor, "test");
            long run = Identity.enterFrame("<a.Actor: void run()>#u1", null);
            if (running) Identity.occurrence(DN.key(), "REGION.run", true);
            long loop = Identity.enterFrame(LOOP, null);
            List<String> indexes = new ArrayList<String>();
            Set<String> producers = new LinkedHashSet<String>();
            for (int turn = 0; turn < 3; turn++) {
                long tick = RuntimeTraceContext.beginTick(actor, "ACTOR");
                long send = Identity.enterFrame(SEND, null);
                Endpoint sent = Identity.endpointAt(
                        Identity.currentOccurrence(DN.key()), SITE, 0);
                indexes.add(sent.siteIndex().render());
                producers.add(sent.id());
                Identity.exitFrame(send);
                RuntimeTraceContext.endTick(tick);
            }
            assertEquals("occurrence running=" + running, row[1], indexes);
            assertEquals("one producer per turn, running=" + running + ": "
                    + producers, 3, producers.size());
            Identity.exitFrame(loop);
            if (running) Identity.regionExit();
            Identity.exitFrame(run);
            RuntimeTraceContext.endRequest(request);
        }
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
