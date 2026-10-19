package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

@RunWith(FreshStatics.class)
public class IdentityTest {
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "SOLR_NODE", "t/node0", 0L);
    private static final SourceRef OTHER =
            new SourceRef("CLUSTER_NODE", "SOLR_NODE", "t/node1", 0L);
    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "t/dn0", 0L);
    private static final String ACCEPT = "<a.Acceptor: void run()>#u5";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Lineage.resetForTests();
        RecordingWindow.reset();
    }

    private static void on(Runnable work) throws InterruptedException {
        Thread thread = new Thread(work);
        thread.start();
        thread.join(5000L);
    }

    private static <T> T claimed(Object carrier, Function<Object, T> work)
            throws InterruptedException {
        List<T> result = new ArrayList<T>();
        on(() -> {
            Identity.claimStart(carrier);
            result.add(work.apply(carrier));
        });
        return result.get(0);
    }

    @Test
    public void aSharedConsumerCarriesEachPuttersScope() throws Exception {
        Object putter = new Object();
        Object sender = new Object();
        RuntimeTraceContext.registerSource(putter, NODE);
        RuntimeTraceContext.registerSource(sender, OTHER);
        Object call = new Object();
        long request = RuntimeTraceContext.beginRequest(putter, "heartbeat");
        Identity.startWork("<a.Chunks: void putBack(a.Chunk)>#u13", call,
                null);
        RuntimeTraceContext.endRequest(request);
        Object[] seen = new Object[1];
        on(() -> {
            long work = Identity.enterFrame("<a.Sender: void run()>", sender);
            Identity.claimItem(call);
            seen[0] = RuntimeTraceContext.explicitSource();
            Identity.exitFrame(work);
        });
        assertEquals(NODE, seen[0]);
    }

    @Test
    public void aTurnInsideAnOccurrenceRestartsNoCount() {
        String loop = "<a.Actor: void offerService()>#u3";
        String send = "<a.Actor: void sendHeartBeat()>#u5";
        String site = "HADOOP_IPC#REQUEST";
        Object[][] table = {
            {true, Arrays.asList(loop + "@0/" + send + "@0/" + site + "@0",
                    loop + "@0/" + send + "@1/" + site + "@0",
                    loop + "@0/" + send + "@2/" + site + "@0")},
            {false, Collections.nCopies(3, send + "@0/" + site + "@0")}};
        for (Object[] row : table) {
            reset();
            boolean running = (Boolean) row[0];
            Object actor = new Object();
            RuntimeTraceContext.registerSource(actor, DN);
            long request = RuntimeTraceContext.beginRequest(actor, "test");
            long run = Identity.enterFrame("<a.Actor: void run()>#u1", null);
            if (running) Identity.occurrence(DN.key(), "REGION.run", true);
            long loopFrame = Identity.enterFrame(loop, null);
            List<String> indexes = new ArrayList<String>();
            Set<String> producers = new LinkedHashSet<String>();
            for (int turn = 0; turn < 3; turn++) {
                long tick = RuntimeTraceContext.beginTick(actor, "ACTOR");
                long sendFrame = Identity.enterFrame(send, null);
                Endpoint sent = Identity.endpointAt(
                        Identity.currentOccurrence(DN.key()), site, 0);
                indexes.add(sent.siteIndex().render());
                producers.add(sent.id());
                Identity.exitFrame(sendFrame);
                RuntimeTraceContext.endTick(tick);
            }
            assertEquals("occurrence running=" + running, row[1], indexes);
            assertEquals("one producer per turn: " + producers, 3,
                    producers.size());
            Identity.exitFrame(loopFrame);
            if (running) Identity.regionExit(null);
            Identity.exitFrame(run);
            RuntimeTraceContext.endRequest(request);
        }
    }

    @Test
    public void unnamedWorkOpensNoOccurrenceUntilAHopNamesIt()
            throws Exception {
        Object daemon = new Object();
        Identity.startWork(ACCEPT, daemon, null);
        List<String> seen = claimed(daemon, carrier -> {
            List<String> said = new ArrayList<String>();
            said.add(opened("REGION.loop"));
            said.add(opened("REGION.step"));
            said.add("ordinal " + Identity.nextBranchOrdinal("loop#u3"));
            for (String turn : new String[] {"turn", "turn"}) {
                long hop = RuntimeTraceContext.beginRequest(DN, turn);
                said.add(Identity.currentOccurrence(DN.key()).render());
                said.add(opened("REGION.inner"));
                said.add("ordinals " + Identity.nextBranchOrdinal("loop#u3")
                        + "," + Identity.nextBranchOrdinal("loop#u3"));
                Identity.regionExit(null);
                RuntimeTraceContext.endRequest(hop);
                said.add(Identity.currentOccurrence(DN.key()).regionId());
            }
            Identity.regionExit(null);
            long hop = RuntimeTraceContext.beginRequest(DN, "last");
            Identity.regionExit(null);
            said.add(Identity.currentOccurrence(DN.key()).regionId());
            RuntimeTraceContext.endRequest(hop);
            return said;
        });
        String turn = DN.key() + "/region/REGION.loop/ctx:Root:CLIENT/turn#";
        assertEquals(Arrays.asList("none", "none", "ordinal 0",
                turn + "1/idx:", "none", "ordinals 1,2", "ROLE.UNKNOWN",
                turn + "2/idx:", "none", "ordinals 1,2", "ROLE.UNKNOWN",
                "ROLE.CLIENT"), seen);

        long request = RuntimeTraceContext.beginRequest(DN, "accept");
        Object named = new Object();
        Identity.startWork(ACCEPT, named, null);
        RuntimeTraceContext.endRequest(request);
        assertEquals("Root:CLIENT/accept#1", claimed(named, carrier -> {
            String first = opened("REGION.handshake");
            Identity.regionExit(null);
            return first;
        }));
    }

    private static String opened(String region) {
        OccurrenceAddress address = Identity.occurrence(DN.key(), region,
                true);
        return Identity.openedNone() ? "none" : address.context().render();
    }
}
