package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
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
            Identity.claimItem(call, null);
            seen[0] = RuntimeTraceContext.explicitSource();
            Identity.exitFrame(work);
        });
        assertEquals(NODE, seen[0]);
    }

    @Test
    public void anItemPendingInTwoQueuesIsClaimedUnderTheQueueItCameOutOf()
            throws Exception {
        String sync = "<a.Server: void commitRequest(a.Request)>#u3";
        String commit = "<a.Server: void commitRequest(a.Request)>#u7";
        Object[][] table = {
            {"sync, commit", "sync", sync, commit},
            {"commit, sync", "sync", sync, commit},
            {"sync, commit", "commit", commit, sync},
            {"commit, sync", "commit", commit, sync},
            {"sync, commit", "other", commit, sync},
            {"commit, sync", "other", sync, commit}};
        for (Object[] row : table) {
            reset();
            Object source = new Object();
            RuntimeTraceContext.registerSource(source, DN);
            Map<String, BlockingQueue<Object>> queues =
                    new HashMap<String, BlockingQueue<Object>>();
            for (String name : new String[] {"sync", "commit", "other"}) {
                queues.put(name, new LinkedBlockingQueue<Object>());
            }
            Object item = new Object();
            long request = RuntimeTraceContext.beginRequest(source, "test");
            for (String put : ((String) row[0]).split(", ")) {
                Identity.startWork("sync".equals(put) ? sync : commit, item,
                        queues.get(put));
            }
            RuntimeTraceContext.endRequest(request);
            List<String> stood = new ArrayList<String>();
            on(() -> {
                long run = Identity.enterFrame("<a.Sync: void run()>", null);
                Identity.claimItem(item, queues.get((String) row[1]));
                stood.add(Identity.occurrence(DN.key(), "REGION.sync", true)
                        .render());
                Identity.regionExit(null);
                Identity.exitFrame(run);
            });
            String said = row[0] + " taken from " + row[1] + ": " + stood;
            assertEquals(said, true, stood.get(0).contains((String) row[2])
                    && !stood.get(0).contains((String) row[3]));
        }
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

    @Test
    public void aContinuationStandsAtItsRegistrantsAddressWhereverItRuns()
            throws Exception {
        String site = "HBASE_RPC#REQUEST:MasterService.MoveRegion";
        List<List<String>> stood = new ArrayList<List<String>>();
        for (boolean inline : new boolean[] {true, false}) {
            reset();
            Object client = new Object();
            Object loop = new Object();
            RuntimeTraceContext.registerSource(client, DN);
            RuntimeTraceContext.registerSource(loop, DN);
            long request = RuntimeTraceContext.beginRequest(client, "test");
            long test = Identity.enterFrame("<a.Test: void move()>#u2", null);
            List<String> seen = new ArrayList<String>();
            BiConsumer<Object, Object> carried = Continuations.carry(
                    (value, error) -> {
                        OccurrenceAddress at = Identity.occurrence(DN.key(),
                                "REGION.call", true);
                        seen.add(at.render());
                        seen.add(Identity.endpointAt(Identity
                                .currentOccurrence(DN.key()), site, 0).id());
                        seen.add(ScheduleLog.contextOf(
                                Identity.contextHere()));
                        seen.add("inbound " + MessageDoors.current());
                        Identity.regionExit(null);
                    });
            Identity.startWork("<a.Admin: void move()>#u4", carried, null);
            if (inline) {
                carried.accept(null, null);
            } else {
                on(() -> {
                    long reply = RuntimeTraceContext.beginRequest(loop,
                            "reply");
                    long finish = Identity.enterFrame(
                            "<a.Connection: void finishCall()>#u3", null);
                    Identity.occurrence(DN.key(), "REGION.finish", true);
                    MessageDoors.putBack(MessageDoors.Inbound.EMPTY);
                    carried.accept(null, null);
                    assertEquals(MessageDoors.Inbound.EMPTY,
                            MessageDoors.current());
                    assertEquals("REGION.finish", Identity.currentOccurrence(
                            DN.key()).regionId());
                    MessageDoors.putBack(null);
                    Identity.regionExit(null);
                    Identity.exitFrame(finish);
                    RuntimeTraceContext.endRequest(reply);
                });
            }
            Identity.exitFrame(test);
            RuntimeTraceContext.endRequest(request);
            stood.add(seen);
        }
        assertEquals(stood.get(0), stood.get(1));
        String registered = "<a.Admin: void move()>#u4:";
        List<String> inline = stood.get(0);
        assertEquals("inbound null", inline.get(3));
        Object[][] table = {
            {inline.get(0), DN.key() + "/region/REGION.call/ctx:Root:CLIENT/"
                    + "test#1/idx:<a.Test: void move()>#u2@0/" + registered},
            {inline.get(2), DN.key() + "|Root:CLIENT/test#1|<a.Test: void"
                    + " move()>#u2@0>" + registered}};
        for (Object[] row : table) {
            String said = (String) row[0];
            assertEquals(said, true, said.startsWith((String) row[1])
                    && said.endsWith("@0"));
        }
    }

    @Test
    public void aHandOffStandsOnItsStartWhateverItsWorkerRanBefore()
            throws Exception {
        String call = "<a.Worker: java.lang.Object call()>";
        String body = "<a.Step: void body()>";
        String submit = "<a.Admin: void submit()>#u4";
        String next = "<a.Step: void run()>#u23";
        List<List<String>> stood = new ArrayList<List<String>>();
        for (int before : new int[] {0, 2}) {
            reset();
            Object source = new Object();
            RuntimeTraceContext.registerSource(source, DN);
            long request = RuntimeTraceContext.beginRequest(source, "test");
            Object first = new Object();
            Object second = new Object();
            Identity.startWork(submit, first, handOffs());
            RuntimeTraceContext.endRequest(request);
            List<String> seen = new ArrayList<String>();
            for (Object step : new Object[] {first, second}) {
                on(() -> {
                    for (int earlier = 0; earlier < before; earlier++) {
                        Identity.exitFrame(Identity.enterFrame(call, null));
                    }
                    long worker = Identity.enterFrame(call, null);
                    long claim = Identity.claimStart(step);
                    long run = Identity.enterFrame(body, null);
                    seen.add(Identity.occurrence(DN.key(), "REGION.step",
                            true).render());
                    if (step == first) {
                        Identity.startWork(next, second, handOffs());
                    }
                    Identity.regionExit(null);
                    Identity.exitFrame(run);
                    Identity.endClaim(claim);
                    Identity.exitFrame(worker);
                });
            }
            stood.add(seen);
        }
        assertEquals(stood.get(0), stood.get(1));
        String idx = "/idx:" + submit + "@0/" + body + "@0";
        Object[][] table = {
            {stood.get(0).get(0), idx},
            {stood.get(0).get(1), idx + "/" + next + "@0/" + body + "@0"}};
        for (Object[] row : table) {
            String said = (String) row[0];
            assertEquals(said, true, said.endsWith((String) row[1]));
        }
    }

    @Test
    public void aHandOffItsStarterRunsInlineKeepsItsStartersFrames()
            throws Exception {
        String test = "<a.Test: void run()>#u2";
        String submit = "<a.Admin: void submit()>#u4";
        String body = "<a.Step: void body()>";
        Object source = new Object();
        RuntimeTraceContext.registerSource(source, DN);
        long request = RuntimeTraceContext.beginRequest(source, "test");
        long frame = Identity.enterFrame(test, null);
        Object step = new Object();
        Identity.startWork(submit, step, handOffs());
        long claim = Identity.claimStart(step);
        long run = Identity.enterFrame(body, null);
        String at = Identity.occurrence(DN.key(), "REGION.step", true)
                .render();
        Identity.regionExit(null);
        Identity.exitFrame(run);
        Identity.endClaim(claim);
        Identity.exitFrame(frame);
        RuntimeTraceContext.endRequest(request);
        assertEquals(DN.key() + "/region/REGION.step/ctx:Root:CLIENT/test#1"
                + "/idx:" + test + "@0/" + submit + "@0/" + body + "@0", at);
    }

    private static ThreadPoolExecutor handOffs() {
        return new ThreadPoolExecutor(0, 1, 1L, TimeUnit.SECONDS,
                new SynchronousQueue<Runnable>());
    }

    @Test
    @FreshStatics.Rows(4)
    public void aHandOffServesOnlyWorkAnotherThreadStarted() throws Exception {
        String step = "<a.Step: void run()>#u23";
        Object[][] table = {
                {"its own inline continuation", false},
                {"a task another thread filed", true},
                {"a task a thread that ended filed", true},
                {"an item no start filed", true},
        };
        int row = FreshStatics.row();
        Object source = new Object();
        RuntimeTraceContext.registerSource(source, DN);
        long request = RuntimeTraceContext.beginRequest(source, "test");
        Object handOff = new Object();
        Identity.startWork(step, handOff, new ThreadPoolExecutor(0, 1, 1L,
                TimeUnit.SECONDS, new SynchronousQueue<Runnable>()));
        Object task = new Object();
        if (row == 1) Identity.startWork("<a.Pool: void submit()>#u4", task,
                null);
        if (row == 2) {
            on(() -> {
                long ended = RuntimeTraceContext.beginRequest(source, "test");
                Identity.startWork("<a.Pool: void submit()>#u4", task, null);
                RuntimeTraceContext.endRequest(ended);
            });
        }
        RuntimeTraceContext.endRequest(request);
        on(() -> {
            long claim = Identity.claimStart(handOff);
            if (row == 0) {
                BiConsumer<Object, Object> carried = Continuations.carry(
                        (value, error) -> {
                        });
                Identity.startWork("<a.Step: void write()>#u3", carried,
                        null);
                carried.accept(null, null);
            } else if (row == 3) {
                Identity.claimItem(task, null);
            } else {
                Identity.endClaim(Identity.claimStart(task));
            }
            Identity.endClaim(claim);
        });
        boolean serving = false;
        for (String start : Identity.servingTasks()) {
            serving |= start.contains(step);
        }
        assertEquals((String) table[row][0], table[row][1], serving);
    }

    @Test
    public void everyRegionEntryClosesTheWorkItClaimedInsideIt()
            throws Exception {
        long request = RuntimeTraceContext.beginRequest(DN, "propose");
        long producing = Identity.enterFrame("<a.Leader: void propose()>#u2",
                null);
        Object[] items = new Object[6];
        for (int k = 0; k < items.length; k++) {
            items[k] = new Object();
            Identity.startWork("<a.Handler: void queuePacket(a.Packet)>#u5",
                    items[k], null);
        }
        Identity.exitFrame(producing);
        RuntimeTraceContext.endRequest(request);
        Object daemon = new Object();
        Identity.startWork(ACCEPT, daemon, null);
        List<String> seen = claimed(daemon, carrier -> {
            List<String> said = new ArrayList<String>();
            int before = Identity.depth();
            said.add(opened("REGION.drain"));
            Identity.claimItem(items[0], null);
            Identity.regionExit(null);
            said.add("an unnamed entry draining a queue closes at "
                    + Identity.depth() + " of " + before);
            long hop = RuntimeTraceContext.beginRequest(DN, "turn");
            int outer = Identity.depth();
            opened("REGION.run");
            Identity.claimItem(items[1], null);
            Identity.claimItem(items[2], null);
            int claimed = Identity.depth();
            opened("REGION.accessor");
            Identity.regionExit(null);
            said.add("a folded entry inside a claimed item keeps it at "
                    + Identity.depth() + " of " + claimed);
            Identity.regionExit(null);
            said.add("an occurrence draining a queue closes at "
                    + Identity.depth() + " of " + outer);
            opened("REGION.run");
            int folded = Identity.depth();
            opened("REGION.drain");
            Identity.claimItem(items[3], null);
            Identity.claimItem(items[4], null);
            Identity.regionExit(null);
            said.add("a folded entry draining a queue closes at "
                    + Identity.depth() + " of " + folded);
            long call = Identity.enterFrame("<a.Sender: void run()>#u3", null);
            int framed = Identity.depth();
            opened("REGION.send");
            Identity.claimItem(items[5], null);
            Identity.regionExit(null);
            said.add("an entry inside its method frame closes at "
                    + Identity.depth() + " of " + framed);
            Identity.exitFrame(call);
            said.add("and its frame's exit agrees at "
                    + Identity.depth() + " of " + folded);
            Identity.regionExit(null);
            RuntimeTraceContext.endRequest(hop);
            return said;
        });
        assertEquals("none", seen.get(0));
        for (String row : seen.subList(1, seen.size())) {
            String[] depths = row.substring(row.lastIndexOf(" at ") + 4)
                    .split(" of ");
            assertEquals(row, depths[1], depths[0]);
        }
        assertEquals(7, seen.size());
    }

    private static String opened(String region) {
        OccurrenceAddress address = Identity.occurrence(DN.key(), region,
                true);
        return Identity.openedNone() ? "none" : address.context().render();
    }
}
