package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * A native reproduction's plant ({@link RecordingPlant}): which rows a
 * plant file may hold, which enclosing occurrence a row plants at, the
 * values calls return in the planted world, the agent that rewrites those
 * calls, and the plants a run cannot make real -- refused by name.
 */
public class RecordingPlantTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String SITE = "<o.a.h.ipc.Client: void send()>#u16";
    private static final String GUARD = "<o.a.h.Sasl: void handle()>#u4";
    private static final String OUTER = address("REGION.outer",
            "wl/dn1#epoch0");
    private static final String ID = OccurrenceAddress.parse(OUTER).id();
    private static final String CLOCK_SITE_ID = "<a.Keys: void roll()>#u3";
    private static final String CLOCK_CALLEE =
            "<java.lang.System: long currentTimeMillis()>";

    @Before
    @After
    public void reset() {
        RecordingPlant.resetForTests();
        RowRuntime.resetForTests();
        Sessions.resetForTests();
        Thread.interrupted();
    }

    /** One plant row, written with single quotes. */
    private static String row(String text) {
        return text.replace('\'', '"') + "\n";
    }

    private RecordingPlant.Plant read(String rows) throws IOException {
        Path plant = folder.newFile().toPath();
        Files.write(plant, rows.getBytes(StandardCharsets.UTF_8));
        return RecordingPlant.read(plant);
    }

    /** A plant file: its markers, hooks, fatal arms and anchor, or
     *  refused. */
    @Test
    public void aPlantHoldsRootsOrdersAndOneTarget() throws Exception {
        String marker = row("{'kind':'ROOT','category':'FAULT','rootId':"
                + "'FAULT:IPC','occurrence':'" + ID + "','siteId':'" + SITE
                + "','value':'true','row':0}");
        String hook = row("{'kind':'ROOT','category':'HOOK','rootId':"
                + "'HDFS.X','occurrence':'" + ID + "','value':'false',"
                + "'row':1}");
        String order = row("{'kind':'ORDER','before':'b|','after':'a|',"
                + "'row':2}");
        String event = "{'kind':'WAKE','context':'c','site':'s','k':0}";
        String realized = row("{'kind':'ORDER','scope':'EVENT','before':"
                + event + ",'after':" + event + ",'row':5}");
        String target = target(ID, "false", 3);
        Map<String, Map<String, Map<Integer, RecordingPlant.Root>>> markers =
                Collections.singletonMap(SITE, Collections.singletonMap(ID,
                        Collections.singletonMap(1,
                                new RecordingPlant.Root(0, "true"))));
        // A grown root answers its own invocation of the marker's call.
        Map<Integer, RecordingPlant.Root> invocations = new LinkedHashMap<>();
        invocations.put(1, new RecordingPlant.Root(0, "true"));
        invocations.put(2, new RecordingPlant.Root(4, "true"));
        Map<String, RecordingPlant.Root> hooks = Collections.singletonMap(
                "HDFS.X", new RecordingPlant.Root(1, "false"));
        Map<?, ?> none = Collections.emptyMap();
        Object[][] files = {
            {marker + hook + order + target, markers, hooks},
            {marker + marker.replace("\"value\"", "\"invocation\":2,"
                    + "\"value\"").replace("\"row\":0", "\"row\":4") + hook
                    + target, Collections.singletonMap(SITE,
                    Collections.singletonMap(ID, invocations)), hooks},
            // One invocation stated twice, or a k below 1.
            {marker + marker.replace("\"row\":0", "\"row\":4") + target,
                null, null},
            {marker.replace("\"value\"", "\"invocation\":0,\"value\"")
                    + target, null, null},
            {order + target, none, none},
            // The confirmed world's realized order, between events.
            {realized + target, none, none},
            // A root of a category no native run plants, a marker without
            // its call site or with no boolean, a row without its number.
            {marker.replace("FAULT", "CONFIG") + target, null, null},
            {marker.replace(SITE, "") + target, null, null},
            {marker.replace("\"true\"", "\"1\"") + target, null, null},
            {hook.replace(",\"row\":1", "") + target, null, null},
            // One root stated twice, an order naming no activation, an
            // event without its k.
            {hook + hook.replace("\"row\":1", "\"row\":4") + target, null,
                null},
            {order.replace("\"b|\"", "\"\"") + target, null, null},
            {realized.replaceFirst(",\"k\":0", "") + target, null, null},
            {row("{'kind':'CLOCK','row':0}") + target, null, null},
            // A clock root without its skew, a configuration without its
            // getters, one site named with two callees.
            {clock("", 0) + target, null, null},
            {row("{'kind':'ROOT','category':'CONFIG','rootId':'CONFIG:k',"
                    + "'occurrence':'" + ID + "','value':'7','sites':[],"
                    + "'row':0}") + target, null, null},
            {clock("5", 0) + reading("<a.Other: long now()>", 1) + target,
                null, null},
            // No target: the run could not tell what it reproduced.
            {marker, null, null},
            {marker + target + target("other", "true", 4), null, null}};
        for (Object[] file : files) {
            try {
                RecordingPlant.Plant read = read((String) file[0]);
                if (file[1] == null) fail("accepted " + file[0]);
                assertEquals((String) file[0], file[1], read.markers);
                assertEquals((String) file[0], file[2], read.hooks);
                assertEquals(Collections.singletonMap(GUARD, false),
                        read.fatalArms);
                assertEquals(ID, read.anchor);
                // The anchor and every root's mint occurrence are focused.
                assertEquals(Collections.singleton(ID), read.focused);
            } catch (IOException refused) {
                if (file[1] != null) throw refused;
            }
        }
    }

    private static String clock(String skew, int row) {
        return row("{'kind':'ROOT','category':'CLOCK','rootId':"
                + "'REGION.outer.in.c','occurrence':'" + ID + "','siteId':'"
                + CLOCK_SITE_ID + "','callee':'" + CLOCK_CALLEE + "',"
                + "'javaType':'long','clock':{'nanos':1000000,'source':"
                + "'currentTimeMillis'},'skew':'" + skew + "','row':" + row
                + "}");
    }

    private static String reading(String callee, int row) {
        return row("{'kind':'CLOCK_SITE','siteId':'" + CLOCK_SITE_ID + "',"
                + "'callee':'" + callee + "','javaType':'long','clock':"
                + "{'nanos':1000000,'source':'currentTimeMillis'},'regions':"
                + "['REGION.outer'],'row':" + row + "}");
    }

    private static String target(String occurrence, String arm, int row) {
        return row("{'kind':'TARGET','occurrence':'" + occurrence
                + "','siteId':'" + GUARD + "','value':" + arm + ",'row':"
                + row + "}");
    }

    private static String address(String region, String node) {
        return OccurrenceAddress.of(NodeId.parse(node), region,
                CausalContext.of(Role.of("CLIENT"), "heartbeat", 1),
                ExecutionIndex.empty()).render();
    }

    /**
     * A plant takes only where the run can make it real: a timed wait's
     * timeout where the real call could time out (SYMBOL-SCOPE §4.2), a
     * SessionExpired as a real expiry of the door's session at its server
     * ({@link Sessions#expires}, the system's expirer).  Otherwise the world
     * is impossible, refused by name and BLOCKING, and the call runs.
     */
    @Test
    public void aPlantTheRunCannotMakeRealIsRefused() throws Exception {
        Path root = folder.getRoot().toPath();
        Fixtures.openSession(root);
        CountDownLatch open = new CountDownLatch(0);
        CountDownLatch closed = new CountDownLatch(1);
        ArrayBlockingQueue<String> holding = new ArrayBlockingQueue<>(1);
        holding.add("x");
        ReentrantLock heldHere = new ReentrantLock();
        heldHere.lock();
        ReentrantReadWriteLock rw = new ReentrantReadWriteLock();
        rw.writeLock().lock();
        String free = "the lock is free or held by this thread";
        Object[][] rows = {
            // what is waited on, the permits asked, why it answers at once
            {open, 1, "the latch is open"},
            {closed, 1, null},
            {CompletableFuture.completedFuture("x"), 1, "the future is done"},
            {new CompletableFuture<String>(), 1, null},
            {holding, 1, "the queue holds an element"},
            {new ArrayBlockingQueue<String>(1), 1, null},
            {new ReentrantLock(), 1, free},
            {heldHere, 1, free},
            {rw.writeLock(), 1, "the write lock is held by this thread"},
            {new Semaphore(2), 2, "the semaphore has the permits"},
            {new Semaphore(1), 2, null},
            {null, 1, null}};
        for (Object[] row : rows) {
            assertEquals(String.valueOf(row[0]), row[2],
                    TimedWaits.answeredAtOnce(row[0], (Integer) row[1]));
        }
        Thread.currentThread().interrupt();
        assertEquals("the thread is interrupted, so the wait throws at once",
                TimedWaits.answeredAtOnce(closed, 1));
        Thread.interrupted();
        assertTrue(TimedWaits.timesOut(closed, 1, "FAULT:TIMED_WAIT:AWAIT"));
        assertFalse(TimedWaits.timesOut(open, 1, "FAULT:TIMED_WAIT:AWAIT"));

        String expiry =
                "FAULT:ZOOKEEPER:WRITE:KeeperException$SessionExpiredException";
        Object client = new Object();
        assertFalse("no expirer", Sessions.expires(client, expiry));
        List<Object> expired = new ArrayList<>();
        Sessions.expirer(owner -> expired.add(owner));
        assertTrue(Sessions.expires(client, expiry));
        assertEquals(Collections.singletonList(client), expired);
        assertTrue("the owner it was asked about", expired.get(0) == client);
        Sessions.expirer(owner -> false);
        assertFalse(Sessions.expires(null, expiry));
        Sessions.expirer(owner -> {
            throw new IllegalStateException("server gone");
        });
        assertFalse(Sessions.expires(client, expiry));

        List<GapRow> gaps = Fixtures.gaps(root);
        String[][] why = {
            {"FAULT:TIMED_WAIT:AWAIT", "the latch is open"},
            {expiry, "no system expirer is registered"},
            {expiry, "knows no session of a static door"},
            {expiry, "failed: java.lang"}};
        assertEquals(why.length, gaps.size());
        for (int at = 0; at < why.length; at++) {
            assertEquals(GapKind.ASSIGNMENT_UNPLANTED, gaps.get(at).kind());
            assertEquals(GapClass.BLOCKING, gaps.get(at).cls());
            assertTrue(gaps.get(at).detail(),
                    gaps.get(at).detail().contains(why[at][1]));
            assertTrue(gaps.get(at).subject(),
                    gaps.get(at).subject().startsWith(why[at][0]));
        }
    }
}
