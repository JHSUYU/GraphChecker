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
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
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
import org.junit.runner.RunWith;
import org.junit.rules.TemporaryFolder;

@RunWith(FreshStatics.class)
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
        Thread.interrupted();
    }

    private static String row(String text) {
        return text.replace('\'', '"') + "\n";
    }

    private RecordingPlant.Plant read(String rows) throws IOException {
        Path plant = folder.newFile().toPath();
        Files.write(plant, rows.getBytes(StandardCharsets.UTF_8));
        return RecordingPlant.read(plant);
    }

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
            {marker + marker.replace("\"row\":0", "\"row\":4") + target,
                null, null},
            {marker.replace("\"value\"", "\"invocation\":0,\"value\"")
                    + target, null, null},
            {order + target, none, none},
            {realized + target, none, none},
            {marker.replace("FAULT", "CONFIG") + target, null, null},
            {marker.replace(SITE, "") + target, null, null},
            {marker.replace("\"true\"", "\"1\"") + target, null, null},
            {hook.replace(",\"row\":1", "") + target, null, null},
            {hook + hook.replace("\"row\":1", "\"row\":4") + target, null,
                null},
            {order.replace("\"b|\"", "\"\"") + target, null, null},
            {realized.replaceFirst(",\"k\":0", "") + target, null, null},
            {row("{'kind':'CLOCK','row':0}") + target, null, null},
            {clock("", 0) + target, null, null},
            {row("{'kind':'ROOT','category':'CONFIG','rootId':'CONFIG:k',"
                    + "'occurrence':'" + ID + "','value':'7','sites':[],"
                    + "'row':0}") + target, null, null},
            {clock("5", 0) + reading("<a.Other: long now()>", 1) + target,
                null, null},
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
                assertEquals(Collections.singleton(ID), read.focused);
            } catch (IOException refused) {
                if (file[1] != null) throw refused;
            }
        }
    }

    public static final class Holder {
        private boolean flag = true;

        public boolean read() {
            return flag;
        }

        public boolean other() {
            return flag;
        }
    }

    private static final String HOLDER = Holder.class.getName();
    private static final String FLAG = "<" + HOLDER + ": boolean flag>";
    private static final String READ = "<" + HOLDER + ": boolean read()>#u2";

    private static String field(String field, String reads, int row) {
        return row("{'kind':'ROOT','category':'CONFIG','rootId':"
                + "'CONFIG:flag==true','occurrence':'" + ID + "','field':'"
                + field + "','reads':[" + reads + "],'value':'false','row':"
                + row + "}");
    }

    @Test
    public void aConfigurationFieldIsWrittenBeforeEachPlannedRead()
            throws Exception {
        String planted = field(FLAG, "'" + READ + "'", 0)
                + target(ID, "false", 1);
        RecordingPlant.Plant plant = read(planted);
        RecordingPlant.Configured configured = plant.fields.get(FLAG);
        assertEquals(Collections.singleton(FLAG), plant.fields.keySet());
        assertEquals(new RecordingPlant.Root(0, "false"), configured.root);
        assertEquals("CONFIG:flag==true", configured.rootId);
        assertEquals(Collections.singleton(READ), configured.reads);
        assertTrue(plant.calls.isEmpty());
        assertEquals(Collections.singleton(ID), plant.focused);
        String key = "read()Z " + FLAG;
        assertEquals(Collections.singletonMap(HOLDER.replace('.', '/'),
                Collections.singleton(key)),
                RecordingPlant.interceptions(plant));
        for (String refused : new String[] {
                field(FLAG, "'" + READ + "'", 0) + field(FLAG, "'" + READ
                        + "'", 2) + target(ID, "false", 1),
                field(FLAG, "", 0) + target(ID, "false", 1),
                field("flag", "'" + READ + "'", 0) + target(ID, "false", 1)}) {
            try {
                read(refused);
                fail("accepted " + refused);
            } catch (IOException expected) {
            }
        }
        try {
            RecordingPlant.interceptions(read(field(FLAG, "'nowhere#u2'", 0)
                    + target(ID, "false", 1)));
            fail("intercepted a read in no method");
        } catch (IOException expected) {
        }

        Path file = folder.newFile().toPath();
        Files.write(file, planted.getBytes(StandardCharsets.UTF_8));
        ClassLoader parent = RecordingPlantTest.class.getClassLoader();
        byte[] bytes;
        try (InputStream in = parent.getResourceAsStream(
                HOLDER.replace('.', '/') + ".class")) {
            byte[] buffer = new byte[1 << 16];
            int length = 0;
            for (int read; (read = in.read(buffer, length,
                    buffer.length - length)) > 0; ) {
                length += read;
            }
            bytes = Arrays.copyOf(buffer, length);
        }
        final byte[] rewritten = PlantAgent.rewrite(bytes,
                Collections.singleton(key));
        Class<?> rewrittenHolder = new ClassLoader(parent) {
            Class<?> define() {
                return defineClass(HOLDER, rewritten, 0, rewritten.length);
            }
        }.define();
        Object holder = rewrittenHolder.getDeclaredConstructor().newInstance();
        System.setProperty(RecordingPlant.PROPERTY, file.toString());
        try {
            assertEquals("a read outside the planned reads is as it was",
                    true, rewrittenHolder.getMethod("other").invoke(holder));
            assertEquals("the planned read reads the world's value", false,
                    rewrittenHolder.getMethod("read").invoke(holder));
            assertEquals("written into the field, as in the VM", false,
                    rewrittenHolder.getMethod("other").invoke(holder));
        } finally {
            System.clearProperty(RecordingPlant.PROPERTY);
        }
        Holder unplanted = new Holder();
        assertEquals(true, unplanted.read());
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
