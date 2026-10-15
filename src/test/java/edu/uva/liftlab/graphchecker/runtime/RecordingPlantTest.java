package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertArrayEquals;
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
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
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
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

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
    private static final String INNER = address("REGION.inner",
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

    /**
     * Which enclosing occurrence (innermost first) answers: the innermost
     * one a marker's rows plant at; for a hook the innermost one the
     * confirmation focuses; for a fatal decision the anchor's, at any depth.
     */
    @Test
    public void theInnermostPlantedEnclosingOccurrenceAnswers() {
        List<String> both = Arrays.asList(INNER, OUTER);
        List<String> inner = Collections.singletonList(INNER);
        List<String> outer = Collections.singletonList(OUTER);
        List<String> nothing = Collections.emptyList();
        Object[][] calls = {
            // enclosing, the marker's planted occurrence, it, the hook's,
            // the anchor's
            {both, OUTER, OUTER, OUTER, OUTER},
            {both, INNER, INNER, OUTER, OUTER},
            {inner, OUTER, null, null, null},
            {outer, OUTER, OUTER, OUTER, OUTER},
            {nothing, OUTER, null, null, null}};
        for (Object[] call : calls) {
            @SuppressWarnings("unchecked")
            List<String> enclosing = (List<String>) call[0];
            String why = Arrays.toString(call);
            assertEquals(why, call[2], RecordingPlant.plantedOccurrence(
                    Collections.singletonMap(OccurrenceAddress.parse(
                            (String) call[1]).id(), new RecordingPlant.Root(0,
                            "true")), enclosing));
            assertEquals(why, call[3], RecordingPlant.focusedOccurrence(
                    Collections.singleton(ID), enclosing));
            assertEquals(why, call[4], RecordingPlant.anchorOf(enclosing,
                    ID));
        }
        assertEquals(null, RecordingPlant.plantedOccurrence(null, outer));
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

    /**
     * Values at calls' returns: a clock root's first reading under its mint
     * occurrence is the host plus its skew and jumps its node's clock; every
     * later declared reading of that clock on that node runs on from it
     * (none before, on another node, or outside a declaring region); a
     * configuration is its value at every getter call; an accessor's read
     * its value under its occurrence; any other call returns what it did.
     * The agent rewrites each caller class at the callees it calls.
     */
    @Test
    public void callReturnsReadThePlantedWorld() throws Exception {
        RecordingPlant.Plant plant = read(clock("100", 0)
                + reading(CLOCK_CALLEE, 1) + row("{'kind':'ROOT','category':"
                + "'CONFIG','rootId':'CONFIG:k','occurrence':'" + ID + "',"
                + "'sites':[{'siteId':'<a.Conf: void f()>#u1','callee':"
                + "'<a.Conf: int getInt()>'}],'javaType':'int','value':'7',"
                + "'row':2}") + row("{'kind':'ROOT','category':'READ',"
                + "'rootId':'READ.r','occurrence':'" + ID + "','siteId':"
                + "'<a.Conf: void g()>#u2','callee':'<a.Box: java.lang.String"
                + " name()>','javaType':'java.lang.String','value':"
                + "'planted','row':3}") + target(ID, "false", 4));
        String other = address("REGION.outer", "wl/dn1#epoch1");
        String dn2 = address("REGION.outer", "wl/dn2#epoch0");
        String name = "<a.Box: java.lang.String name()>";
        Object[][] calls = {
            // before the jump: the host
            {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(other), 5L, 5L},
            // the mint: host plus skew, and the node's clock jumps
            {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(INNER, OUTER), 10L,
                110L},
            {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(OUTER), 20L, 120L},
            // another node, no region declaring it, another callee
            {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(dn2), 30L, 30L},
            {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(INNER), 40L, 40L},
            {CLOCK_SITE_ID, "<a.Other: long now()>", Arrays.asList(OUTER),
                50L, 50L},
            {"<a.Conf: void f()>#u1", "<a.Conf: int getInt()>",
                Collections.<String>emptyList(), 3, 7},
            {"<a.Conf: void g()>#u2", name, Arrays.asList(OUTER),
                "recorded", "planted"},
            {"<a.Conf: void g()>#u2", name, Arrays.asList(INNER),
                "recorded", "recorded"},
            {"<a.Conf: void h()>#u9", CLOCK_CALLEE, Arrays.asList(OUTER),
                60L, 60L}};
        for (Object[] call : calls) {
            @SuppressWarnings("unchecked")
            List<String> enclosing = (List<String>) call[2];
            assertEquals(Arrays.toString(call), call[4],
                    RecordingPlant.returnedAt(plant, (String) call[0],
                            (String) call[1], enclosing, call[3]));
        }
        Map<String, java.util.Set<String>> intercepted =
                RecordingPlant.interceptions(plant);
        assertEquals(Arrays.asList("a/Keys", "a/Conf"),
                new ArrayList<String>(intercepted.keySet()));
        assertEquals(new TreeSet<String>(Arrays.asList("a/Conf.getInt ()I",
                "a/Box.name ()Ljava/lang/String;")),
                new TreeSet<String>(intercepted.get("a/Conf")));
    }

    /**
     * An answer at a port's call-return capture: carried as a replay's
     * attach carries it, its leaf named by the endpoint a replay's attach
     * names in the occurrence of a region declaring the port, and written
     * when the plant answers that endpoint -- once, and only there.
     */
    @Test
    public void anAnswerIsWrittenAtTheEndpointAReplayNames() throws Exception {
        String port = "XCH.1.resp.key-id";
        String[] expected = new String[1];
        on(() -> expected[0] = Identity.endpointAt(
                OccurrenceAddress.parse(OUTER), port, 0).id());
        RecordingPlant.Plant plant = read(row("{'kind':'ANSWER','endpoint':'"
                + expected[0] + "','port':'" + port + "','siteId':"
                + "'<a.H: void h()>#u4','callee':'<a.Msg: long keyId()>',"
                + "'regions':['REGION.outer'],'value':'9','row':0}")
                + target(ID, "false", 1));
        List<Object> answered = new ArrayList<>();
        on(() -> {
            for (List<String> enclosing : Arrays.asList(Arrays.asList(INNER,
                    OUTER), Arrays.asList(INNER, OUTER), Arrays.asList(
                    INNER))) {
                answered.add(RecordingPlant.returnedAt(plant,
                        "<a.H: void h()>#u4", "<a.Msg: long keyId()>",
                        enclosing, 4L));
            }
        });
        assertEquals(Arrays.asList(9L, 4L, 4L), answered);
    }

    private static void on(Runnable work) throws InterruptedException {
        Thread thread = new Thread(work);
        thread.start();
        thread.join();
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
     * The plant-run agent's rewrite: after every invoke of a named callee,
     * the plant's call for its return type (a reference through Object and
     * a cast back), nothing after an unnamed or void one; the rewritten
     * class verifies and, with no plant, returns what it returned.  And the
     * JVM spelling of a Soot signature the agent matches invokes by.
     */
    @Test
    public void namedInvokesHandTheirReturnsToThePlant() throws Exception {
        byte[] rewritten = PlantAgent.rewrite(fixtureBytes(),
                new LinkedHashSet<String>(Arrays.asList(
                        "java/lang/System.currentTimeMillis ()J",
                        "java/lang/Integer.parseInt (Ljava/lang/String;)I",
                        "java/lang/String.split (Ljava/lang/String;)"
                                + "[Ljava/lang/String;",
                        "java/lang/String.valueOf (Ljava/lang/Object;)"
                                + "Ljava/lang/String;",
                        "java/lang/System.gc ()V")));
        List<String> after = new ArrayList<String>();
        new ClassReader(rewritten).accept(new ClassVisitor(Opcodes.ASM5) {
            @Override
            public MethodVisitor visitMethod(int access, String name,
                    String descriptor, String signature, String[] thrown) {
                return new MethodVisitor(Opcodes.ASM5) {
                    @Override
                    public void visitMethodInsn(int opcode, String owner,
                            String called, String desc, boolean onInterface) {
                        if (owner.endsWith("RecordingPlant")) {
                            after.add(called + desc);
                        }
                    }

                    @Override
                    public void visitTypeInsn(int opcode, String type) {
                        if (opcode == Opcodes.CHECKCAST) after.add(type);
                    }
                };
            }
        }, 0);
        String object = "returned(Ljava/lang/Object;)Ljava/lang/Object;";
        assertEquals(Arrays.asList("returned(J)J", "returned(I)I", object,
                "[Ljava/lang/String;", object, "java/lang/String"), after);
        String fixture = PlantAgentFixture.class.getName();
        Class<?> loaded = new ClassLoader(getClass().getClassLoader()) {
            @Override
            protected Class<?> loadClass(String name, boolean resolve)
                    throws ClassNotFoundException {
                if (!fixture.equals(name)) return super.loadClass(name,
                        resolve);
                synchronized (getClassLoadingLock(name)) {
                    Class<?> defined = findLoadedClass(name);
                    return defined != null ? defined : defineClass(name,
                            rewritten, 0, rewritten.length);
                }
            }
        }.loadClass(fixture);
        long before = System.currentTimeMillis();
        assertTrue((Long) method(loaded, "clock", boolean.class)
                .invoke(null, true) > before);
        assertEquals(12, method(loaded, "parsed", String.class)
                .invoke(null, "12"));
        assertArrayEquals(new String[] {"a", "b"}, (String[]) method(loaded,
                "split", String.class).invoke(null, "a,b"));
        assertEquals("5", method(loaded, "named", Object.class)
                .invoke(null, 5));
        method(loaded, "collected").invoke(null);

        Object[][] signatures = {
            {"<java.lang.System: long nanoTime()>",
                "java/lang/System nanoTime ()J"},
            {"<a.B$C: java.lang.String[] f(int,java.util.List)>",
                "a/B$C f (ILjava/util/List;)[Ljava/lang/String;"},
            {"<org.apache.hadoop.util.Timer: long now()>",
                "org/apache/hadoop/util/Timer now ()J"},
            {"a.B#f", null}, {"", null}};
        for (Object[] signature : signatures) {
            String[] parsed = JvmSignature.parse((String) signature[0]);
            assertEquals(Arrays.toString(signature), signature[1],
                    parsed == null ? null : String.join(" ", parsed));
        }
    }

    private static Method method(Class<?> owner, String name,
                                 Class<?>... parameters) throws Exception {
        return owner.getMethod(name, parameters);
    }

    private static byte[] fixtureBytes() throws IOException {
        try (InputStream in = RecordingPlantTest.class.getResourceAsStream(
                "PlantAgentFixture.class")) {
            java.io.ByteArrayOutputStream out =
                    new java.io.ByteArrayOutputStream();
            byte[] buffer = new byte[8192];
            for (int read; (read = in.read(buffer)) > 0; ) {
                out.write(buffer, 0, read);
            }
            return out.toByteArray();
        }
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
