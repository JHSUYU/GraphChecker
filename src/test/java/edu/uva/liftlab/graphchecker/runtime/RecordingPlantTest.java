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

    private static final String ROOT_METHOD = "<a.P: void preflight()>";
    private static final String PREFLIGHT = "REGION.preflight";
    private static final String CLIENT = "t/client0";

    private static OccurrenceAddress preflight(int request, int frame) {
        return OccurrenceAddress.of(NodeId.parse(CLIENT + "#epoch0"),
                PREFLIGHT, CausalContext.of(Role.of("CLIENT"), "test",
                        request), frame < 0 ? ExecutionIndex.empty()
                        : ExecutionIndex.of(Collections.singletonList(
                        edu.uva.liftlab.graphchecker.contract.Frame.of(
                                "<a.P: void p()>#u1", frame))));
    }

    private static String planned(OccurrenceAddress address, String shape,
                                  String beside, long rootCall,
                                  String receiverClass) {
        return "{'occurrence':'" + address.render() + "','shape':[" + shape
                + "],'recordedBeside':[" + beside + "],'rootCall':"
                + rootCall + ",'receiverClass':'" + receiverClass + "'}";
    }

    private static String shapedTarget(String anchor, String planned) {
        return row("{'kind':'TARGET','occurrence':'" + anchor + "','siteId':'"
                + GUARD + "','value':true,'rootMethod':'" + ROOT_METHOD
                + "','planned':[" + planned + "],'row':0}");
    }

    public static final class Disable {
    }

    @Test
    public void anOccurrenceAnswersThePlannedTaskTheReplayWould()
            throws Exception {
        String test = "'Root:CLIENT/test'";
        String receiver = Disable.class.getName();
        OccurrenceAddress first = preflight(1, -1);
        OccurrenceAddress second = preflight(2, 4);
        String tasks = planned(first, test, "", 10, receiver) + ","
                + planned(second, test, "'" + first.id() + "'", 20, receiver);
        RecordingPlant.Plant plant = read(shapedTarget(second.id(), tasks));
        assertEquals(PREFLIGHT, plant.answers.regionId);
        assertEquals(2, plant.answers.planned.size());
        assertEquals(null, read(target(second.id(), "true", 0)).answers);
        String[] refused = {
            shapedTarget(second.id(), tasks).replace(ROOT_METHOD, ""),
            shapedTarget(second.id(), tasks.replace(first.render(), "x")),
            shapedTarget(second.id(), tasks.replace(",'rootCall':10", "")),
            shapedTarget(second.id(), planned(first, test, "", 10, receiver)),
            shapedTarget(second.id(), planned(first, test, "", 10, receiver)
                    + "," + planned(second, "", "", 20, receiver)),
            shapedTarget(second.id(), tasks + "," + planned(
                    OccurrenceAddress.parse(first.render().replace(PREFLIGHT,
                            "REGION.other")), test, "", 30, receiver)),
            shapedTarget(second.id(), tasks) + shapedTarget(second.id(),
                    tasks.replace(",'rootCall':20", ",'rootCall':21"))
                    .replace("'row':0", "'row':1")};
        for (String rows : refused) {
            try {
                read(rows);
                fail("accepted " + rows);
            } catch (IOException expected) {
            }
        }
        Object disable = new Disable();
        Object other = new Object();
        RecordingPlant.Answers answers = plant.answers;
        assertTrue(answers.offered(ROOT_METHOD, preflight(5, -1).render()));
        assertFalse("another root method of the region is another group",
                answers.offered("<a.P: void other()>", first.render()));
        assertFalse("another region", answers.offered(ROOT_METHOD,
                first.render().replace(PREFLIGHT, "REGION.other")));
        Object[][] runs = {
            {"the first by its address, the retry answers the second",
                new OccurrenceAddress[] {first, preflight(3, -1)},
                new Object[] {disable, disable},
                new OccurrenceAddress[] {null, second}},
            {"a run of the second's shape before the first answers the "
                + "first, the earliest open task: the retry is then the "
                + "first's own address and answers nothing",
                new OccurrenceAddress[] {preflight(3, -1), first},
                new Object[] {disable, disable},
                new OccurrenceAddress[] {first, null}},
            {"another receiver class fits no task",
                new OccurrenceAddress[] {first, preflight(3, -1)},
                new Object[] {disable, other},
                new OccurrenceAddress[] {null, null}},
            {"a context a task plans the region in is that task's",
                new OccurrenceAddress[] {first, preflight(2, -1)},
                new Object[] {disable, disable},
                new OccurrenceAddress[] {null, null}},
            {"another shape answers no task",
                new OccurrenceAddress[] {first, OccurrenceAddress.of(
                        NodeId.parse(CLIENT + "#epoch0"), PREFLIGHT,
                        CausalContext.of(Role.of("CLIENT"), "other", 3),
                        ExecutionIndex.empty())},
                new Object[] {disable, disable},
                new OccurrenceAddress[] {null, null}},
            {"each task is answered once",
                new OccurrenceAddress[] {first, preflight(3, -1),
                    preflight(4, -1), second},
                new Object[] {disable, disable, disable, disable},
                new OccurrenceAddress[] {null, second, null, null}}};
        for (Object[] run : runs) {
            RecordingPlant.Answers fresh = read(shapedTarget(second.id(),
                    tasks)).answers;
            OccurrenceAddress[] ran = (OccurrenceAddress[]) run[1];
            for (int at = 0; at < ran.length; at++) {
                RecordingPlant.Planned answered = fresh.answer(ROOT_METHOD,
                        ((Object[]) run[2])[at], ran[at]);
                OccurrenceAddress want = ((OccurrenceAddress[]) run[3])[at];
                assertEquals(run[0] + " #" + at, want, answered == null
                        ? null : answered.address);
            }
        }
        RecordingPlant.Answers recorded = read(shapedTarget(second.id(),
                planned(first, test, "", 10, receiver) + "," + planned(second,
                        test, "'" + preflight(3, -1).id() + "'", 20,
                        receiver))).answers;
        recorded.answer(ROOT_METHOD, disable, first);
        assertEquals("an address the recording opened answers no task by "
                + "shape", null, recorded.answer(ROOT_METHOD, disable,
                preflight(3, -1)));
    }

    @Test
    public void aNativeRunTakesTheFatalAtTheOccurrenceThatAnsweredTheAnchor()
            throws Exception {
        Path dir = folder.newFolder("answered").toPath();
        String test = "'Root:CLIENT/test'";
        String receiver = Disable.class.getName();
        OccurrenceAddress first = preflight(1, -1);
        OccurrenceAddress second = preflight(2, 4);
        Path plant = dir.resolve("plant.jsonl");
        Files.write(plant, shapedTarget(second.id(), planned(first, test, "",
                10, receiver) + "," + planned(second, test, "'" + first.id()
                + "'", 20, receiver)).replace(GUARD, ROOT_METHOD + "#u34")
                .getBytes(StandardCharsets.UTF_8));
        List<String> command = new ArrayList<>(java.util.Arrays.asList(
                java.nio.file.Paths.get(System.getProperty("java.home"),
                        "bin", "java").toString(),
                "-D" + RecordingPlant.PROPERTY + "=" + plant, "-cp",
                System.getProperty("java.class.path"),
                Native.class.getName()));
        ProcessBuilder builder = new ProcessBuilder(command)
                .redirectErrorStream(true)
                .redirectOutput(dir.resolve("jvm.log").toFile());
        builder.environment().put("CAUSYNTH_CONCOLIC_WORKER_DIR", "");
        builder.environment().put("CAUSYNTH_CONCOLIC_SESSIONS", "");
        builder.environment().put("CAUSYNTH_TRACE_MODE", "discovery");
        builder.environment().put("CAUSYNTH_TRACE_OUTPUT_DIR", dir.toString());
        Process jvm = builder.start();
        if (!jvm.waitFor(60L, java.util.concurrent.TimeUnit.SECONDS)) {
            jvm.destroyForcibly();
            fail("the native run did not end");
        }
        String log = new String(Files.readAllBytes(dir.resolve("jvm.log")),
                StandardCharsets.UTF_8);
        List<String> plants = new ArrayList<>();
        List<String> entered = new ArrayList<>();
        for (String line : Files.readAllLines(dir.resolve(
                "runtime_trace.jsonl"), StandardCharsets.UTF_8)) {
            if (line.contains("\"event\":\"PLANT_")) plants.add(line);
            if (line.contains("\"event\":\"METHOD_ENTER\"")
                    && line.contains(PREFLIGHT)) {
                entered.add(line);
            }
        }
        assertEquals(log, 0, jvm.exitValue());
        assertTrue(log, log.contains("ends AT_ANCHOR"));
        assertEquals(log + plants, 2, plants.size());
        assertTrue(plants.get(0), plants.get(0).contains(
                "\"event\":\"PLANT_ANSWERED\"")
                && plants.get(0).contains("\"plannedId\":\"" + second.id()
                + "\"") && plants.get(0).contains("\"occurrenceAddress\":\""
                + preflight(3, -1).render() + "\""));
        assertTrue(plants.get(1), plants.get(1).contains(
                "\"event\":\"PLANT_FATAL\"")
                && plants.get(1).contains("\"atAnchor\":true")
                && plants.get(1).contains(second.render()));
        assertEquals(entered.toString(), 2, entered.size());
        assertTrue(entered.get(0), entered.get(0).contains(first.render()));
        assertTrue(entered.get(1), entered.get(1).contains(second.render()));
    }

    public static final class Native {
        public static void main(String[] args) throws Exception {
            CausynthTraceRecorder.startRecording();
            Object client = new Object();
            RuntimeTraceContext.registerSource(client,
                    new SourceRef("CLIENT", "client", CLIENT, 0L));
            Object disable = new Disable();
            String[] regions = {PREFLIGHT, "REGION.other", PREFLIGHT};
            for (int request = 0; request < regions.length; request++) {
                long call = RuntimeTraceContext.beginRequest(client, "test");
                long id = CausynthTraceRecorder.enterMethod(ROOT_METHOD,
                        disable, regions[request]);
                if (request == 2) {
                    CausynthTraceRecorder.recordBranch(id, ROOT_METHOD, 34,
                            "", true);
                    Thread.sleep(30000L);
                }
                CausynthTraceRecorder.exitActiveMethod(null, "", true);
                RuntimeTraceContext.endRequest(call);
            }
            System.out.println("the fatal never ended the run");
            System.exit(5);
        }
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
