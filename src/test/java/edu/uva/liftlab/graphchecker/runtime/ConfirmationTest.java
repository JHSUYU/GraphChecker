package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.rules.TemporaryFolder;

@RunWith(FreshStatics.class)
public class ConfirmationTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String ANCHOR =
            "hdfs/dn0#epoch0/region/REGION.7c569c3f/ctx:Root:XCEIVER#1/idx:"
                    + "<a.Handler: void handle()>@0";
    private static final String MINT =
            "hdfs/nn0#epoch0/region/REGION.08ab84c9/ctx:Root:TICK#1/idx:"
                    + "<a.Manager: void tick()>@0";
    private static final String PRODUCER =
            "hdfs/nn0#epoch0/region/REGION.5dc77212/ctx:Root:TICK#1/idx:"
                    + "<a.Convert: void convert()>@0";
    private static final OccurrenceAddress READER =
            OccurrenceAddress.parse(ANCHOR);
    private static final OccurrenceAddress DECODER =
            OccurrenceAddress.parse(MINT);
    private static final String UNTIL = Endpoint.activation(READER,
            ExecutionIndex.empty());
    private static final LocationId CELL =
            LocationId.of(LocationKind.INSTANCE, "1", "40");
    private static final Endpoint WRITER =
            endpoint(MINT, "a.Manager#tick()#7:WRITE");

    @Before
    @After
    public void reset() {
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        System.clearProperty(Confirmation.ORDER_TIMEOUT_PROPERTY);
        System.clearProperty(Confirmation.VIEW_HOLD_MAX_PROPERTY);
    }

    private void handed(String focusRow, List<String> edges)
            throws Exception {
        Path worker = folder.newFolder().toPath();
        Files.write(worker.resolve("focused_task.jsonl"),
                focusRow.getBytes(StandardCharsets.UTF_8));
        if (edges != null) {
            Files.write(worker.resolve(Confirmation.FILE), (String.join("\n",
                    edges).replace('\'', '"') + "\n")
                    .getBytes(StandardCharsets.UTF_8));
        }
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
    }

    private static String confirm(String members) {
        return Fixtures.focusRow(ANCHOR, "'schemaVersion':1,'kind':"
                + "'FOCUSED_TASK','taskId':'CONFIRM','obligationId':'CONFIRM',"
                + "'pathId':'p1'" + members) + "\n";
    }

    private static Endpoint endpoint(String occurrence, String site) {
        return Endpoint.of(OccurrenceAddress.parse(occurrence), site,
                ExecutionIndex.empty(), 0);
    }

    private static String wire(Endpoint consumer, Endpoint producer,
                               String value) {
        return "{'kind':'WIRE','consumer':'" + consumer.id() + "','producer':'"
                + producer.id() + "'" + (value == null ? ""
                : ",'value':'" + value + "'") + "}";
    }

    private static String state(Endpoint reader, String more, String writer,
                                String version) {
        return "{'kind':'STATE','reader':'" + reader.id() + "'" + more
                + ",'writer':'" + writer + "','version':'" + version + "'}";
    }

    private static String order(String before, String after) {
        return "{'kind':'ORDER','before':'" + before + "','after':'" + after
                + "'}";
    }

    @Test
    @FreshStatics.Rows(2)
    public void theEdgesAreComparedAndNeverEnforced() throws Exception {
        if (FreshStatics.row() == 0) {
            Path plain = folder.newFolder("plain").toPath()
                    .resolve("execution_task_plan.jsonl");
            Files.write(plain, new byte[0]);
            System.setProperty(FocusedReplay.PLAN_PROPERTY, plain.toString());
            assertEquals("", Confirmation.attached(endpoint(ANCHOR, "x"),
                    endpoint(MINT, "y"), null).mismatch);
            assertTrue(Confirmation.close().isEmpty());
            return;
        }

        Endpoint consumer = endpoint(ANCHOR, "XCH.1.resp.key-id");
        Endpoint chosen = endpoint(PRODUCER, "XCH.1.resp.key-id");
        Endpoint other = endpoint(MINT, "XCH.1.resp.key-id");
        Endpoint reader = endpoint(ANCHOR, "a.Handler#handle()#12:READ");
        Endpoint absent = endpoint(ANCHOR, "a.Handler#handle()#99:READ");
        Endpoint held = endpoint(ANCHOR, "XCH.2.resp.expire-at");
        Endpoint polled = turn(2);
        Endpoint behind = endpoint(MINT, "a.Manager#tick()#9:READ");
        handed(confirm(""), Arrays.asList(wire(consumer, chosen, null),
                wire(held, chosen, "2000"),
                state(reader, "", WRITER.id(), "121"),
                state(absent, "", WRITER.id(), "122"),
                state(polled, ",'readerAnyTurn':'"
                        + Confirmation.anyTurn(polled) + "'", WRITER.id(),
                        "123"),
                state(behind, ",'afterAnchor':true", WRITER.id(), "124"),
                "{'kind':'MARKER','root':'FAULT:IPC','value':true}"));
        assertEquals("the chosen producer is no mismatch", "",
                Confirmation.attached(consumer, chosen, null).mismatch);
        String mismatch = Confirmation.attached(consumer, other, null)
                .mismatch;
        assertTrue(mismatch, mismatch.contains("the model chose producer "
                + chosen.id() + ", the run paired " + other.id()));
        assertEquals("a consumer the model chose nothing for", "",
                Confirmation.attached(other, chosen, null).mismatch);
        assertEquals("a held leaf: the model's value delivered", "",
                Confirmation.attached(held, chosen, "2000").mismatch);
        mismatch = Confirmation.attached(held, chosen, "1999").mismatch;
        assertTrue(mismatch, mismatch.endsWith("the model's value is "
                + "\"2000\", the run delivered \"1999\""));
        Confirmation.read(reader, CELL, 121L, ReadRow.UNKNOWN_VERSION);
        Confirmation.wrote(CELL, 121L, other, false);
        Confirmation.read(turn(1), CELL, 123L, ReadRow.UNKNOWN_VERSION);
        Confirmation.wrote(CELL, 123L, WRITER, false);
        List<String> close = Confirmation.close();
        assertEquals("a read held behind the anchor is not required: "
                + close, 2, close.size());
        assertTrue(close.get(0), close.get(0).startsWith("STATE "
                + reader.id() + ": the model joined this read to writer "
                + WRITER.id() + " (version 121), the run observed")
                && close.get(0).endsWith("written by " + other.id()));
        assertTrue(close.get(1), close.get(1).contains(absent.id())
                && close.get(1).endsWith("the run never read here"));
    }

    private static Endpoint turn(int k) {
        return Endpoint.of(READER, "a.Handler#poll()#5:READ",
                ExecutionIndex.of(Arrays.asList(Frame.of(
                        "<a.Handler: java.util.Map rules()>", k),
                        Frame.of("a.Handler#poll()#5:READ", 0))), 0);
    }

    @Test
    @FreshStatics.Rows(5)
    public void anObligationReplayIsAdmittedOnlyOverItsPairing()
            throws Exception {
        Frame loop = Frame.of("<a.Detector: void run()>", 0);
        String site = "a.Metrics#bound()#43:READ";
        Endpoint guard = Endpoint.of(READER, site, ExecutionIndex.of(
                Arrays.asList(loop, Frame.of(site, 0))), 0);
        Endpoint limit = Endpoint.of(READER, site, ExecutionIndex.of(
                Arrays.asList(loop, Frame.of(site, 1))), 0);
        Endpoint first = endpoint(ANCHOR, "a.Metrics#bound()#43:INITIAL");
        LocationId cell = LocationId.of(LocationKind.INSTANCE, "1", "48");
        String flipped = "<a.Detector: void run()>#u63";
        String initial = anyTurnState(guard, Confirmation.INITIAL);
        Object[][] table = {
            {Arrays.asList(initial), 4L, 0L, true, ""},
            {Arrays.asList(initial), 5L, 0L, false, "STATE"},
            {Arrays.asList(initial, anyTurnState(limit,
                    Confirmation.INITIAL)), 4L, 5L, false,
                "STATE " + limit.id()},
            {null, 4L, 0L, false, "EDGES"},
            {Arrays.asList(initial, anyTurnState(guard, WRITER.id())), 4L,
                0L, false, "STATE_CONFLICT"}};
        Object[] row = table[FreshStatics.row()];
        @SuppressWarnings("unchecked")
        List<String> edges = (List<String>) row[0];
        handed(Fixtures.focusRow(ANCHOR, "'obligationId':'OBL.1',"
                + "'pathId':'p1','flip':{'siteId':'" + flipped + "',"
                + "'ordinal':1,'outcome':true},'pairings':{'"
                + Confirmation.id(guard) + "':'" + Confirmation.INITIAL
                + "'}") + "\n", edges);
        FocusedReplay.observeDecision(READER, flipped, 1, true);
        Confirmation.wrote(cell, 4L, first, true);
        Confirmation.wrote(cell, 5L, WRITER, false);
        Confirmation.read(guard, cell, (Long) row[1],
                ReadRow.UNKNOWN_VERSION);
        if ((Long) row[2] > 0L) {
            Confirmation.read(limit, cell, (Long) row[2],
                    ReadRow.UNKNOWN_VERSION);
        }
        ObligationResult result = FocusedReplay.results("s").get(0);
        boolean admitted = (Boolean) row[3];
        assertEquals(result.detail(), admitted ? Verdict.ADMITTED
                : Verdict.NOT_ADMITTED, result.verdict());
        assertEquals(result.detail(), !admitted, result.detail()
                .startsWith("PAIRING_UNTAKEN: ")
                && result.detail().contains((String) row[4]));
    }

    private static String anyTurnState(Endpoint reader, String writer) {
        return state(reader, ",'readerAnyTurn':'"
                + Confirmation.anyTurn(reader) + "'", writer, "4");
    }

    @Test
    @FreshStatics.Rows(2)
    public void aConfirmationWithoutItsEdgesIsAMismatch() throws Exception {
        String confirming = "{\"taskId\":\"CONFIRM\",\"obligationId\":"
                + "\"CONFIRM\",\"pathId\":\"p1\",\"flip\":null}\n";
        List<String> edges = Arrays.asList(Arrays.asList(
                "{'kind':'WIRE','consumer'"), (List<String>) null)
                .get(FreshStatics.row());
        handed(confirming, edges);
        List<String> close = Confirmation.close();
        assertEquals(close.toString(), 1, close.size());
        assertTrue(close.get(0), edges != null
                ? close.get(0).startsWith("EDGES: ")
                && close.get(0).contains("could not be read")
                : close.get(0).startsWith("EDGES: this CONFIRM run found"
                + " no readable " + Confirmation.FILE));
    }

    @Test
    public void aReaderWaitsForItsWriterAndAnUnrealizableOrderIsAMismatch()
            throws Exception {
        String writer = Endpoint.activation(DECODER, ExecutionIndex.empty());
        String never = Endpoint.activation(OccurrenceAddress.parse(PRODUCER),
                ExecutionIndex.empty());
        handed("", Arrays.asList(order(writer, UNTIL), order(never, writer)));
        System.setProperty(Confirmation.ORDER_TIMEOUT_PROPERTY, "300");
        assertTrue(Confirmation.ordering());
        long[] entered = new long[1];
        Thread read = new Thread(() -> {
            Confirmation.entering(UNTIL);
            entered[0] = System.nanoTime();
        });
        read.start();
        Thread.sleep(100L);
        long exited = System.nanoTime();
        Confirmation.exited(writer);
        read.join(5000L);
        assertTrue("the reader entered only after the writer exited",
                entered[0] >= exited);
        Confirmation.entering(writer);
        List<String> mismatches = Confirmation.close();
        assertEquals(1, mismatches.size());
        assertTrue(mismatches.get(0), mismatches.get(0)
                .startsWith("ORDER " + writer));
    }
    @Test
    public void aHandOffIsHeldAtItsClaimsEntry() throws Exception {
        RuntimeTraceContext.resetForTests();
        Lineage.resetForTests();
        RecordingWindow.reset();
        SourceRef node = new SourceRef("CLUSTER_NODE", "HMASTER", "t/m0", 0L);
        String site = "<a.Step: void handOff(a.Procedure)>#u18";
        String key = node.key() + "|Root:CLIENT/test#1|" + site + "@0";
        String writer = Endpoint.activation(DECODER, ExecutionIndex.empty());
        handed("", Arrays.asList(order(writer, Confirmation.claim(
                ActivationRow.CLAIMED + key))));
        System.setProperty(Confirmation.ORDER_TIMEOUT_PROPERTY, "60000");
        assertTrue(Confirmation.ordering());
        assertEquals("a turn count is no part of a claim's name",
                Confirmation.claim("n|Root:WAKE/a.P#3|x@0"),
                Confirmation.claim(ActivationRow.CLAIMED
                        + "n|Root:WAKE/a.P#5|x@0"));
        List<Long> claimedAt = Collections.synchronizedList(
                new ArrayList<Long>());
        ScheduleLog.install(row -> {
            if ("CLAIM".equals(row.has("kind") ? row.get("kind")
                    .getAsString() : "")) {
                claimedAt.add(System.nanoTime());
            }
        });
        RecordingWindow.open();
        Object source = new Object();
        RuntimeTraceContext.registerSource(source, node);
        long request = RuntimeTraceContext.beginRequest(source, "test");
        Object step = new Object();
        Identity.startWork(site, step, new ThreadPoolExecutor(0, 1, 1L,
                TimeUnit.SECONDS, new SynchronousQueue<Runnable>()));
        RuntimeTraceContext.endRequest(request);
        long[] entered = new long[1];
        String[] claimed = new String[1];
        Thread worker = new Thread(() -> {
            long claim = Identity.claimStart(step);
            entered[0] = System.nanoTime();
            claimed[0] = Identity.claimedStart();
            Identity.endClaim(claim);
        });
        worker.start();
        Thread.sleep(100L);
        long exited = System.nanoTime();
        Confirmation.exited(writer);
        worker.join(5000L);
        assertEquals(key, claimed[0]);
        assertTrue("the hand-off ran only after the writer exited",
                entered[0] >= exited);
        assertEquals("its CLAIM is observed once", 1, claimedAt.size());
        assertTrue("and only once the hold let it go",
                claimedAt.get(0) >= exited);
        assertTrue(Confirmation.close().isEmpty());
    }

    @Test
    @FreshStatics.Rows(2)
    public void aCheckedOrderIsObservedWhereItsLaterEndEntersNeverWaitedFor()
            throws Exception {
        boolean realized = FreshStatics.row() == 0;
        String writer = Endpoint.activation(DECODER, ExecutionIndex.empty());
        handed("", Arrays.asList("{'kind':'ORDER','before':'" + writer
                + "','after':'" + UNTIL + "','check':true}"));
        System.setProperty(Confirmation.ORDER_TIMEOUT_PROPERTY, "60000");
        assertTrue(Confirmation.ordering());
        if (realized) Confirmation.exited(writer);
        long started = System.nanoTime();
        Confirmation.entering(UNTIL);
        Confirmation.entering(UNTIL);
        assertTrue("a checked order is never waited for",
                System.nanoTime() - started < 5_000_000_000L);
        List<String> mismatches = Confirmation.close();
        List<String> observed = Confirmation.observed();
        assertEquals(realized ? 0 : 1, mismatches.size());
        assertEquals(realized ? 1 : 0, observed.size());
        String named = realized ? observed.get(0) : mismatches.get(0);
        assertTrue(named, named.startsWith("ORDER " + UNTIL + ": "));
        assertTrue(named, named.contains(writer));
    }
}
