package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * A CONFIRM replay: the focus row flips nothing, and the expected edges
 * are compared -- never enforced -- against what the run pairs and joins.
 */
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

    @Before
    @After
    public void reset() {
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        RowRuntime.resetForTests();
    }

    /** Hands the replay a worker directory holding these two files; null
     *  edges writes none. */
    private void handed(String focusRow, List<String> edges)
            throws Exception {
        Path worker = folder.newFolder().toPath();
        Files.write(worker.resolve("focused_task.jsonl"),
                focusRow.getBytes(StandardCharsets.UTF_8));
        if (edges != null) {
            Files.write(worker.resolve(Confirmation.FILE),
                    (String.join("\n", edges) + "\n")
                            .getBytes(StandardCharsets.UTF_8));
        }
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
    }

    private static Endpoint endpoint(String occurrence, String site) {
        return Endpoint.of(OccurrenceAddress.parse(occurrence), site,
                ExecutionIndex.empty(), 0);
    }

    @Test
    public void aNullFlipOwesNoDecisionAndIsAdmittedByItsPlants()
            throws Exception {
        handed("{\"schemaVersion\":1,\"kind\":\"FOCUSED_TASK\","
                + "\"taskId\":\"CONFIRM\",\"obligationId\":\"CONFIRM\","
                + "\"pathId\":\"p1\",\"focused\":\"" + ANCHOR + "\","
                + "\"focusedOccurrenceId\":\""
                + OccurrenceAddress.parse(ANCHOR).id() + "\","
                + "\"seedSessionId\":\"seed\",\"flip\":null,"
                + "\"inheritedFlips\":[],"
                + "\"rootAssignments\":{\"HDFS.SERIAL\":\"119980\"},"
                + "\"clockDeltas\":{\"CLOCK.a\":\"43198429\"},"
                + "\"answers\":{},\"rootMints\":{\"HDFS.SERIAL\":\"" + MINT
                + "\",\"CLOCK.a\":\"" + MINT + "\"},\"unproducible\":[]}\n",
                Arrays.asList("{\"kind\":\"ANCHOR\",\"occurrence\":\"x\"}"));
        OccurrenceAddress anchor = OccurrenceAddress.parse(ANCHOR);
        assertTrue("a focused replay", FocusedReplay.focusedSession());
        assertTrue("the anchor is focused", FocusedReplay.focused(anchor));
        assertTrue("the mint is focused, so it plants",
                FocusedReplay.focused(OccurrenceAddress.parse(MINT)));
        assertEquals("the skew is stated", Long.valueOf(43198429L),
                FocusedReplay.clockSkew("CLOCK.a"));
        assertEquals("119980", FocusedReplay.rootAssignment("HDFS.SERIAL"));
        assertTrue("no decision is owed, so the anchor is never abandoned",
                FocusedReplay.complete(anchor));
        // A decision the anchor takes contradicts nothing: there is no
        // flip to take the wrong arm of.
        FocusedReplay.observeDecision(anchor, "<a.Handler: void handle()>#u8",
                1, true);
        assertTrue(FocusedReplay.refusal(anchor).isEmpty());
        assertEquals("unplanted until the mints ran", Verdict.NOT_ADMITTED,
                FocusedReplay.results("s").get(0).verdict());
        FocusedReplay.mintPublished("HDFS.SERIAL");
        FocusedReplay.mintPublished("CLOCK.a");
        assertEquals(Verdict.ADMITTED,
                FocusedReplay.results("s").get(0).verdict());
        assertTrue(FocusedReplay.results("s").get(0).detail()
                .contains("no flip was owed"));
    }

    @Test
    public void theEdgesAreComparedAndNeverEnforced() throws Exception {
        // A replay handed no edges compares nothing.
        Path plain = folder.newFolder("plain").toPath()
                .resolve("execution_task_plan.jsonl");
        Files.write(plain, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plain.toString());
        assertEquals("", Confirmation.attached(
                endpoint(ANCHOR, "x"), endpoint(MINT, "y"), null, null).mismatch);
        assertTrue(Confirmation.close().isEmpty());
        reset();

        Endpoint consumer = endpoint(ANCHOR, "XCH.1.resp.key-id");
        Endpoint chosen = endpoint(PRODUCER, "XCH.1.resp.key-id");
        Endpoint other = endpoint(MINT, "XCH.1.resp.key-id");
        Endpoint reader = endpoint(ANCHOR, "a.Handler#handle()#12:READ");
        Endpoint writer = endpoint(MINT, "a.Manager#tick()#7:WRITE");
        Endpoint absent = endpoint(ANCHOR, "a.Handler#handle()#99:READ");
        Endpoint hole = endpoint(ANCHOR, "kv:expireAt");
        // A read in a loop that polls for its write: the model's at turn 2,
        // this run's at turn 1 (SOLR-18413 stream7b: MigrateCmd's poll saw
        // the routing rule one turn sooner).
        Endpoint polled = turn(2);
        String state = "SOLR_ZK /collections/c/state.json@5";
        handed("{\"schemaVersion\":1,\"kind\":\"FOCUSED_TASK\","
                + "\"taskId\":\"CONFIRM\",\"obligationId\":\"CONFIRM\","
                + "\"pathId\":\"p1\",\"focused\":\"" + ANCHOR + "\","
                + "\"focusedOccurrenceId\":\""
                + OccurrenceAddress.parse(ANCHOR).id() + "\","
                + "\"seedSessionId\":\"seed\",\"flip\":null,"
                + "\"rootAssignments\":{},\"clockDeltas\":{},"
                + "\"answers\":{},\"rootMints\":{}}\n",
                Arrays.asList(
                        "{\"kind\":\"WIRE\",\"consumer\":\"" + consumer.id()
                                + "\",\"producer\":\"" + chosen.id() + "\"}",
                        "{\"kind\":\"WIRE\",\"consumer\":\"" + hole.id()
                                + "\",\"producer\":\"" + chosen.id()
                                + "\",\"messageKey\":\"" + state
                                + "\",\"value\":\"2000\"}",
                        "{\"kind\":\"STATE\",\"reader\":\"" + reader.id()
                                + "\",\"writer\":\"" + writer.id()
                                + "\",\"version\":\"121\"}",
                        "{\"kind\":\"STATE\",\"reader\":\"" + absent.id()
                                + "\",\"writer\":\"" + writer.id()
                                + "\",\"version\":\"122\"}",
                        "{\"kind\":\"STATE\",\"reader\":\"" + polled.id()
                                + "\",\"readerAnyTurn\":\""
                                + Confirmation.anyTurn(polled)
                                + "\",\"writer\":\"" + writer.id()
                                + "\",\"version\":\"123\"}",
                        "{\"kind\":\"MARKER\",\"root\":\"FAULT:IPC\","
                                + "\"value\":true}"));
        LocationId cell = LocationId.of(LocationKind.INSTANCE, "1", "40");
        assertEquals("the chosen producer is no mismatch", "",
                Confirmation.attached(consumer, chosen, null, null).mismatch);
        String mismatch = Confirmation.attached(consumer, other, null, null).mismatch;
        assertTrue(mismatch, mismatch.contains("the model chose producer "
                + chosen.id() + ", the run paired " + other.id()));
        assertEquals("a consumer the model chose nothing for", "",
                Confirmation.attached(other, chosen, null, null).mismatch);
        // A codec's hole: its message's store version and its text too.
        assertEquals("the chosen version, decoded as the model's value", "",
                Confirmation.attached(hole, chosen, state, "2000").mismatch);
        mismatch = Confirmation.attached(hole, chosen,
                "SOLR_ZK /collections/c/state.json@4", "2000").mismatch;
        assertTrue(mismatch, mismatch.contains("the model's arm came from "
                + "message " + state + ", the run decoded SOLR_ZK "
                + "/collections/c/state.json@4"));
        mismatch = Confirmation.attached(hole, chosen, state, "1999").mismatch;
        assertTrue(mismatch, mismatch.endsWith("the model's value is "
                + "\"2000\", the run delivered \"1999\""));
        // The writer of a version is published after the read that saw
        // it, so the state edge is answered at the close.
        Confirmation.read(reader, cell, 121L,
                edu.uva.liftlab.graphchecker.contract.ReadRow.UNKNOWN_VERSION);
        Confirmation.wrote(cell, 121L, other);
        Confirmation.read(turn(1), cell, 123L,
                edu.uva.liftlab.graphchecker.contract.ReadRow.UNKNOWN_VERSION);
        Confirmation.wrote(cell, 123L, writer);
        List<String> close = Confirmation.close();
        assertEquals(close.toString(), 2, close.size());
        assertTrue(close.get(0), close.get(0).startsWith("STATE "
                + reader.id() + ": the model joined this read to writer "
                + writer.id() + " (version 121), the run observed"));
        assertTrue(close.get(0), close.get(0).endsWith("written by "
                + other.id()));
        assertTrue(close.get(1), close.get(1).contains(absent.id())
                && close.get(1).endsWith("the run never read here"));
    }

    /** A delivery into the anchor is the model's when its producer answers
     *  the model's producer's question: the same site, site index and
     *  attempt of an occurrence of the same region and node under a chain of
     *  the same shape, delivering the model's value (hdfs-11741 V6: the
     *  balancer's second move to dn1 rode its next dispatcher iteration in
     *  the witness, its first in the CONFIRM run).  The substitution is
     *  named, never silent. */
    @Test
    public void aDeliveryIntoTheAnchorIsComparedByItsProducersQuestion()
            throws Exception {
        String site = "XCH.1.resp.key-id";
        Endpoint consumer = endpoint(ANCHOR, site);
        Endpoint chosen = endpoint(PRODUCER, site);
        String nextTurn = PRODUCER.replace("TICK#1", "TICK#2");
        handed("", Arrays.asList("{\"kind\":\"WIRE\",\"consumer\":\""
                + consumer.id() + "\",\"producer\":\"" + chosen.id()
                + "\",\"value\":\"7\",\"" + Confirmation.PRODUCER_QUESTION
                + "\":{\"occurrence\":\"" + PRODUCER + "\",\"site\":\""
                + site + "\",\"siteIndex\":\""
                + ExecutionIndex.empty().hash() + "\",\"attempt\":0,"
                + "\"shape\":[\"Root:TICK\"]}}"));
        // producer, the value it delivered, substituted?, a mismatch?
        Object[][] table = {
            {endpoint(nextTurn, site), "7", true, false},
            {endpoint(nextTurn, site), "8", true, true},
            {Endpoint.of(OccurrenceAddress.parse(nextTurn), site,
                    ExecutionIndex.of(Arrays.asList(Frame.of("a.X#y", 1))),
                    0), "7", false, true},
            {Endpoint.of(OccurrenceAddress.parse(nextTurn), site,
                    ExecutionIndex.empty(), 1), "7", false, true},
            {endpoint(nextTurn.replace("nn0", "nn1"), site), "7", false,
                true},
            {chosen, "7", false, false},
        };
        for (Object[] row : table) {
            Confirmation.Compared compared = Confirmation.attached(consumer,
                    (Endpoint) row[0], null, (String) row[1]);
            String subject = row[0] + " delivering " + row[1];
            assertEquals(subject + ": " + compared.substitution, row[2],
                    !compared.substitution.isEmpty());
            assertEquals(subject + ": " + compared.mismatch, row[3],
                    !compared.mismatch.isEmpty());
        }
    }

    /** The poll's read at one turn of its loop. */
    private static Endpoint turn(int k) {
        return Endpoint.of(OccurrenceAddress.parse(ANCHOR),
                "a.Handler#poll()#5:READ", ExecutionIndex.of(Arrays.asList(
                        Frame.of("<a.Handler: java.util.Map rules()>", k),
                        Frame.of("a.Handler#poll()#5:READ", 0))), 0);
    }

    /** A CONFIRM run that cannot read the edges the model chose compared
     *  none, so its close says so -- a half-written file or a missing one --
     *  and the fatal alone confirms nothing (it used to, silently). */
    @Test
    public void aConfirmationWithoutItsEdgesIsAMismatch() throws Exception {
        String confirming = "{\"taskId\":\"CONFIRM\",\"obligationId\":"
                + "\"CONFIRM\",\"pathId\":\"p1\",\"flip\":null}\n";
        handed(confirming, Arrays.asList("{\"kind\":\"WIRE\",\"consumer\""));
        List<String> close = Confirmation.close();
        assertEquals(close.toString(), 1, close.size());
        assertTrue(close.get(0), close.get(0).startsWith("EDGES: ")
                && close.get(0).contains("could not be read"));
        reset();
        handed(confirming, null);
        close = Confirmation.close();
        assertEquals(close.toString(), 1, close.size());
        assertTrue(close.get(0), close.get(0).startsWith("EDGES: this CONFIRM"
                + " run found no readable " + Confirmation.FILE));
    }

    /** The ORDER a CONFIRM run is held to: the reader's activation enters
     *  only once the writer's has exited; an order that cannot come is a
     *  mismatch, not a hang. */
    @Test
    public void aReaderWaitsForItsWriterAndAnUnrealizableOrderIsAMismatch()
            throws Exception {
        String writer = Endpoint.activation(OccurrenceAddress.parse(MINT),
                ExecutionIndex.empty());
        String reader = Endpoint.activation(OccurrenceAddress.parse(ANCHOR),
                ExecutionIndex.empty());
        String never = Endpoint.activation(OccurrenceAddress.parse(PRODUCER),
                ExecutionIndex.empty());
        handed("", Arrays.asList(
                "{\"kind\":\"ORDER\",\"before\":\"" + writer
                        + "\",\"after\":\"" + reader + "\"}",
                "{\"kind\":\"ORDER\",\"before\":\"" + never
                        + "\",\"after\":\"" + writer + "\"}"));
        System.setProperty(Confirmation.ORDER_TIMEOUT_PROPERTY, "300");
        try {
            assertTrue(Confirmation.ordering());
            long[] entered = new long[1];
            Thread read = new Thread(() -> {
                Confirmation.entering(reader);
                entered[0] = System.nanoTime();
            });
            read.start();
            Thread.sleep(100L);
            long exited = System.nanoTime();
            Confirmation.exited(writer);
            read.join(5000L);
            assertTrue("the reader entered only after the writer exited",
                    entered[0] >= exited);
            // Nothing ever exits `never`: the writer's entry times out.
            Confirmation.entering(writer);
            List<String> mismatches = Confirmation.close();
            assertEquals(1, mismatches.size());
            assertTrue(mismatches.get(0), mismatches.get(0)
                    .startsWith("ORDER " + writer));
        } finally {
            System.clearProperty(Confirmation.ORDER_TIMEOUT_PROPERTY);
        }
    }

    /**
     * An ORDER on claimed work (a server pipeline's request) is held at the
     * send that started it, up the chain of claimed work; on any other
     * activation, where it runs; and refused where no send runs outside
     * claimed work.
     */
    @Test
    public void claimedWorkIsHeldAtTheSendThatStartedIt() {
        OccurrenceAddress client = OccurrenceAddress.parse(
                "zk/client0#epoch0/region/REGION.start/ctx:Root:CLIENT/test#1"
                        + "/idx:<a.Election: void start()>@0");
        Endpoint send = Endpoint.of(client, "ZOOKEEPER#REQUEST",
                ExecutionIndex.of(Arrays.asList(Frame.of(
                        "<a.ZooKeeper: byte[] getData()>", 0))), 0);
        OccurrenceAddress prep = OccurrenceAddress.parse(
                "zk/server0#epoch0/region/REGION.prep/ctx:Anchor:"
                        + send.id() + "@ZOOKEEPER/test/idx:<a.Prep: void p()>@0");
        Endpoint relayed = Endpoint.of(prep, "SYNC#REQUEST",
                ExecutionIndex.empty(), 0);
        OccurrenceAddress served = OccurrenceAddress.parse(
                "zk/server0#epoch0/region/REGION.final/ctx:Anchor:"
                        + relayed.id() + "@SYNC/test/idx:<a.Final: void f()>@0");
        // row of each occurrence: claimed, its anchor's producer
        Object[][] table = {
                // held at the client's send, through the relaying stage
                {served, true, relayed, prep, true, send, send},
                // a client thread's own activation is held where it runs
                {client, false, null, null, false, null, null},
                // claimed work that names no send: no hold
                {served, true, null, null, false, null, "ORDER_UNHELD"},
        };
        for (Object[] row : table) {
            Map<String, ActivationRow> rows =
                    new HashMap<String, ActivationRow>();
            put(rows, (OccurrenceAddress) row[0], (Boolean) row[1],
                    (Endpoint) row[2]);
            if (row[3] != null) {
                put(rows, (OccurrenceAddress) row[3], (Boolean) row[4],
                        (Endpoint) row[5]);
            }
            Object held;
            try {
                held = Confirmation.submitter((OccurrenceAddress) row[0],
                        rows::get);
            } catch (IllegalStateException unheld) {
                held = unheld.getMessage().split(":")[0];
            }
            assertEquals(String.valueOf(row[0]), row[6], held);
        }
    }

    private static void put(Map<String, ActivationRow> rows,
                            OccurrenceAddress at, boolean claimed,
                            Endpoint producer) {
        rows.put(at.id(), ActivationRow.of("s0", at, "", false, true,
                claimed ? ActivationRow.CLAIMED + at.id() : "main#1",
                producer));
    }
}
