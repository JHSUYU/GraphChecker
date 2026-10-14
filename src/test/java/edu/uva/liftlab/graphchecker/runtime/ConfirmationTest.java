package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
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
        RunNames.resetForTests();
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

    /**
     * A view's writer is its version whichever side of the window its
     * decode stood on (review re-check B3: a view's INITIAL spelled
     * INITIAL and the same version decoded in the window VIEW@v, so a
     * pairing EXPLORE planted to one was refuted by CONFIRM's other); any
     * other location's INITIAL is INITIAL, a write its endpoint.
     */
    @Test
    public void aViewsWriterIsItsVersionOnEitherSideOfTheWindow() {
        Endpoint at = endpoint(ANCHOR, "SOLR_ZK#VIEW:.aliases.json");
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/aliases.json");
        LocationId field = LocationId.of(LocationKind.INSTANCE, "7", "3");
        Object[][] rows = {
                {WriteRow.initial("s", 0L, at, view, 3L, "", "J"), "VIEW@3"},
                {WriteRow.of("s", 9L, at, view, 3L, "", "J"), "VIEW@3"},
                {WriteRow.initial("s", 0L, at, field, 0L, "", "I"),
                        Confirmation.INITIAL},
                {WriteRow.of("s", 9L, at, field, 1L, "", "I"),
                        Confirmation.id(at)},
        };
        for (Object[] row : rows) {
            assertEquals(row[0].toString(), row[1],
                    Confirmation.writer((WriteRow) row[0]));
        }
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

    /**
     * A held leaf's value names each node's run-only name by the node on
     * both sides -- the model's by its arm's run (ConfirmMain#named), what
     * arrives by this run's -- and is compared exactly after that: the same
     * node at another port is the model's value (NC3-reindex attempt 0000:
     * 127.0.0.1:41564_solr against 127.0.0.1:33130_solr, both
     * auto0/node1); another node, or any other difference, refutes; a value
     * no spelling names is compared as it is.
     */
    @Test
    public void aWireValueNamesItsNodesByEachRunsSpelling()
            throws Exception {
        Endpoint chosen = endpoint(PRODUCER, "XCH.1.resp.leader");
        Endpoint leader = endpoint(ANCHOR, "XCH.1.resp.leader");
        Endpoint url = endpoint(ANCHOR, "XCH.2.resp.url");
        Endpoint count = endpoint(ANCHOR, "XCH.3.resp.count");
        handed("{\"schemaVersion\":1,\"kind\":\"FOCUSED_TASK\","
                + "\"taskId\":\"CONFIRM\",\"obligationId\":\"CONFIRM\","
                + "\"pathId\":\"p1\",\"focused\":\"" + ANCHOR + "\","
                + "\"focusedOccurrenceId\":\""
                + OccurrenceAddress.parse(ANCHOR).id() + "\","
                + "\"seedSessionId\":\"seed\",\"flip\":null,"
                + "\"rootAssignments\":{},\"clockDeltas\":{},"
                + "\"answers\":{},\"rootMints\":{}}\n",
                Arrays.asList(wire(leader, chosen, "{auto0/node1}"),
                        wire(url, chosen, "http://{auto0/node1}/solr/c1"),
                        wire(count, chosen, "2000")));
        RunNames.spelled("auto0/node0", "127.0.0.1:33129_solr");
        RunNames.spelled("auto0/node1", "127.0.0.1:33130_solr");
        Object[][] table = {
                // consumer, what arrived, a mismatch?
                {leader, "127.0.0.1:33130_solr", false},
                {leader, "127.0.0.1:33129_solr", true},
                {leader, "127.0.0.1:33130_solr ", true},
                // a spelling inside a longer string: the host and port
                {url, "http://127.0.0.1:33130/solr/c1", false},
                {url, "http://127.0.0.1:33130/solr/c2", true},
                {url, "http://127.0.0.1:33129/solr/c1", true},
                // no spelling names it: as it is
                {count, "2000", false},
                {count, "1999", true},
        };
        for (Object[] row : table) {
            String mismatch = Confirmation.attached((Endpoint) row[0],
                    chosen, (String) row[1]).mismatch;
            assertEquals(row[1] + " -> " + mismatch, row[2],
                    !mismatch.isEmpty());
        }
        assertTrue(Confirmation.attached(leader, chosen,
                "127.0.0.1:33129_solr").mismatch.endsWith("the run delivered"
                + " \"127.0.0.1:33129_solr\" ({auto0/node0})"));
    }

    private static String wire(Endpoint consumer, Endpoint producer,
                               String value) {
        return "{\"kind\":\"WIRE\",\"consumer\":\"" + consumer.id()
                + "\",\"producer\":\"" + producer.id() + "\",\"value\":\""
                + value + "\"}";
    }

    @Test
    public void theEdgesAreComparedAndNeverEnforced() throws Exception {
        // A replay handed no edges compares nothing.
        Path plain = folder.newFolder("plain").toPath()
                .resolve("execution_task_plan.jsonl");
        Files.write(plain, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plain.toString());
        assertEquals("", Confirmation.attached(
                endpoint(ANCHOR, "x"), endpoint(MINT, "y"), null).mismatch);
        assertTrue(Confirmation.close().isEmpty());
        reset();

        Endpoint consumer = endpoint(ANCHOR, "XCH.1.resp.key-id");
        Endpoint chosen = endpoint(PRODUCER, "XCH.1.resp.key-id");
        Endpoint other = endpoint(MINT, "XCH.1.resp.key-id");
        Endpoint reader = endpoint(ANCHOR, "a.Handler#handle()#12:READ");
        Endpoint writer = endpoint(MINT, "a.Manager#tick()#7:WRITE");
        Endpoint absent = endpoint(ANCHOR, "a.Handler#handle()#99:READ");
        Endpoint held = endpoint(ANCHOR, "XCH.2.resp.expire-at");
        // A read in a loop that polls for its write: the model's at turn 2,
        // this run's at turn 1 (SOLR-18413 stream7b: MigrateCmd's poll saw
        // the routing rule one turn sooner).
        Endpoint polled = turn(2);
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
                        "{\"kind\":\"WIRE\",\"consumer\":\"" + held.id()
                                + "\",\"producer\":\"" + chosen.id()
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
                Confirmation.attached(consumer, chosen, null).mismatch);
        String mismatch = Confirmation.attached(consumer, other, null).mismatch;
        assertTrue(mismatch, mismatch.contains("the model chose producer "
                + chosen.id() + ", the run paired " + other.id()));
        assertEquals("a consumer the model chose nothing for", "",
                Confirmation.attached(other, chosen, null).mismatch);
        // A held leaf: its text too.
        assertEquals("the model's value delivered", "",
                Confirmation.attached(held, chosen, "2000").mismatch);
        mismatch = Confirmation.attached(held, chosen, "1999").mismatch;
        assertTrue(mismatch, mismatch.endsWith("the model's value is "
                + "\"2000\", the run delivered \"1999\""));
        // The writer of a version is published after the read that saw
        // it, so the state edge is answered at the close.
        Confirmation.read(reader, cell, 121L,
                edu.uva.liftlab.graphchecker.contract.ReadRow.UNKNOWN_VERSION);
        Confirmation.wrote(cell, 121L, other, false);
        Confirmation.read(turn(1), cell, 123L,
                edu.uva.liftlab.graphchecker.contract.ReadRow.UNKNOWN_VERSION);
        Confirmation.wrote(cell, 123L, writer, false);
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

    /**
     * A placeholder's pairing is taken where a placeholder of the run, at
     * whichever occurrence read first, observed a version of the model's
     * location that the model's writer wrote -- an INITIAL included, which
     * is every location's, so another location's INITIAL is not it.
     */
    @Test
    public void aPlaceholderIsComparedByItsWriterAtItsLocation()
            throws Exception {
        Endpoint writer = endpoint(MINT, "a.Manager#tick()#7:WRITE");
        Endpoint first = endpoint(MINT, "a.Manager#tick()#7:INITIAL");
        LocationId cell = LocationId.of(LocationKind.INSTANCE, "1", "40");
        LocationId other = LocationId.of(LocationKind.INSTANCE, "1", "41");
        // the model's writer, the placeholder's location and version, taken?
        Object[][] table = {
                {writer.id(), cell, 5L, true},
                {Confirmation.INITIAL, cell, 4L, true},
                {Confirmation.INITIAL, other, 4L, false},
                {Confirmation.INITIAL, cell, 5L, false},
        };
        for (Object[] row : table) {
            reset();
            handed("{\"schemaVersion\":1,\"kind\":\"FOCUSED_TASK\","
                    + "\"taskId\":\"CONFIRM\",\"obligationId\":\"CONFIRM\","
                    + "\"pathId\":\"p1\",\"focused\":\"" + ANCHOR + "\","
                    + "\"focusedOccurrenceId\":\""
                    + OccurrenceAddress.parse(ANCHOR).id() + "\","
                    + "\"seedSessionId\":\"seed\",\"flip\":null,"
                    + "\"rootAssignments\":{},\"clockDeltas\":{},"
                    + "\"answers\":{},\"rootMints\":{}}\n",
                    Collections.singletonList("{\"kind\":\"STATE\","
                            + "\"reader\":\"" + endpoint(ANCHOR,
                            "a.Handler#h()#12:READ").id() + "\",\"mint\":true,"
                            + "\"writer\":\"" + row[0] + "\",\"version\":\"4\","
                            + "\"location\":\"INSTANCE/1#40\"}"));
            for (LocationId location : Arrays.asList(cell, other)) {
                Confirmation.wrote(location, 4L, first, true);
            }
            Confirmation.wrote(cell, 5L, writer, false);
            Confirmation.read(endpoint(PRODUCER, "a.Convert#c()#3:READ"),
                    (LocationId) row[1], (Long) row[2], 9L);
            List<String> close = Confirmation.close();
            assertEquals(Arrays.toString(row) + ": " + close,
                    (Boolean) row[3], close.isEmpty());
        }
    }

    /**
     * An obligation replay whose world pairs a read with its location's
     * INITIAL is admitted only where that exact read observed the INITIAL's
     * version.  hdfs-bugs-slowdisk-zero SD5: the guard read the INITIAL and
     * the limit, the same accessor site one call later -- one read at any
     * turn -- the reconfiguration's 0; another turn's INITIAL says nothing
     * of this one.  A focus row with pairings and no edges compared nothing,
     * and two writers for one read are no model: neither is admitted.
     */
    @Test
    public void anObligationReplayIsAdmittedOnlyOverItsPairing()
            throws Exception {
        Frame loop = Frame.of("<a.Detector: void run()>", 0);
        String site = "a.Metrics#bound()#43:READ";
        Endpoint guard = Endpoint.of(OccurrenceAddress.parse(ANCHOR), site,
                ExecutionIndex.of(Arrays.asList(loop, Frame.of(site, 0))), 0);
        Endpoint limit = Endpoint.of(OccurrenceAddress.parse(ANCHOR), site,
                ExecutionIndex.of(Arrays.asList(loop, Frame.of(site, 1))), 0);
        Endpoint first = endpoint(ANCHOR, "a.Metrics#bound()#43:INITIAL");
        Endpoint writer = endpoint(MINT, "a.Manager#tick()#7:WRITE");
        LocationId cell = LocationId.of(LocationKind.INSTANCE, "1", "48");
        String flipped = "<a.Detector: void run()>#u63";
        OccurrenceAddress anchor = OccurrenceAddress.parse(ANCHOR);
        String initial = state(guard, Confirmation.INITIAL);
        // rows, the version each of guard and limit observed (0: no read),
        // admitted?, what refused it
        Object[][] table = {
                {Arrays.asList(initial), 4L, 0L, true, ""},
                {Arrays.asList(initial), 5L, 0L, false, "STATE"},
                {Arrays.asList(initial, state(limit, Confirmation.INITIAL)),
                        4L, 5L, false, "STATE " + limit.id()},
                {null, 4L, 0L, false, "EDGES"},
                {Arrays.asList(initial, state(guard, writer.id())), 4L, 0L,
                        false, "STATE_CONFLICT"},
        };
        for (Object[] row : table) {
            @SuppressWarnings("unchecked")
            List<String> edges = (List<String>) row[0];
            handed("{\"taskId\":\"T\",\"obligationId\":\"OBL.1\","
                    + "\"pathId\":\"p1\",\"focused\":\"" + ANCHOR + "\","
                    + "\"focusedOccurrenceId\":\"" + anchor.id() + "\","
                    + "\"seedSessionId\":\"seed\",\"flip\":{\"siteId\":\""
                    + flipped + "\",\"ordinal\":1,\"outcome\":true},"
                    + "\"pairings\":{\"" + Confirmation.id(guard) + "\":\""
                    + Confirmation.INITIAL + "\"}}\n", edges);
            FocusedReplay.observeDecision(anchor, flipped, 1, true);
            Confirmation.wrote(cell, 4L, first, true);
            Confirmation.wrote(cell, 5L, writer, false);
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
            reset();
        }
    }

    /** One STATE row of an obligation's edges. */
    private static String state(Endpoint reader, String writer) {
        return "{\"kind\":\"STATE\",\"reader\":\"" + reader.id()
                + "\",\"readerAnyTurn\":\"" + Confirmation.anyTurn(reader)
                + "\",\"writer\":\"" + writer + "\",\"version\":\"4\"}";
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
                    (Endpoint) row[0], (String) row[1]);
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

    /** One VIEW_HOLD row over {@code view} past {@code above}, its reader
     *  the work of {@code reader}, held until {@code until} exits. */
    private static String viewHold(LocationId view, long above,
                                   OccurrenceAddress reader, String until,
                                   String readerEndpoint) {
        return "{\"kind\":\"VIEW_HOLD\",\"view\":\""
                + Confirmation.viewKey(view) + "\",\"above\":" + above + ","
                + "\"readerContext\":\"" + Confirmation.contextKey(reader)
                + "\"," + (readerEndpoint == null ? ""
                : "\"reader\":\"" + readerEndpoint + "\",")
                + "\"until\":\"" + until + "\"}";
    }

    /** A publication that counts itself applied ({@code applied}). */
    private static Runnable publication(List<Long> applied, long version) {
        return () -> {
            synchronized (applied) {
                applied.add(version);
                applied.notifyAll();
            }
        };
    }

    /** The node every test publication is made on. */
    private static final String NODE = "hdfs/dn0#epoch0";

    /** {@link Confirmation#publishing} on {@link #NODE}, with no scope. */
    private static boolean publishing(LocationId view, long version,
                                      OccurrenceAddress at, Runnable apply) {
        return Confirmation.publishing(view, version, at, NODE, null, apply,
                null);
    }

    /** Waits for {@code applied} to hold {@code count} publications. */
    private static void awaitApplied(List<Long> applied, int count)
            throws InterruptedException {
        long deadline = System.currentTimeMillis() + 5000L;
        synchronized (applied) {
            while (applied.size() < count
                    && System.currentTimeMillis() < deadline) {
                applied.wait(50L);
            }
        }
    }

    /**
     * THE PUBLICATION HOLD (a'), per row: a node's publication of a view
     * past the paired version is deferred until the reader's region exits,
     * then applied in the order it came; one at or below the version is
     * not, nor the reader's own work's; the thread goes on.  A hold whose
     * reader never comes gives way at VIEW_HOLD_MAX, named: the queue
     * applies and the pairing is a mismatch.
     */
    @Test
    public void aViewsLaterPublicationIsDeferredUntilTheReadersRegionExits()
            throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/aliases.json");
        OccurrenceAddress reader = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress decoder = OccurrenceAddress.parse(MINT);
        String until = Endpoint.activation(reader, ExecutionIndex.empty());
        handed("", Collections.singletonList(viewHold(view, 1L, reader,
                until, null)));
        List<Long> applied = new ArrayList<Long>();
        // Not deferred: the paired version, and the reader's own work.
        assertFalse(publishing(view, 1L, decoder, publication(applied, 1L)));
        assertFalse(publishing(view, 4L, reader, publication(applied, 4L)));
        // Deferred: past the version, on another work's thread; the
        // caller goes on at once.
        long started = System.nanoTime();
        assertTrue(publishing(view, 3L, decoder, publication(applied, 3L)));
        assertTrue(publishing(view, 2L, decoder, publication(applied, 2L)));
        assertTrue("the thread goes on",
                System.nanoTime() - started < 200_000_000L);
        Thread.sleep(100L);
        assertTrue("nothing applied while the reader runs: " + applied,
                applied.isEmpty());
        Confirmation.exited(until);
        awaitApplied(applied, 2);
        assertEquals("applied in the order they came at the reader's exit",
                Arrays.asList(3L, 2L), applied);
        assertTrue(Confirmation.close().isEmpty());

        Confirmation.resetForTests();
        handed("", Collections.singletonList(viewHold(view, 1L, reader,
                until, null)));
        System.setProperty(Confirmation.VIEW_HOLD_MAX_PROPERTY, "200");
        try {
            List<Long> late = new ArrayList<Long>();
            assertTrue(publishing(view, 2L, decoder,
                    publication(late, 2L)));
            awaitApplied(late, 1);
            assertEquals("applied at VIEW_HOLD_MAX", Arrays.asList(2L), late);
            List<String> mismatches = Confirmation.close();
            assertEquals(mismatches.toString(), 1, mismatches.size());
            assertTrue(mismatches.get(0), mismatches.get(0)
                    .startsWith("VIEW_HOLD " + Confirmation.viewKey(view))
                    && mismatches.get(0).contains("VIEW_HOLD_MAX"));
        } finally {
            System.clearProperty(Confirmation.VIEW_HOLD_MAX_PROPERTY);
        }
    }

    /**
     * A deferred publication applied after a later synchronous one (a
     * forced refresh published version 3 while 2 waited) publishes nothing
     * older over it: the system's own compare (Solr's CAS on the znode
     * version, {@code setIfNewer}) holds the newest, and the engine applies
     * the queue as it stands.
     */
    @Test
    public void aDeferredPublicationNeverRegressesALaterSynchronousOne()
            throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/state.json");
        OccurrenceAddress reader = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress decoder = OccurrenceAddress.parse(MINT);
        String until = Endpoint.activation(reader, ExecutionIndex.empty());
        handed("", Collections.singletonList(viewHold(view, 1L, reader,
                until, null)));
        java.util.concurrent.atomic.AtomicLong published =
                new java.util.concurrent.atomic.AtomicLong(1L);
        List<Long> applied = new ArrayList<Long>();
        assertTrue(publishing(view, 2L, decoder, () -> {
            published.accumulateAndGet(2L, Math::max);
            publication(applied, 2L).run();
        }));
        // The forced refresh: synchronous, never deferred (MessageDoors).
        published.accumulateAndGet(3L, Math::max);
        Confirmation.exited(until);
        awaitApplied(applied, 1);
        assertEquals("the newest stands", 3L, published.get());
    }

    /**
     * A publication is deferred only on a thread delivering a store's
     * notification, for the whole callback -- after it read the version that
     * caused it too --, outside a refresh the system asked for
     * (MessageDoors#publishing): a forced refresh's -- or a refresh the
     * system makes inside a callback and reads right after on its thread,
     * Solr's StateWatcher#refreshAndWatch() and AliasesManager#update(),
     * bracketed the same way --, or one on a thread that delivers none,
     * publishes at once.
     */
    @Test
    public void onlyANotificationsPublicationIsDeferred() throws Exception {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        Lineage.resetForTests();
        SourceRef node = new SourceRef("CLUSTER_NODE", "SOLR_NODE",
                "auto0/node0", 0);
        java.util.concurrent.CountDownLatch held =
                new java.util.concurrent.CountDownLatch(1);
        boolean[] answered = new boolean[4];
        Object owner = new Object();
        RuntimeTraceContext.registerSource(owner, node);
        // The watch thread starts before the reader's request, so its work
        // is its own, under its own request.
        Thread watch = new Thread(() -> {
            long scope = RuntimeTraceContext.beginRequest(node, "watch");
            try {
                MessageDoors.stored("SOLR_ZK", "/notified/state.json@2",
                        owner, null);
                held.await();
                answered[0] = MessageDoors.publishing("SOLR_ZK",
                            "/notified/state.json", 2L, () -> { });
                MessageDoors.notified("Watcher", () -> {
                    long token = MessageDoors.refreshStarting();
                    try {
                        answered[1] = MessageDoors.publishing("SOLR_ZK",
                                "/notified/state.json", 2L, () -> { });
                    } finally {
                        MessageDoors.refreshEnded(token);
                    }
                    // The callback reads its cause first, which ends the
                    // notification's inbound: it delivers it all the same.
                    MessageDoors.fetched("SOLR_ZK", "/notified/state.json@2",
                            owner, null);
                    answered[3] = MessageDoors.current() != null;
                    answered[2] = MessageDoors.publishing("SOLR_ZK",
                            "/notified/state.json", 2L, () -> { });
                });
            } catch (InterruptedException stopped) {
                Thread.currentThread().interrupt();
            } finally {
                RuntimeTraceContext.endRequest(scope);
            }
        });
        watch.start();
        long hop = RuntimeTraceContext.beginRequest(node, "read");
        try {
            OccurrenceAddress reader = Identity.occurrence(node.key(),
                    "REGION.reader", true);
            LocationId view = MessageDoors.viewOf(MessageDoors.storeLocation(
                    "SOLR_ZK", "/notified/state.json"), reader);
            Confirmation.resetForTests();
            handed("", Collections.singletonList(viewHold(view, 1L, reader,
                    Endpoint.activation(reader, ExecutionIndex.empty()),
                    null)));
            held.countDown();
            watch.join(5000L);
            assertFalse("no notification: published at once", answered[0]);
            assertFalse("a forced refresh: published at once", answered[1]);
            assertTrue("the callback read its cause", answered[3]);
            assertTrue("a notification's, past its read: deferred",
                    answered[2]);
        } finally {
            RuntimeTraceContext.endRequest(hop);
            Identity.resetForTests();
        }
    }

    /**
     * ONE ORDER PER VIEW (review F1): once a publication of a view is
     * deferred, every later one of it on a notification's thread follows
     * it, a removal (-1) and a same-version update (per-replica states, -2)
     * too, and they apply in the order they came -- a removal never
     * overtakes the deferred version it came after, and the per-replica
     * update applies onto the state then published.
     */
    @Test
    public void removalsAndSameVersionUpdatesFollowWhatWasDeferred()
            throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/collections/c/state.json");
        OccurrenceAddress reader = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress decoder = OccurrenceAddress.parse(MINT);
        String until = Endpoint.activation(reader, ExecutionIndex.empty());
        handed("", Collections.singletonList(viewHold(view, 1L, reader,
                until, null)));
        List<Long> applied = new ArrayList<Long>();
        assertTrue(publishing(view, 2L, decoder, publication(applied, 2L)));
        assertTrue("a same-version update follows",
                publishing(view, -2L, decoder, publication(applied, -2L)));
        assertTrue("a removal follows",
                publishing(view, -1L, decoder, publication(applied, -1L)));
        Thread.sleep(100L);
        assertTrue(applied.toString(), applied.isEmpty());
        Confirmation.exited(until);
        awaitApplied(applied, 3);
        assertEquals(Arrays.asList(2L, -2L, -1L), applied);
        assertTrue(Confirmation.close().isEmpty());
    }

    /**
     * NEVER SILENT (snapshot-no-active, rounds Z3E/Z3F): a version the system
     * puts in force at once -- a publication no hold defers (a request that
     * carried a newer view, Solr's compareStateVersions; a refresh it asked
     * for), or a refresh's decode its reader reads as it is (a lazy
     * collection's live fetch) -- past a hold still standing before its read
     * overrides it: named once per hold (a CONFIRM mismatch, and the read's
     * PAIRING_UNTAKEN says who), and nothing is held or released by it.  At
     * or below the paired version, after the read, or the reader's own
     * work's (exempt by the hold), it overrides nothing.
     */
    @Test
    public void theSystemsOwnPublicationPastAHoldBeforeItsReadIsNamed()
            throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/collections/c/state.json");
        Endpoint read = endpoint(ANCHOR, "<a.Handler: void handle()>#u1");
        OccurrenceAddress reader = read.occurrence();
        OccurrenceAddress request = OccurrenceAddress.parse(MINT);
        String until = Endpoint.activation(reader, ExecutionIndex.empty());
        String id = Confirmation.id(read);
        // what, version, read first, named
        Object[][] rows = {
                {"a request's refresh past the hold", 8L, false, true},
                {"a refresh at the paired version", 7L, false, false},
                {"a refresh after the read", 8L, true, false},
                {"the reader's own work, which the hold exempts", 8L, false,
                        false},
                {"a lazy fetch's decode past the hold", 8L, false, true},
        };
        for (Object[] row : rows) {
            String what = (String) row[0];
            long version = (Long) row[1];
            Confirmation.resetForTests();
            handed("", Collections.singletonList(viewHold(view, 7L, reader,
                    until, id)));
            if ((Boolean) row[2]) {
                Confirmation.read(read, view, 7L, ReadRow.UNKNOWN_VERSION);
            }
            if (what.startsWith("the reader's own")) {
                assertFalse(what + ": published at once", publishing(view,
                        version, reader, () -> { }));
            } else if (what.startsWith("a lazy")) {
                Confirmation.overridden(view, version, request, "a lazy"
                        + " fetch");
                Confirmation.overridden(view, version + 1L, request,
                        "a lazy fetch");
            } else {
                Confirmation.published(view, version, request,
                        "a request's refresh", null, null);
            }
            String because = Confirmation.untakenBecause(id);
            List<String> mismatches = Confirmation.close();
            if ((Boolean) row[3]) {
                assertTrue(what + ": " + because,
                        because.startsWith("overridden: version " + version));
                assertEquals(what + ": once per hold " + mismatches, 1,
                        mismatches.size());
                assertTrue(what + ": " + mismatches.get(0), mismatches.get(0)
                        .contains("published at once at "
                                + request.render()));
            } else {
                assertEquals(what, "", because);
                assertTrue(what + ": " + mismatches, mismatches.isEmpty());
            }
        }
    }

    /**
     * A publication the system makes at once read the store after the
     * deferred ones did: it drops a deferred removal and what came before
     * it -- applied after, the removal would delete what it published --,
     * and a removal of its own drops them all; a deferred version with no
     * removal after it stays and applies, the system's compare keeping the
     * newest.
     */
    @Test
    public void aSynchronousPublicationDropsTheDeferredRemovalsBeforeIt()
            throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/collections/c/state.json");
        OccurrenceAddress reader = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress decoder = OccurrenceAddress.parse(MINT);
        String until = Endpoint.activation(reader, ExecutionIndex.empty());
        for (long synchronous : new long[] {-1L, 5L}) {
            Confirmation.resetForTests();
            handed("", Collections.singletonList(viewHold(view, 1L, reader,
                    until, null)));
            List<Long> applied = new ArrayList<Long>();
            assertTrue(publishing(view, 2L, decoder,
                    publication(applied, 2L)));
            assertTrue(publishing(view, -1L, decoder,
                    publication(applied, -1L)));
            assertTrue(publishing(view, 4L, decoder,
                    publication(applied, 4L)));
            Confirmation.published(view, synchronous,
                    OccurrenceAddress.parse(MINT), "a forced refresh", null,
                    null);
            Confirmation.exited(until);
            if (synchronous != -1L) awaitApplied(applied, 1);
            Thread.sleep(100L);
            assertEquals("after a synchronous " + synchronous,
                    synchronous == -1L ? Collections.<Long>emptyList()
                            : Arrays.asList(4L), applied);
        }
    }

    /**
     * VIEW_HOLD_MAX counts per hold, from the first publication that hold
     * deferred (review L1): a hold that began deferring later gives way
     * later, whatever waited in the queue before it.
     */
    @Test
    public void aHoldGivesWayAtItsOwnBoundFromItsFirstDeferral()
            throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/aliases.json");
        OccurrenceAddress first = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress second = OccurrenceAddress.parse(
                "hdfs/dn1#epoch0/region/REGION.7c569c3f/ctx:Root:XCEIVER#2"
                        + "/idx:<a.Handler: void handle()>@0");
        OccurrenceAddress decoder = OccurrenceAddress.parse(MINT);
        String firstExits = Endpoint.activation(first,
                ExecutionIndex.empty());
        handed("", Arrays.asList(viewHold(view, 1L, first, firstExits, null),
                viewHold(view, 2L, second, Endpoint.activation(second,
                        ExecutionIndex.empty()), null)));
        System.setProperty(Confirmation.VIEW_HOLD_MAX_PROPERTY, "600");
        try {
            List<Long> applied = new ArrayList<Long>();
            long began = System.nanoTime();
            // Held by the first hold alone (2 is not past the second's 2).
            assertTrue(publishing(view, 2L, decoder,
                    publication(applied, 2L)));
            Thread.sleep(400L);
            // Held by both: the second's bound counts from here.
            assertTrue(publishing(view, 3L, decoder,
                    publication(applied, 3L)));
            Confirmation.exited(firstExits);
            awaitApplied(applied, 1);
            long due = began + 800_000_000L - System.nanoTime();
            if (due > 0L) Thread.sleep(due / 1_000_000L);
            synchronized (applied) {
                assertEquals("past the first deferral's bound, the second"
                        + " hold still stands", Arrays.asList(2L), applied);
            }
            awaitApplied(applied, 2);
            assertEquals(Arrays.asList(2L, 3L), applied);
            List<String> mismatches = Confirmation.close();
            assertEquals(mismatches.toString(), 1, mismatches.size());
            assertTrue(mismatches.get(0), mismatches.get(0)
                    .contains("past version 2"));
        } finally {
            System.clearProperty(Confirmation.VIEW_HOLD_MAX_PROPERTY);
        }
    }

    /**
     * A node's one publisher outlives an interrupt and the system's own
     * throw in an apply (named the system's failure, never the engine's);
     * an apply that blocks past VIEW_HOLD_MAX is named, its node's later
     * publications waiting behind it.
     */
    @Test
    public void thePublisherOutlivesAnInterruptAndTheSystemsThrow()
            throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/aliases.json");
        OccurrenceAddress reader = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress decoder = OccurrenceAddress.parse(MINT);
        String until = Endpoint.activation(reader, ExecutionIndex.empty());
        handed("", Collections.singletonList(viewHold(view, 1L, reader,
                until, null)));
        System.setProperty(Confirmation.VIEW_HOLD_MAX_PROPERTY, "300");
        java.util.concurrent.CountDownLatch blocked =
                new java.util.concurrent.CountDownLatch(1);
        try {
            List<Long> applied = new ArrayList<Long>();
            assertTrue(publishing(view, 2L, decoder, () -> {
                throw new IllegalStateException("the system's own");
            }));
            assertTrue(publishing(view, 3L, decoder,
                    publication(applied, 3L)));
            assertTrue(publishing(view, 4L, decoder, () -> {
                try {
                    blocked.await(5L, java.util.concurrent.TimeUnit.SECONDS);
                } catch (InterruptedException stopped) {
                    Thread.currentThread().interrupt();
                }
                publication(applied, 4L).run();
            }));
            Thread publisher = null;
            for (Thread thread : Thread.getAllStackTraces().keySet()) {
                if (thread.getName().equals("causynth-view-publisher-"
                        + NODE)) {
                    publisher = thread;
                }
            }
            assertTrue("one publisher per node", publisher != null);
            publisher.interrupt();
            Thread.sleep(100L);
            assertTrue("an interrupt never ends it", publisher.isAlive());
            Confirmation.exited(until);
            awaitApplied(applied, 1);
            assertEquals("the system's throw ends nothing",
                    Arrays.asList(3L), applied);
            Thread.sleep(500L);
            List<String> mismatches = Confirmation.close();
            assertEquals(mismatches.toString(), 1, mismatches.size());
            assertTrue(mismatches.get(0), mismatches.get(0)
                    .contains("ran past VIEW_HOLD_MAX"));
        } finally {
            blocked.countDown();
            System.clearProperty(Confirmation.VIEW_HOLD_MAX_PROPERTY);
        }
    }

    /**
     * A view's deferred publications queue per path, not per store life
     * (review re-check 2026-10-12): the collection removed and created
     * again, the new life's publication follows the old life's deferred
     * version and removal, so the node ends with the new collection's
     * state, not without one.
     */
    @Test
    public void aRecreatedViewsPublicationFollowsTheOldLifesQueue()
            throws Exception {
        LocationId old = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/collections/c/state.json");
        LocationId recreated = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/collections/c/state.json#2");
        OccurrenceAddress reader = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress decoder = OccurrenceAddress.parse(MINT);
        String until = Endpoint.activation(reader, ExecutionIndex.empty());
        handed("", Collections.singletonList(viewHold(old, 1L, reader,
                until, null)));
        List<Long> applied = new ArrayList<Long>();
        assertTrue(publishing(old, 5L, decoder, publication(applied, 5L)));
        assertTrue(publishing(old, -1L, decoder, publication(applied, -1L)));
        assertTrue("the new life's follows",
                publishing(recreated, 0L, decoder, publication(applied, 0L)));
        Thread.sleep(100L);
        assertTrue(applied.toString(), applied.isEmpty());
        Confirmation.exited(until);
        awaitApplied(applied, 3);
        assertEquals(Arrays.asList(5L, -1L, 0L), applied);
        assertEquals(Confirmation.queueKey(old),
                Confirmation.queueKey(recreated));
    }

    /**
     * A window's measure states whether its run ended inside it: a closed
     * window is the workload's whole, one a run ended inside (a replay
     * halted at its witness) is marked cut, which the campaign names.
     */
    @Test
    public void aWindowItsRunEndedInsideIsMarkedCut() throws Exception {
        Path file = folder.newFile("window_ms").toPath();
        System.setProperty(RecordingWindow.WINDOW_MS_FILE, file.toString());
        try {
            for (boolean closes : new boolean[] {true, false}) {
                RecordingWindow.reset();
                RecordingWindow.open();
                if (closes) {
                    RecordingWindow.close();
                } else {
                    RecordingWindow.measured();
                }
                String stated = new String(Files.readAllBytes(file),
                        StandardCharsets.UTF_8).trim();
                assertTrue(stated, closes ? stated.matches("[0-9]+")
                        : stated.matches("[0-9]+\t" + RecordingWindow.CUT));
            }
        } finally {
            System.clearProperty(RecordingWindow.WINDOW_MS_FILE);
            RecordingWindow.reset();
        }
    }

    /**
     * A read of a view no hook publishes, held at the version its session
     * observed, is a STATE row and no VIEW_HOLD ({@code
     * explore.ConfirmMain#stateEdges}), compared exactly: a run whose read
     * observed that version took the edge; one whose fetch decoded and read
     * another took none, a misread, and is not confirmed.
     */
    @Test
    public void anUnheldViewReadIsComparedAtItsVersion() throws Exception {
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/snapshots/s/s-M");
        Endpoint fetched = endpoint(ANCHOR, "SOLR_ZK#VIEW:.snapshots.s.s-M");
        Endpoint viewed = endpoint(ANCHOR, "a.Handler#h()#20:READ#VIEW");
        // the version the run's fetch decoded and its read observed, taken
        Object[][] table = {{1L, true}, {2L, false}};
        for (Object[] row : table) {
            reset();
            handed("", Collections.singletonList("{\"kind\":\"STATE\","
                    + "\"reader\":\"" + Confirmation.id(viewed) + "\","
                    + "\"mint\":false,\"writer\":\""
                    + Confirmation.viewWriter(1L) + "\",\"version\":1,"
                    + "\"location\":\"VIEW/SOLR_ZK@hdfs/dn0#epoch0#"
                    + "/snapshots/s/s-M\"}"));
            long version = (Long) row[0];
            Confirmation.wrote(view, version, fetched, false);
            Confirmation.read(viewed, view, version, ReadRow.UNKNOWN_VERSION);
            assertFalse("no view is held", Confirmation.holdsViews());
            List<String> close = Confirmation.close();
            assertEquals(row[0] + ": " + close, row[1], close.isEmpty());
            assertEquals(row[0] + ": misread", row[1],
                    Confirmation.held().misread.isEmpty());
            if (!(Boolean) row[1]) {
                assertTrue(close.get(0), close.get(0).startsWith("STATE "
                        + Confirmation.id(viewed) + ": the model joined this"
                        + " read to writer VIEW@1 (version 1), the run"
                        + " observed"));
            }
        }
    }

    /**
     * A view hold whose reader read in role work, which no hook closes, ends
     * at the first region that work closes after the read, in the run as it
     * goes: a region of its context closing before the read ends nothing.
     */
    @Test
    public void aRoleReadersHoldEndsAtTheFirstRegionItsWorkClosesAfterTheRead()
            throws Exception {
        OccurrenceAddress region = OccurrenceAddress.parse(ANCHOR);
        OccurrenceAddress role = OccurrenceAddress.of(region.node(),
                OccurrenceAddress.ROLE_REGION + "XCEIVER", region.context(),
                ExecutionIndex.empty());
        Endpoint read = endpoint(ANCHOR, "SOLR_ZK#VIEWED:|aliases.json#VIEW");
        read = Endpoint.of(role, read.site(), ExecutionIndex.empty(), 0);
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs/dn0#epoch0", "/aliases.json");
        handed("", Collections.singletonList(viewHold(view, 1L, role, "",
                Confirmation.id(read))));
        List<Long> applied = new ArrayList<Long>();
        assertTrue(publishing(view, 2L,
                OccurrenceAddress.parse(MINT), publication(applied, 2L)));
        Confirmation.regionClosed(region);
        Thread.sleep(100L);
        assertTrue("a region closing before the read ends nothing",
                applied.isEmpty());
        Confirmation.read(read, view, 1L, ReadRow.UNKNOWN_VERSION);
        Confirmation.regionClosed(region);
        awaitApplied(applied, 1);
        assertEquals("released at the region's close after the read",
                Arrays.asList(2L), applied);
    }

    /**
     * How a replay held its world ({@code Confirmation#held}, condition (b)
     * of a WORLD_REFUTED): a hold an interrupt ended stands while its
     * activation does nothing tracked after it, and gave way once it does;
     * a placeholder read that observed another writer than its MINT edge's
     * is a misread, one never minted none; edges a world plants and the
     * replay cannot read fail it whole.
     */
    @Test
    public void anInterruptedHoldStandsOnlyUntilItsActivationRunsOn()
            throws Exception {
        String reader = Endpoint.activation(OccurrenceAddress.parse(ANCHOR),
                ExecutionIndex.empty());
        String never = Endpoint.activation(OccurrenceAddress.parse(PRODUCER),
                ExecutionIndex.empty());
        Endpoint writer = endpoint(MINT, "a.Manager#tick()#7:WRITE");
        LocationId cell = LocationId.of(LocationKind.INSTANCE, "1", "40");
        // ran on after the interrupt, a placeholder read at the edge's cell
        // (null: none), stands, misread
        Object[][] table = {
                {false, null, true, false},
                {true, null, false, false},
                {false, Boolean.TRUE, true, false},
                {false, Boolean.FALSE, true, true}};
        for (Object[] row : table) {
            reset();
            handed("", Arrays.asList(
                    "{\"kind\":\"ORDER\",\"before\":\"" + never
                            + "\",\"after\":\"" + reader + "\"}",
                    "{\"kind\":\"STATE\",\"reader\":\"" + endpoint(ANCHOR,
                            "a.Handler#h()#12:READ").id() + "\",\"mint\":true,"
                            + "\"writer\":\"" + writer.id()
                            + "\",\"version\":\"4\","
                            + "\"location\":\"INSTANCE/1#40\"}"));
            assertTrue(Confirmation.ordering());
            Thread held = new Thread(() -> {
                Thread.currentThread().interrupt();
                Confirmation.entering(reader);
                if ((Boolean) row[0]) {
                    Confirmation.wrote(cell, 9L, writer, false);
                }
            });
            held.start();
            held.join(5000L);
            if (row[1] != null) {
                Confirmation.wrote(cell, 4L, (Boolean) row[1] ? writer
                        : endpoint(PRODUCER, "a.Convert#c()#2:WRITE"), false);
                Confirmation.read(endpoint(PRODUCER, "a.Convert#c()#3:READ"),
                        cell, 4L, 9L);
            }
            Confirmation.Held run = Confirmation.held();
            String what = Arrays.toString(row) + ": " + run.gaveWay + " "
                    + run.waiting + " " + run.misread;
            assertEquals(what, (Boolean) row[2], run.gaveWay.isEmpty()
                    && run.waiting.containsKey(reader));
            assertEquals(what, (Boolean) row[3], !run.misread.isEmpty());
        }
        // Two holds an interrupt ended on one thread both stand: the later
        // one never hides the earlier.
        reset();
        String second = Endpoint.activation(OccurrenceAddress.parse(MINT),
                ExecutionIndex.empty());
        handed("", Arrays.asList(
                "{\"kind\":\"ORDER\",\"before\":\"" + never
                        + "\",\"after\":\"" + reader + "\"}",
                "{\"kind\":\"ORDER\",\"before\":\"" + never
                        + "\",\"after\":\"" + second + "\"}"));
        assertTrue(Confirmation.ordering());
        Thread both = new Thread(() -> {
            Thread.currentThread().interrupt();
            Confirmation.entering(reader);
            Thread.currentThread().interrupt();
            Confirmation.entering(second);
        });
        both.start();
        both.join(5000L);
        Confirmation.Held twice = Confirmation.held();
        assertTrue(twice.waiting.toString(), twice.gaveWay.isEmpty()
                && twice.waiting.containsKey(reader)
                && twice.waiting.containsKey(second));
        reset();
        Path worker = folder.newFolder().toPath();
        Files.write(worker.resolve("focused_task.jsonl"), ("{\"taskId\":"
                + "\"T\",\"obligationId\":\"OB\",\"pathId\":\"p\","
                + "\"focused\":\"" + ANCHOR + "\",\"seedSessionId\":\"seed\","
                + "\"flip\":null,\"pairings\":{\"r\":\"w\"}}\n")
                .getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, new byte[0]);
        System.setProperty(FocusedReplay.PLAN_PROPERTY, plan.toString());
        assertTrue("edges a world plants and the replay cannot read",
                Confirmation.held().misread.get(0).startsWith("EDGES: "));
    }

    /**
     * An ORDER on a queued task or a queue item (a server pipeline's
     * request) is held at the send that started it, up the chain of such
     * work; so is one on a hand-off task that served a queue (a
     * ConcurrentUpdate client's Runner, its session's servingTasks) and on
     * claimed work a row from before claimKind states no kind of.  On any
     * other activation -- a hand-off task that served none among them --
     * it is held where it runs; and it is refused, naming the claim's kind,
     * where no send runs where it can be held.
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
        String none = "NONE";
        String item = "ITEM";
        String queued = "QUEUED_TASK";
        String handed = "HANDOFF_TASK";
        // a hand-off task that took other work on its thread
        String serving = "HANDOFF_TASK serving";
        // a row from before claimKind: a claimed key, no kind
        String legacy = "NONE claimed";
        // row of each occurrence: its claim, its anchor's producer
        Object[][] table = {
                // held at the client's send, through the relaying stage
                {served, item, relayed, prep, item, send, send},
                // a client thread's own activation is held where it runs
                {client, none, null, null, none, null, null},
                // an item that names no send: no hold
                {served, item, null, null, none, null, "ORDER_UNHELD"},
                // a single-thread executor's task (queued) likewise
                {served, queued, null, null, none, null, "ORDER_UNHELD"},
                // a hand-off executor's task (an Overseer command's Runner,
                // a turn of its own with no anchor) is held where it runs
                {served, handed, null, null, none, null, null},
                // a send made inside a handed-off task is held there
                {served, item, relayed, prep, handed, null, relayed},
                // a Runner that polled its update queue is held at its send
                {served, serving, relayed, prep, none, null, relayed},
                {served, serving, null, null, none, null, "ORDER_UNHELD"},
                // and is no place to hold a send made inside it
                {served, item, relayed, prep, serving, send, send},
                // a claimed row of no stated kind keeps the send rule
                {served, legacy, relayed, prep, none, null, relayed},
                {served, legacy, null, null, none, null, "ORDER_UNHELD"},
        };
        for (Object[] row : table) {
            Map<String, ActivationRow> rows =
                    new HashMap<String, ActivationRow>();
            Set<String> servingTasks = new HashSet<String>();
            put(rows, servingTasks, (OccurrenceAddress) row[0],
                    (String) row[1], (Endpoint) row[2]);
            if (row[3] != null) {
                put(rows, servingTasks, (OccurrenceAddress) row[3],
                        (String) row[4], (Endpoint) row[5]);
            }
            Object held;
            try {
                held = Confirmation.submitter((OccurrenceAddress) row[0],
                        rows::get, servingTasks);
            } catch (IllegalStateException unheld) {
                assertTrue(unheld.getMessage(), unheld.getMessage().contains(
                        rows.get(((OccurrenceAddress) row[0]).id())
                                .claimedAs(servingTasks)));
                held = unheld.getMessage().split(":")[0];
            }
            assertEquals(row[0] + " " + row[1], row[6], held);
        }
    }

    /** An activation row stating {@code claim} ("KIND", "KIND serving"
     *  for a hand-off task that served a queue, "NONE claimed" for a row
     *  from before claimKind). */
    private static void put(Map<String, ActivationRow> rows,
                            Set<String> servingTasks, OccurrenceAddress at,
                            String claim, Endpoint producer) {
        String[] parts = claim.split(" ");
        ActivationRow.ClaimKind kind =
                ActivationRow.ClaimKind.valueOf(parts[0]);
        String threadKey = kind == ActivationRow.ClaimKind.NONE
                && parts.length == 1 ? "main#1"
                : ActivationRow.CLAIMED + at.id();
        if (claim.endsWith(" serving")) servingTasks.add(threadKey);
        rows.put(at.id(), ActivationRow.of("s0", at, "", false, true,
                threadKey, kind, producer));
    }
}
