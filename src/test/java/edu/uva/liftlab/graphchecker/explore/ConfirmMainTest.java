package edu.uva.liftlab.graphchecker.explore;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * CONFIRM's inputs, off a claim, its manifest and the sessions the witness
 * rests on: the focus row that flips nothing, the schedule cut at the
 * anchor, and the edges the model chose.
 */
public class ConfirmMainTest {
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
    private static final LocationId CELL =
            LocationId.of(LocationKind.INSTANCE, "1", "40");

    private final OccurrenceAddress anchor = OccurrenceAddress.parse(ANCHOR);
    private final OccurrenceAddress mint = OccurrenceAddress.parse(MINT);
    private final Endpoint consumer = endpoint(ANCHOR, "XCH.1.resp.key-id");
    private final Endpoint producer = endpoint(PRODUCER, "XCH.1.resp.key-id");
    private final Endpoint reader = endpoint(ANCHOR, "a.Handler#h()#12:READ");
    private final Endpoint unknown = endpoint(ANCHOR, "a.Handler#h()#13:READ");
    private final Endpoint writer = endpoint(MINT, "a.Manager#tick()#7:WRITE");

    private static Endpoint endpoint(String occurrence, String site) {
        return Endpoint.of(OccurrenceAddress.parse(occurrence), site,
                ExecutionIndex.empty(), 0);
    }

    private RootMintRow root(String session, String id, String symbol,
                             RootKind kind, String value) {
        return RootMintRow.of(session, 1L, mint, id, symbol, kind, value,
                null, null, true);
    }

    /** The recording and the selected session, as the corpus holds them. */
    private Path iteration() throws Exception {
        Path iteration = folder.newFolder("iteration-0000").toPath();
        SessionDir seed = SessionDir.of(iteration, "seed").create();
        RowCodec.writeAll(seed.roots(), Arrays.asList(
                root("seed", "HDFS.SERIAL", "M_I_serial", RootKind.INTEGRAL,
                        "119978"),
                root("seed", "CLOCK.a", "M_J_clock.seed", RootKind.CLOCK,
                        "1000"),
                root("seed", "FAULT:IPC", "M_Z_fault", RootKind.MARKER,
                        "false"),
                root("seed", "OTHER", "M_I_other", RootKind.INTEGRAL, "7")),
                RowCodec::writeRootMint);
        manifest(seed, SessionManifest.Role.SEED);
        SessionDir sel = SessionDir.of(iteration, "sel").create();
        RowCodec.writeAll(sel.roots(), Arrays.asList(
                root("sel", "HDFS.SERIAL", "M_I_serial.sel",
                        RootKind.INTEGRAL, "119978"),
                root("sel", "CLOCK.a", "M_J_clock.sel", RootKind.CLOCK,
                        "2000")), RowCodec::writeRootMint);
        RowCodec.writeAll(sel.targets(), Collections.singletonList(
                TargetRow.of("sel", 40L, anchor, "<a.Handler: void handle()>"
                        + "#u8#1", "EXPR.phi", true, true)),
                RowCodec::writeTarget);
        RowCodec.writeAll(sel.writes(), Collections.singletonList(
                WriteRow.of("sel", 10L, writer, CELL, 5L, "EXPR.w", "I")),
                RowCodec::writeWrite);
        RowCodec.writeAll(sel.reads(), Arrays.asList(
                ReadRow.of("sel", 30L, reader, CELL, 5L, "INSTANCE_FIELD/1"
                        + "#40@v5", "I", "3"),
                ReadRow.of("sel", 31L, unknown, CELL, -1L, "INSTANCE_FIELD/1"
                        + "#40@v?", "I", "3")), RowCodec::writeRead);
        RowCodec.writeAll(sel.attaches(), Collections.singletonList(
                AttachRow.of("sel", 20L, consumer, "M_I_field_HOFF.1", "I",
                        "119979", false, null, producer, "ipc-25",
                        "HANDLE")), RowCodec::writeAttach);
        List<JsonObject> schedule = new ArrayList<JsonObject>();
        schedule.add(event(0, "a", ""));
        schedule.add(event(1, "b", ""));
        JsonObject mark = new JsonObject();
        mark.addProperty("mark", anchor.id());
        mark.addProperty("at", 2L);
        schedule.add(mark);
        schedule.add(event(2, "c", anchor.id()));
        schedule.add(event(3, "d", ""));
        RowCodec.writeJsonl(sel.schedule(), schedule);
        manifest(sel, SessionManifest.Role.FOCUSED);
        return iteration;
    }

    private static void manifest(SessionDir dir, SessionManifest.Role role)
            throws Exception {
        RowCodec.writeExpressions(dir.expressions(), ExpressionTable.empty());
        RowCodec.writeManifest(dir.manifest(), SessionManifest.of(
                dir.sessionId(), role, role == SessionManifest.Role.SEED
                        ? Collections.<String>emptyList()
                        : Collections.singletonList("OBL.x")));
    }

    private static JsonObject event(long seq, String site,
                                    String occurrence) {
        return RowCodec.writeScheduleEvent(ScheduleEvent.of(seq,
                ScheduleEvent.Kind.SEND, "node|Root:X", site, 0, occurrence));
    }

    private Path claim(String movedCell) throws Exception {
        Path file = folder.newFile("claim.json").toPath();
        Files.write(file, ("{\"kind\":\"CLAIM\",\"anchor\":\"" + ANCHOR
                + "\",\"seedSessionId\":\"seed\","
                + "\"claim\":{\"kind\":\"CLOCK_SKEW\",\"valuationOrdinal\":1,"
                + "\"movedRoots\":{\"" + movedCell + "\":\"45000\"},"
                + "\"polarityDecides\":true,\"gaps\":[]},"
                + "\"valuations\":[{\"ordinal\":0,\"status\":\"unsat\","
                + "\"selectedPathId\":\"\",\"selectedSessionId\":\"\"},"
                + "{\"ordinal\":1,\"status\":\"sat\","
                + "\"assignment\":{\"HDFS.SERIAL\":\"119980\"},"
                + "\"moved\":{\"FAULT:IPC\":\"true\"},"
                + "\"selectedPathId\":\"p1\",\"selectedSessionId\":\"sel\","
                + "\"fatalObserved\":true,\"selectedArms\":[{"
                + "\"selector\":\"message_arm__1__abc\","
                + "\"family\":\"message_family__1__abc\",\"groupId\":\""
                + consumer.id() + "\",\"attachEndpointIds\":[\""
                + consumer.id() + "\"],\"sessionId\":\"sel\","
                + "\"producerPathId\":\"p9\",\"interactionIds\":[\"i1\"],"
                + "\"expressionRefs\":[\"EXPR.e\"],\"attested\":true},"
                // A free arm of a path the model did NOT select: its
                // selector was unconstrained, so z3 may set it, and it
                // is no edge of the selected path.
                + "{\"selector\":\"message_arm__2__zzz\","
                + "\"family\":\"message_family__2__zzz\",\"groupId\":\"g\","
                + "\"attachEndpointIds\":[\"" + consumer.id() + "\"],"
                + "\"sessionId\":\"other\",\"producerPathId\":\"p2\","
                + "\"interactionIds\":[],\"expressionRefs\":[],"
                + "\"attested\":true}],"
                + "\"unsatCore\":[]}]}").getBytes(StandardCharsets.UTF_8));
        return file;
    }

    private Path manifest() throws Exception {
        Path file = folder.newFile("manifest.json").toPath();
        Files.write(file, ("{\"kind\":\"COMPOSITION_MANIFEST\",\"paths\":["
                + "{\"pathId\":\"p1\",\"sessionId\":\"sel\","
                + "\"selector\":\"path_selector__1__abc\","
                + "\"fatalObserved\":true},"
                + "{\"pathId\":\"p2\",\"sessionId\":\"other\","
                + "\"selector\":\"path_selector__2__zzz\","
                + "\"fatalObserved\":false}],\"roots\":["
                + "{\"rootId\":\"HDFS.SERIAL\",\"kind\":\"INTEGRAL\","
                + "\"recordedValue\":\"119978\"},"
                + "{\"rootId\":\"CLOCK.a\",\"kind\":\"CLOCK\","
                + "\"recordedValue\":\"1000\"},"
                + "{\"rootId\":\"FAULT:IPC\",\"kind\":\"MARKER\","
                + "\"recordedValue\":\"false\"},"
                + "{\"rootId\":\"OTHER\",\"kind\":\"INTEGRAL\","
                + "\"recordedValue\":\"7\"}]}")
                .getBytes(StandardCharsets.UTF_8));
        return file;
    }

    @Test
    public void theWorkerIsHandedTheModelTheScheduleAndTheEdges()
            throws Exception {
        Path iteration = iteration();
        Path out = folder.newFolder("worker").toPath();

        JsonObject summary = ConfirmMain.write(iteration,
                claim("M_J_clock.sel"), manifest(), out);

        assertEquals("p1", summary.get("selectedPathId").getAsString());
        List<JsonObject> focus = RowCodec.readJsonl(
                out.resolve("focused_task.jsonl"));
        assertEquals(1, focus.size());
        JsonObject row = focus.get(0);
        assertTrue("no flip is forced", row.get("flip").isJsonNull());
        assertEquals(0, row.getAsJsonArray("inheritedFlips").size());
        assertEquals(ANCHOR, row.get("focused").getAsString());
        assertEquals(anchor.id(), row.get("focusedOccurrenceId").getAsString());
        assertEquals("seed", row.get("seedSessionId").getAsString());
        JsonObject roots = row.getAsJsonObject("rootAssignments");
        assertEquals("the valuation's assignment", "119980",
                roots.get("HDFS.SERIAL").getAsString());
        assertEquals("the valuation's moved marker", "true",
                roots.get("FAULT:IPC").getAsString());
        assertTrue("a root the valuation left unvaried is not planted: it"
                + " needs no plant, and its mint may not recur",
                !roots.has("OTHER"));
        assertTrue("a clock is a skew, never a value",
                !roots.has("CLOCK.a"));
        assertEquals("model instant minus the selected session's reading",
                "43000", row.getAsJsonObject("clockDeltas").get("CLOCK.a")
                        .getAsString());
        JsonObject mints = row.getAsJsonObject("rootMints");
        assertEquals(3, mints.size());
        assertEquals("where the RECORDING mints it", MINT,
                mints.get("CLOCK.a").getAsString());
        assertEquals("cut at the anchor's first event", 2,
                row.getAsJsonObject("schedulePrefix").get("events").getAsInt());
        assertEquals(2, SessionReader.readSchedule(
                out.resolve(SchedulePrefix.FILE)).size());
        assertEquals(2, SessionReader.readSchedule(
                out.resolve(SchedulePrefix.REST_FILE)).size());

        Map<String, JsonObject> edges = new LinkedHashMap<String, JsonObject>();
        List<JsonObject> rows = RowCodec.readJsonl(
                out.resolve(Confirmation.FILE));
        for (JsonObject edge : rows) {
            edges.put(edge.get("kind").getAsString(), edge);
        }
        assertEquals("one edge each, and none from the free arm of the"
                + " path the model did not select", 4, rows.size());
        assertEquals(4, edges.size());
        assertEquals("the export the arm's own session paired the consumer"
                + " with", producer.id(),
                edges.get("WIRE").get("producer").getAsString());
        assertEquals(consumer.id(),
                edges.get("WIRE").get("consumer").getAsString());
        assertEquals("the read joined to the version it observed",
                reader.id(), edges.get("STATE").get("reader").getAsString());
        assertEquals(writer.id(),
                edges.get("STATE").get("writer").getAsString());
        assertEquals(5L, edges.get("STATE").get("version").getAsLong());
        assertEquals("FAULT:IPC", edges.get("MARKER").get("root").getAsString());
        assertTrue(edges.get("MARKER").get("value").getAsBoolean());
        assertEquals(anchor.id(),
                edges.get("ANCHOR").get("occurrence").getAsString());
        assertEquals(40L, edges.get("ANCHOR").get("seq").getAsLong());
    }

    @Test
    public void aMovedCellNoSessionOfTheWitnessMintedIsRefusedByName()
            throws Exception {
        Path iteration = iteration();
        try {
            ConfirmMain.write(iteration, claim("M_J_clock.elsewhere"),
                    manifest(), folder.newFolder("worker").toPath());
            fail("a cell nobody minted was planted");
        } catch (ConfirmMain.Refused refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "M_J_clock.elsewhere") && refused.getMessage()
                    .contains("no session of the witness minted"));
        }
    }
}
