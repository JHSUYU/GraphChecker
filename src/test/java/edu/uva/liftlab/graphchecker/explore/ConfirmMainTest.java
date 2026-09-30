package edu.uva.liftlab.graphchecker.explore;

import java.util.ArrayList;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.Hole;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
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
    private final Endpoint after = endpoint(ANCHOR, "a.Handler#h()#14:READ");
    private final Endpoint writer = endpoint(MINT, "a.Manager#tick()#7:WRITE");

    private static Endpoint endpoint(String occurrence, String site) {
        return Endpoint.of(OccurrenceAddress.parse(occurrence), site,
                ExecutionIndex.empty(), 0);
    }

    private RootMintRow root(String session, String id, String symbol,
                             RootKind kind, String value) {
        return RootMintRow.of(session, 1L, mint, id, symbol, kind, value,
                null, null, true, kind == RootKind.CLOCK ? 1_000_000L : 0L);
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
                root("seed", "CLOCK.b", "M_J_clock.b", RootKind.CLOCK,
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
                        "2000"),
                root("sel", "CLOCK.b", "M_J_clock.b", RootKind.CLOCK,
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
                        + "#40@v?", "I", "3"),
                // After the target (seq 40): a fatal run throws before it.
                ReadRow.of("sel", 45L, after, CELL, 5L, "INSTANCE_FIELD/1"
                        + "#40@v5", "I", "3")), RowCodec::writeRead);
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
        // The obligation whose replay published "sel": the world it ran.
        Path worker = Files.createDirectories(
                iteration.resolve("obligations-0000").resolve("w1"));
        JsonObject result = new JsonObject();
        result.addProperty("sessionId", "sel");
        RowCodec.writeJsonl(worker.resolve(ObligationDir.RESULT),
                Collections.singletonList(result));
        JsonObject world = new JsonObject();
        JsonObject assignments = new JsonObject();
        assignments.addProperty("HDFS.SERIAL", "119980");
        assignments.addProperty("FAULT:IPC", "true");
        world.add("rootAssignments", assignments);
        JsonObject deltas = new JsonObject();
        deltas.addProperty("CLOCK.a", "43000");
        world.add("clockDeltas", deltas);
        world.add("answers", new JsonObject());
        JsonObject mints = new JsonObject();
        mints.addProperty("HDFS.SERIAL", "M_I_serial");
        mints.addProperty("CLOCK.a", MINT);
        mints.addProperty("FAULT:IPC", "M_Z_fault");
        world.add("rootMints", mints);
        RowCodec.writeJsonl(worker.resolve(ObligationDir.FOCUSED_TASK),
                Collections.singletonList(world));
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
        return claim(movedCell, "45000");
    }

    private Path claim(String movedCell, String movedValue) throws Exception {
        Path file = Files.createTempFile(folder.getRoot().toPath(), "claim",
                ".json");
        Files.write(file, ("{\"kind\":\"CLAIM\",\"anchor\":\"" + ANCHOR
                + "\",\"seedSessionId\":\"seed\","
                + "\"claim\":{\"kind\":\"CLOCK_SKEW\",\"valuationOrdinal\":1,"
                + "\"movedRoots\":{\"" + movedCell + "\":\"" + movedValue
                + "\"},"
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
        return manifest("INSTANCE/1#40", "INSTANCE/8#16", "MAP/20#-3",
                "MAP/30#-3");
    }

    /** The composition manifest, its selected path resting on these. */
    private Path manifest(String... restsOn) throws Exception {
        Path file = Files.createTempFile(folder.getRoot().toPath(),
                "manifest", ".json");
        Files.write(file, ("{\"kind\":\"COMPOSITION_MANIFEST\",\"paths\":["
                + "{\"pathId\":\"p1\",\"sessionId\":\"sel\","
                + "\"selector\":\"path_selector__1__abc\","
                + "\"fatalObserved\":true,\"restsOn\":"
                + new com.google.gson.Gson().toJson(restsOn) + "},"
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

    /**
     * A read of a version no row wrote (a store outside every region, VM
     * 22f2707a1) joins nothing: the run holds it to nothing unless the model
     * chose a writer for it, and then it is held like any chosen join -- to
     * that writer's own write, with the orders around it.
     */
    @Test
    public void aReadNoRowAnswersIsHeldOnlyToTheWriterTheModelChose()
            throws Exception {
        Path iteration = iteration();
        RowCodec.writeAll(SessionDir.of(iteration, "sel").reads(),
                Collections.singletonList(ReadRow.of("sel", 30L, reader, CELL,
                        9L, "INSTANCE_FIELD/1#40@v9@sel", "I", "4")),
                RowCodec::writeRead);
        for (boolean chosen : new boolean[]{false, true}) {
            Path claim = claim("FAULT:IPC", "true");
            if (chosen) {
                JsonObject document = JsonParser.parseString(new String(
                        Files.readAllBytes(claim), StandardCharsets.UTF_8))
                        .getAsJsonObject();
                JsonObject arm = new JsonObject();
                arm.addProperty("selector", "writer_arm__1__w");
                // As the composer spells it: the writer's OCCURRENCE; the
                // interaction it fills is what names the write.
                arm.addProperty("groupId", writer.occurrence().id());
                JsonArray fills = new JsonArray();
                fills.add(Interaction.of(InteractionKind.STATE, writer,
                        reader).id());
                arm.add("interactionIds", fills);
                document.getAsJsonArray("valuations").get(1)
                        .getAsJsonObject().getAsJsonArray("selectedArms")
                        .add(arm);
                Files.write(claim, document.toString()
                        .getBytes(StandardCharsets.UTF_8));
            }
            Path out = folder.newFolder("outside-" + chosen).toPath();
            ConfirmMain.write(iteration, claim, manifest(), out);
            JsonObject state = null;
            for (JsonObject edge : RowCodec.readJsonl(
                    out.resolve(Confirmation.FILE))) {
                if ("STATE".equals(edge.get("kind").getAsString())) {
                    state = edge;
                }
            }
            assertEquals("held only to a writer the model chose", chosen,
                    state != null);
            if (chosen) {
                assertEquals("at that writer's own write", 5L,
                        state.get("version").getAsLong());
            }
        }
    }

    /**
     * A query through a re-pointable reference, by variant of what the
     * model chose: another writer's store for the reference and a state of
     * the map that store delivered is held as two joins -- the reference
     * read to the store, the query's read to the write of that state, each
     * with every other writer of its location outside the two -- and the
     * session, which read neither, is no realization of it; the observed
     * store with nothing else is the session itself, its arm being the write
     * the read observed though its endpoint stored again later; a state
     * asked outside every read, or one no write states, is refused by name.
     */
    @Test
    public void aQueryThroughAReplacedReferenceIsHeldToTheStateTheModelChose()
            throws Exception {
        String third = "hdfs/nn0#epoch0/region/REGION.9a0f1e2d/ctx:Root:"
                + "TICK#2/idx:<a.Cleaner: void clean()>@0";
        LocationId reference = LocationId.of(LocationKind.INSTANCE, "8",
                "16");
        LocationId ran = LocationId.of(LocationKind.MAP, "30", "-3");
        LocationId other = LocationId.of(LocationKind.MAP, "20", "-3");
        Endpoint cell = endpoint(ANCHOR, "a.Handler#h()#20:READ");
        Endpoint query = endpoint(ANCHOR, "a.Handler#h()#21:READ");
        Endpoint observed = endpoint(MINT, "a.Manager#store()#1:WRITE");
        Endpoint store = endpoint(PRODUCER, "a.Convert#store()#1:WRITE");
        Endpoint built = endpoint(PRODUCER, "a.Convert#put()#2:WRITE");
        Endpoint later = endpoint(third, "a.Cleaner#remove()#3:WRITE");
        Object[][] variants = {
                // variant, the store chosen, the state's reader, version
                {"chosen", store, query.id(), 1L},
                {"observed", observed, null, 0L},
                {"outside", store, "", 1L},
                {"unwritten", store, query.id(), 9L}};
        Path iteration = iteration();
        SessionDir sel = SessionDir.of(iteration, "sel");
        RowCodec.writeAll(sel.roots(), Collections.singletonList(
                root("sel", "FAULT:IPC", "M_Z_fault.sel",
                        RootKind.MARKER, "true")),
                RowCodec::writeRootMint);
        RowCodec.writeAll(sel.writes(), Arrays.asList(
                WriteRow.of("sel", 7L, built, other, 1L, "EXPR.b", "L"),
                WriteRow.of("sel", 8L, store, reference, 5L, "EXPR.s",
                        "L", WriteRow.Referent.of(other, 1L), null),
                WriteRow.of("sel", 11L, observed, ran, 4L, "EXPR.r",
                        "L"),
                WriteRow.of("sel", 12L, observed, reference, 6L,
                        "EXPR.o", "L", WriteRow.Referent.of(ran, 4L),
                        null),
                WriteRow.of("sel", 35L, later, other, 2L, "EXPR.l",
                        "L"),
                // The observed store's endpoint stores again after the
                // read: its arm is still the write the read observed.
                WriteRow.of("sel", 36L, observed, reference, 8L, "EXPR.o",
                        "L", WriteRow.Referent.of(ran, 4L), null)),
                RowCodec::writeWrite);
        RowCodec.writeAll(sel.reads(), Arrays.asList(
                ReadRow.of("sel", 30L, cell, reference, 6L, "kc", "L",
                        null),
                ReadRow.of("sel", 31L, query, ran, 4L, "q", "L", null)),
                RowCodec::writeRead);
        for (Object[] variant : variants) {
            Path claim = claim("FAULT:IPC", "true");
            JsonObject document = JsonParser.parseString(new String(
                    Files.readAllBytes(claim), StandardCharsets.UTF_8))
                    .getAsJsonObject();
            JsonObject arm = new JsonObject();
            arm.addProperty("selector", "writer_arm__1__w");
            JsonArray fills = new JsonArray();
            fills.add(Interaction.of(InteractionKind.STATE,
                    (Endpoint) variant[1], cell).id());
            arm.add("interactionIds", fills);
            arm.addProperty("sessionId", "sel");
            JsonArray states = new JsonArray();
            if (variant[2] != null) {
                JsonObject state = new JsonObject();
                state.addProperty("selector", "nest__x");
                state.addProperty("reader", (String) variant[2]);
                state.addProperty("writer", built.id());
                state.addProperty("location", "MAP/20#-3");
                state.addProperty("version", (Long) variant[3]);
                states.add(state);
            }
            arm.add("referentStates", states);
            document.getAsJsonArray("valuations").get(1).getAsJsonObject()
                    .getAsJsonArray("selectedArms").add(arm);
            Files.write(claim, document.toString()
                    .getBytes(StandardCharsets.UTF_8));
            Path out = folder.newFolder("state-" + variant[0]).toPath();
            String refused = "";
            try {
                ConfirmMain.write(iteration, claim, manifest(), out);
            } catch (ConfirmMain.Refused refusal) {
                refused = refusal.getMessage();
            }
            String name = (String) variant[0];
            assertEquals(name + ": " + refused, "outside".equals(name),
                    refused.contains("asked outside every read"));
            assertEquals(name + ": " + refused, "unwritten".equals(name),
                    refused.contains("states no write"));
            assertEquals(name, "observed".equals(name),
                    Files.exists(out.resolve(ConfirmMain.REALIZED)));
            if (!"chosen".equals(name)) continue;
            List<String> held = new ArrayList<String>();
            List<String> orders = new ArrayList<String>();
            for (JsonObject edge : RowCodec.readJsonl(
                    out.resolve(Confirmation.FILE))) {
                String kind = edge.get("kind").getAsString();
                if ("STATE".equals(kind)) {
                    held.add(edge.get("reader").getAsString() + " <- "
                            + edge.get("writer").getAsString() + " "
                            + edge.get("location").getAsString() + "@"
                            + edge.get("version").getAsLong());
                } else if ("ORDER".equals(kind)) {
                    orders.add(edge.get("before").getAsString() + " < "
                            + edge.get("after").getAsString());
                }
            }
            assertEquals("the reference to the store, the query to the"
                    + " state of the map it delivered", Arrays.asList(
                    cell.id() + " <- " + store.id() + " INSTANCE/8#16@5",
                    query.id() + " <- " + built.id() + " MAP/20#-3@1"),
                    held);
            assertEquals("each writer before its reader, the run's store"
                    + " and the later mutation after it", Arrays.asList(
                    store.activation() + " < " + cell.activation(),
                    cell.activation() + " < " + observed.activation(),
                    query.activation() + " < " + later.activation()),
                    orders);
        }
    }

    /**
     * A selected session that already took every edge the model chose, ran
     * the moved root at the model's value and observed the fatal IS the run
     * that confirms the claim: nothing is handed to a replay.
     */
    @Test
    public void aSessionThatRealizedTheClaimIsItsConfirmation()
            throws Exception {
        Path iteration = iteration();
        SessionDir sel = SessionDir.of(iteration, "sel");
        RowCodec.writeAll(sel.roots(), Arrays.asList(
                root("sel", "HDFS.SERIAL", "M_I_serial.sel",
                        RootKind.INTEGRAL, "119978"),
                root("sel", "FAULT:IPC", "M_Z_fault.sel", RootKind.MARKER,
                        "true")), RowCodec::writeRootMint);
        Path out = folder.newFolder("realized").toPath();

        JsonObject summary = ConfirmMain.write(iteration,
                claim("FAULT:IPC", "true"), manifest(), out);

        assertEquals("sel", summary.get("realizedBy").getAsString());
        List<JsonObject> rows = RowCodec.readJsonl(
                out.resolve(ConfirmMain.REALIZED));
        assertEquals(1, rows.size());
        assertTrue(rows.get(0).get("confirmed").getAsBoolean());
        assertEquals("sel", rows.get(0).get("sessionId").getAsString());
        assertTrue("and no replay is handed anything",
                !Files.exists(out.resolve("focused_task.jsonl")));

        Path other = folder.newFolder("not-realized").toPath();
        ConfirmMain.write(iteration, claim("FAULT:IPC", "false"),
                manifest(), other);
        assertTrue("a moved root the session ran at another value is a run "
                        + "a replay has to make",
                !Files.exists(other.resolve(ConfirmMain.REALIZED))
                        && Files.exists(other.resolve("focused_task.jsonl")));
    }

    /**
     * WIRE-CODEC §6.5: a codec hole's WIRE edge states the store version its
     * message was, so a reader of another version is a mismatch, and the
     * text the model's valuation of it decodes to, where COMPOSE stated one
     * ({@code holeTexts}: a value resting on no clock).  An exchange's
     * correlation id is its own run's, so its hole is held to its producer
     * alone.
     */
    @Test
    public void aHoleEdgeStatesItsStoreVersionAndTheModelsText()
            throws Exception {
        Path iteration = iteration();
        Endpoint exchange = endpoint(ANCHOR, "pb:BlockKeyProto.keyId");
        String state = "SOLR_ZK /collections/c/state.json@5";
        RowCodec.writeAll(SessionDir.of(iteration, "sel").attaches(),
                Arrays.asList(AttachRow.of("sel", 20L, consumer,
                        "M_J_field_HOFF.1", "J", "2000", false, null, producer,
                        state, AttachRow.ENVELOPE, Hole.of("SOLR_JSON",
                                Arrays.asList("c", "expireAt"), 0)),
                        AttachRow.of("sel", 21L, exchange, "M_I_field_HOFF.2",
                                "I", "7", false, null, producer,
                                "hadoop-ipc-0a0b-25", AttachRow.ENVELOPE,
                                Hole.of("PROTOBUF", Arrays.asList("keys",
                                        "currentKey", "keyId"), 0))),
                RowCodec::writeAttach);
        Path claim = claim("M_J_clock.sel");
        JsonObject written = new JsonParser().parse(new String(
                Files.readAllBytes(claim), StandardCharsets.UTF_8))
                .getAsJsonObject();
        JsonObject arm = written.getAsJsonArray("valuations").get(1)
                .getAsJsonObject().getAsJsonArray("selectedArms").get(0)
                .getAsJsonObject();
        arm.getAsJsonArray("attachEndpointIds").add(exchange.id());
        JsonObject texts = new JsonObject();
        texts.addProperty(consumer.id(), "2000");
        arm.add("holeTexts", texts);
        Files.write(claim, written.toString().getBytes(
                StandardCharsets.UTF_8));
        Path out = folder.newFolder("hole-worker").toPath();

        ConfirmMain.write(iteration, claim, manifest(), out);

        Map<String, JsonObject> wire = new LinkedHashMap<String, JsonObject>();
        for (JsonObject edge : RowCodec.readJsonl(
                out.resolve(Confirmation.FILE))) {
            if ("WIRE".equals(edge.get("kind").getAsString())) {
                wire.put(edge.get("consumer").getAsString(), edge);
            }
        }
        assertEquals(2, wire.size());
        JsonObject stored = wire.get(consumer.id());
        assertEquals(state, stored.get("messageKey").getAsString());
        assertEquals("2000", stored.get("value").getAsString());
        JsonObject exchanged = wire.get(exchange.id());
        assertEquals(producer.id(), exchanged.get("producer").getAsString());
        assertTrue(exchanged.toString(), !exchanged.has("messageKey")
                && !exchanged.has("value"));
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
        assertEquals("the replay ends once the anchor observes the fatal",
                ANCHOR, row.get("declaredTarget").getAsString());
        assertEquals("seed", row.get("seedSessionId").getAsString());
        JsonObject roots = row.getAsJsonObject("rootAssignments");
        assertEquals("the world the selected session ran", "119980",
                roots.get("HDFS.SERIAL").getAsString());
        assertEquals("its marker, planted rather than forced", "true",
                roots.get("FAULT:IPC").getAsString());
        assertTrue("a root that session did not plant is not planted",
                !roots.has("OTHER"));
        assertTrue("a clock is a skew, never a value",
                !roots.has("CLOCK.a"));
        assertEquals("the skew that session ran with", "43000", row.getAsJsonObject("clockDeltas").get("CLOCK.a")
                        .getAsString());
        JsonObject mints = row.getAsJsonObject("rootMints");
        assertEquals(3, mints.size());
        assertEquals("where that session minted it", MINT,
                mints.get("CLOCK.a").getAsString());
        assertEquals("no recorded order is held: the model's is", 0,
                row.getAsJsonObject("schedulePrefix").get("events").getAsInt());
        assertEquals(0, SessionReader.readSchedule(
                out.resolve(SchedulePrefix.FILE)).size());
        assertEquals("the WAKEs still wait for what they followed", 4,
                SessionReader.readSchedule(
                        out.resolve(SchedulePrefix.REST_FILE)).size());

        Map<String, JsonObject> edges = new LinkedHashMap<String, JsonObject>();
        List<JsonObject> rows = RowCodec.readJsonl(
                out.resolve(Confirmation.FILE));
        for (JsonObject edge : rows) {
            edges.put(edge.get("kind").getAsString(), edge);
        }
        assertEquals("one edge each, none from the free arm of the path the"
                + " model did not select", 5, rows.size());
        assertEquals(5, edges.size());
        assertEquals("the export the arm's own session paired the consumer"
                + " with", producer.id(),
                edges.get("WIRE").get("producer").getAsString());
        assertEquals(consumer.id(),
                edges.get("WIRE").get("consumer").getAsString());
        assertEquals("a pinned join is the model's too, once no recorded"
                + " order holds it", writer.id(),
                edges.get("STATE").get("writer").getAsString());
        assertEquals("the read before the target, not the one after it: a "
                + "run that takes the fatal arm throws first", reader.id(),
                edges.get("STATE").get("reader").getAsString());
        assertEquals("the writer's activation exits before the reader's"
                + " enters", writer.activation(),
                edges.get("ORDER").get("before").getAsString());
        assertEquals(reader.activation(),
                edges.get("ORDER").get("after").getAsString());
        assertEquals("FAULT:IPC", edges.get("MARKER").get("root").getAsString());
        assertTrue(edges.get("MARKER").get("value").getAsBoolean());
        assertEquals(anchor.id(),
                edges.get("ANCHOR").get("occurrence").getAsString());
        assertEquals(40L, edges.get("ANCHOR").get("seq").getAsLong());
        // A join at a location the fatal does not rest on is no edge: under
        // the moved root the run may read it elsewhere or not at all.
        Path unheld = folder.newFolder("unheld").toPath();
        ConfirmMain.write(iteration, claim("M_J_clock.sel"),
                manifest("MAP/20#-3"), unheld);
        for (JsonObject edge : RowCodec.readJsonl(
                unheld.resolve(Confirmation.FILE))) {
            assertTrue(edge.toString(), !"STATE".equals(edge.get("kind")
                    .getAsString()) && !"ORDER".equals(edge.get("kind")
                    .getAsString()));
        }

        // A model that moved the clock elsewhere (DECIDE leaves clocks free)
        // is the world handed over, as the skew off that session's reading.
        Path moved = folder.newFolder("moved").toPath();
        ConfirmMain.write(iteration, claim("M_J_clock.sel", "50000"),
                manifest(), moved);
        assertEquals("the model's instant, 50000, less the 2000 read",
                "48000", RowCodec.readJsonl(moved.resolve(
                        "focused_task.jsonl")).get(0).getAsJsonObject(
                        "clockDeltas").get("CLOCK.a").getAsString());
        // A cell the recording read too is anchored at the recording's
        // reading: the model's instants are on its timeline, and the
        // selected replay's host read 1000 later.
        Path anchored = folder.newFolder("anchored").toPath();
        ConfirmMain.write(iteration, claim("M_J_clock.b", "50000"),
                manifest(), anchored);
        assertEquals("the model's instant less the recording's 1000",
                "49000", RowCodec.readJsonl(anchored.resolve(
                        "focused_task.jsonl")).get(0).getAsJsonObject(
                        "clockDeltas").get("CLOCK.b").getAsString());
    }
}
