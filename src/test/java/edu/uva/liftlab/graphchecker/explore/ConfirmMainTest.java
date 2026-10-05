package edu.uva.liftlab.graphchecker.explore;

import java.util.ArrayList;
import edu.uva.liftlab.graphchecker.compose.ComposeMain;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
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
        return RootMintRow.of(session, 1L, mint, id, symbol, kind,
                kind == RootKind.CLOCK ? RootCategory.CLOCK
                        : kind == RootKind.MARKER ? RootCategory.FAULT
                        : RootCategory.HOOK, value,
                null, null, true, kind == RootKind.CLOCK
                ? Clock.of(1_000_000L, Clock.WALL) : null, 0L);
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
        // A skew on a cell the composition does not anchor: outside the
        // model, so the world keeps it.
        JsonObject deltas = new JsonObject();
        deltas.addProperty("CLOCK.gone", "7000");
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

    /** The selected session's world, planting nothing: the recording's. */
    private static void plantNothing(Path iteration) throws Exception {
        Path focus = iteration.resolve("obligations-0000").resolve("w1")
                .resolve(ObligationDir.FOCUSED_TASK);
        JsonObject world = RowCodec.readJsonl(focus).get(0);
        for (String member : new String[]{"rootAssignments", "clockDeltas",
                "answers", "pairings"}) {
            world.add(member, new JsonObject());
        }
        RowCodec.writeJsonl(focus, Collections.singletonList(world));
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

    /** The composition manifest, anchoring one more clock cell. */
    private Path manifestAnchoring(String rootId, String reading)
            throws Exception {
        Path file = manifest();
        JsonObject manifest = ExploreCodec.readObject(file);
        JsonObject root = new JsonObject();
        root.addProperty("rootId", rootId);
        root.addProperty("kind", "CLOCK");
        root.addProperty("recordedValue", reading);
        manifest.getAsJsonArray("roots").add(root);
        Files.write(file, manifest.toString().getBytes(StandardCharsets.UTF_8));
        return file;
    }

    /** The composition manifest, its selected path resting on these and
     *  decided at its target row (seq 40). */
    private Path manifest(String... restsOn) throws Exception {
        return manifestCut(40L, restsOn);
    }

    /** The same, its selected path decided at {@code cutoff}. */
    private Path manifestCut(long cutoff, String... restsOn)
            throws Exception {
        Path file = Files.createTempFile(folder.getRoot().toPath(),
                "manifest", ".json");
        Files.write(file, ("{\"kind\":\"COMPOSITION_MANIFEST\",\"paths\":["
                + "{\"pathId\":\"p1\",\"sessionId\":\"sel\","
                + "\"selector\":\"path_selector__1__abc\","
                + "\"fatalObserved\":true,\"cutoff\":" + cutoff
                + ",\"restsOn\":"
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
     * A model that chose a location's INITIAL for a read holds the read to
     * the INITIAL's version, which no occurrence wrote: every write of the
     * location goes after the read.  An obligation whose world pairs the
     * read so is held by the same rows ({@link ConfirmMain#holding}), and
     * the writer the recording ran first is where its prefix ends.  The
     * INITIAL's row, which stands at the access that started the log with
     * that access's frames, places no hold (hdfs-bugs-slowdisk-zero SD4).
     * CONFIRM holds the write after the read's activation; an obligation,
     * whose choice binds every read the occurrence makes of the location,
     * after the occurrence (SD5: the turn re-read the bound for its limit);
     * and CONFIRM of a session whose world planted the pairing, by the rows
     * its replay was held to.
     */
    @Test
    public void aModelThatChoseTheInitialHoldsEveryWriteAfterTheRead()
            throws Exception {
        Path iteration = iteration();
        Endpoint observedAt = Endpoint.of(mint, "a.Manager#tick()#7:INITIAL",
                ExecutionIndex.of(Collections.singletonList(Frame.of(
                        "a.Manager#tick()#7:WRITE", 0))), 0);
        RowCodec.writeAll(SessionDir.of(iteration, "sel").writes(),
                Arrays.asList(WriteRow.initial("sel", 9L, observedAt, CELL,
                        4L, "EXPR.w", "I"), WriteRow.of("sel", 10L, writer,
                        CELL, 5L, "EXPR.w", "I")), RowCodec::writeWrite);
        // The read in a call of its own, as an accessor's is.
        Endpoint polled = Endpoint.of(anchor, "a.Handler#h()#12:READ",
                ExecutionIndex.of(Arrays.asList(Frame.of(
                        "<a.Handler: int bound()>", 0), Frame.of(
                        "a.Handler#h()#12:READ", 0))), 0);
        RowCodec.writeAll(SessionDir.of(iteration, "sel").reads(),
                Collections.singletonList(ReadRow.of("sel", 30L, polled,
                        CELL, 5L, "INSTANCE_FIELD/1#40@v5", "I", "3")),
                RowCodec::writeRead);
        Path claim = claim("FAULT:IPC", "true");
        JsonObject document = JsonParser.parseString(new String(
                Files.readAllBytes(claim), StandardCharsets.UTF_8))
                .getAsJsonObject();
        JsonObject arm = new JsonObject();
        arm.addProperty("selector", "writer_arm__1__i");
        arm.addProperty("groupId", "INITIAL|" + SmtLowering.locationKey(CELL));
        JsonArray fills = new JsonArray();
        fills.add(Interaction.of(InteractionKind.STATE, observedAt, polled)
                .id());
        arm.add("interactionIds", fills);
        document.getAsJsonArray("valuations").get(1).getAsJsonObject()
                .getAsJsonArray("selectedArms").add(arm);
        Files.write(claim, document.toString()
                .getBytes(StandardCharsets.UTF_8));
        Path out = folder.newFolder("initial-chosen").toPath();
        ConfirmMain.write(iteration, claim, manifest(), out);
        // The selected session's world planted the pairing, so its read
        // observed the INITIAL; the model chose no arm for it.
        RowCodec.writeAll(SessionDir.of(iteration, "sel").reads(),
                Collections.singletonList(ReadRow.of("sel", 30L, polled,
                        CELL, 4L, "INSTANCE_FIELD/1#40@v4", "I", "3")),
                RowCodec::writeRead);
        Path focus = iteration.resolve("obligations-0000").resolve("w1")
                .resolve(ObligationDir.FOCUSED_TASK);
        JsonObject world = RowCodec.readJsonl(focus).get(0);
        JsonObject pairings = new JsonObject();
        pairings.addProperty(Confirmation.id(polled), Confirmation.INITIAL);
        world.add("pairings", pairings);
        RowCodec.writeJsonl(focus, Collections.singletonList(world));
        Path planted = folder.newFolder("initial-planted").toPath();
        ConfirmMain.write(iteration, claim("FAULT:IPC", "true"), manifest(),
                planted);
        ConfirmMain.Holding paired = ConfirmMain.holding(
                SessionReader.read(iteration, "sel"),
                Collections.singletonMap(Confirmation.id(polled),
                        Confirmation.INITIAL));
        Map<List<JsonObject>, String> after =
                new LinkedHashMap<List<JsonObject>, String>();
        after.put(RowCodec.readJsonl(out.resolve(Confirmation.FILE)),
                polled.activation());
        after.put(paired.edges, Confirmation.activation(anchor,
                ExecutionIndex.empty()));
        after.put(RowCodec.readJsonl(planted.resolve(Confirmation.FILE)),
                Confirmation.activation(anchor, ExecutionIndex.empty()));
        for (Map.Entry<List<JsonObject>, String> each : after.entrySet()) {
            List<JsonObject> edges = each.getKey();
            List<String> held = new ArrayList<String>();
            for (JsonObject edge : edges) {
                String kind = edge.get("kind").getAsString();
                if ("ORDER".equals(kind)) {
                    held.add(edge.get("before").getAsString() + " < "
                            + edge.get("after").getAsString());
                } else if ("STATE".equals(kind) && edge.get("reader")
                        .getAsString().equals(Confirmation.id(polled))) {
                    held.add(edge.get("writer").getAsString() + "@"
                            + edge.get("version").getAsString());
                }
            }
            assertEquals("the INITIAL's version, the write after the read",
                    Arrays.asList(Confirmation.INITIAL + "@4",
                            each.getValue() + " < " + writer.activation()),
                    held);
        }
        assertEquals("the write the session ran before the read",
                Collections.singleton(mint.id()), paired.reordered);
        // The model chose the INITIAL and the world held the read to the
        // write: one read, two writers, refused by name.
        pairings.addProperty(Confirmation.id(polled), Confirmation.id(writer));
        RowCodec.writeJsonl(focus, Collections.singletonList(world));
        String refused = "";
        try {
            ConfirmMain.write(iteration, claim, manifest(),
                    folder.newFolder("initial-conflict").toPath());
        } catch (ConfirmMain.Refused conflict) {
            refused = conflict.getMessage();
        }
        assertTrue(refused, refused.startsWith("STATE_CONFLICT: read "
                + Confirmation.id(polled)));
    }

    /**
     * An event in its occurrence's outermost activation -- a loop body's
     * store, standing on the loop's method, which spans every turn -- is
     * ordered by its occurrence: a read paired with it waits for the turn
     * to close, and a store held after a read waits at the turn's opening
     * (hdfs-bugs-slowdisk-zero SD8: the anchor waited for the detector's
     * run() to exit, past the order's timeout).  A deeper call is its own
     * activation.  An occurrence closes at its last recorded event, so a
     * store the session ran after the read but before the reader's
     * occurrence closed is reordered, as its ORDER puts it after the close.
     */
    @Test
    public void aLoopTurnsOutermostEventIsOrderedByItsTurn()
            throws Exception {
        Path iteration = iteration();
        Frame loop = Frame.of("<a.Manager: void run()>", 0);
        Endpoint store = Endpoint.of(mint, "a.Manager#run()#9:WRITE",
                ExecutionIndex.of(Arrays.asList(loop, Frame.of(
                        "a.Manager#run()#9:WRITE", 0))), 0);
        Endpoint scan = Endpoint.of(mint, "a.Manager#scan()#4:READ",
                ExecutionIndex.of(Arrays.asList(loop, Frame.of(
                        "<a.Manager: void scan()>", 0), Frame.of(
                        "a.Manager#scan()#4:READ", 0))), 0);
        Endpoint first = endpoint(MINT, "a.Manager#run()#9:INITIAL");
        String turn = Confirmation.activation(mint, ExecutionIndex.empty());
        String read = Confirmation.activation(anchor, ExecutionIndex.empty());
        SessionDir sel = SessionDir.of(iteration, "sel");
        RowCodec.writeAll(sel.writes(), Arrays.asList(
                WriteRow.initial("sel", 9L, first, CELL, 4L, "EXPR.w", "I"),
                WriteRow.of("sel", 20L, store, CELL, 5L, "EXPR.w", "I")),
                RowCodec::writeWrite);
        LocationId elsewhere = LocationId.of(LocationKind.INSTANCE, "1",
                "41");
        // the version the read saw, its pairing, the ORDER it needs, the
        // read's seq, the reordered occurrences
        Object[][] table = {
                {5L, Confirmation.id(store), turn + " < " + read, 30L,
                        Collections.emptySet()},
                {4L, Confirmation.INITIAL, read + " < " + turn, 30L,
                        Collections.singleton(mint.id())},
                {4L, Confirmation.INITIAL, read + " < " + turn, 15L,
                        Collections.singleton(mint.id())},
        };
        for (Object[] row : table) {
            RowCodec.writeAll(sel.reads(), Arrays.asList(
                    ReadRow.of("sel", 25L, scan, elsewhere, 2L,
                            "INSTANCE_FIELD/1#41@v2", "I", "0"),
                    ReadRow.of("sel", (Long) row[3], reader, CELL,
                            (Long) row[0], "INSTANCE_FIELD/1#40@v" + row[0],
                            "I", "3"),
                    ReadRow.of("sel", 31L, endpoint(ANCHOR,
                            "a.Handler#h()#13:READ"), elsewhere, 2L,
                            "INSTANCE_FIELD/1#41@v2", "I", "0")),
                    RowCodec::writeRead);
            List<String> orders = new ArrayList<String>();
            ConfirmMain.Holding holding = ConfirmMain.holding(
                    SessionReader.read(iteration, "sel"),
                    Collections.singletonMap(Confirmation.id(reader),
                            (String) row[1]));
            for (JsonObject edge : holding.edges) {
                if ("ORDER".equals(edge.get("kind").getAsString())) {
                    orders.add(edge.get("before").getAsString() + " < "
                            + edge.get("after").getAsString());
                }
            }
            assertEquals(row[1] + "@" + row[3],
                    Collections.singletonList(row[2]), orders);
            assertEquals(row[1] + "@" + row[3], row[4], holding.reordered);
        }
    }

    /**
     * A query through a re-pointable reference, by variant of what the
     * model chose: another writer's store for the reference and a state of
     * the map that store delivered is held as two joins -- the reference
     * read to the store, the query's read to the write of that state, each
     * with every other writer of its location outside the two -- and the
     * session, which read neither, is no realization of it; the observed
     * store with nothing else is the session itself (its world planting
     * nothing), its arm being the write the read observed though its
     * endpoint stored again later; a state asked outside every read, or one
     * no write states, is refused by name.
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
        plantNothing(iteration);
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
     * A selected session that took every edge the model chose, ran the
     * moved root at the model's value, ran the model's clocks and observed
     * the fatal IS the run that confirms the claim -- unless its world
     * planted a pairing: a choice its run took under an order its replay
     * held, which CONFIRM makes again in a replay of its own, strict.  A
     * planted root or answer is the session's own run; a skew planted on a
     * clock cell the composition anchors is no clock of the model's, and
     * its replay drops it and keeps one outside the composition.
     */
    @Test
    public void aSessionIsItsConfirmationUnlessItsWorldPlantedAPairing()
            throws Exception {
        Path iteration = iteration();
        SessionDir sel = SessionDir.of(iteration, "sel");
        RowCodec.writeAll(sel.roots(), Arrays.asList(
                root("sel", "HDFS.SERIAL", "M_I_serial.sel",
                        RootKind.INTEGRAL, "119978"),
                root("sel", "FAULT:IPC", "M_Z_fault.sel", RootKind.MARKER,
                        "true")), RowCodec::writeRootMint);
        Path focus = iteration.resolve("obligations-0000").resolve("w1")
                .resolve(ObligationDir.FOCUSED_TASK);
        plantNothing(iteration);
        JsonObject planted = RowCodec.readJsonl(focus).get(0);
        // what the world planted (member -> key -> value), realized?
        Object[][] table = {
                {null, null, null, true},
                {"rootAssignments", "FAULT:IPC", "true", true},
                {"clockDeltas", "CLOCK.gone", "7000", false},
                {"answers", consumer.id(), "119979", true},
                {"pairings", Confirmation.id(reader), Confirmation.id(writer),
                        false},
        };
        for (Object[] row : table) {
            JsonObject world = planted.deepCopy();
            if (row[0] != null) {
                world.getAsJsonObject((String) row[0]).addProperty(
                        (String) row[1], (String) row[2]);
            }
            if ("clockDeltas".equals(row[0])) {
                world.getAsJsonObject("clockDeltas").addProperty("CLOCK.a",
                        "43000");
            }
            RowCodec.writeJsonl(focus, Collections.singletonList(world));
            Path out = folder.newFolder("world-" + row[0]).toPath();
            JsonObject summary = ConfirmMain.write(iteration,
                    claim("FAULT:IPC", "true"), manifest(), out);
            boolean realized = (Boolean) row[3];
            assertEquals(row[0] + ": " + summary, realized,
                    summary.has("realizedBy"));
            assertEquals(row[0] + ": a realized claim hands no replay "
                    + "anything", !realized, Files.exists(out.resolve(
                    ObligationDir.FOCUSED_TASK)));
            if (realized) {
                List<JsonObject> rows = RowCodec.readJsonl(
                        out.resolve(ConfirmMain.REALIZED));
                assertTrue(rows.get(0).get("confirmed").getAsBoolean());
                assertEquals("sel", rows.get(0).get("sessionId")
                        .getAsString());
            }
            if ("clockDeltas".equals(row[0])) {
                JsonObject deltas = RowCodec.readJsonl(out.resolve(
                        ObligationDir.FOCUSED_TASK)).get(0)
                        .getAsJsonObject("clockDeltas");
                assertTrue("the session's own skew is not the model's: "
                        + deltas, !deltas.has("CLOCK.a"));
                assertEquals("one outside the composition is kept", "7000",
                        deltas.get("CLOCK.gone").getAsString());
            }
            if ("pairings".equals(row[0])) {
                int held = 0;
                for (JsonObject edge : RowCodec.readJsonl(
                        out.resolve(Confirmation.FILE))) {
                    if ("STATE".equals(edge.get("kind").getAsString())
                            && edge.get("reader").getAsString().equals(
                            Confirmation.id(reader))) {
                        held++;
                    }
                }
                assertTrue("the world's pairing is held", held > 0);
            }
        }
        // And with a world that planted nothing, a moved root the session
        // ran at another value is a run a replay has to make.
        Path other = folder.newFolder("not-realized").toPath();
        ConfirmMain.write(iteration, claim("FAULT:IPC", "false"),
                manifest(), other);
        assertTrue(!Files.exists(other.resolve(ConfirmMain.REALIZED))
                && Files.exists(other.resolve(ObligationDir.FOCUSED_TASK)));
    }

    /**
     * The run as recorded is no counterfactual (owner 2026-10-04): a claim
     * on the seed's own path that moves no root and takes only the seed's
     * own deliveries is refuted by name before anything is planted or
     * replayed -- hdfs-adhoc-32 (HG4) was confirmed by its seed replay,
     * which had diverged from its recording into the fatal.  Rows that
     * state no runnable model (here, a manifest stating no cutoff) are
     * refused: a defect of the run, which refutes nothing.
     */
    @Test
    public void theRunAsRecordedIsRefutedAndADefectRefusedByName()
            throws Exception {
        Path iteration = iteration();
        Path claim = claim("FAULT:IPC", "true");
        JsonObject recorded = ExploreCodec.readObject(claim);
        recorded.addProperty("seedSessionId", "sel");
        recorded.getAsJsonObject("claim").add("movedRoots", new JsonObject());
        Files.write(claim, recorded.toString().getBytes(
                StandardCharsets.UTF_8));
        JsonObject uncut = ExploreCodec.readObject(manifest());
        uncut.getAsJsonArray("paths").get(0).getAsJsonObject()
                .remove("cutoff");
        Path uncutFile = Files.createTempFile(folder.getRoot().toPath(),
                "uncut", ".json");
        Files.write(uncutFile, uncut.toString().getBytes(
                StandardCharsets.UTF_8));
        // manifest, the refusal's start, whether it refutes
        Object[][] table = {
                {manifest(), "the claim moves nothing: its witness is the "
                        + "run as recorded", true},
                {uncutFile, "the manifest states no selector, no restsOn or "
                        + "no cutoff", false}};
        for (Object[] row : table) {
            Path out = folder.newFolder().toPath();
            try {
                ConfirmMain.write(iteration, claim, (Path) row[0], out);
                fail(row[1] + ": handed to a confirmation");
            } catch (ConfirmMain.Refused refused) {
                assertTrue(refused.getMessage(), refused.getMessage()
                        .startsWith((String) row[1]));
                assertEquals(refused.getMessage(), row[2], refused.refutes);
            }
            assertFalse(Files.exists(out.resolve(ConfirmMain.REALIZED)));
        }
    }

    /**
     * A witness whose path left the way to the throw at a symbolic guard
     * (its fatal arm that guard's other arm) never reached the anchor in
     * its own run, and its session may state no target row there at all:
     * it is planted and judged as any other, its closure cut at the guard
     * the manifest names -- a read after the guard is no edge.
     */
    @Test
    public void aWayGuardWitnessIsPlantedWithItsClosureCutAtTheGuard()
            throws Exception {
        for (boolean anyTarget : new boolean[]{true, false}) {
            Path iteration = folder.newFolder("way-" + anyTarget).toPath()
                    .resolve("iteration-0000");
            Files.move(iteration(), iteration);
            RowCodec.writeAll(SessionDir.of(iteration, "sel").targets(),
                    anyTarget ? Collections.singletonList(TargetRow.of("sel",
                            40L, anchor, "<a.Handler: void handle()>#u8#1",
                            "false", false, false))
                            : Collections.<TargetRow>emptyList(),
                    RowCodec::writeTarget);
            Path out = folder.newFolder("way-out-" + anyTarget).toPath();
            JsonObject summary = ConfirmMain.write(iteration,
                    claim("M_J_clock.sel"), manifestCut(31L,
                            "INSTANCE/1#40"), out);
            assertFalse("a run that never observed the fatal is no "
                    + "realization: " + summary, summary.has("realizedBy"));
            List<String> readers = new ArrayList<String>();
            long cut = -1L;
            for (JsonObject edge : RowCodec.readJsonl(
                    out.resolve(Confirmation.FILE))) {
                String kind = edge.get("kind").getAsString();
                if ("STATE".equals(kind)) {
                    readers.add(edge.get("reader").getAsString());
                } else if ("ANCHOR".equals(kind)) {
                    cut = edge.get("seq").getAsLong();
                }
            }
            assertEquals("the read before the guard", Collections
                    .singletonList(Confirmation.id(reader)), readers);
            assertEquals(31L, cut);
        }
    }

    /**
     * A healthy confirmation run refutes the model only where it ran it:
     * every moved root minted at the model's value (a clock's cell minted)
     * and no plant refused; else it names why it did not run the model.
     */
    @Test
    public void aHealthyRunRefutesOnlyWhereItPlantedTheModel()
            throws Exception {
        JsonObject claim = ExploreCodec.readObject(claim("FAULT:IPC",
                "true"));
        JsonObject planted = RowCodec.writeRootMint(root("c", "FAULT:IPC",
                "M_Z_fault", RootKind.MARKER, "true"));
        JsonObject other = RowCodec.writeRootMint(root("c", "FAULT:IPC",
                "M_Z_fault", RootKind.MARKER, "false"));
        JsonObject refusedPlant = new JsonObject();
        refusedPlant.addProperty("kind", "ASSIGNMENT_UNPLANTED");
        refusedPlant.addProperty("subject", "PORT.x");
        // roots minted, gaps, the reason's start ("" = it ran the model)
        Object[][] table = {
                {Collections.singletonList(planted),
                        Collections.<JsonObject>emptyList(), ""},
                {Collections.singletonList(other),
                        Collections.<JsonObject>emptyList(),
                        "it ran the moved root FAULT:IPC at false"},
                {Collections.<JsonObject>emptyList(),
                        Collections.<JsonObject>emptyList(),
                        "it minted no row of the moved root FAULT:IPC"},
                {Collections.singletonList(planted),
                        Collections.singletonList(refusedPlant),
                        "it refused a plant (PORT.x)"}};
        for (Object[] row : table) {
            @SuppressWarnings("unchecked")
            String why = ConfirmMain.unplanted(claim,
                    (List<JsonObject>) row[1], (List<JsonObject>) row[0]);
            assertTrue(why, row[2].equals("") ? why.isEmpty()
                    : why.startsWith((String) row[2]));
        }
    }

    /**
     * A WIRE edge states the text the model's valuation of its leaf
     * delivers where COMPOSE stated one ({@code texts}: a value resting on
     * no clock); another consumer of the arm is held to its producer alone.
     */
    @Test
    public void aWireEdgeStatesTheModelsTextWhereComposeStatedOne()
            throws Exception {
        Path iteration = iteration();
        Endpoint other = endpoint(ANCHOR, "XCH.req.key-id");
        RowCodec.writeAll(SessionDir.of(iteration, "sel").attaches(),
                Arrays.asList(AttachRow.of("sel", 20L, consumer,
                        "M_J_field_HOFF.1", "J", "2000", false, null, producer,
                        "corr-1", AttachRow.HANDLE),
                        AttachRow.of("sel", 21L, other, "M_I_field_HOFF.2",
                                "I", "7", false, null, producer, "corr-2",
                                AttachRow.HANDLE)),
                RowCodec::writeAttach);
        Path claim = claim("M_J_clock.sel");
        JsonObject written = new JsonParser().parse(new String(
                Files.readAllBytes(claim), StandardCharsets.UTF_8))
                .getAsJsonObject();
        JsonObject arm = written.getAsJsonArray("valuations").get(1)
                .getAsJsonObject().getAsJsonArray("selectedArms").get(0)
                .getAsJsonObject();
        arm.getAsJsonArray("attachEndpointIds").add(other.id());
        JsonObject texts = new JsonObject();
        texts.addProperty(consumer.id(), "2000");
        arm.add(ComposeMain.TEXTS, texts);
        Files.write(claim, written.toString().getBytes(
                StandardCharsets.UTF_8));
        Path out = folder.newFolder("text-worker").toPath();

        ConfirmMain.write(iteration, claim, manifest(), out);

        Map<String, JsonObject> wire = new LinkedHashMap<String, JsonObject>();
        for (JsonObject edge : RowCodec.readJsonl(
                out.resolve(Confirmation.FILE))) {
            if ("WIRE".equals(edge.get("kind").getAsString())) {
                wire.put(edge.get("consumer").getAsString(), edge);
            }
        }
        assertEquals(2, wire.size());
        assertEquals("2000", wire.get(consumer.id()).get("value")
                .getAsString());
        JsonObject held = wire.get(other.id());
        assertEquals(producer.id(), held.get("producer").getAsString());
        assertTrue(held.toString(), !held.has("value"));
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
        assertEquals("the model's 45000 off the composition's reading 1000",
                "44000",
                row.getAsJsonObject("clockDeltas").get("CLOCK.a")
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
        // The reader's activation called another method before the read:
        // the order holds that call's entry, the last one before the read,
        // not the activation's own -- one that polls for what it caused to
        // be written (SOLR-18413 s13a: MigrateCmd#migrateKey) is entered
        // before the write and would wait out the order there.
        SessionDir sel = SessionDir.of(iteration, "sel");
        List<ReadRow> reads = new ArrayList<ReadRow>(
                SessionReader.read(iteration, "sel").reads());
        Frame poll = Frame.of("<a.Handler: java.util.Map rules()>", 3);
        reads.add(ReadRow.of("sel", 25L, Endpoint.of(anchor,
                "a.Handler#rules()#2:READ", ExecutionIndex.of(Arrays.asList(
                        poll, Frame.of("a.Handler#rules()#2:READ", 0))), 0),
                LocationId.of(LocationKind.INSTANCE, "9", "1"), 4L,
                "INSTANCE_FIELD/9#1@v4", "I", "0"));
        RowCodec.writeAll(sel.reads(), reads, RowCodec::writeRead);
        Path polled = folder.newFolder("polled").toPath();
        ConfirmMain.write(iteration, claim("M_J_clock.sel"), manifest(),
                polled);
        int held = 0;
        for (JsonObject edge : RowCodec.readJsonl(
                polled.resolve(Confirmation.FILE))) {
            if (!"ORDER".equals(edge.get("kind").getAsString())) continue;
            held++;
            assertEquals(Endpoint.activation(anchor, ExecutionIndex.of(
                    Collections.singletonList(poll))),
                    edge.get("after").getAsString());
        }
        assertEquals(1, held);

        // A delivery into the anchor is held to the producer the arm's
        // session paired; only where that session answered the anchor by
        // its question (IDENTITY §9, an ADDRESS_UNSTABLE row naming it) did
        // another chain of the question's shape carry it, and the edge
        // states its producer's question, which CONFIRM compares by site,
        // site index, attempt and shape.
        for (boolean answered : new boolean[]{false, true}) {
            if (answered) {
                List<GapRow> gaps = new ArrayList<GapRow>(RowCodec.readAll(
                        sel.gaps(), RowCodec::readGap));
                gaps.add(GapRow.of("sel", GapKind.ADDRESS_UNSTABLE,
                        GapClass.DIAGNOSTIC, anchor.render(),
                        "the declared occurrence ran at another address"));
                RowCodec.writeAll(sel.gaps(), gaps, RowCodec::writeGap);
            }
            Path asked = folder.newFolder("asked-" + answered).toPath();
            ConfirmMain.write(iteration, claim("M_J_clock.sel"), manifest(),
                    asked);
            for (JsonObject edge : RowCodec.readJsonl(
                    asked.resolve(Confirmation.FILE))) {
                if (!"WIRE".equals(edge.get("kind").getAsString())) continue;
                assertEquals("answered " + answered, answered,
                        edge.has(Confirmation.PRODUCER_QUESTION));
                if (!answered) continue;
                JsonObject question = edge.getAsJsonObject(
                        Confirmation.PRODUCER_QUESTION);
                assertEquals(producer.site(),
                        question.get("site").getAsString());
                assertEquals(producer.siteIndex().hash(),
                        question.get("siteIndex").getAsString());
                assertEquals(producer.attempt(),
                        question.get("attempt").getAsInt());
            }
        }

        // A join the run took to an INITIAL holds nothing: no occurrence
        // wrote it, only the access that first observed the location
        // (SOLR-18413 stream7b: the leader's first lookup of the cluster
        // state).  A write is a write.  Every STATE row names its reader at
        // any turn too.
        for (boolean initial : new boolean[]{true, false}) {
            RowCodec.writeAll(sel.writes(), Collections.singletonList(initial
                    ? WriteRow.initial("sel", 10L, writer, CELL, 5L, "EXPR.w",
                    "I")
                    : WriteRow.of("sel", 10L, writer, CELL, 5L, "EXPR.w",
                    "I")), RowCodec::writeWrite);
            Path snapshot = folder.newFolder("initial" + initial).toPath();
            ConfirmMain.write(iteration, claim("M_J_clock.sel"), manifest(),
                    snapshot);
            int stated = 0;
            for (JsonObject edge : RowCodec.readJsonl(
                    snapshot.resolve(Confirmation.FILE))) {
                if (!"STATE".equals(edge.get("kind").getAsString())) continue;
                stated++;
                assertEquals(Confirmation.anyTurn(reader),
                        edge.get("readerAnyTurn").getAsString());
            }
            assertEquals("initial " + initial, initial ? 0 : 1, stated);
        }

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

        // A model that moved a clock elsewhere (DECIDE leaves clocks free) is
        // the world handed over, as the skew off the reading the composition
        // anchored the cell to -- the model's instants are on that timeline,
        // and the selected replay's host read 1000 later -- whichever
        // session's symbol names the cell; a cell it anchors nowhere, or one
        // the recording mints nowhere, is refused by name.
        String[][] clocks = {
                {"M_J_clock.sel", "CLOCK.a", "49000"},
                {"M_J_clock.b", "CLOCK.b", "49000"},
                {"M_J_clock.b", "CLOCK.b", null},
                // A cell only another session read: the recording mints it
                // nowhere, so no replay can be focused to plant it.
                {"M_J_clock.elsewhere", "CLOCK.c", null},
        };
        for (int index = 0; index < clocks.length; index++) {
            String[] clock = clocks[index];
            Path moved = folder.newFolder("moved-" + index).toPath();
            Path composed = clock[2] == null ? manifest() : manifestAnchoring(
                    clock[1], "1000");
            try {
                ConfirmMain.write(iteration, claim(clock[0], "50000"),
                        composed, moved);
                assertEquals(clock[0], clock[2], RowCodec.readJsonl(
                        moved.resolve("focused_task.jsonl")).get(0)
                        .getAsJsonObject("clockDeltas").get(clock[1])
                        .getAsString());
            } catch (ConfirmMain.Refused refused) {
                assertEquals(clock[0] + ": " + refused.getMessage(), null,
                        clock[2]);
            }
        }
    }

    /**
     * A native run's plant is CONFIRM's world: a ROOT per root it assigns
     * (here a tree hook's, at the occurrence the recording mints it at), the
     * ORDER rows CONFIRM holds, TARGET rows at the anchor, each numbered.  A
     * world the recording weave cannot plant is refused by name: a clock
     * skew, a root of no plantable category, or nothing at all.
     */
    @Test
    public void aNativePlantIsConfirmsWorld() throws Exception {
        Path iteration = iteration();
        Path focus = iteration.resolve("obligations-0000").resolve("w1")
                .resolve(ObligationDir.FOCUSED_TASK);
        JsonObject world = RowCodec.readJsonl(focus).get(0);
        Files.write(iteration.resolve("execution_task_plan.jsonl"),
                new byte[0]);
        Path scopeMap = folder.newFile("static_scope_map.jsonl").toPath();
        JsonObject site = new JsonObject();
        site.addProperty("schemaVersion", 1);
        site.addProperty("kind", StaticScopeMap.SITE_KIND);
        site.addProperty("role", StaticScopeMap.TARGET_SITE);
        site.addProperty("regionId", anchor.regionId());
        site.addProperty("siteId", "<a.Handler: void handle()>#u8");
        JsonArray guards = new JsonArray();
        guards.add("<a.Handler: void handle()>#u5");
        site.add("guards", guards);
        JsonArray arms = new JsonArray();
        arms.add(false);
        site.add("guardOutcomes", arms);
        Files.write(scopeMap, Collections.singletonList(site.toString()),
                StandardCharsets.UTF_8);
        // The world, then the claim's moved root; null: refused.
        Object[][] worlds = {
                {"{}", "HDFS.SERIAL", "ROOT HOOK HDFS.SERIAL " + mint.id()
                        + " 119981"},
                {"{\"CLOCK.gone\":\"7000\"}", "HDFS.SERIAL", null},
                // A marker no plan input calls: no site to answer at.
                {"{}", "M_Z_fault", null},
        };
        for (Object[] row : worlds) {
            JsonObject planted = world.deepCopy();
            planted.add("rootAssignments", new JsonObject());
            planted.add("rootMints", new JsonObject());
            planted.add("clockDeltas", JsonParser.parseString(
                    (String) row[0]).getAsJsonObject());
            RowCodec.writeJsonl(focus, Collections.singletonList(planted));
            Path claim = claim((String) row[1], "119981");
            Path plant = folder.newFile().toPath();
            try {
                ConfirmMain.writePlant(iteration, claim, manifest(), scopeMap,
                        plant);
                if (row[2] == null) fail("planted " + Arrays.toString(row));
            } catch (ConfirmMain.Refused refused) {
                assertTrue(refused.getMessage(), refused.getMessage()
                        .startsWith("NATIVE_PLANT_UNSUPPORTED"));
                assertEquals(refused.getMessage(), null, row[2]);
                continue;
            }
            List<JsonObject> rows = RowCodec.readJsonl(plant);
            JsonObject root = rows.get(0);
            assertEquals(row[2], root.get("kind").getAsString() + " "
                    + root.get("category").getAsString() + " "
                    + root.get("rootId").getAsString() + " "
                    + root.get("occurrence").getAsString() + " "
                    + root.get("value").getAsString());
            // CONFIRM's own ORDER rows, as its replay is held to them.
            Path out = folder.newFolder().toPath();
            ConfirmMain.write(iteration, claim, manifest(), out);
            List<JsonObject> orders = new ArrayList<JsonObject>();
            for (JsonObject edge : RowCodec.readJsonl(
                    out.resolve(Confirmation.FILE))) {
                if ("ORDER".equals(edge.get("kind").getAsString())) {
                    orders.add(edge);
                }
            }
            assertFalse("the closure orders nothing", orders.isEmpty());
            List<JsonObject> held = new ArrayList<JsonObject>();
            for (JsonObject planted2 : rows) {
                if (!"ORDER".equals(planted2.get("kind").getAsString())) {
                    continue;
                }
                JsonObject order = planted2.deepCopy();
                order.remove("row");
                held.add(order);
            }
            assertEquals(orders, held);
            JsonObject target = rows.get(rows.size() - 1);
            assertEquals("TARGET " + anchor.id() + " false",
                    target.get("kind").getAsString() + " "
                            + target.get("occurrence").getAsString() + " "
                            + target.get("value").getAsBoolean());
            for (int index = 0; index < rows.size(); index++) {
                assertEquals(index, rows.get(index).get("row").getAsInt());
            }
        }
    }
}
