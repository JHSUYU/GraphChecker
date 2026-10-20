package edu.uva.liftlab.graphchecker.explore;

import java.util.ArrayList;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.compose.ComposeMain;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ClientProgramOrder;
import edu.uva.liftlab.graphchecker.contract.ExpressionLogs;
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
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.runtime.RecordingPlant;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.Rule;
import edu.uva.liftlab.graphchecker.runtime.MessageDoors;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

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

    private static List<JsonObject> edges(Path out) throws Exception {
        return RowCodec.readJsonl(out.resolve(Confirmation.FILE));
    }

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
                        + "#u8#1", "EXPR.phi", true, true, null)),
                RowCodec::writeTarget);
        RowCodec.writeAll(sel.writes(), Collections.singletonList(
                WriteRow.of("sel", 10L, writer, CELL, 5L, "EXPR.w", "I")),
                RowCodec::writeWrite);
        RowCodec.writeAll(sel.reads(), Arrays.asList(
                ReadRow.of("sel", 30L, reader, CELL, 5L, "INSTANCE_FIELD/1"
                        + "#40@v5", "I", "3"),
                ReadRow.of("sel", 31L, unknown, CELL, -1L, "INSTANCE_FIELD/1"
                        + "#40@v?", "I", "3"),
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
        ExpressionLogs.write(dir.expressions(),
                Collections.<String, JsonObject>emptyMap());
        RowCodec.writeManifest(dir.manifest(), SessionManifest.of(
                dir.sessionId(), role, role == SessionManifest.Role.SEED
                        ? Collections.<String>emptyList()
                        : Collections.singletonList("OBL.x")));
    }

    private static JsonObject event(long seq, String site,
                                    String occurrence) {
        return RowCodec.writeScheduleEvent(ScheduleEvent.of(seq,
                ScheduleEvent.Kind.SEND, "node|Root:X", site, 0, occurrence, ""));
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
                + "{\"selector\":\"message_arm__2__zzz\","
                + "\"family\":\"message_family__2__zzz\",\"groupId\":\"g\","
                + "\"attachEndpointIds\":[\"" + consumer.id() + "\"],"
                + "\"sessionId\":\"other\",\"producerPathId\":\"p2\","
                + "\"interactionIds\":[],\"expressionRefs\":[],"
                + "\"attested\":true}],"
                + "\"unsatCore\":[]}]}").getBytes(StandardCharsets.UTF_8));
        return file;
    }

    private static void chose(Path claim, Endpoint writer, Endpoint reader)
            throws Exception {
        JsonObject document = ExploreCodec.readObject(claim);
        JsonObject arm = new JsonObject();
        arm.addProperty("selector", "writer_arm__1__w");
        arm.addProperty("groupId", writer.occurrence().id());
        JsonArray fills = new JsonArray();
        fills.add(Interaction.of(InteractionKind.STATE, writer, reader).id());
        arm.add("interactionIds", fills);
        document.getAsJsonArray("valuations").get(1).getAsJsonObject()
                .getAsJsonArray("selectedArms").add(arm);
        Files.write(claim, document.toString()
                .getBytes(StandardCharsets.UTF_8));
    }

    private Path manifest() throws Exception {
        return manifest("INSTANCE/1#40", "INSTANCE/8#16", "MAP/20#-3",
                "MAP/30#-3");
    }

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

    private Path manifest(String... restsOn) throws Exception {
        return manifestCut(40L, restsOn);
    }

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

    @Test
    public void aStoreReadIsComparedByItsVersionAndOrderedByNothing()
            throws Exception {
        Path iteration = iteration();
        LocationId store = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/collections/t/state.json");
        RowCodec.writeAll(SessionDir.of(iteration, "sel").writes(),
                Arrays.asList(WriteRow.of("sel", 10L, writer, store, 3L, "",
                        "[B"), WriteRow.of("sel", 35L, producer, store, 4L,
                        "", "[B")), RowCodec::writeWrite);
        RowCodec.writeAll(SessionDir.of(iteration, "sel").reads(),
                Collections.singletonList(ReadRow.of("sel", 30L, reader,
                        store, 3L, "S_state3", "[B", null)),
                RowCodec::writeRead);
        Path out = folder.newFolder("store-read").toPath();
        ConfirmMain.write(iteration, claim("FAULT:IPC", "true"),
                manifest(SmtLowering.locationKey(store)), out);
        List<String> held = new ArrayList<String>();
        for (JsonObject edge : edges(out)) {
            String kind = edge.get("kind").getAsString();
            if ("STATE".equals(kind)) {
                held.add("STATE " + edge.get("reader").getAsString() + "@"
                        + edge.get("version").getAsString());
            } else if ("ORDER".equals(kind)) {
                held.add("ORDER");
            }
        }
        assertEquals(Collections.singletonList("STATE "
                + Confirmation.id(reader) + "@3"), held);
    }

    @Test
    public void aStoreReadPairedWithALaterTombstoneIsHeldUntilItAndNoEarlier()
            throws Exception {
        Path iteration = iteration();
        LocationId store = LocationId.of(LocationKind.STORE, "HBASE_ZK",
                "/hbase/flush-table-proc/acquired/t");
        long tombstone = MessageDoors.TOMBSTONE;
        RowCodec.writeAll(SessionDir.of(iteration, "sel").writes(),
                Arrays.asList(WriteRow.of("sel", 10L, writer, store, 0L, "",
                        "[B"), WriteRow.of("sel", 35L, producer, store,
                        tombstone, "", "[B")), RowCodec::writeWrite);
        RowCodec.writeAll(SessionDir.of(iteration, "sel").reads(),
                Arrays.asList(ReadRow.of("sel", 30L, reader, store, 0L,
                        "S_barrier0", "[B", null), ReadRow.of("sel", 45L,
                        after, store, tombstone, "S_gone", "[B", null)),
                RowCodec::writeRead);
        SessionReader session = SessionReader.read(iteration, "sel");
        Object[][] rows = {
                {reader, Confirmation.storeWriter(tombstone), "STATE "
                        + Confirmation.storeWriter(tombstone) + "@" + tombstone
                        + " STORE_HOLD " + store.key() + "@" + tombstone, 30L},
                {reader, Confirmation.id(writer), "STATE "
                        + Confirmation.id(writer) + "@0", Long.MAX_VALUE},
                {after, Confirmation.storeWriter(0L), "PAIRING_UNHELD", 0L},
        };
        for (Object[] row : rows) {
            Map<String, String> pairings = Collections.singletonMap(
                    Confirmation.id((Endpoint) row[0]), (String) row[1]);
            List<String> held = new ArrayList<String>();
            long cut;
            try {
                ConfirmMain.Holding holding = ConfirmMain.holding(session,
                        pairings);
                for (JsonObject edge : holding.edges) {
                    String kind = edge.get("kind").getAsString();
                    held.add("STATE".equals(kind) ? "STATE " + edge.get(
                            "writer").getAsString() + "@" + edge.get(
                            "version").getAsString()
                            : kind + " " + edge.get("location").getAsString()
                            + "@" + edge.get("version").getAsString());
                }
                cut = holding.cutBefore;
            } catch (ConfirmMain.Refused refused) {
                held.add(refused.getMessage().substring(0,
                        refused.getMessage().indexOf(':')));
                cut = 0L;
            }
            assertEquals(String.valueOf(row[1]), row[2], String.join(" ",
                    held));
            assertEquals(String.valueOf(row[1]), (long) (Long) row[3], cut);
        }
    }

    @Test
    public void aForcedPathIsConfirmedUnforcedOnTheRecordingsSchedule()
            throws Exception {
        Path iteration = iteration();
        SessionDir sel = SessionDir.of(iteration, "sel");
        RowCodec.writeAll(sel.targets(), Collections.singletonList(
                TargetRow.of("sel", 40L, anchor, "<a.Handler: void handle()>"
                        + "#u8#1", "EXPR.phi", false, true, null).forced()),
                RowCodec::writeTarget);
        manifest(sel, SessionManifest.Role.FORCED);
        RowCodec.writeJsonl(SessionDir.of(iteration, "seed").schedule(),
                Collections.singletonList(event(0, "recorded", "")));
        Path out = folder.newFolder("forced-path").toPath();
        JsonObject summary = ConfirmMain.write(iteration,
                claim("FAULT:IPC", "true"), manifest(), out);
        assertEquals("the recording's schedule, not the forced run's",
                "seed", summary.getAsJsonObject("schedulePrefix")
                        .get("sessionId").getAsString());
        JsonObject focus = RowCodec.readJsonl(out.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        assertFalse("CONFIRM forces nothing", focus.has("force")
                && focus.get("force").getAsBoolean());
    }

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
        Object[][] table = {
                {null, null, null, true},
                {"rootAssignments", "FAULT:IPC", "true", true},
                {"rootAssignments", "OTHER", "7", true},
                {"rootAssignments", "OTHER", "8", false},
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
            Path out = folder.newFolder("world-" + row[0] + "-" + row[2])
                    .toPath();
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
                for (JsonObject edge : edges(out)) {
                    if ("STATE".equals(edge.get("kind").getAsString())
                            && edge.get("reader").getAsString().equals(
                            Confirmation.id(reader))) {
                        held++;
                    }
                }
                assertTrue("the world's pairing is held", held > 0);
            }
        }
        Path other = folder.newFolder("not-realized").toPath();
        ConfirmMain.write(iteration, claim("FAULT:IPC", "false"),
                manifest(), other);
        assertTrue(!Files.exists(other.resolve(ConfirmMain.REALIZED))
                && Files.exists(other.resolve(ObligationDir.FOCUSED_TASK)));
    }

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

    @Test
    public void aRePairingOnTheSeedPathIsAMoveAndReachesTheReplay()
            throws Exception {
        Path iteration = iteration();
        Endpoint earlier = endpoint(MINT, "a.Manager#tick()#6:WRITE");
        RowCodec.writeAll(SessionDir.of(iteration, "sel").writes(),
                Arrays.asList(WriteRow.of("sel", 5L, earlier, CELL, 4L,
                        "EXPR.w0", "I"), WriteRow.of("sel", 10L, writer,
                        CELL, 5L, "EXPR.w", "I")), RowCodec::writeWrite);
        Object[][] table = {
                {earlier, null, false},
                {writer, null, true},
                {null, "writer_arm__1__w", false}};
        for (Object[] row : table) {
            Path claim = claim("FAULT:IPC", "true");
            JsonObject recorded = ExploreCodec.readObject(claim);
            recorded.addProperty("seedSessionId", "sel");
            recorded.getAsJsonObject("claim").add("movedRoots",
                    new JsonObject());
            if (row[1] != null) {
                JsonArray repaired = new JsonArray();
                repaired.add((String) row[1]);
                recorded.getAsJsonArray("valuations").get(1).getAsJsonObject()
                        .add("repairedArms", repaired);
            }
            if (row[0] != null) {
                JsonObject arm = new JsonObject();
                arm.addProperty("selector", "writer_arm__1__w");
                arm.addProperty("sessionId", "sel");
                JsonArray fills = new JsonArray();
                fills.add(Interaction.of(InteractionKind.STATE,
                        (Endpoint) row[0], after).id());
                arm.add("interactionIds", fills);
                recorded.getAsJsonArray("valuations").get(1).getAsJsonObject()
                        .getAsJsonArray("selectedArms").add(arm);
            }
            Files.write(claim, recorded.toString().getBytes(
                    StandardCharsets.UTF_8));
            Path out = folder.newFolder().toPath();
            String refusal = "";
            try {
                ConfirmMain.write(iteration, claim, manifest(), out);
            } catch (ConfirmMain.Refused refused) {
                refusal = refused.getMessage();
            }
            assertEquals(row[0] + "/" + row[1] + ": " + refusal, row[2],
                    refusal.startsWith("the claim moves nothing"));
        }
    }

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
        List<JsonObject> rows = edges(out);
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
        for (JsonObject edge : edges(polled)) {
            if (!"ORDER".equals(edge.get("kind").getAsString())) continue;
            held++;
            assertEquals(Endpoint.activation(anchor, ExecutionIndex.of(
                    Collections.singletonList(poll))),
                    edge.get("after").getAsString());
        }
        assertEquals(1, held);

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
            for (JsonObject edge : edges(asked)) {
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
            for (JsonObject edge : edges(snapshot)) {
                if (!"STATE".equals(edge.get("kind").getAsString())) continue;
                stated++;
                assertEquals(Confirmation.anyTurn(reader),
                        edge.get("readerAnyTurn").getAsString());
            }
            assertEquals("initial " + initial, initial ? 0 : 1, stated);
        }

        Path unheld = folder.newFolder("unheld").toPath();
        ConfirmMain.write(iteration, claim("M_J_clock.sel"),
                manifest("MAP/20#-3"), unheld);
        for (JsonObject edge : edges(unheld)) {
            assertTrue(edge.toString(), !"STATE".equals(edge.get("kind")
                    .getAsString()) && !"ORDER".equals(edge.get("kind")
                    .getAsString()));
        }

        String[][] clocks = {
                {"M_J_clock.sel", "CLOCK.a", "49000"},
                {"M_J_clock.b", "CLOCK.b", "49000"},
                {"M_J_clock.b", "CLOCK.b", null},
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

    @Test
    public void aRootOnlyAnArmsBodyNamesIsPlantedWhereItsSessionMintedIt()
            throws Exception {
        Path iteration = iteration();
        Object[][] sessions = {{"arm", mint},
                {"arm2", OccurrenceAddress.parse(PRODUCER)}};
        for (Object[] each : sessions) {
            String id = (String) each[0];
            SessionDir dir = SessionDir.of(iteration, id).create();
            RowCodec.writeAll(dir.roots(), Collections.singletonList(
                    RootMintRow.of(id, 1L, (OccurrenceAddress) each[1],
                            "CLOCK.t0", "M_J_clock.t0", RootKind.CLOCK,
                            RootCategory.CLOCK, "1500", null, null, true,
                            Clock.of(1_000_000L, Clock.WALL), 0L)),
                    RowCodec::writeRootMint);
            RowCodec.writeAll(dir.attaches(), Collections.singletonList(
                    AttachRow.of(id, 20L, consumer, "M_I_field_HOFF.1", "I",
                            "119979", false, null, producer, "ipc-25",
                            "HANDLE")), RowCodec::writeAttach);
            manifest(dir, SessionManifest.Role.FOCUSED);
        }
        Object[][] table = {
                {new String[]{"arm"}, "arm arm"},
                {new String[]{}, "the claim moves M_J_clock.t0, which the "
                        + "recording, the selected session and the arms"},
                {new String[]{"arm", "arm2"}, "the claim moves M_J_clock.t0,"
                        + " which the sessions mint at different occurrences"}};
        for (Object[] row : table) {
            Path claim = claim("M_J_clock.t0", "50000");
            JsonObject document = ExploreCodec.readObject(claim);
            JsonArray arms = document.getAsJsonArray("valuations").get(1)
                    .getAsJsonObject().getAsJsonArray("selectedArms");
            for (String namer : (String[]) row[0]) {
                JsonObject arm = arms.get(0).getAsJsonObject().deepCopy();
                arm.addProperty("selector", "message_arm__1__" + namer);
                arm.addProperty("sessionId", namer);
                JsonArray roots = new JsonArray();
                roots.add("CLOCK.t0");
                arm.add(ComposeMain.ROOTS, roots);
                arms.add(arm);
            }
            Files.write(claim, document.toString().getBytes(
                    StandardCharsets.UTF_8));
            Path out = folder.newFolder().toPath();
            String expected = (String) row[1];
            try {
                ConfirmMain.write(iteration, claim,
                        manifestAnchoring("CLOCK.t0", "1000"), out);
                JsonObject focus = RowCodec.readJsonl(out.resolve(
                        ObligationDir.FOCUSED_TASK)).get(0);
                assertEquals("49000", focus.getAsJsonObject("clockDeltas")
                        .get("CLOCK.t0").getAsString());
                assertEquals(MINT, focus.getAsJsonObject("rootMints")
                        .get("CLOCK.t0").getAsString());
                JsonObject result = new JsonObject();
                result.addProperty("verdict", "NOT_ADMITTED");
                RowCodec.writeJsonl(out.resolve(ObligationDir.RESULT),
                        Collections.singletonList(result));
                assertEquals(expected, ConfirmMain.decide(claim, out,
                        folder.newFolder().toPath()).getAsJsonObject(
                        "mintFrom").get("CLOCK.t0").getAsString());
            } catch (ConfirmMain.Refused refused) {
                assertTrue(refused.getMessage(),
                        refused.getMessage().startsWith(expected));
                assertFalse(refused.refutes);
            }
        }
    }

    @Test
    public void aNativePlantIsConfirmsWorld() throws Exception {
        Path iteration = iteration();
        Path focus = iteration.resolve("obligations-0000").resolve("w1")
                .resolve(ObligationDir.FOCUSED_TASK);
        JsonObject world = RowCodec.readJsonl(focus).get(0);
        Files.write(iteration.resolve("execution_task_plan.jsonl"),
                new byte[0]);
        Path scopeMap = targetScopeMap();
        Object[][] worlds = {
                {"{}", "HDFS.SERIAL", "119981", "ROOT HOOK HDFS.SERIAL "
                        + mint.id() + " 119981"},
                {"{\"CLOCK.gone\":\"7000\"}", "HDFS.SERIAL", "119981", null},
                {"{}", "M_Z_fault", "119981", null},
                {"{}", "M_Z_fault", "false", null},
        };
        for (Object[] row : worlds) {
            JsonObject planted = world.deepCopy();
            planted.add("rootAssignments", new JsonObject());
            planted.add("rootMints", new JsonObject());
            planted.add("clockDeltas", JsonParser.parseString(
                    (String) row[0]).getAsJsonObject());
            RowCodec.writeJsonl(focus, Collections.singletonList(planted));
            Path claim = claim((String) row[1], (String) row[2]);
            Path plant = folder.newFile().toPath();
            try {
                ConfirmMain.writePlant(iteration, claim, manifest(), scopeMap,
                        iteration.resolve("sessions").resolve("sel"), plant);
                if (row[3] == null) fail("planted " + Arrays.toString(row));
            } catch (ConfirmMain.Refused refused) {
                assertTrue(refused.getMessage(), refused.getMessage()
                        .startsWith("NATIVE_PLANT_UNSUPPORTED"));
                assertEquals(refused.getMessage(), null, row[3]);
                continue;
            }
            List<JsonObject> rows = RowCodec.readJsonl(plant);
            JsonObject root = rows.get(0);
            assertEquals(row[3], root.get("kind").getAsString() + " "
                    + root.get("category").getAsString() + " "
                    + root.get("rootId").getAsString() + " "
                    + root.get("occurrence").getAsString() + " "
                    + root.get("value").getAsString());
            Path out = folder.newFolder().toPath();
            ConfirmMain.write(iteration, claim, manifest(), out);
            List<JsonObject> edges = edges(out);
            List<JsonObject> orders = new ArrayList<JsonObject>();
            for (JsonObject edge : edges) {
                if ("ORDER".equals(edge.get("kind").getAsString())) {
                    orders.add(edge);
                }
            }
            assertFalse("the closure orders nothing", orders.isEmpty());
            assertEquals("the join's rows are the plant's none",
                    Collections.<JsonObject>emptyList(), ordersOf(rows));
            Path chosen = claim((String) row[1], (String) row[2]);
            chose(chosen, writer, reader);
            Path outChosen = folder.newFolder().toPath();
            ConfirmMain.write(iteration, chosen, manifest(), outChosen);
            assertEquals("CONFIRM's edges", edges, edges(outChosen));
            Path plantChosen = folder.newFile().toPath();
            ConfirmMain.writePlant(iteration, chosen, manifest(), scopeMap,
                    iteration.resolve("sessions").resolve("sel"),
                    plantChosen);
            assertEquals("what the model chose is planted", orders,
                    ordersOf(RowCodec.readJsonl(plantChosen)));
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

    @Test
    public void aConfigurationRootIsPlantedAtTheGetterItsActionNames()
            throws Exception {
        String getter = "<org.apache.hadoop.conf.Configuration: long "
                + "getLong(java.lang.String,long)>";
        String site = "<a.Master: void activate()>#u13";
        Object[][] table = {
                {"the getter's action names the root as its source",
                        "CONFIG:skew", null, site + " " + getter},
                {"the world also answers an attach with what its producer "
                        + "sent: no plant", "CONFIG:skew", "119979",
                        site + " " + getter},
                {"an answer the producer did not send, at a port no capture "
                        + "states", "CONFIG:skew", "5", null},
                {"no action names it", "", null, null},
        };
        Path iteration = iteration();
        Path focus = iteration.resolve("obligations-0000").resolve("w1")
                .resolve(ObligationDir.FOCUSED_TASK);
        JsonObject world = RowCodec.readJsonl(focus).get(0);
        world.add("rootAssignments", new JsonObject());
        world.add("rootMints", new JsonObject());
        world.add("clockDeltas", new JsonObject());
        RowCodec.writeJsonl(focus, Collections.singletonList(world));
        RowCodec.writeAll(SessionDir.of(iteration, "sel").roots(),
                Arrays.asList(root("sel", "HDFS.SERIAL", "M_I_serial.sel",
                        RootKind.INTEGRAL, "119978"),
                        RootMintRow.of("sel", 2L, mint, "CONFIG:skew",
                                "M_J_skew", RootKind.INTEGRAL,
                                RootCategory.CONFIG, "0", null, null, true,
                                null, 0L)), RowCodec::writeRootMint);
        for (Object[] row : table) {
            JsonObject answered = world.deepCopy();
            JsonObject answers = new JsonObject();
            if (row[2] != null) {
                answers.addProperty(consumer.id(), (String) row[2]);
            }
            answered.add("answers", answers);
            RowCodec.writeJsonl(focus, Collections.singletonList(answered));
            JsonObject action = new JsonObject();
            action.addProperty("portId", "REGION.08ab84c9.in.p");
            action.addProperty(InputActionCatalog.DECLARED_CONFIG_SOURCE,
                    (String) row[1]);
            action.addProperty("location", "CALL_RETURN");
            action.addProperty("siteId", site);
            action.addProperty("declaredCallee", getter);
            action.addProperty("javaType", "long");
            JsonObject task = new JsonObject();
            task.addProperty("regionId", "REGION.08ab84c9");
            task.addProperty("occurrenceId", MINT);
            JsonArray actions = new JsonArray();
            actions.add(action);
            task.add(InputActionCatalog.FIELD, actions);
            RowCodec.writeJsonl(iteration.resolve("execution_task_plan.jsonl"),
                    Collections.singletonList(task));
            Path plant = folder.newFile().toPath();
            try {
                ConfirmMain.writePlant(iteration, claim("CONFIG:skew",
                        "-2001"), manifest(), targetScopeMap(),
                        iteration.resolve("sessions").resolve("sel"), plant);
                if (row[3] == null) fail((String) row[0]);
            } catch (ConfirmMain.Refused refused) {
                assertTrue(refused.getMessage(), refused.getMessage()
                        .startsWith("NATIVE_PLANT_UNSUPPORTED: "
                                + (row[2] == null ? "root CONFIG:skew"
                                : "the world answers attach")));
                assertNull((String) row[0], row[3]);
                continue;
            }
            List<JsonObject> rows = RowCodec.readJsonl(plant);
            for (JsonObject planted : rows) {
                assertFalse((String) row[0] + ": " + planted,
                        RecordingPlant.ANSWER.equals(planted.get("kind")
                                .getAsString()));
            }
            JsonObject root = rows.get(0);
            JsonObject call = root.getAsJsonArray("sites").get(0)
                    .getAsJsonObject();
            assertEquals((String) row[0], "CONFIG CONFIG:skew -2001 " + row[3],
                    root.get("category").getAsString() + " "
                            + root.get("rootId").getAsString() + " "
                            + root.get("value").getAsString() + " "
                            + call.get("siteId").getAsString() + " "
                            + call.get("callee").getAsString());
        }
    }

    private Path targetScopeMap() throws Exception {
        Path scopeMap = folder.newFile().toPath();
        JsonObject site = new JsonObject();
        site.addProperty("schemaVersion", 1);
        site.addProperty("kind", StaticScopeMap.SITE_KIND);
        site.addProperty("role", StaticScopeMap.TARGET_SITE);
        site.addProperty("regionId", anchor.regionId());
        site.addProperty("siteId", "<a.Handler: void handle()>#u8");
        site.add("guards", JsonParser.parseString(
                "[\"<a.Handler: void handle()>#u5\"]"));
        site.add("guardOutcomes", JsonParser.parseString("[false]"));
        Files.write(scopeMap, Collections.singletonList(site.toString()),
                StandardCharsets.UTF_8);
        return scopeMap;
    }

    private static List<JsonObject> ordersOf(List<JsonObject> rows) {
        List<JsonObject> held = new ArrayList<JsonObject>();
        for (JsonObject row : rows) {
            if (!"ORDER".equals(row.get("kind").getAsString())) continue;
            JsonObject order = row.deepCopy();
            order.remove("row");
            held.add(order);
        }
        return held;
    }
    @Test
    public void anOrderNoHoldRealizesIsCheckedWhereItsLaterEndRuns()
            throws Exception {
        Endpoint send = endpoint(PRODUCER, "a.Convert#send()#3:SEND");
        String step = "n0#epoch0|Root:WAKE/a.Scheduler.poll#2|<a.Step: void"
                + " run()>#u23@0";
        Object[][] rows = {
                {"held where it runs", null, null, reader.activation(),
                        false},
                {"held at the send that started it", send, null,
                        send.activation(), false},
                {"no send started it", null, null, reader.activation(), true},
                {"its writer stands under that send", send, send,
                        reader.activation(), true},
                {"a hand-off held at its claim's entry", null, null,
                        Confirmation.claim(ActivationRow.CLAIMED + step),
                        false},
                {"both ends in one hand-off claim", null, null,
                        reader.activation(), false},
                {"the earlier end in a continuation the claim runs", null,
                        null, reader.activation(), false},
                {"the earlier end on another worker, recorded after the"
                        + " event", null, null, Confirmation.claim(
                        ActivationRow.CLAIMED + step), false},
        };
        for (int index = 0; index < rows.length; index++) {
            Object[] row = rows[index];
            String name = (String) row[0];
            Path iteration = iteration();
            List<ActivationRow> activations = new ArrayList<ActivationRow>();
            if (index >= 4) {
                activations.add(ActivationRow.of("sel", anchor, "TASK.r",
                        false, true, ActivationRow.CLAIMED + step,
                        ActivationRow.ClaimKind.HANDOFF_TASK, null));
            }
            if (index == 4) {
                activations.add(ActivationRow.of("sel", mint, "TASK.w",
                        false, true, "thread-7",
                        ActivationRow.ClaimKind.NONE, null));
            } else if (index == 7) {
                activations.add(ActivationRow.of("sel", mint, "TASK.w",
                        false, true, ActivationRow.CLAIMED + step.replace(
                                "#u23@0", "#u23@1"),
                        ActivationRow.ClaimKind.HANDOFF_TASK, null));
                RowCodec.writeAll(SessionDir.of(iteration, "sel").writes(),
                        Collections.singletonList(WriteRow.of("sel", 50L,
                                writer, CELL, 5L, "EXPR.w", "I")),
                        RowCodec::writeWrite);
            } else if (index >= 5) {
                activations.add(ActivationRow.of("sel", mint, "TASK.w",
                        false, true, ActivationRow.CLAIMED + step
                                + (index == 5 ? "" : "/<a.Cont: void accept("
                                + "java.lang.Object)>#u3:a.Step.write@0"),
                        index == 5 ? ActivationRow.ClaimKind.HANDOFF_TASK
                                : ActivationRow.ClaimKind.QUEUED_TASK, null));
            } else if (index > 0 && index < 4) {
                activations.add(ActivationRow.of("sel", anchor, "TASK.r",
                        false, true, ActivationRow.CLAIMED + "pool#1",
                        ActivationRow.ClaimKind.QUEUED_TASK,
                        (Endpoint) row[1]));
            }
            if (row[2] != null) {
                activations.add(ActivationRow.of("sel", mint, "TASK.w",
                        false, true, "thread-7",
                        ActivationRow.ClaimKind.NONE, (Endpoint) row[2]));
            }
            RowCodec.writeAll(SessionDir.of(iteration, "sel").activations(),
                    activations, RowCodec::writeActivation);
            Path out = folder.newFolder("checked-" + index).toPath();
            ConfirmMain.write(iteration, claim("M_J_clock.sel"), manifest(),
                    out);
            int orders = 0;
            for (JsonObject edge : edges(out)) {
                if (!"ORDER".equals(edge.get("kind").getAsString())) continue;
                orders++;
                assertEquals(name, writer.activation(),
                        edge.get("before").getAsString());
                assertEquals(name, row[3], edge.get("after").getAsString());
                assertEquals(name, row[4], RecordingPlant.checked(edge));
            }
            assertEquals(name, 1, orders);
            folder.delete();
            folder.create();
        }
    }
    @Test
    public void aClaimRunningAnotherOrdersEarlierEndBeforeItsEventIsNotHeldAtItsEntry() {
        String c = "start:m|ctx|<a.C: void run()>@0";
        String d = "start:m|ctx|<a.D: void run()>@0";
        String e = "start:m|ctx|<a.E: void run()>@0";
        String thread = "worker#7";
        Object[][] table = {
                {"22: the release waits for the creation's read; the"
                        + " creation's write waits for the release",
                        new String[] {d, c}, new String[] {c, d},
                        new long[] {30L, 12L}, new long[] {12L, 40L},
                        Arrays.asList(false, true)},
                {"two claims, each running the other's earlier end first",
                        new String[] {c, d}, new String[] {d, c},
                        new long[] {10L, 20L}, new long[] {30L, 35L},
                        Arrays.asList(true, true)},
                {"three claims in a cycle", new String[] {c, d, e},
                        new String[] {d, e, c}, new long[] {10L, 12L, 15L},
                        new long[] {33L, 34L, 36L},
                        Arrays.asList(true, true, true)},
                {"an earlier end in a continuation the claim ran first",
                        new String[] {c, d}, new String[] {d,
                        c + "/<a.K: void accept(java.lang.Object)>#u3:a.C.run@0"},
                        new long[] {45L, 5L}, new long[] {31L, 40L},
                        Arrays.asList(true, false)},
                {"its own earlier end for an order held elsewhere runs first",
                        new String[] {c, null}, new String[] {thread, c},
                        new long[] {10L, 20L}, new long[] {30L, 35L},
                        Arrays.asList(true, false)},
        };
        for (Object[] row : table) {
            String[] claims = (String[]) row[1];
            String[] firsts = (String[]) row[2];
            List<Long> firstSeqs = new ArrayList<Long>();
            List<Long> thenSeqs = new ArrayList<Long>();
            for (long seq : (long[]) row[3]) firstSeqs.add(seq);
            for (long seq : (long[]) row[4]) thenSeqs.add(seq);
            assertEquals((String) row[0], row[5], ConfirmMain.prefixed(
                    Arrays.asList(claims), Arrays.asList(firsts), firstSeqs,
                    thenSeqs));
        }
    }

    @Test
    public void aReadTheModelHoldsBehindTheAnchorIsNotRequired() {
        String release = Confirmation.CLAIM
                + "m|Anchor:d|<a.P: void step()>@0";
        String creation = Confirmation.CLAIM
                + "m|Anchor:c|<a.P: void step()>@0";
        Map<String, String> claims = new LinkedHashMap<String, String>();
        claims.put("R|", release);
        claims.put("A|", creation);
        String read = "A|<a.N: int count()>@0";
        String removal = "R|<a.N: void remove()>@0";
        String nested = "W|<a.Q: void run()>@0/<a.N: int count()>@0";
        Object[][] table = {
                {"22: the release step's own read, its claim held behind the"
                        + " anchor's read", removal,
                        Arrays.asList(order(read, release)), true},
                {"a read inside the anchor occurrence",
                        "A|<a.N: void add()>@0",
                        Arrays.asList(order(read, creation)), false},
                {"a read held behind another occurrence's end", removal,
                        Arrays.asList(order("B|<a.N: void add()>@0", release)),
                        false},
                {"a read inside an activation held behind a held claim's end",
                        nested, Arrays.asList(order(read, release),
                        order(removal, "W|<a.Q: void run()>@0")), true},
                {"a read merely recorded after the anchor", nested,
                        Collections.<JsonObject>emptyList(), false},
        };
        for (Object[] row : table) {
            @SuppressWarnings("unchecked")
            List<JsonObject> edges = new ArrayList<JsonObject>(
                    (List<JsonObject>) row[2]);
            JsonObject state = JsonParser.parseString("{'kind':'STATE',"
                    + "'reader':'r','mint':false,'writer':'w','version':3}")
                    .getAsJsonObject();
            edges.add(state);
            assertEquals((String) row[0], row[3], !ConfirmMain.afterAnchor(
                    edges, "A|", claims, Collections.singletonMap("r",
                            (String) row[1])).isEmpty());
            assertEquals((String) row[0], row[3],
                    state.has(Confirmation.AFTER_ANCHOR));
        }
    }

    private static JsonObject order(String before, String after) {
        JsonObject order = new JsonObject();
        order.addProperty("kind", "ORDER");
        order.addProperty("before", before);
        order.addProperty("after", after);
        return order;
    }

    @Test
    public void aTurnCountedOrderIsLeftOutOfTheNativePlantOnly()
            throws Exception {
        Path iteration = iteration();
        Path focus = iteration.resolve("obligations-0000").resolve("w1")
                .resolve(ObligationDir.FOCUSED_TASK);
        JsonObject world = RowCodec.readJsonl(focus).get(0);
        world.add("rootAssignments", new JsonObject());
        world.add("rootMints", new JsonObject());
        world.add("clockDeltas", new JsonObject());
        RowCodec.writeJsonl(focus, Collections.singletonList(world));
        Files.write(iteration.resolve("execution_task_plan.jsonl"),
                new byte[0]);
        Endpoint polled = endpoint("hdfs/nn0#epoch0/region/REGION.08ab84c9/"
                + "ctx:Root:WAKE/a.Pool.poll#3/idx:<a.Manager: void tick()>@0",
                "a.Manager#tick()#7:WRITE");
        RowCodec.writeAll(SessionDir.of(iteration, "sel").writes(),
                Collections.singletonList(WriteRow.of("sel", 10L, polled,
                        CELL, 5L, "EXPR.w", "I")), RowCodec::writeWrite);
        Path claim = claim("HDFS.SERIAL", "119981");
        chose(claim, polled, reader);
        Path plant = folder.newFile().toPath();
        JsonObject summary = ConfirmMain.writePlant(iteration, claim,
                manifest(), targetScopeMap(),
                iteration.resolve("sessions").resolve("sel"), plant);
        assertEquals("a poll's turn is the VM's timing", 1,
                summary.get("turnOrders").getAsInt());
        assertEquals(Collections.<JsonObject>emptyList(),
                ordersOf(RowCodec.readJsonl(plant)));
        Path out = folder.newFolder().toPath();
        ConfirmMain.write(iteration, claim, manifest(), out);
        int held = 0;
        for (JsonObject edge : edges(out)) {
            if (!"ORDER".equals(edge.get("kind").getAsString())) continue;
            held++;
            assertEquals("CONFIRM still holds it", Confirmation.activation(
                    polled.occurrence(), ExecutionIndex.empty()),
                    edge.get("before").getAsString());
        }
        assertEquals(1, held);
    }

    @Test
    public void anOrderTheClientsRepliesImplyIsLeftOutOfTheNativePlant() {
        String client = "auto0/client0#epoch0|Root:CLIENT/test#1";
        List<ScheduleEvent> schedule = Arrays.asList(
                ScheduleEvent.of(1L, ScheduleEvent.Kind.SEND, client,
                        "HBASE_RPC#REQUEST:MasterService.AddRSGroup", 0, "",
                        "r1"),
                ScheduleEvent.of(2L, ScheduleEvent.Kind.SEND,
                        "auto0/master0#epoch0|Anchor:r1@HBASE_RPC/test",
                        "HBASE_RPC#RESPONSE", 0, "", "p1"),
                ScheduleEvent.of(3L, ScheduleEvent.Kind.RECV,
                        "auto0/client0#epoch0|Anchor:p1@HBASE_RPC/test",
                        "HBASE_RPC#RESPONSE", 0, "", ""),
                ScheduleEvent.of(4L, ScheduleEvent.Kind.SEND, client,
                        "HBASE_RPC#REQUEST:MasterService.MoveServers", 0, "",
                        "r2"),
                ScheduleEvent.of(5L, ScheduleEvent.Kind.SEND,
                        "auto0/client0#epoch0|Root:CLIENT/test#2",
                        "HBASE_RPC#REQUEST:MasterService.MoveServers", 0, "",
                        "r3"),
                ScheduleEvent.of(6L, ScheduleEvent.Kind.SEND, client,
                        "HBASE_RPC#REQUEST:MasterService.CreateNamespace", 0,
                        "", "r5"),
                ScheduleEvent.of(7L, ScheduleEvent.Kind.SEND, client,
                        "HBASE_RPC#REQUEST:MasterService.RemoveRSGroup", 0,
                        "", "r6"),
                ScheduleEvent.of(8L, ScheduleEvent.Kind.SEND,
                        "auto0/master0#epoch0|Anchor:r5@HBASE_RPC/test",
                        "HBASE_RPC#RESPONSE", 0, "", "p5"),
                ScheduleEvent.of(9L, ScheduleEvent.Kind.RECV,
                        "auto0/client0#epoch0|Anchor:p5@HBASE_RPC/test",
                        "HBASE_RPC#RESPONSE", 0, "", ""));
        ClientProgramOrder program = ClientProgramOrder.of(schedule);
        OccurrenceAddress added = under("REGION.add", "r1");
        Object[][] table = {
            {"one client thread received r1's reply before it sent r2",
                    added, under("REGION.move", "r2"), true, true},
            {"the earlier end is claimed work: it can outlive the reply",
                    added, under("REGION.move", "r2"), false, false},
            {"the same thread sent r6 before r5's reply came",
                    under("REGION.create", "r5"),
                    under("REGION.remove", "r6"), true, false},
            {"another client thread sent r3",
                    added, under("REGION.move", "r3"), true, false},
        };
        for (Object[] row : table) {
            OccurrenceAddress before = (OccurrenceAddress) row[1];
            java.util.Set<String> unclaimed = (Boolean) row[3]
                    ? Collections.singleton(before.id())
                    : Collections.<String>emptySet();
            String said = ConfirmMain.implied(new OccurrenceAddress[] {
                    before, (OccurrenceAddress) row[2]}, program, unclaimed);
            assertEquals((String) row[0] + ": " + said, row[4],
                    !said.isEmpty());
        }
    }

    private static OccurrenceAddress under(String region, String request) {
        return OccurrenceAddress.parse("auto0/master0#epoch0/region/" + region
                + "/ctx:Anchor:" + request + "@HBASE_RPC/test/idx:");
    }
}
