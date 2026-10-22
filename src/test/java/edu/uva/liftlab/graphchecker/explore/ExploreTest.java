package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExpressionLogs;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.plan.SystemView;

import org.junit.After;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class ExploreTest {
    private static final ObligationFactory.Bounds DEFAULT_BOUNDS =
            new ObligationFactory.Bounds(
                    ObligationFactory.DEFAULT_MAX_PATHS_PER_TASK,
                    ObligationFactory.DEFAULT_MAX_FLIPS_PER_PATH,
                    ObligationFactory.DEFAULT_MAX_WORLD_DEPTH);

    private static final String TARGET_SELECTOR =
            "hdfs-case/dn0#epoch0/region/REGION.target#1";
    private static final OccurrenceAddress PRODUCER = occurrence("hdfs-case/nn0",
            "REGION.rotate", CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", 1),
            "o.a.h.h.s.b.BlockManager#run#8");
    private static final OccurrenceAddress TARGET = occurrence("hdfs-case/dn0",
            "REGION.target", CausalContext.of(Role.of("DATA_XCEIVER"), "", 1),
            "o.a.h.h.s.d.DataXceiver#run#12");
    private static final OccurrenceAddress WRITER = occurrence("hdfs-case/dn0",
            "REGION.addkeys", CausalContext.of(exportedId(),
                    "DatanodeProtocol#registerDatanode"),
            "o.a.h.h.s.d.BPServiceActor#offerService#41");
    private static final Map<String, String> NONE = Collections.emptyMap();
    private static final List<String> NONE_STATED =
            Collections.<String>emptyList();
    private static final LocationId ALL_KEYS =
            LocationId.of(LocationKind.MAP, "21", "allKeys");
    private static final Endpoint ROTATED = at(PRODUCER,
            "XCH.resp.block-key-id", "PBHelper#convert#9");
    private static final Endpoint DELIVERED = at(WRITER,
            "XCH.resp.block-key-id", "PBHelper#convert#9");
    private static final Endpoint STORED = at(WRITER,
            Endpoint.stateSite("BlockTokenSecretManager", "addKeys", 12, true),
            "BlockTokenSecretManager#addKeys#12");
    private static final Endpoint LOOKED_UP = at(TARGET,
            Endpoint.stateSite("BlockTokenSecretManager",
                    "retrieveDataEncryptionKey", 8, false),
            "BlockTokenSecretManager#retrieveDataEncryptionKey#8");
    private static final OccurrenceAddress READER =
            occurrence("hdfs-case/dn0", "REGION.reader",
                    CausalContext.of(Role.of("DATA_XCEIVER"), "", 2),
                    "o.a.h.h.s.d.DataXceiver#run#44");
    private static final OccurrenceAddress SIDECAR =
            occurrence("hdfs-case/sidecar", "REGION.sidecar",
                    CausalContext.of(Role.of("SIDECAR"), "", 1),
                    "o.a.h.Sidecar#run#2");
    private static final Endpoint SENT = at(SIDECAR,
            "XCH.req.token-id", "PBHelper#convert#17");
    private static final Endpoint RECEIVED = at(READER,
            "XCH.req.token-id", "PBHelper#convert#17");
    private static final Endpoint CONSULTED = at(READER,
            Endpoint.stateSite("BlockTokenSecretManager",
                    "checkAccess", 4, false),
            "BlockTokenSecretManager#checkAccess#4");

    @Before
    public void publishedViews() {
        System.setProperty(
                edu.uva.liftlab.graphchecker.causynth.LibraryCatalog
                        .SYSTEM_DOORS, Paths.get("src", "test", "resources",
                        "published-views.jsonl").toAbsolutePath().toString());
    }

    @After
    public void noSystemDoors() {
        System.clearProperty(edu.uva.liftlab.graphchecker.causynth
                .LibraryCatalog.SYSTEM_DOORS);
    }

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @Test
    public void aKilledForceRunIsAskedAgainThenHeldBounded() throws Exception {
        String killed = ObligationResult.REPLAY_BOUNDED + ": replay exceeded"
                + " replay_timeout_s=2400";
        String diverged = "FORCE_DIVERGED: the occurrence closed first";
        Object[][] rows = {
            {new String[] {killed}, true, "PROPOSED", "[]"},
            {new String[] {killed, killed}, false, "BOUNDED", "[FORCE x2]"},
            {new String[] {killed, diverged}, false, "NOT_ADMITTED", "[]"},
        };
        int at = 0;
        for (Object[] row : rows) {
            String name = "force-killed-" + at++;
            Path iteration = tree.newFolder(name).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            seed.marker(TARGET, "CASE.A", "M_A", "false");
            seed.decision(TARGET, "Guard#u8", 1, false, "M_A");
            seed.flush();
            JsonObject target = com.google.gson.JsonParser.parseString(
                    targetSite("REGION.target", "Throw#u30", "Guard#u8"))
                    .getAsJsonObject();
            target.add("force", com.google.gson.JsonParser.parseString(
                    "[{\"siteId\":\"Guard#u8\",\"arm\":true}]"));
            scopeMap(iteration, target.toString());
            Path out = tree.newFolder(name + "-out").toPath();
            Path results = results(out);
            String[] replays = (String[]) row[0];
            JsonObject manifest = null;
            for (int k = 0; k <= replays.length; k++) {
                String wave = String.format("obligations-%04d", k);
                manifest = plan(iteration, TARGET_SELECTOR, null, results,
                        out.resolve(wave), k);
                Obligation force = obligations(out.resolve(wave)).stream()
                        .filter(Obligation::force).findFirst().orElse(null);
                if (k == replays.length) {
                    assertEquals(name + ": asked again", row[1],
                            force != null);
                    break;
                }
                assertNotNull(name + ": asked in round " + k, force);
                Path worker = iteration.resolve(wave)
                        .resolve(force.obligationId());
                solve(iteration, out.resolve(wave), force,
                        iteration.resolve(wave), force.obligationId());
                ObligationResult answer = ObligationResult.of(
                        force.obligationId(), Verdict.NOT_ADMITTED, "",
                        replays[k]);
                Files.write(worker.resolve(ObligationDir.RESULT),
                        (RowCodec.toLine(RowCodec.writeObligationResult(
                                answer)) + "\n")
                                .getBytes(StandardCharsets.UTF_8));
                Path asked = worker.resolve(ObligationDir.QUESTION_ASKED);
                if (answer.replayBounded()) {
                    Files.delete(asked);
                } else {
                    Files.move(asked, worker.resolve(ObligationDir.QUESTION));
                }
                record(results, answer);
            }
            assertEquals(name + ": its state", row[2], manifest
                    .getAsJsonObject("force").get("state").getAsString());
            assertEquals(name + ": the round names it", row[3],
                    names(manifest.getAsJsonArray("boundedFlips")));
        }
    }

    @Test
    public void aServedRoundIsAFreshPlannersRound() throws Exception {
        Path iteration = tree.newFolder("served").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        seed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        seed.decision(TARGET, "Guard#u8", 1, false, "EXPR.0000000000000001");
        seed.keyChain();
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"));
        Path results = results(iteration);
        Path fresh = tree.newFolder("served-fresh").toPath();
        ExploreMain served = new ExploreMain(iteration, TARGET_SELECTOR, null,
                iteration.resolve(StaticScopeMap.FILE), "epoch0",
                ClosurePlanner.DEFAULT_MAX_TASKS, DEFAULT_BOUNDS,
                ClientFaults.NONE, SystemView.of(""));
        String[][] landings = {{}, {"land", "s-a"}, {"leave", "s-a"},
                {"land", "s-b"}, {"unlisted", "s-c"}};
        Map<String, Integer> kinds = new LinkedHashMap<String, Integer>();
        Set<String> held = new LinkedHashSet<String>();
        for (int round = 0; round < landings.length; round++) {
            String[] landing = landings[round];
            if (landing.length > 0 && landing[0].equals("land")) {
                landed(iteration, landing[1]);
                worker(iteration, String.format("obligations-%04d", round - 1),
                        "w-" + landing[1], "o-" + landing[1], landing[1],
                        TARGET, "Guard#u8", NONE, NONE);
            } else if (landing.length > 0 && landing[0].equals("leave")) {
                deleteTree(iteration.resolve("sessions").resolve(landing[1]));
            }
            String name = String.format("obligations-%04d", round);
            Path own = fresh.resolve(name);
            plan(iteration, TARGET_SELECTOR, null, results, own, round);
            List<String> corpus = new ArrayList<String>();
            try (java.util.stream.Stream<Path> listed =
                         Files.list(iteration.resolve("sessions"))) {
                listed.forEach(session -> corpus.add(session.getFileName()
                        .toString()));
            }
            if (landing.length > 0 && landing[0].equals("unlisted")) {
                landed(iteration, landing[1]);
            }
            Path mine = iteration.resolve(name);
            long reads = 0L;
            for (String sessionId : corpus) {
                if (held.contains(sessionId)) continue;
                try (java.util.stream.Stream<Path> files = Files.list(
                        iteration.resolve("sessions").resolve(sessionId))) {
                    for (Path file : (Iterable<Path>) files::iterator) {
                        reads += ArtifactIO.decodedSize(file);
                    }
                }
            }
            assertEquals("round " + round + " reads its new sessions' files",
                    reads, served.toRead(corpus));
            served.round(round, null, results, corpus, mine);
            held = new LinkedHashSet<String>(corpus);
            List<String> files = new ArrayList<String>();
            try (java.util.stream.Stream<Path> listed = Files.list(own)) {
                listed.forEach(file -> files.add(file.getFileName()
                        .toString()));
            }
            assertTrue("round " + round + " writes its slot changes: "
                    + files, files.contains(SlotTable.FILE));
            for (String file : files) {
                assertEquals("round " + round + ": " + file,
                        new String(Files.readAllBytes(own.resolve(file)),
                                StandardCharsets.UTF_8),
                        new String(Files.readAllBytes(mine.resolve(file)),
                                StandardCharsets.UTF_8));
            }
            for (JsonObject row : RowCodec.readJsonl(
                    mine.resolve(SlotTable.FILE))) {
                kinds.merge(row.get("kind").getAsString(), 1, Integer::sum);
            }
        }
        assertTrue("slots were opened and dropped: " + kinds,
                kinds.containsKey(SlotTable.OPENED)
                        && kinds.containsKey(SlotTable.DROPPED));
    }

    @Test
    public void aRoundOnOneCoreIsARoundOnMany() throws Exception {
        Path iteration = tree.newFolder("cores").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        seed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        seed.decision(TARGET, "Guard#u8", 1, false, "EXPR.0000000000000001");
        seed.keyChain();
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"));
        for (int world = 0; world < 6; world++) {
            landed(iteration, "s-" + world);
            worker(iteration, "obligations-0000", "w-" + world, "o-s-" + world,
                    "s-" + world, TARGET, "Guard#u8", NONE, NONE);
        }
        Path results = results(iteration);
        Map<Integer, Path> planned = new LinkedHashMap<Integer, Path>();
        try {
            for (int cores : new int[] {1, 8}) {
                Parallel.width(cores);
                Path out = tree.newFolder("cores-" + cores).toPath();
                plan(iteration, TARGET_SELECTOR, null, results, out, 1);
                planned.put(cores, out);
            }
        } finally {
            Parallel.width(1);
        }
        List<String> files = new ArrayList<String>();
        try (java.util.stream.Stream<Path> listed =
                     Files.list(planned.get(1))) {
            listed.forEach(file -> files.add(file.getFileName().toString()));
        }
        assertTrue("the round wrote its files: " + files,
                files.contains("obligations.jsonl")
                        && files.contains(SlotTable.FILE));
        for (String file : files) {
            assertArrayEquals(file, Files.readAllBytes(
                    planned.get(1).resolve(file)), Files.readAllBytes(
                    planned.get(8).resolve(file)));
        }
    }

    private static Session landed(Path iteration, String id)
            throws IOException {
        Session world = new Session(iteration, id);
        world.activation(TARGET, true);
        world.marker(TARGET, "CASE.MARKER", "M_MARKER", "true");
        world.decision(TARGET, "Guard#u8", 1, true, "M_MARKER");
        world.keyChain();
        world.answered(ObligationResult.of("o-" + id, Verdict.ADMITTED, id,
                "the flip ran"));
        world.flush();
        return world;
    }

    private static void deleteTree(Path dir) throws IOException {
        List<Path> all = new ArrayList<Path>();
        try (java.util.stream.Stream<Path> walked = Files.walk(dir)) {
            walked.forEach(all::add);
        }
        Collections.reverse(all);
        for (Path path : all) Files.delete(path);
    }

    private static void worker(Path iteration, String wave, String dir,
                               String obligationId, String sessionId,
                               OccurrenceAddress focused, String siteId,
                               Map<String, String> roots,
                               Map<String, String> clockDeltas)
            throws IOException {
        worker(iteration, wave, dir, obligationId, sessionId, focused, siteId,
                roots, clockDeltas, Collections.<Corpus.Flip>emptyList());
    }

    private static void worker(Path iteration, String wave, String dir,
                               String obligationId, String sessionId,
                               OccurrenceAddress focused, String siteId,
                               Map<String, String> roots,
                               Map<String, String> clockDeltas,
                               List<Corpus.Flip> inherited)
            throws IOException {
        Path at = iteration.resolve(wave).resolve(dir);
        Files.createDirectories(at);
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "FOCUSED_TASK");
        row.addProperty("obligationId", obligationId);
        row.addProperty("taskId", "task-" + focused.regionId());
        row.addProperty("pathId", Corpus.pathId(sessionId, focused));
        row.addProperty("focused", focused.render());
        row.addProperty("focusedOccurrenceId", focused.id());
        row.addProperty("seedSessionId", "s-seed");
        JsonObject flip = new JsonObject();
        flip.addProperty("siteId", siteId);
        flip.addProperty("ordinal", 1);
        flip.addProperty("outcome", true);
        row.add("flip", flip);
        JsonObject assigned = new JsonObject();
        for (Map.Entry<String, String> root : roots.entrySet()) {
            assigned.addProperty(root.getKey(), root.getValue());
        }
        row.add("rootAssignments", assigned);
        JsonObject skews = new JsonObject();
        for (Map.Entry<String, String> delta : clockDeltas.entrySet()) {
            skews.addProperty(delta.getKey(), delta.getValue());
        }
        row.add("clockDeltas", skews);
        row.add("answers", new JsonObject());
        row.add("rootMints", new JsonObject());
        JsonArray carried = new JsonArray();
        for (Corpus.Flip one : inherited) {
            carried.add(ExploreCodec.writeFlip(one));
        }
        row.add("inheritedFlips", carried);
        row.add("unproducible", new JsonArray());
        RowCodec.writeJsonl(at.resolve(ObligationDir.FOCUSED_TASK),
                Collections.singletonList(row));
        RowCodec.writeJsonl(at.resolve(ObligationDir.RESULT),
                Collections.singletonList(RowCodec.writeObligationResult(
                        ObligationResult.of(obligationId, Verdict.ADMITTED,
                                sessionId,
                                "the focused prefix reproduced"))));
    }

    @Test
    public void aRoundNamesItsWitnessesAndHoldsWhatIsInFlight()
            throws Exception {
        Path iteration = tree.newFolder("witness").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        seed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        seed.decision(TARGET, "Guard#u8", 1, false, "EXPR.0000000000000001");
        seed.flush();
        Session fatal = new Session(iteration, "s-fatal");
        fatal.activation(TARGET, true);
        fatal.fatal(TARGET, "Throw#u30", "true");
        fatal.answered(ObligationResult.of("OBL.s-fatal", Verdict.ADMITTED,
                "s-fatal", "the focused prefix reproduced"));
        fatal.flush();
        worker(iteration, "obligations-0002", "OBL.s-fatal", "OBL.s-fatal",
                "s-fatal", TARGET, "Guard#u8", NONE, NONE);
        Files.write(iteration.resolve("obligations-0002")
                        .resolve(ExploreMain.MANIFEST_FILE),
                "{\"wave\": 1}\n".getBytes(StandardCharsets.UTF_8));
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"));
        Path out = tree.newFolder("witness-out").toPath();
        Path results = results(out);

        Path asked = out.resolve("obligations-0003");
        JsonObject manifest = plan(iteration, TARGET_SELECTOR, null, results,
                asked, 3);
        assertEquals("OBLIGATIONS_PROPOSED",
                manifest.get("state").getAsString());
        assertEquals("[\"s-fatal\"]",
                manifest.get("witnesses").toString());
        assertEquals("one past the wave s-fatal's obligation was planned in",
                2, manifest.get("wave").getAsInt());
        List<Obligation> proposed = obligations(asked);
        assertFalse(proposed.isEmpty());

        Obligation first = proposed.get(0);
        Path flying = out.resolve("in_flight.jsonl");
        RowCodec.writeAll(flying, Arrays.asList(Obligation.of("OBL.moved",
                first.taskId(), first.pathId(), first.siteId(),
                first.ordinal(), first.flippedOutcome(),
                NONE,
                NONE,
                Collections.<String>emptyList())),
                ExploreCodec::writeObligation);
        Path held = out.resolve("obligations-0004");
        JsonObject awaiting = plan(iteration, results, flying, held, 4,
                DEFAULT_BOUNDS);
        assertEquals(proposed.size() - 1, obligations(held).size());
        assertEquals(1, awaiting.get("heldInFlight").getAsInt());
        assertEquals(1, awaiting.get("inFlight").getAsInt());
        if (proposed.size() == 1) {
            assertEquals("nothing new while an arm is in flight is no fixed "
                    + "point", "AWAITING",
                    awaiting.get("state").getAsString());
        }
    }

    @Test
    public void aBranchWithoutTheDeclaredRegionUnderItsContextStops()
            throws Exception {
        Path iteration = tree.newFolder("branches").toPath();
        OccurrenceAddress shifted = occurrence("hdfs-case/dn0",
                "REGION.target",
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 3),
                "o.a.h.h.s.d.DataXceiver#run#14");
        OccurrenceAddress elsewhere = occurrence("hdfs-case/dn0",
                "REGION.target", CausalContext.of(Role.of("BALANCER"), "", 1),
                "o.a.h.h.s.d.DataXceiver#run#12");
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.flush();
        for (String[] row : new String[][] {
                {"s-shifted", "ADMITTED"}, {"s-elsewhere", "ADMITTED"},
                {"s-refused", "NOT_ADMITTED"}}) {
            Session focused = new Session(iteration, row[0]);
            focused.activation(row[0].equals("s-shifted") ? shifted
                    : elsewhere, true);
            focused.answered(ObligationResult.of("OBL." + row[0],
                    Verdict.valueOf(row[1]), row[0], "fixture"));
            focused.flush();
        }
        List<GapRow> gaps = new ArrayList<GapRow>();
        Branches branches = Branches.of(Corpus.read(iteration, null),
                Collections.singletonList(TARGET), gaps);
        assertTrue(branches.parents("s-seed"));
        assertTrue("the same chain at another index",
                branches.parents("s-shifted"));
        assertFalse("another chain", branches.parents("s-elsewhere"));
        assertFalse("a refused replay", branches.parents("s-refused"));
        assertEquals(1, branches.stopped());
        assertEquals(1, gaps.size());
        assertEquals("s-elsewhere", gaps.get(0).subject());
        assertEquals(GapClass.DIAGNOSTIC, gaps.get(0).cls());
    }

    @Test
    public void anArmIsKeyedByWhatItsGuardDependsOn() throws Exception {
        Path iteration = tree.newFolder("depends").toPath();
        LocationId qop = LocationId.of(LocationKind.INSTANCE, "33", "qop");
        Endpoint negotiated = at(WRITER,
                Endpoint.stateSite("DigestMD5Base", "<init>", 31, true),
                "DigestMD5Base#<init>#31");
        OccurrenceAddress lateWriter = occurrence("hdfs-case/dn0",
                "REGION.late", CausalContext.of(Role.of("DATA_XCEIVER"), "",
                        3), "o.a.h.h.s.d.DataXceiver#run#57");
        String[][] sessions = {
            {"s-seed", "true", "true", "1", "1", "0"},
            {"s-idle", "true", "true", "1", "1", "0"},
            {"s-far", "true", "false", "1", "1", "0"},
            {"s-noise", "true", "true", "1", "3", "0"},
            {"s-coreader", "true", "true", "1", "1", "1"},
            {"s-near", "false", "true", "1", "1", "0"},
            {"s-more", "true", "true", "2", "1", "0"},
        };
        for (String[] row : sessions) {
            Session session = new Session(iteration, row[0]);
            session.activation(TARGET, !"s-seed".equals(row[0]));
            session.activation(WRITER, false);
            session.integral(TARGET, "CASE.A", "M_A", "0", "0", "10");
            session.integral(TARGET, "CASE.B", "M_B", "0", "0", "10");
            session.symbolic("e.stored", "M_A");
            for (int i = 0; i < Integer.parseInt(row[3]); i++) {
                session.write(STORED, ALL_KEYS, 5L + i, "e.stored");
            }
            for (int i = 0; i < Integer.parseInt(row[4]); i++) {
                session.write(negotiated, qop, 1L + i, "e.stored");
            }
            session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "0");
            session.activation(READER, false);
            session.read(CONSULTED, ALL_KEYS, 5L, "M_SEEN_KEY", "0");
            for (int i = 0; i < Integer.parseInt(row[5]); i++) {
                session.attach(RECEIVED, "M_HOFF_TOKEN", "554433", SENT);
            }
            session.decision(TARGET, "Near#u2", 1,
                    Boolean.parseBoolean(row[1]), "(> M_A 1)");
            session.decision(TARGET, "Far#u4", 1,
                    Boolean.parseBoolean(row[2]), "(> M_B 1)");
            session.decision(TARGET, "Guard#u8", 1, false,
                    "(> (+ M_A M_READ_KEY) 3)");
            if ("s-idle".equals(row[0])) session.activation(lateWriter, false);
            session.flush();
        }
        Session afterGuard = new Session(iteration, "s-later");
        afterGuard.activation(TARGET, true);
        afterGuard.activation(WRITER, false);
        afterGuard.integral(TARGET, "CASE.A", "M_A", "0", "0", "10");
        afterGuard.integral(TARGET, "CASE.B", "M_B", "0", "0", "10");
        afterGuard.symbolic("e.stored", "M_A");
        afterGuard.write(STORED, ALL_KEYS, 5L, "e.stored");
        afterGuard.write(negotiated, qop, 1L, "e.stored");
        afterGuard.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "0");
        afterGuard.activation(READER, false);
        afterGuard.read(CONSULTED, ALL_KEYS, 5L, "M_SEEN_KEY", "0");
        afterGuard.decision(TARGET, "Near#u2", 1, true, "(> M_A 1)");
        afterGuard.decision(TARGET, "Far#u4", 1, true, "(> M_B 1)");
        afterGuard.decision(TARGET, "Guard#u8", 1, false,
                "(> (+ M_A M_READ_KEY) 3)");
        afterGuard.decision(TARGET, "Later#u20", 1, true, "(> M_A 5)");
        afterGuard.flush();
        LocationId inner = LocationId.of(LocationKind.INSTANCE, "40", "7");
        OccurrenceAddress innerA = occurrence("hdfs-case/dn0",
                "REGION.innerA", CausalContext.of(Role.of("INNER_A"), "", 1),
                "o.a.h.h.s.d.InnerA#run#1");
        OccurrenceAddress innerA2 = occurrence("hdfs-case/dn0",
                "REGION.innerA", CausalContext.of(Role.of("INNER_A"), "", 2),
                "o.a.h.h.s.d.InnerA#run#2");
        OccurrenceAddress innerB = occurrence("hdfs-case/dn0",
                "REGION.innerB", CausalContext.of(Role.of("INNER_B"), "", 1),
                "o.a.h.h.s.d.InnerB#run#1");
        JsonObject symbolA = leaf("M_A", "I");
        JsonObject innerRead = leaf("M_INNER", "I");
        Object[][] writtenRows = {
            {"s-plus", binary("+", symbolA, literal(10)), null},
            {"s-minus", binary("-", symbolA, literal(1)), null},
            {"s-plus-again", binary("+", symbolA, literal(10)), null},
            {"s-inner-a", innerRead, innerA},
            {"s-inner-a2", innerRead, innerA2},
            {"s-inner-b", innerRead, innerB},
        };
        for (Object[] row : writtenRows) {
            Session session = new Session(iteration, (String) row[0]);
            session.activation(TARGET, true);
            session.activation(WRITER, false);
            session.integral(TARGET, "CASE.A", "M_A", "0", "0", "10");
            session.integral(TARGET, "CASE.B", "M_B", "0", "0", "10");
            session.symbolic("e.stored", "M_A");
            session.expression("EXPR.00000000000000e2", (JsonObject) row[1]);
            session.write(STORED, ALL_KEYS, 5L, "EXPR.00000000000000e2");
            if (row[2] != null) {
                OccurrenceAddress writer = (OccurrenceAddress) row[2];
                session.constant("EXPR.00000000000000e3", "3");
                session.write(at(writer, writer.regionId() + "#u1:WRITE",
                        writer.regionId() + "#u1"), inner, 7L,
                        "EXPR.00000000000000e3");
                session.read(at(WRITER, "Inner#u2:READ", "Inner#u2"), inner,
                        7L, "M_INNER", "3");
            }
            session.write(negotiated, qop, 1L, "e.stored");
            session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "0");
            session.activation(READER, false);
            session.read(CONSULTED, ALL_KEYS, 5L, "M_SEEN_KEY", "0");
            session.decision(TARGET, "Near#u2", 1, true, "(> M_A 1)");
            session.decision(TARGET, "Far#u4", 1, true, "(> M_B 1)");
            session.decision(TARGET, "Guard#u8", 1, false,
                    "(> (+ M_A M_READ_KEY) 3)");
            session.flush();
        }
        for (String[] written : new String[][] {{"s-five", "5"},
                {"s-seven", "7"}, {"s-seven-again", "7"}}) {
            Session session = new Session(iteration, written[0]);
            session.activation(TARGET, true);
            session.activation(WRITER, false);
            session.integral(TARGET, "CASE.A", "M_A", "0", "0", "10");
            session.integral(TARGET, "CASE.B", "M_B", "0", "0", "10");
            session.symbolic("e.stored", "M_A");
            session.constant("EXPR.00000000000000e1", written[1]);
            session.write(STORED, ALL_KEYS, 5L, "EXPR.00000000000000e1");
            session.write(negotiated, qop, 1L, "e.stored");
            session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "0");
            session.activation(READER, false);
            session.read(CONSULTED, ALL_KEYS, 5L, "M_SEEN_KEY", "0");
            session.decision(TARGET, "Near#u2", 1, true, "(> M_A 1)");
            session.decision(TARGET, "Far#u4", 1, true, "(> M_B 1)");
            session.decision(TARGET, "Guard#u8", 1, false,
                    "(> (+ M_A M_READ_KEY) 3)");
            session.flush();
        }
        worker(iteration, "obligations-0000", "ob-later", "OBL.later",
                "s-later", TARGET, "Later#u20", NONE, NONE);
        Corpus corpus = Corpus.read(iteration, null);
        Task task = ClosurePlanner.taskOf(corpus,
                ClosurePlanner.taskId(TARGET));
        assertNotNull(task);
        String seed = dependence(corpus, task, "s-seed", "Guard#u8");
        assertEquals("a world's flip after the guard is no condition of its"
                + " arm", seed, dependence(corpus, task, "s-later",
                "Guard#u8"));
        assertFalse("a feeder that wrote another term where the guard reads"
                        + " is another world (M_A against 7)",
                seed.equals(dependence(corpus, task, "s-seven", "Guard#u8")));
        assertFalse("and another constant too (5 against 7)",
                dependence(corpus, task, "s-five", "Guard#u8").equals(
                        dependence(corpus, task, "s-seven", "Guard#u8")));
        assertEquals("the same term written again is the same world",
                dependence(corpus, task, "s-seven", "Guard#u8"),
                dependence(corpus, task, "s-seven-again", "Guard#u8"));
        assertFalse("M_A+10 against M_A-1 at one site re-keys (the review's"
                        + " scenario)",
                dependence(corpus, task, "s-plus", "Guard#u8").equals(
                        dependence(corpus, task, "s-minus", "Guard#u8")));
        assertEquals("the same canonical term in another session folds",
                dependence(corpus, task, "s-plus", "Guard#u8"),
                dependence(corpus, task, "s-plus-again", "Guard#u8"));
        assertFalse("a term reading a location another writer wrote "
                        + "re-keys",
                dependence(corpus, task, "s-inner-a", "Guard#u8").equals(
                        dependence(corpus, task, "s-inner-b", "Guard#u8")));
        assertEquals("a writer of the same class and site, the same value,"
                        + " folds",
                dependence(corpus, task, "s-inner-a", "Guard#u8"),
                dependence(corpus, task, "s-inner-a2", "Guard#u8"));
        assertEquals("a prefix decision over a root the guard never names "
                + "is not what it depends on", seed,
                dependence(corpus, task, "s-far", "Guard#u8"));
        assertEquals("nor are a factor member's writes to state the guard "
                + "does not read", seed,
                dependence(corpus, task, "s-noise", "Guard#u8"));
        assertTrue("a co-reader of the map is in the factor: "
                + task.factor(), task.factor().contains(READER));
        assertEquals("but it writes nothing the task reads, so what it "
                + "received is not the task's world", seed,
                dependence(corpus, task, "s-coreader", "Guard#u8"));
        assertFalse("a prefix decision over the guard's own root is",
                seed.equals(dependence(corpus, task, "s-near", "Guard#u8")));
        assertEquals("but not the same value written again where it reads"
                + " (semantic counts only)", seed,
                dependence(corpus, task, "s-more", "Guard#u8"));
        List<OccurrenceAddress> reversed =
                new ArrayList<OccurrenceAddress>(task.factor());
        Collections.reverse(reversed);
        Set<String> qopKey = Collections.singleton(
                SmtLowering.locationKey(qop));
        assertEquals("the factor is a set: the order the corpus lists it in "
                        + "moves as sessions land",
                corpus.inputShape("s-more", TARGET, task.factor(), qopKey,
                        NONE_STATED),
                corpus.inputShape("s-more", TARGET, reversed, qopKey,
                        NONE_STATED));
        Path raced = tree.newFolder("raced").toPath();
        for (String order : new String[] {"s-ab", "s-ba"}) {
            Session session = new Session(raced, order);
            session.activation(TARGET, true);
            session.activation(WRITER, false);
            Endpoint[] from = order.equals("s-ab")
                    ? new Endpoint[] {ROTATED, SENT}
                    : new Endpoint[] {SENT, ROTATED};
            for (Endpoint producer : from) {
                session.attach(DELIVERED, "M_HOFF_" + producer.id(), "1",
                        producer);
            }
            session.flush();
        }
        Corpus racedCorpus = Corpus.read(raced, null);
        assertEquals("who delivered is a set: the order replies arrive in "
                        + "is a race",
                racedCorpus.inputShape("s-ab", TARGET,
                        Collections.singletonList(WRITER), qopKey,
                        NONE_STATED),
                racedCorpus.inputShape("s-ba", TARGET,
                        Collections.singletonList(WRITER), qopKey,
                        NONE_STATED));
        Session late = new Session(iteration, "s-late");
        late.activation(lateWriter, false);
        late.symbolic("e.late", "M_A");
        late.write(at(lateWriter, Endpoint.stateSite("BlockTokenSecretManager",
                "addKeys", 12, true), "BlockTokenSecretManager#addKeys#12"),
                ALL_KEYS, 9L, "e.late");
        late.flush();
        Corpus grown = Corpus.read(iteration, null);
        Task later = ClosurePlanner.taskOf(grown, task.taskId());
        assertTrue("the corpus found a feeder: " + later.factor(),
                later.factor().contains(lateWriter));
        assertEquals("one the seed never ran re-keys none of its arms", seed,
                dependence(grown, later, "s-seed", "Guard#u8"));
        assertEquals("nor does one a session ran that delivered nothing"
                        + " (solr-bugs-reindex-cleanup SG1: 87 % of its"
                        + " re-keyed ids)", seed,
                dependence(grown, later, "s-idle", "Guard#u8"));
        ObligationFactory.Candidate located = ObligationFactory.locate(corpus,
                Obligation.of("OBL.as-the-wave-named-it", task.taskId(),
                        Corpus.pathId("s-seed", TARGET), "Guard#u8", 1, true,
                        NONE,
                        NONE,
                        Collections.<String>emptyList()));
        assertEquals("OBL.as-the-wave-named-it", located.obligationId);
    }

    @Test
    public void theClosureGrowsWhatItDemandsAndNoSessionCaptured()
            throws Exception {
        OccurrenceAddress lost = occurrence("hdfs-case/nn0",
                "ROLE.IPC_HANDLER", CausalContext.of(Role.of("IPC_HANDLER")),
                "o.a.h.ipc.Server$Handler#run#1");
        OccurrenceAddress anchored = occurrence("hdfs-case/nn0",
                "REGION.rotate", CausalContext.of("e-tick", "HADOOP_IPC"),
                "o.a.h.h.s.b.BlockManager#run#8");
        Object[][] cases = {
            {PRODUCER, true, false, -1, false},
            {PRODUCER, false, true, -1, false},
            {PRODUCER, false, true, 1, false},
            {PRODUCER, false, true, 0, true},
            {anchored, false, true, 1, true},
            {PRODUCER, false, false, -1, false},
            {lost, false, true, -1, false},
        };
        for (Object[] row : cases) {
            OccurrenceAddress producer = (OccurrenceAddress) row[0];
            boolean captured = (Boolean) row[1];
            boolean focused = (Boolean) row[2];
            int recorded = (Integer) row[3];
            boolean past = (Boolean) row[4];
            Path iteration = tree.newFolder().toPath();
            if (recorded >= 0) {
                List<JsonObject> ticks = new ArrayList<JsonObject>();
                ticks.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                        ScheduleEvent.Kind.PUBLISH, producer.node().render()
                                + "|VIEW", ScheduleEvent.published("SOLR_ZK",
                                "/collections/c/state.json", 3L), 0, "", "")));
                if (recorded > 0) {
                    ticks.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                            ScheduleEvent.Kind.WAKE, producer.node().render()
                                    + "|" + CausalContext.of(Role.of(
                                    "KEY_MANAGER_TICK"), "", recorded)
                                    .render(), "tick.KEY_MANAGER_TICK", 0,
                            "", "")));
                }
                RowCodec.writeJsonl(iteration.resolve(
                        "recorded_schedule.jsonl"), ticks);
            }
            Endpoint exported = at(producer, "XCH.resp.block-key-id",
                    "PBHelper#convert#9");
            for (String sessionId : focused
                    ? Arrays.asList("s-seed", "s-flip")
                    : Collections.singletonList("s-seed")) {
                Session session = new Session(iteration, sessionId);
                session.activation(TARGET, sessionId.equals("s-flip"));
                session.activation(WRITER, false);
                if (captured) session.activation(producer, false);
                session.symbolic("e.stored", "M_HOFF_KEY");
                session.attach(DELIVERED, "M_HOFF_KEY", "119992", exported);
                session.write(STORED, ALL_KEYS, 5L, "e.stored");
                session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
                session.anchored(TARGET);
                if (sessionId.equals("s-flip")) {
                    session.answered(ObligationResult.of("OBL.s-flip",
                            Verdict.ADMITTED, "s-flip",
                            "the focused prefix reproduced"));
                }
                session.flush();
                if (sessionId.equals("s-flip") && producer == anchored) {
                    RowCodec.writeJsonl(SessionDir.of(iteration, sessionId)
                            .schedule(), Collections.singletonList(
                            RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                                    ScheduleEvent.Kind.SEND, producer.node()
                                            .render() + "|" + CausalContext.of(
                                            Role.of("KEY_MANAGER_TICK"), "", 3)
                                            .render(), "HADOOP_IPC#REQUEST", 0,
                                    "", "e-tick"))));
                }
            }
            StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                    targetSite("REGION.target",
                            "BlockTokenSecretManager#u120")));
            ClosurePlanner.Plan plan = closure(Corpus.read(iteration, null),
                    TARGET, map);
            boolean task = false;
            for (Task planned : plan.tasks) {
                task |= planned.focused().equals(producer);
            }
            String lineage = "";
            for (GapRow gap : gapsOf(plan)) {
                if (!gap.subject().equals(producer.render())) continue;
                assertEquals("never BLOCKING while a session ran it: "
                        + gap.detail(), GapClass.DIAGNOSTIC, gap.cls());
                if (gap.kind() == GapKind.LINEAGE_LOST) lineage = gap.detail();
            }
            String label = producer.regionId() + " captured=" + captured
                    + " focused=" + focused + " recorded=" + recorded;
            String tick = "";
            for (GapRow gap : gapsOf(plan)) {
                if (gap.subject().equals(producer.render())
                        && gap.detail().contains("daemon tick")) {
                    tick = gap.detail();
                }
            }
            if (past) {
                assertFalse(label, task);
                assertTrue("a tick past the recording is not grown: " + label,
                        plan.exposed.isEmpty() && plan.waiting.isEmpty());
                assertFalse("and it says so: " + label, tick.isEmpty());
            } else if (captured) {
                assertTrue("a captured occurrence is a task: " + label, task);
                assertTrue(label, plan.exposed.isEmpty());
            } else if (producer.role()) {
                assertFalse(label, task);
                assertTrue("a role is no region to grow: " + label,
                        plan.exposed.isEmpty());
                assertFalse("the lost scope is named: " + label,
                        lineage.isEmpty());
            } else if (focused) {
                assertFalse("uncaptured is no task: " + label, task);
                assertEquals("grown from the focused replay naming it: "
                                + label, "s-flip",
                        plan.exposed.get(producer));
                JsonObject plannedRow = new JsonObject();
                plannedRow.addProperty("occurrenceId", producer.render());
                RowCodec.writeJsonl(iteration.resolve(
                        "execution_task_plan.jsonl"),
                        Collections.singletonList(plannedRow));
                Path wave = iteration.resolve("obligations-0000");
                Path results = iteration.resolve("results.jsonl");
                Files.write(results, new byte[0]);
                plan(iteration, TARGET_SELECTOR, null, results, wave, 0);
                assertTrue("a planned address grows no row: " + label,
                        RowCodec.readJsonl(wave.resolve(WaveGraph.GROWTH))
                                .isEmpty());
            } else {
                assertFalse(label, task);
                assertTrue("the seed replay is not re-run: " + label,
                        plan.exposed.isEmpty());
                assertTrue("it waits for a focused replay: " + label,
                        plan.waiting.contains(producer));
                Path wave = iteration.resolve("obligations-0000");
                Path results = iteration.resolve("results.jsonl");
                Files.write(results, new byte[0]);
                assertEquals("FIXED_POINT", plan(iteration, TARGET_SELECTOR,
                        null, results, wave, 0).get("state").getAsString());
                assertTrue("so at the fixpoint the closure is incomplete",
                        anyGap(wave, gap -> gap.cls() == GapClass.BLOCKING
                                && gap.subject().equals(producer.render())));
            }
        }
    }

    private static String dependence(Corpus corpus, Task task,
                                     String sessionId, String siteId)
            throws IOException {
        for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
            if (!path.sessionId.equals(sessionId)) continue;
            for (int index = 0; index < path.decisions.size(); index++) {
                if (path.decisions.get(index).siteId().equals(siteId)) {
                    return ObligationFactory.dependence(corpus, task, path,
                            index);
                }
            }
        }
        throw new AssertionError(sessionId + " took no " + siteId);
    }

    @Test
    public void aRefutedWorldIsExcludedAndTheArmAskedAgain() throws Exception {
        Assume.assumeTrue(z3Available());
        String helper = "State#u2";
        Path iteration = tree.newFolder("refuted-arm").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.integral(TARGET, "CASE.SERIAL", "M_SERIAL", "7", "7", "11");
        seed.decision(TARGET, helper, 1, false, "(> M_SERIAL 10)");
        seed.targets.add(TargetRow.of("s-seed", 99L, TARGET, "Throw#u30",
                "false", false, true, TargetRow.OpenArm.of(helper, 1, true,
                        helper, 1)));
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u9"));
        Corpus corpus = Corpus.read(iteration, null);
        assertTrue("a flip toward the open arm runs it",
                corpus.openArmFlip(TARGET, helper, 1, true));
        assertFalse("the same decision flipped away from it is ordinary",
                corpus.openArmFlip(TARGET, helper, 1, false));
        Path out = tree.newFolder("refuted-arm-out").toPath();
        Path results = out.resolve("results.jsonl");
        Files.write(results, new byte[0]);
        plan(iteration, TARGET_SELECTOR, null, results,
                out.resolve("obligations-0000"), 0);
        Obligation asked = obligations(out.resolve("obligations-0000"))
                .get(0);
        Worker first = solve(iteration, out.resolve("obligations-0000"),
                asked, out, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, first.verdict);
        assertEquals("the one world that takes it",
                "11", first.obligation.rootAssignments().get("CASE.SERIAL"));
        ObligationResult refuted = ObligationResult.of(asked.obligationId(),
                Verdict.NOT_ADMITTED, "s-flip", "WORLD_REFUTED: never entered",
                edu.uva.liftlab.graphchecker.contract.WorldRefutation.of(
                        Arrays.asList("(a)", "(b)", "(c)", "(d)"),
                        "java.io.IOException: closed", "A.close(A.java:9)",
                        "T.test(T.java:3)"));
        Path landed = iteration.resolve("obligations-0000")
                .resolve(asked.obligationId());
        Files.createDirectories(landed);
        Files.copy(first.directory.resolve(ObligationDir.FOCUSED_TASK),
                landed.resolve(ObligationDir.FOCUSED_TASK));
        Files.copy(first.directory.resolve(ObligationDir.QUESTION_ASKED),
                landed.resolve(ObligationDir.QUESTION_ASKED));
        record(landed.resolve(ObligationDir.RESULT), refuted);
        record(results, refuted);
        JsonObject again = plan(iteration, TARGET_SELECTOR, null, results,
                out.resolve("obligations-0001"), 1);
        List<Obligation> reasked = obligations(out.resolve("obligations-0001"));
        assertEquals("asked again: " + reasked, 1, reasked.size());
        JsonObject arm = again.getAsJsonArray("openArms").get(0)
                .getAsJsonObject();
        assertEquals("PENDING", arm.get("state").getAsString());
        JsonArray worlds = arm.getAsJsonArray("refutedWorlds");
        assertEquals("named: " + arm, 1, worlds.size());
        assertEquals("java.io.IOException: closed", worlds.get(0)
                .getAsJsonObject().get("exception").getAsString());
        Worker second = solve(iteration, out.resolve("obligations-0001"),
                reasked.get(0), out, "w1");
        assertEquals("no other world takes the arm", Verdict.UNSAT,
                second.verdict);
        String query = queryText(second.directory);
        assertTrue(query, query.contains("; refuted world "
                + worlds.get(0).getAsJsonObject().get("world")
                .getAsString()));
        ObligationResult closed = RowCodec.readAll(second.directory
                .resolve(ObligationDir.RESULT), RowCodec::readObligationResult)
                .get(0);
        assertTrue(closed.detail(), closed.detail().contains(
                "rests: " + worlds.get(0).getAsJsonObject().get("world")
                        .getAsString()));
        record(results, closed);
        Path closing = iteration.resolve("obligations-0001")
                .resolve(closed.obligationId());
        Files.createDirectories(closing);
        Files.copy(second.directory.resolve(ObligationDir.QUESTION),
                closing.resolve(ObligationDir.QUESTION));
        record(closing.resolve(ObligationDir.RESULT), closed);
        JsonObject last = plan(iteration, TARGET_SELECTOR, null, results,
                out.resolve("obligations-0002"), 2);
        JsonObject named = last.getAsJsonArray("openArms").get(0)
                .getAsJsonObject();
        assertEquals("UNSAT", named.get("state").getAsString());
        assertEquals(1, named.getAsJsonArray("refutedWorlds").size());
    }

    private static JsonObject leaf(String symbol, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", symbol);
        node.addProperty("_java_type", javaType);
        return node;
    }

    private static JsonObject literal(long value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_java_type", "I");
        node.addProperty("_exp", "Y_I_" + value);
        return node;
    }

    private static JsonObject binary(String operator, JsonObject left,
                                     JsonObject right) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", operator);
        node.add("_left", left);
        node.add("_right", right);
        return node;
    }

    private static JsonObject guardedRead(LocationId location, long version,
                                          String javaType,
                                          JsonObject projection) {
        return guardedRead(location, version, javaType, projection, -1L);
    }

    private static JsonObject guardedRead(LocationId location, long version,
                                          String javaType,
                                          JsonObject projection,
                                          long readEventId) {
        JsonObject read = readNode(location, version, javaType, projection);
        if (readEventId >= 0) read.addProperty("readEventId", readEventId);
        return read;
    }

    private static JsonObject readNode(LocationId location, long version,
                                       String javaType,
                                       JsonObject projection) {
        JsonObject where = new JsonObject();
        where.addProperty("locationKind", location.kind().name());
        where.addProperty("ownerSymRid", location.owner());
        where.addProperty("slot", location.slot());
        JsonObject observed = new JsonObject();
        observed.addProperty("fieldVersionId", version);
        observed.addProperty("versionKind", "STATE_PUT");
        if (projection != null) observed.add("expression", projection);
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ReadFromExpression");
        node.addProperty("_java_type", javaType);
        node.addProperty("expressionAuthority", "VM_GUARDED_READ_FROM_V1");
        node.add("location", where);
        node.add("observedVersion", observed);
        return node;
    }

    @Test
    public void onlyAWholeAnswerIsKept() throws Exception {
        List<String> asks = Arrays.asList("x", "y");
        String q = "(declare-const x Int)\n(declare-const y Int)\n";
        for (Object[] row : new Object[][]{
                {"unsat", "", true},
                {"sat", "x y", true},
                {"sat", "x", false},
                {"sat", "", false}}) {
            Map<String, String> values = new LinkedHashMap<String, String>();
            for (String symbol : ((String) row[1]).split(" ")) {
                if (!symbol.isEmpty()) values.put(symbol, "1");
            }
            Z3.Answer z3 = Z3.Answer.decided((String) row[0], values);
            Solved solved = Solved.in(tree.newFolder().toPath());
            assertSame(z3, solved.answer(q, asks, () -> z3));
            int[] runs = {0};
            solved.answer(q, asks, () -> {
                runs[0]++;
                return z3;
            });
            assertEquals(Arrays.toString(row), row[2], runs[0] == 0);
        }
        Z3.Answer unsat = Z3.Answer.decided("unsat",
                Collections.<String, String>emptyMap());
        Solved unwritable = Solved.at(tree.newFile("a-file").toPath()
                .resolve(Solved.DIR));
        assertSame(unsat, unwritable.answer(q, asks, () -> unsat));
    }

    @Test
    public void aQueryIsAnsweredForEveryRenamingOfItsNames() throws Exception {
        String asked = "; task A path P session S1\n(set-logic ALL)\n"
                + "(declare-fun x__aa () Int)\n(declare-fun y__bb () Int)\n"
                + "(declare-fun s__cc () String)\n(define-fun d__dd () Int"
                + " (+ x__aa 1))\n(assert (> x__aa 41))\n(assert (= y__bb"
                + " d__dd))\n(assert (= s__cc \"x__aa\"))\n(assert (not (="
                + " nullRef (string_ref s__cc))))\n(check-sat)\n(get-value"
                + " ( x__aa y__bb s__cc))\n";
        String renamed = asked.replace("; task A path P session S1",
                "; task B path Q session S2\n; x__ee = a root")
                .replace("x__aa ", "x__ee ").replace("x__aa)", "x__ee)")
                .replace("y__bb", "y__ff").replace("s__cc", "s__gg")
                .replace("d__dd", "d__hh").replace("\n(assert", "\n\n(assert");
        assertTrue(renamed, renamed.contains("\"x__aa\""));
        String[] others = {
                asked.replace("41", "40"),
                asked.replace("\"x__aa\"", "\"x__ee\""),
                asked.replace("(assert (> x__aa 41))", "(assert (> y__bb 41))"),
        };
        assertEquals(Solved.Key.of(asked).sha256,
                Solved.Key.of(renamed).sha256);
        for (String other : others) {
            assertNotEquals(other, Solved.Key.of(asked).sha256,
                    Solved.Key.of(other).sha256);
        }
        assertFalse(Solved.Key.of(asked).names.containsKey("nullRef"));
        Map<String, String> values = new LinkedHashMap<String, String>();
        values.put("x__aa", "42");
        values.put("y__bb", "43");
        values.put("s__cc", "\"x__aa\"");
        Z3.Answer sat = Z3.Answer.decided("sat", values);
        Solved solved = Solved.in(tree.newFolder().toPath());
        assertSame(sat, solved.answer(asked, Arrays.asList("x__aa", "y__bb",
                "s__cc"), () -> sat));
        Z3.Answer again = solved.answer(renamed, Arrays.asList("x__ee",
                "y__ff", "s__gg"), () -> {
            throw new AssertionError("a renaming of a kept query ran z3");
        });
        assertEquals("sat", again.status());
        assertEquals("42", again.values().get("x__ee"));
        assertEquals("43", again.values().get("y__ff"));
        assertEquals("\"x__aa\"", again.values().get("s__gg"));
        int[] runs = {0};
        solved.answer(others[0], Arrays.asList("x__aa", "y__bb", "s__cc"),
                () -> {
                    runs[0]++;
                    return sat;
                });
        assertEquals(1, runs[0]);
        Map<String, String> naming = new LinkedHashMap<String, String>();
        naming.put("x", "(+ y 1)");
        Z3.Answer namesAnother = Z3.Answer.decided("sat", naming);
        String twoNames = "(declare-const x Int)\n(declare-const y Int)\n";
        solved.answer(twoNames, Arrays.asList("x"), () -> namesAnother);
        runs[0] = 0;
        solved.answer(twoNames, Arrays.asList("x"), () -> {
            runs[0]++;
            return namesAnother;
        });
        assertEquals("a model value naming the query's own symbols is not"
                + " kept", 1, runs[0]);
    }

    @Test
    public void aQueryTextIsAnsweredOnceWhateverAsksIt() throws Exception {
        Assume.assumeTrue(z3Available());
        Object[][] rows = {
                {"(= M_READ_KEY 2)", Verdict.SAT_MODEL_READY},
                {"(and (= M_READ_KEY 2) (= M_READ_KEY 3))", Verdict.UNSAT},
        };
        int at = 0;
        for (Object[] row : rows) {
            String name = "solver-key-" + at++;
            Path iteration = twoWriters(name, (String) row[0], null);
            Path out = tree.newFolder(name + "-out").toPath();
            Path wave0 = out.resolve("obligations-0000");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave0, 0);
            Obligation lookup = named(obligations(wave0), "Lookup#u8");
            Corpus corpus = Corpus.read(iteration, null);
            ObligationFactory.Candidate candidate =
                    ObligationFactory.locate(corpus, lookup);
            Solved solved = Solved.in(iteration);
            Map<String, ObligationDir.Answer> none =
                    Collections.<String, ObligationDir.Answer>emptyMap();
            ObligationFactory.Outcome asked = corpus.asking(() ->
                    ObligationFactory.solve(corpus, candidate, new Z3(
                            Paths.get("z3"), 10_000L, 1152), solved,
                            "plan A", none, null));
            assertEquals(name + ": " + asked.result.detail(), row[1],
                    asked.result.verdict());
            Path kept = solved.dir().resolve(
                    Solved.Key.of(asked.smt2).sha256 + ".json");
            assertTrue(name + ": kept by its text", Files.exists(kept));
            ObligationFactory.Outcome again = corpus.asking(() ->
                    ObligationFactory.solve(corpus, candidate, new Z3(
                            Paths.get("no-z3-here"), 10_000L, 1152), solved,
                            "plan B", none, null));
            assertFalse(name, asked.question.equals(again.question));
            assertEquals(name, RowCodec.writeObligationResult(asked.result),
                    RowCodec.writeObligationResult(again.result));
            assertEquals(name, asked.obligation, again.obligation);
            assertEquals(name, asked.smt2, again.smt2);
            assertEquals(name, asked.settles, again.settles);
            Files.delete(kept);
            Path silent = tree.newFile(name + "-silent-z3").toPath();
            Files.write(silent, "#!/bin/sh\nexec sleep 60\n"
                    .getBytes(StandardCharsets.UTF_8));
            assertTrue(silent.toFile().setExecutable(true));
            ObligationFactory.Outcome timedOut = corpus.asking(() ->
                    ObligationFactory.solve(corpus, candidate, new Z3(
                            silent, 300L, 1152), solved, "plan C",
                            none, null));
            assertTrue(name + ": " + timedOut.result.detail(),
                    timedOut.result.detail().startsWith("SOLVER_TIMEOUT"));
            assertFalse(name, Files.exists(kept));
        }
    }

    @Test
    public void aRootTheSeedDoesNotMintIsPlantedAtThePathSessionsMint()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Object[][] rows = {
            {false, TARGET},
            {true, WRITER},
        };
        int at = 0;
        for (Object[] row : rows) {
            String name = "path-mint-" + at++;
            Path iteration = tree.newFolder(name).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activations(false, TARGET, WRITER);
            if ((Boolean) row[0]) {
                seed.marker(WRITER, "REGION.target.in.door", "M_DOOR",
                        "false");
            }
            seed.decision(TARGET, "Door#u4", 1, true, "");
            seed.flush();
            Session rerun = new Session(iteration, "s-rerun");
            rerun.activation(TARGET, true);
            rerun.marker(TARGET, "REGION.target.in.door", "M_DOOR", "false");
            rerun.decision(TARGET, "Door#u4", 1, true, "(not M_DOOR)");
            rerun.answered(ObligationResult.of("OBL.s-rerun",
                    Verdict.ADMITTED, "s-rerun", "the exposing re-run"));
            rerun.flush();
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Door#u4"));
            Path out = tree.newFolder(name + "-out").toPath();
            Path wave0 = out.resolve("obligations-0000");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave0, 0);
            Obligation door = named(obligations(wave0), "Door#u4");
            assertNotNull(name, door);
            Corpus corpus = Corpus.read(iteration, null);
            ObligationFactory.Candidate candidate =
                    ObligationFactory.locate(corpus, door);
            ObligationFactory.Outcome asked = corpus.asking(() ->
                    ObligationFactory.solve(corpus, candidate, new Z3(
                            Paths.get("z3"), 10_000L, 1152),
                            Solved.in(iteration), "plan", Collections
                                    .<String, ObligationDir.Answer>emptyMap(),
                            null));
            String said = name + ": " + asked.result.detail();
            assertEquals(said, Verdict.SAT_MODEL_READY,
                    asked.result.verdict());
            assertEquals(said, ((OccurrenceAddress) row[1]).render(),
                    asked.rootMints.get("REGION.target.in.door"));
        }
    }

    @Test
    public void aConstantGuardBesideAMintedBoxIsNotFlippable()
            throws Exception {
        LocationId header = LocationId.of(LocationKind.INSTANCE, "31", "20");
        LocationId box = LocationId.of(LocationKind.INSTANCE, "32", "24");
        Object[][] rows = {
            {7L, Verdict.UNSAT, FlipQuery.NOT_FLIPPABLE + ":Lookup#u8#1"},
            {8L, Verdict.NOT_ADMITTED, "ADMISSION_GAP:Lookup#u8#1"}};
        int at = 0;
        for (Object[] row : rows) {
            String name = "minted-box-" + at++;
            Path iteration = tree.newFolder(name).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activations(false, TARGET);
            seed.constant("e.0", "0");
            seed.initial(at(TARGET, Endpoint.initialSite(Endpoint.stateSite(
                    "Request", "<init>", 3, true)), "Request#init#3"),
                    header, 5L, "e.0");
            long throttled = seed.read(at(TARGET, Endpoint.stateSite(
                    "Request", "isThrottled", 4, false),
                    "Request#isThrottled#4"), header, 5L, "M_THROTTLED", "0");
            seed.expression("EXPR.00000000000000a1", binary("==", guardedRead(header,
                    5L, "I", literal(0), throttled), literal(1)));
            seed.mint(at(TARGET, "INSTANCE_FIELD/32#24#PLACEHOLDER#0:READ",
                    "Prep#pRequest2Txn#10"), box, 7L, "M_CLOCK", "123");
            seed.root(TARGET, "REGION.target.in.clock", "M_CLOCK",
                    RootKind.CLOCK, "123", null, null, true);
            seed.read(at(TARGET, Endpoint.stateSite("java.lang.Long",
                    "longValue", 1, false), "Long#longValue#1"), box,
                    (Long) row[0], "M_UNBOXED", "123");
            seed.decision(TARGET, "Lookup#u8", 1, false, "EXPR.00000000000000a1");
            seed.flush();
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Lookup#u8"));
            Path out = tree.newFolder(name + "-out").toPath();
            Path wave0 = out.resolve("obligations-0000");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave0, 0);
            Obligation lookup = named(obligations(wave0), "Lookup#u8");
            Corpus corpus = Corpus.read(iteration, null);
            ObligationFactory.Candidate candidate =
                    ObligationFactory.locate(corpus, lookup);
            ObligationFactory.Outcome asked = corpus.asking(() ->
                    ObligationFactory.solve(corpus, candidate, new Z3(
                            Paths.get("no-z3-here"), 10_000L, 1152),
                            Solved.in(iteration), "plan", Collections
                                    .<String, ObligationDir.Answer>emptyMap(),
                            null));
            String said = name + ": " + asked.result.detail();
            assertEquals(said, row[1], asked.result.verdict());
            assertTrue(said, asked.result.detail().contains((String) row[2]));
        }
    }

    @Test
    public void onlyAFaithfulNotAdmittedSettlesTheArm() throws Exception {
        String ran = ObligationResult.WORLD_RAN + ": occurrence o never"
                + " reached Lookup#u8#1 in this replay, and the world it ran"
                + " was the one asked";
        String unrun = "occurrence o never reached Lookup#u8#1 in this"
                + " replay; its world did not run: the inherited root R was"
                + " never minted";
        String atArm = ObligationResult.ARM_REFUSED + ": the query was"
                + " refused: ADMISSION_GAP:Lookup#u8#1";
        String inWorld = "the query was refused: ADMISSION_GAP:Rotate#u5#1";
        String killed = ObligationResult.REPLAY_BOUNDED + ": replay exceeded"
                + " replay_timeout_s=2400";
        String memout = "SOLVER_MEMOUT at 1984 MB";
        Object[][] rows = {
            {ran, 1, true, false, false},
            {unrun, 1, false, true, false},
            {unrun, 2, false, false, false},
            {atArm, 1, true, false, false},
            {inWorld, 1, false, true, false},
            {memout, 1, false, true, false},
            {killed, 1, false, true, false},
            {new String[] {killed, unrun}, 2, false, true, false},
            {killed, 2, false, false, true},
        };
        int at = 0;
        for (Object[] row : rows) {
            String name = "faithful-" + at++;
            Path iteration = twoWriters(name, "(= M_READ_KEY 2)", null);
            Path out = tree.newFolder(name + "-out").toPath();
            Path results = out.resolve("results.jsonl");
            plan(iteration, TARGET_SELECTOR, null, results,
                    out.resolve("obligations-0000"), 0);
            Obligation lookup = named(obligations(
                    out.resolve("obligations-0000")), "Lookup#u8");
            String flip = ObligationFactory.flip(lookup.taskId(),
                    lookup.pathId(), lookup.siteId(), lookup.ordinal(),
                    lookup.flippedOutcome());
            String[] details = row[0] instanceof String[]
                    ? (String[]) row[0] : new String[] {(String) row[0]};
            ObligationResult answer = ObligationResult.of(
                    lookup.obligationId(), Verdict.NOT_ADMITTED, "",
                    details[0]);
            record(results, answer);
            for (int k = 0; k < (Integer) row[1]; k++) {
                answer(iteration, "OB." + k, ObligationDir.QUESTION,
                        flip + ":content", Verdict.NOT_ADMITTED, "",
                        details[Math.min(k, details.length - 1)]);
                RowCodec.writeAll(iteration.resolve("obligations-0000")
                                .resolve("OB." + k)
                                .resolve(ObligationDir.OBLIGATION),
                        Collections.singletonList(lookup),
                        ExploreCodec::writeObligation);
            }
            Frontier frontier = new Frontier(Corpus.read(iteration, null),
                    Collections.<Task>emptyList(),
                    Collections.<String, Set<String>>emptyMap());
            frontier.consume(Collections.singletonList(answer),
                    ExploreMain.answersByFlip(iteration));
            assertEquals(name + ": the arm settled for every world",
                    row[2], !frontier.settled(lookup.obligationId())
                            .isEmpty());
            assertEquals(name + ": the flip held BOUNDED",
                    row[4], frontier.boundedFlips().contains(flip));
            Path next = out.resolve("obligations-0001");
            JsonObject manifest = plan(iteration, TARGET_SELECTOR, null,
                    results, next, 1);
            assertEquals(name + ": the flip asked again from its path",
                    row[3], named(obligations(next), "Lookup#u8") != null);
            assertEquals(name + ": the round names it", (Boolean) row[4]
                    ? "[Lookup#u8 x2]" : "[]",
                    names(manifest.getAsJsonArray("boundedFlips")));
        }
    }

    private static String names(JsonArray bounded) {
        List<String> names = new ArrayList<String>();
        for (JsonElement element : bounded) {
            JsonObject row = element.getAsJsonObject();
            names.add((row.has("force") ? "FORCE"
                    : row.get("siteId").getAsString()) + " x"
                    + row.getAsJsonArray("killed").size());
        }
        return names.toString();
    }

    private static void answer(Path iteration, String obligationId,
                               String questionFile, String question,
                               Verdict verdict, String sessionId,
                               String detail) throws IOException {
        Path worker = Files.createDirectories(iteration.resolve(
                "obligations-0000").resolve(obligationId));
        Files.write(worker.resolve(questionFile),
                (question + "\n").getBytes(StandardCharsets.UTF_8));
        Files.write(worker.resolve(ObligationDir.RESULT),
                (RowCodec.toLine(RowCodec.writeObligationResult(
                        ObligationResult.of(obligationId, verdict,
                                sessionId, detail))) + "\n")
                        .getBytes(StandardCharsets.UTF_8));
    }

    private static final String VM_LOOKUP = "EXPR.0000000000000002";
    private static final LocationId KEY_ID =
            LocationId.of(LocationKind.INSTANCE, "21", "40");

    private Path twoWriters(String name, String term, String limit)
            throws IOException {
        return twoWriters(name, term, limit, "I");
    }

    private Path twoWriters(String name, String term, String limit,
                            String secondType) throws IOException {
        return twoWriters(name, term, limit, secondType, 6L);
    }

    private Path twoWriters(String name, String term, String limit,
                            String secondType, long seen)
            throws IOException {
        Path iteration = tree.newFolder(name).toPath();
        OccurrenceAddress again = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.of("KEY_UPDATE"), "",
                        2), "o.a.h.h.s.d.BPServiceActor#offerService#41");
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, WRITER);
        seed.activation(again, false, true, "fixture#key-updater");
        seed.constant("e.1", "1");
        if ("Z".equals(secondType)) {
            seed.expression("e.2", binary("==", literal(2), literal(2)));
        } else {
            seed.constant("e.2", "2");
        }
        seed.write(STORED, KEY_ID, 5L, "e.1");
        seed.write(at(again, Endpoint.stateSite("BlockTokenSecretManager",
                "addKeys", 12, true), "BlockTokenSecretManager#addKeys#12"),
                KEY_ID, 6L, "e.2");
        seed.read(LOOKED_UP, KEY_ID, 5L, "M_READ_KEY", "1");
        seed.read(at(TARGET, Endpoint.stateSite("BlockTokenSecretManager",
                "retrieveDataEncryptionKey", 9, false),
                "BlockTokenSecretManager#retrieveDataEncryptionKey#9"),
                KEY_ID, seen, "M_READ_AGAIN", "2");
        seed.expression(VM_LOOKUP, binary("==", readNode(KEY_ID, 5L, "I",
                literal(1)), literal(2)));
        if (limit != null) {
            seed.integral(TARGET, "CASE.LIMIT", "M_LIMIT", limit, "0", "10");
        }
        seed.decision(TARGET, "Lookup#u8", 1, false, term);
        seed.flush();
        scopeMap(iteration,
                targetSite("REGION.target", "Throw#u30", "Lookup#u8"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""));
        return iteration;
    }

    private static String detail(Worker worker) throws IOException {
        List<ObligationResult> rows = RowCodec.readAll(
                worker.directory.resolve("obligation_result.jsonl"),
                RowCodec::readObligationResult);
        return rows.isEmpty() ? "" : rows.get(0).detail();
    }

    private static String query(Worker worker) throws IOException {
        return queryText(worker.directory);
    }

    private static String queryText(Path worker) throws IOException {
        java.io.ByteArrayOutputStream text = new java.io.ByteArrayOutputStream();
        try (java.io.InputStream in = ArtifactIO.input(
                worker.resolve(ObligationSolverMain.QUERY))) {
            byte[] buffer = new byte[1 << 16];
            for (int read; (read = in.read(buffer)) > 0; ) {
                text.write(buffer, 0, read);
            }
        }
        return new String(text.toByteArray(), StandardCharsets.UTF_8);
    }


    private JsonObject plan(Path iteration, String selector, Path domains,
                            Path results, Path roundDir, int round)
            throws IOException {
        return ExploreMain.plan(iteration, selector, domains, results, null,
                iteration.resolve(StaticScopeMap.FILE), roundDir, round,
                "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                DEFAULT_BOUNDS);
    }

    private static JsonObject plan(Path iteration, Path results,
            Path inFlight, Path roundDir, int round,
            ObligationFactory.Bounds bounds) throws IOException {
        return ExploreMain.plan(iteration, TARGET_SELECTOR, null, results,
                inFlight, iteration.resolve(StaticScopeMap.FILE), roundDir,
                round, "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS, bounds);
    }

    private static ObligationFactory.Bounds bounds(int maxPaths,
                                                   int maxDepth) {
        return new ObligationFactory.Bounds(maxPaths,
                ObligationFactory.DEFAULT_MAX_FLIPS_PER_PATH, maxDepth);
    }

    @Test
    public void theWalkAheadPlansWhatItPlansAlone() throws Exception {
        Path iteration = tree.newFolder("asked-ahead").toPath();
        Endpoint other = at(PRODUCER, "XCH.resp.block-key-expiry",
                "PBHelper#convert#12");
        Endpoint side = at(TARGET, Endpoint.stateSite(
                "BlockTokenSecretManager", "retrieveDataEncryptionKey", 9,
                false), "BlockTokenSecretManager#retrieveDataEncryptionKey#9");
        for (int at = 0; at < 70; at++) {
            String sessionId = at == 0 ? "s-seed" : "s-" + at;
            Session session = new Session(iteration, sessionId);
            session.activations(false, TARGET, WRITER, PRODUCER);
            session.constant("e.11999" + at, "11999" + at);
            session.symbolic("e.stored", "M_HOFF_KEY");
            session.export(other, "e.11999" + at, 11L + at, "11999" + at);
            session.attach(DELIVERED, "M_HOFF_KEY", "11999" + at, other);
            session.write(STORED, ALL_KEYS, 5L, "e.stored");
            session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY" + at,
                    "11999" + at);
            session.seq--;
            session.read(side, LocationId.of(LocationKind.MAP, "" + (40 + at),
                    "-3"), 0L, "M_SIDE" + at, "0");
            session.target(TARGET, "BlockTokenSecretManager"
                    + "#retrieveDataEncryptionKey#8", "(and (= M_READ_KEY"
                    + at + " 0) (= M_SIDE" + at + " 0))");
            session.flush();
        }
        StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                targetSite("REGION.target", "BlockTokenSecretManager#u120")));
        List<String> plans = onEachPool(iteration, map);
        assertTrue("the producer and the writer are planned: "
                + plans.get(0), plans.get(0).contains(
                ClosurePlanner.taskId(PRODUCER))
                && plans.get(0).contains(ClosurePlanner.taskId(WRITER)));
        assertEquals("on four cores, the one-core plan", plans.get(0),
                plans.get(1));
        assertEquals("on the host's cores, the one-core plan",
                plans.get(0), plans.get(2));
    }

    @Test
    public void aStepWhoseDemandChangedIsWalkedAgain() throws Exception {
        Path iteration = tree.newFolder("walked-again").toPath();
        OccurrenceAddress w1 = occurrence("hdfs-case/dn0", "REGION.w1",
                CausalContext.of(Role.of("RV_W1"), "", 1), "o.a.Rv#w1#1");
        OccurrenceAddress w2 = occurrence("hdfs-case/dn0", "REGION.w2",
                CausalContext.of(Role.of("RV_W2"), "", 1), "o.a.Rv#w2#1");
        OccurrenceAddress w4 = occurrence("hdfs-case/dn0", "REGION.w4",
                CausalContext.of(Role.of("RV_W4"), "", 1), "o.a.Rv#w4#1");
        OccurrenceAddress w5 = occurrence("hdfs-case/dn1", "REGION.w5",
                CausalContext.of(Role.of("RV_W5"), "", 1), "o.a.Rv#w5#1");
        OccurrenceAddress w6 = occurrence("hdfs-case/dn1", "REGION.w6",
                CausalContext.of(Role.of("RV_W6"), "", 1), "o.a.Rv#w6#1");
        OccurrenceAddress w7 = occurrence("hdfs-case/dn1", "REGION.w7",
                CausalContext.of(Role.of("RV_W7"), "", 1), "o.a.Rv#w7#1");
        OccurrenceAddress w8 = occurrence("hdfs-case/dn2", "REGION.w8",
                CausalContext.of(Role.of("RV_W8"), "", 1), "o.a.Rv#w8#1");
        LocationId a = LocationId.of(LocationKind.MAP, "51", "a");
        LocationId b = LocationId.of(LocationKind.MAP, "52", "b");
        LocationId e = LocationId.of(LocationKind.MAP, "54", "e");
        LocationId f = LocationId.of(LocationKind.MAP, "55", "f");
        Endpoint wroteE = at(w5, Endpoint.stateSite("Rv", "w5", 3, true),
                "Rv#w5#3");
        Endpoint readE = at(w4, Endpoint.stateSite("Rv", "w4", 4, false),
                "Rv#w4#4");
        Endpoint wroteF = at(w6, Endpoint.stateSite("Rv", "w6", 3, true),
                "Rv#w6#3");
        Endpoint readF = at(w2, Endpoint.stateSite("Rv", "w2", 6, false),
                "Rv#w2#6");
        Endpoint wroteA = at(w7, Endpoint.stateSite("Rv", "w7", 3, true),
                "Rv#w7#3");
        Endpoint x8 = at(w8, "XCH.resp.rv8", "Rv#x8#1");
        Endpoint r8 = at(w7, "XCH.resp.rv8", "Rv#r8#1");
        Endpoint readA = at(w1, Endpoint.stateSite("Rv", "w1", 5, false),
                "Rv#w1#5");
        Endpoint readB = at(w2, Endpoint.stateSite("Rv", "w2", 5, false),
                "Rv#w2#5");
        Endpoint x1 = at(w1, "XCH.resp.rv1", "Rv#x1#1");
        Endpoint x2 = at(w2, "XCH.resp.rv2", "Rv#x2#1");
        Endpoint x4 = at(w4, "XCH.resp.rv4", "Rv#x4#1");
        Endpoint x4b = at(w4, "XCH.resp.rv4b", "Rv#x4b#1");
        Endpoint t1 = at(TARGET, "XCH.resp.rv1", "Rv#t1#1");
        Endpoint t2 = at(TARGET, "XCH.resp.rv2", "Rv#t2#1");
        Endpoint t4 = at(TARGET, "XCH.resp.rv4", "Rv#t4#1");
        Endpoint r4b = at(w1, "XCH.resp.rv4b", "Rv#r4b#1");
        for (int at = 0; at < 70; at++) {
            String sessionId = at == 0 ? "s-seed" : "s-" + at;
            Session session = new Session(iteration, sessionId);
            session.activations(false, TARGET, w1, w2, w4, w5, w6, w7, w8);
            session.constant("e.w5", "5" + at);
            session.constant("e.w8", "8" + at);
            session.symbolic("e.a", "M_P" + at);
            session.constant("e.w6", "6" + at);
            session.constant("e.h4", "4" + at);
            session.symbolic("e.h4b", "M_Q" + at);
            session.symbolic("e.h1", "M_C" + at);
            session.symbolic("e.h2", "M_B" + at);
            session.write(wroteE, e, 1L, "e.w5");
            session.write(wroteF, f, 1L, "e.w6");
            session.read(readE, e, 1L, "M_Q" + at, "5" + at);
            session.export(x4b, "e.h4b", 30L + at, "5" + at);
            session.export(x4, "e.h4", 40L + at, "4" + at);
            session.attach(r4b, "M_C" + at, "5" + at, x4b);
            session.export(x8, "e.w8", 50L + at, "8" + at);
            session.attach(r8, "M_P" + at, "8" + at, x8);
            session.write(wroteA, a, 1L, "e.a");
            session.read(readA, a, 1L, "M_A" + at, "8" + at);
            session.seq--;
            session.read(readB, b, 0L, "M_B" + at, "0");
            session.read(readF, f, 1L, "M_A" + at, "6" + at);
            session.export(x1, "e.h1", 10L + at, "5" + at);
            session.export(x2, "e.h2", 20L + at, "0");
            session.attach(t1, "M_H1", "5" + at, x1);
            session.attach(t2, "M_H2", "0", x2);
            session.attach(t4, "M_H4", "4" + at, x4);
            session.target(TARGET, "BlockTokenSecretManager"
                    + "#retrieveDataEncryptionKey#8",
                    "(and (= M_H1 0) (= M_H2 0) (= M_H4 0))");
            session.flush();
        }
        StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                targetSite("REGION.target", "BlockTokenSecretManager#u120")));
        List<String> plans = onEachPool(iteration, map);
        assertTrue("W4 grown reads e, which W5 wrote: " + plans.get(0),
                plans.get(0).contains(ClosurePlanner.taskId(w5)));
        assertTrue("W2's delivery rests on the leaves W1's row gave the"
                + " seq, which name f, which W6 wrote: " + plans.get(0),
                plans.get(0).contains(ClosurePlanner.taskId(w6)));
        assertEquals("on four cores, the one-core plan", plans.get(0),
                plans.get(1));
        assertEquals("on the host's cores, the one-core plan",
                plans.get(0), plans.get(2));
    }

    @Test
    public void aStepNeverIndexesAGroup() throws Exception {
        Path iteration = tree.newFolder("indexed-ahead").toPath();
        List<OccurrenceAddress> producers = new ArrayList<OccurrenceAddress>();
        StringBuilder phi = new StringBuilder("(and");
        for (int at = 1; at <= 12; at++) {
            producers.add(occurrence("hdfs-case/dn" + at, "REGION.p" + at,
                    CausalContext.of(Role.of("RV_P" + at), "", 1),
                    "o.a.Rv#p" + at + "#1"));
            phi.append(" (= M_H").append(at).append(" 0)");
        }
        phi.append(")");
        for (int run = 0; run < 3; run++) {
            String sessionId = run == 0 ? "s-seed" : "s-" + run;
            Session session = new Session(iteration, sessionId);
            session.activation(TARGET, false);
            for (int at = 1; at <= 12; at++) {
                OccurrenceAddress producer = producers.get(at - 1);
                Endpoint sent = at(producer, "XCH.resp.p" + at,
                        "Rv#p" + at + "#1");
                session.activation(producer, false);
                session.constant("e.p" + at, "" + at);
                session.export(sent, "e.p" + at, 10L * at + run, "" + at);
                session.attach(at(TARGET, "XCH.resp.p" + at,
                        "Rv#t" + at + "#1"), "M_H" + at, "" + at, sent);
            }
            session.target(TARGET, "BlockTokenSecretManager"
                    + "#retrieveDataEncryptionKey#8", phi.toString());
            session.flush();
        }
        StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                targetSite("REGION.target", "BlockTokenSecretManager#u120")));
        String alone = onEachPool(iteration, map).get(0);
        for (OccurrenceAddress producer : producers) {
            assertTrue("every producer is planned: " + alone,
                    alone.contains(ClosurePlanner.taskId(producer)));
        }
        Corpus corpus = Corpus.read(iteration, null);
        for (int run = 0; run < 200; run++) {
            assertEquals("run " + run + " on the host's cores", alone,
                    rendered(plannedOn(corpus, map, ClosurePlanner.CORES)));
        }
    }

    private static List<String> onEachPool(Path iteration,
                                           StaticScopeMap map)
            throws IOException {
        java.util.concurrent.ForkJoinPool one =
                new java.util.concurrent.ForkJoinPool(1);
        java.util.concurrent.ForkJoinPool four =
                new java.util.concurrent.ForkJoinPool(4);
        try {
            List<String> plans = new ArrayList<String>();
            for (java.util.concurrent.ForkJoinPool cores : Arrays.asList(
                    one, four, ClosurePlanner.CORES)) {
                plans.add(rendered(plannedOn(Corpus.read(iteration, null),
                        map, cores)));
            }
            return plans;
        } finally {
            one.shutdownNow();
            four.shutdownNow();
        }
    }

    private static ClosurePlanner.Plan plannedOn(Corpus corpus,
            StaticScopeMap map, java.util.concurrent.ForkJoinPool cores) {
        Set<GapRow> said = new LinkedHashSet<GapRow>();
        return saying(ClosurePlanner.plan(corpus, TARGET,
                ClosurePlanner.DEFAULT_MAX_TASKS,
                ClosurePlanner.CLOSURE_CEILING, map,
                Branches.of(corpus, Collections.singletonList(TARGET),
                        new ArrayList<GapRow>()),
                Collections.<String>emptySet(),
                Collections.<String>emptySet(), ClientFaults.NONE,
                SystemView.of(""), cores,
                ZkChain.of(Collections.<JsonObject>emptyList()), said::add),
                said);
    }

    private static String rendered(ClosurePlanner.Plan plan) {
        return plan.tasks + "\n" + plan.why + "\n" + plan.flipSites + "\n"
                + gapsOf(plan) + "\n" + plan.exposed + "\n" + plan.waiting
                + "\n" + plan.truncated + "\n" + plan.unpaused + "\n"
                + plan.runWhole + "\n" + plan.ceilingCut;
    }

    private static void written(Session session, OccurrenceAddress at,
                                LocationId store, long version, String leaf) {
        session.write(at(at, "SOLR_ZK#WRITE:" + store.slot(),
                "ZkStateWriter#write#3"), store, version, "");
        session.export(at(at, ContentPort.of("SOLR_ZK", store.slot(), leaf),
                "Utils#toJSON#7"), "", 0L, "0");
    }

    private static ClosurePlanner.Plan closure(Corpus corpus,
                                               OccurrenceAddress anchor,
                                               StaticScopeMap map) {
        Set<GapRow> said = new LinkedHashSet<GapRow>();
        return saying(ClosurePlanner.plan(corpus, anchor,
                ClosurePlanner.DEFAULT_MAX_TASKS, map,
                Branches.of(corpus, Collections.singletonList(anchor),
                        new ArrayList<GapRow>()),
                Collections.<String>emptySet(),
                Collections.<String>emptySet(), ClientFaults.NONE,
                SystemView.of(""), said::add), said);
    }

    private static final Map<ClosurePlanner.Plan, List<GapRow>> SAID =
            Collections.synchronizedMap(new java.util.IdentityHashMap<
                    ClosurePlanner.Plan, List<GapRow>>());

    private static ClosurePlanner.Plan saying(ClosurePlanner.Plan plan,
                                              Set<GapRow> said) {
        SAID.put(plan, new ArrayList<GapRow>(said));
        return plan;
    }

    private static List<GapRow> gapsOf(ClosurePlanner.Plan plan) {
        return SAID.get(plan);
    }

    @Test
    public void aConnectedCandidateIsPlannedAndCandidatesTakeTurnsByClass()
            throws Exception {
        Path iteration = tree.newFolder("candidate-turns").toPath();
        LocationId allKeys = LocationId.of(LocationKind.MAP, "21", "allKeys");
        OccurrenceAddress sibling = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.CLIENT, "", 9),
                "o.a.h.h.s.d.BPServiceActor#offerService#41");
        OccurrenceAddress siblingB = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.CLIENT, "", 11),
                "o.a.h.h.s.d.BPServiceActor#offerService#43");
        OccurrenceAddress siblingC = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.CLIENT, "", 12),
                "o.a.h.h.s.d.BPServiceActor#offerService#44");
        OccurrenceAddress refresher = occurrence("hdfs-case/dn0",
                "REGION.refresh", CausalContext.of(Role.of("KEY_REFRESH"), "",
                        1), "o.a.h.h.s.d.KeyRefresh#run#1");
        Endpoint exported = at(siblingB, "XCH.resp.block-key-id",
                "PBHelper#convert#9");
        Endpoint attached = at(WRITER, "XCH.resp.block-key-id",
                "PBHelper#convert#9");
        Session seed = new Session(iteration, "s-seed");
        for (OccurrenceAddress at : Arrays.asList(TARGET, WRITER, sibling,
                siblingB, siblingC, refresher)) {
            seed.activation(at, false);
        }
        seed.constant("e.119992", "119992");
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.export(exported, "e.119992", 11L, "119992");
        seed.attach(attached, "M_HOFF_KEY", "119992", exported);
        seed.write(STORED, allKeys, 5L, "e.stored");
        seed.read(at(TARGET, Endpoint.stateSite("BlockTokenSecretManager",
                        "retrieveDataEncryptionKey", 8, false),
                        "BlockTokenSecretManager#retrieveDataEncryptionKey#8"),
                allKeys, 5L, "M_READ_KEY", "119992");
        seed.anchored(TARGET);
        seed.flush();
        StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", "")),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.refresh",
                        "KeyManager#u4", "KeyManager#refresh",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""))));
        Corpus corpus = Corpus.read(iteration, null);
        Object[][] rows = {
            {0, Collections.<OccurrenceAddress>emptyList(),
                    Arrays.asList(sibling, siblingC, refresher)},
            {2, Arrays.asList(sibling, refresher),
                    Collections.singletonList(siblingC)},
        };
        for (Object[] row : rows) {
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, TARGET,
                    (Integer) row[0], map, Branches.of(corpus,
                            Collections.singletonList(TARGET),
                            new ArrayList<GapRow>()),
                Collections.<String>emptySet(),
                Collections.<String>emptySet(), ClientFaults.NONE,
                SystemView.of(""), gap -> { });
            Set<String> planned = new LinkedHashSet<String>();
            for (Task task : plan.tasks) planned.add(task.focused().render());
            Set<String> expected = new LinkedHashSet<String>(Arrays.asList(
                    TARGET.render(), WRITER.render(), siblingB.render()));
            for (Object at : (List<?>) row[1]) {
                expected.add(((OccurrenceAddress) at).render());
            }
            assertEquals("bound " + row[0] + ": " + planned, expected,
                    planned);
            Set<String> cut = new LinkedHashSet<String>();
            for (Object at : (List<?>) row[2]) {
                cut.add(((OccurrenceAddress) at).render());
            }
            assertEquals("bound " + row[0], cut, plan.truncated);
            assertTrue(plan.ceilingCut.isEmpty());
        }
        ClosurePlanner.Plan capped = ClosurePlanner.plan(corpus, TARGET, 2, 2,
                map, Branches.of(corpus, Collections.singletonList(TARGET),
                        new ArrayList<GapRow>()),
            Collections.<String>emptySet(),
                Collections.<String>emptySet(), ClientFaults.NONE,
                SystemView.of(""), gap -> { });
        Set<String> kept = new LinkedHashSet<String>();
        for (Task task : capped.tasks) kept.add(task.focused().render());
        assertEquals(new LinkedHashSet<String>(Arrays.asList(TARGET.render(),
                WRITER.render())), kept);
        assertEquals(Collections.singleton(siblingB.render()),
                capped.ceilingCut);
        assertEquals(new LinkedHashSet<String>(Arrays.asList(
                siblingB.render(), sibling.render(), siblingC.render(),
                refresher.render())), new LinkedHashSet<String>(
                capped.truncated));
    }

    @Test
    public void aClientsStaticWriterPairsAcrossNodesByObjectAlone()
            throws Exception {
        Object[][] table = {
            {"hdfs-case/dn0", Collections.<String>emptySet(), true},
            {"hdfs-case/nn0", Collections.<String>emptySet(), false},
            {"hdfs-case/client0",
                    Collections.singleton("hdfs-case/client0#epoch0"), true},
            {"hdfs-case/nn0",
                    Collections.singleton("hdfs-case/dn0#epoch0"), true},
            {"hdfs-case/nn0",
                    Collections.singleton("hdfs-case/client0#epoch0"), false},
        };
        int at = 0;
        for (Object[] row : table) {
            Path iteration = tree.newFolder("client-pairs-" + at++).toPath();
            OccurrenceAddress refresher = occurrence((String) row[0],
                    "REGION.refresh", CausalContext.of(Role.of("KEY_REFRESH"),
                            "", 1), "o.a.h.h.s.d.KeyRefresh#run#1");
            Session seed = new Session(iteration, "s-seed");
            for (OccurrenceAddress active : Arrays.asList(TARGET, WRITER,
                    refresher)) {
                seed.activation(active, false);
            }
            @SuppressWarnings("unchecked")
            Set<String> clients = (Set<String>) row[1];
            seed.clients.addAll(clients);
            seed.symbolic("e.stored", "M_HOFF_KEY");
            seed.write(STORED, ALL_KEYS, 5L, "e.stored");
            seed.read(at(TARGET, Endpoint.stateSite("BlockTokenSecretManager",
                            "retrieveDataEncryptionKey", 8, false),
                            "BlockTokenSecretManager#retrieveDataEncryptionKey#8"),
                    ALL_KEYS, 5L, "M_READ_KEY", "119992");
            seed.anchored(TARGET);
            seed.flush();
            StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                    targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                    put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                            "BlockTokenSecretManager#u12",
                            "BlockTokenSecretManager#addKeys",
                            "<example.Keys: int value>",
                            "<example.Manager: example.Keys allKeys>", "")),
                    put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.refresh",
                            "KeyManager#u4", "KeyManager#refresh",
                            "<example.Keys: int value>",
                            "<example.Manager: example.Keys allKeys>", ""))));
            List<String> planned = focused(plannedOn(Corpus.read(iteration,
                    null), map, ClosurePlanner.CORES));
            assertEquals(row[0] + " wrote, clients " + row[1] + ": " + planned,
                    row[2], planned.contains(refresher.render()));
        }
    }

    @Test
    public void aWriterThatRanForItsDoorsAloneIsDemandedThroughAReadInsideAValue()
            throws Exception {
        Path iteration = tree.newFolder("doors-only-writer").toPath();
        OccurrenceAddress boot = occurrence("hdfs-case/dn0", "REGION.boot",
                CausalContext.of(Role.of("BOOT"), "", 1),
                "o.a.h.h.s.d.Boot#run#1");
        LocationId limit = LocationId.of(LocationKind.INSTANCE, "9", "2");
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty("_java_type", "I");
        read.addProperty("readEventId", 3L);
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", 9L);
        location.addProperty("slot", 2L);
        location.addProperty("locationKind", "INSTANCE_FIELD");
        read.add("location", location);
        JsonObject site = new JsonObject();
        site.addProperty("className", "example/Config");
        site.addProperty("methodName", "limit");
        site.addProperty("methodDescriptor", "()I");
        site.addProperty("bci", 4);
        read.add("site", site);
        JsonObject observed = new JsonObject();
        observed.addProperty("fieldVersionId", 1L);
        observed.addProperty("versionKind", "INITIAL");
        read.add("observedVersion", observed);
        for (boolean ranWhole : new boolean[] {false, true}) {
            Path at = iteration.resolve("ran-whole-" + ranWhole);
            Files.createDirectories(at);
            Session seed = new Session(at, "s-seed");
            for (OccurrenceAddress each : Arrays.asList(TARGET, WRITER,
                    boot)) {
                seed.activation(each, false);
            }
            if (!ranWhole) seed.doorsOnly.add(boot.render());
            seed.write(at(boot, Endpoint.stateSite("example.Boot", "run", 2,
                    true), "Boot#run#2"), LocationId.of(LocationKind.INSTANCE,
                    "77", "1"), 1L, "");
            seed.writes.add(WriteRow.initial("s-seed", 0L, at(WRITER,
                    Endpoint.initialSite("example.Config#limit()I#4:READ"),
                    "Config#limit#4"), limit, 1L, "", "I"));
            seed.expression("e.stored", read);
            seed.write(STORED, ALL_KEYS, 5L, "e.stored");
            seed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "7");
            seed.anchored(TARGET);
            seed.flush();
            Files.write(at.resolve(StaticScopeMap.REGIONS),
                    ("{\"regionId\":\"REGION.boot\",\"methods\":["
                            + "\"<example.Boot: void run()>\","
                            + "\"<example.Config: void init()>\"]}\n")
                            .getBytes(StandardCharsets.UTF_8));
            StaticScopeMap map = StaticScopeMap.read(scopeMap(at,
                    targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                    scopeSite(StaticScopeMap.READ_SITE, "REGION.addkeys",
                            "<example.Config: int limit()>#u1",
                            "example.Config#limit()I",
                            "<example.Config: int limit>",
                            "<example.Config: int limit>", ""),
                    scopeSite(StaticScopeMap.WRITE_SITE, "REGION.init",
                            "<example.Config: void init()>#u1",
                            "example.Config#init()V",
                            "<example.Config: int limit>",
                            "<example.Config: int limit>", "")));
            ClosurePlanner.Plan plan = closure(Corpus.read(at, null), TARGET,
                    map);
            Set<String> whole = new LinkedHashSet<String>();
            for (OccurrenceAddress each : plan.unpaused.keySet()) {
                whole.add(each.render());
            }
            for (OccurrenceAddress each : plan.runWhole) {
                whole.add(each.render());
            }
            assertEquals("ran whole " + ranWhole + ", planned: "
                    + focused(plan), !ranWhole,
                    focused(plan).contains(boot.render()));
            assertEquals("ran whole " + ranWhole + ": " + whole, !ranWhole,
                    whole.contains(boot.render()));
        }
    }

    @Test
    public void aVersionNoRowWroteDemandsTheRecordedWritersOfItsCarrier()
            throws Exception {
        LocationId limit = LocationId.of(LocationKind.INSTANCE, "9", "2");
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty("_java_type", "I");
        read.addProperty("readEventId", 3L);
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", 9L);
        location.addProperty("slot", 2L);
        location.addProperty("locationKind", "INSTANCE_FIELD");
        read.add("location", location);
        JsonObject site = new JsonObject();
        site.addProperty("className", "example/Config");
        site.addProperty("methodName", "limit");
        site.addProperty("methodDescriptor", "()I");
        site.addProperty("bci", 4);
        read.add("site", site);
        JsonObject observed = new JsonObject();
        observed.addProperty("fieldVersionId", 1L);
        observed.addProperty("versionKind", "INITIAL");
        read.add("observedVersion", observed);
        Object[][] rows = {
            {"the version no row wrote", "<example.Boot: void run()>", false,
                    "", true},
            {"a view class's work", "<example.View: void decode()>", false,
                    "example.View", false},
            {"a version a row wrote", "<example.Boot: void run()>", true,
                    "", false},
        };
        int at = 0;
        for (Object[] row : rows) {
            Path iteration = tree.newFolder("unrecorded-" + at++).toPath();
            OccurrenceAddress writer = occurrence("hdfs-case/dn0",
                    "REGION.boot", CausalContext.of(Role.of("BOOT"), "", 1),
                    (String) row[1]);
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            seed.activation(writer, false, false);
            Endpoint first = at(TARGET, Endpoint.initialSite(
                    "example.Config#limit()I#4:READ"), "Config#limit#4");
            if ((Boolean) row[2]) {
                seed.write(at(WRITER, Endpoint.stateSite("example.Config",
                        "init", 1, true), "Config#init#1"), limit, 1L, "",
                        "I");
            } else {
                seed.writes.add(WriteRow.initial("s-seed", 0L, first, limit,
                        1L, "", "I"));
            }
            seed.expression("EXPR.0a1b", read);
            seed.decision(TARGET, "BlockTokenSecretManager#u120", 1, true,
                    "EXPR.0a1b");
            seed.target(TARGET, "BlockTokenSecretManager"
                    + "#retrieveDataEncryptionKey#8", "(not EXPR.0a1b)");
            seed.flush();
            Files.write(iteration.resolve(StaticScopeMap.REGIONS),
                    ("{\"regionId\":\"REGION.boot\",\"methods\":["
                            + "\"<example.Config: void init()>\"]}\n")
                            .getBytes(StandardCharsets.UTF_8));
            StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                    targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                    scopeSite(StaticScopeMap.READ_SITE, "REGION.target",
                            "<example.Config: int limit()>#u1",
                            "example.Config#limit()I",
                            "<example.Config: int limit>",
                            "<example.Config: int limit>", ""),
                    scopeSite(StaticScopeMap.WRITE_SITE, "REGION.init",
                            "<example.Config: void init()>#u1",
                            "example.Config#init()V",
                            "<example.Config: int limit>",
                            "<example.Config: int limit>", "")));
            Corpus corpus = Corpus.read(iteration, null);
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, TARGET,
                    ClosurePlanner.DEFAULT_MAX_TASKS, map, Branches.of(corpus,
                            Collections.singletonList(TARGET),
                            new ArrayList<GapRow>()),
                    Collections.<String>emptySet(),
                    Collections.<String>emptySet(), ClientFaults.NONE,
                    SystemView.of((String) row[3]), gap -> { });
            Set<OccurrenceAddress> reached =
                    new LinkedHashSet<OccurrenceAddress>(plan.exposed.keySet());
            reached.addAll(plan.waiting);
            assertEquals(row[0] + ": " + reached + " " + focused(plan),
                    row[4], reached.contains(writer));
            assertEquals(row[0] + ": only the seed ran it, so it grows the "
                    + "plan alone, in the seed's name",
                    (Boolean) row[4] ? "s-seed" : null,
                    plan.exposed.get(writer));
            Task anchor = null;
            for (Task task : plan.tasks) {
                if (task.focused().equals(TARGET)) anchor = task;
            }
            Frontier frontier = new Frontier(corpus, plan.tasks,
                    plan.flipSites);
            Map<String, List<ObligationResult>> none =
                    Collections.<String, List<ObligationResult>>emptyMap();
            assertTrue(row[0] + ": unplanned yet, no re-run",
                    PathReruns.of(corpus, anchor, plan.unrecordedWriters,
                            Collections.<String>emptySet(), frontier, none,
                            gap -> { }).isEmpty());
            List<Obligation> reruns = PathReruns.of(corpus, anchor,
                    plan.unrecordedWriters, Collections.singleton(
                            writer.render()), frontier, none, gap -> { });
            assertEquals(row[0] + ": planned, the seed's path re-runs its "
                    + "world: " + reruns, (Boolean) row[4] ? 1 : 0,
                    reruns.size());
            if (reruns.isEmpty()) continue;
            Obligation rerun = reruns.get(0);
            assertTrue(rerun.rerun() && !rerun.force());
            assertEquals("the anchor's own decision, as recorded",
                    Arrays.asList("BlockTokenSecretManager#u120", 1, true),
                    Arrays.<Object>asList(rerun.siteId(), rerun.ordinal(),
                            rerun.flippedOutcome()));
            assertEquals("a row of the round as any obligation", rerun,
                    ExploreCodec.readObligation(
                            ExploreCodec.writeObligation(rerun)));
            Path wave = iteration.resolve("obligations-0001");
            Files.createDirectories(wave);
            RowCodec.writeAll(wave.resolve("obligations.jsonl"),
                    Collections.singletonList(rerun),
                    ExploreCodec::writeObligation);
            Path worker = wave.resolve(rerun.obligationId());
            ObligationSolverMain.solve(corpus, iteration,
                    wave.resolve("obligations.jsonl"), rerun.obligationId(),
                    worker, Paths.get("z3"), 10_000L, 1152, null);
            assertEquals("no query: the world is replayed as recorded",
                    Verdict.SAT_MODEL_READY, RowCodec.readAll(
                            worker.resolve(ObligationDir.RESULT),
                            RowCodec::readObligationResult).get(0).verdict());
            JsonObject focus = ExploreCodec.readObject(
                    worker.resolve(ObligationDir.FOCUSED_TASK));
            assertEquals("s-seed", focus.get("pathSessionId").getAsString());
            assertTrue("the replay is judged by its recorded arm: " + focus,
                    focus.getAsJsonObject("flip").get("outcome")
                            .getAsBoolean());
            assertTrue("and runs the path's own world: no flip of its own",
                    ExploreCodec.readWorld(focus).flips.isEmpty());
            String flip = ObligationFactory.flip(rerun.taskId(),
                    rerun.pathId(), rerun.siteId(), rerun.ordinal(),
                    rerun.flippedOutcome());
            frontier.inFlight(Collections.singletonList(rerun));
            assertTrue("one re-run of a path at a time",
                    PathReruns.of(corpus, anchor, plan.unrecordedWriters,
                            Collections.singleton(writer.render()),
                            frontier, none, gap -> { }).isEmpty());
            Session again = new Session(iteration, "s-again");
            again.activation(TARGET, false);
            again.activation(writer, false, true);
            again.flush();
            Corpus landed = Corpus.read(iteration, null);
            assertTrue("a landed re-run that ran the writers owes no other",
                    PathReruns.of(landed, anchor, plan.unrecordedWriters,
                            Collections.singleton(writer.render()),
                            new Frontier(landed, plan.tasks, plan.flipSites),
                            Collections.singletonMap(flip,
                                    Collections.singletonList(
                                            ObligationResult.of(
                                                    rerun.obligationId(),
                                                    Verdict.ADMITTED,
                                                    "s-again", "ran"))),
                            gap -> { }).isEmpty());
        }
    }

    @Test
    public void anArmOverAReadNoRowWroteIsAnotherQuestionThanOverAWrittenOne()
            throws Exception {
        LocationId limit = LocationId.of(LocationKind.INSTANCE, "9", "2");
        Object[][] rows = {
            {"s-held", false}, {"s-held-again", false}, {"s-written", true},
        };
        Path iteration = tree.newFolder("held-arms").toPath();
        for (Object[] row : rows) {
            Session session = new Session(iteration, (String) row[0]);
            session.activation(TARGET, false);
            Endpoint at = at(TARGET, "example.Config#limit()I#4:READ",
                    "Config#limit#4");
            session.writes.add(WriteRow.initial((String) row[0], 0L, at,
                    limit, 1L, "", "I"));
            if ((Boolean) row[1]) {
                session.write(at(TARGET, "example.Config#set(I)V#2:WRITE",
                        "Config#set#2"), limit, 2L, "", "I");
            }
            session.read(at, limit, (Boolean) row[1] ? 2L : 1L, "read_limit",
                    "4");
            session.decision(TARGET, "Config#u7", 1, true, "(> read_limit 3)");
            session.flush();
        }
        Corpus corpus = Corpus.read(iteration, null);
        Task task = Task.of(ClosurePlanner.taskId(TARGET), TARGET,
                Collections.<OccurrenceAddress>emptyList(), "s-held");
        List<ObligationFactory.Keyed> arms =
                new ArrayList<ObligationFactory.Keyed>();
        List<String> sessions = new ArrayList<String>();
        for (Corpus.RecordedPath path : corpus.pathsOf(TARGET)) {
            arms.add(new ObligationFactory.Keyed(task, path, 0));
            sessions.add(path.sessionId);
        }
        List<String> keys = ObligationFactory.dependences(corpus, arms);
        Map<String, String> bySession = new LinkedHashMap<String, String>();
        for (int at = 0; at < keys.size(); at++) {
            bySession.put(sessions.get(at), keys.get(at));
        }
        assertEquals("two paths that read what no row wrote ask one question",
                bySession.get("s-held"), bySession.get("s-held-again"));
        assertFalse("a path whose read a row wrote asks another: "
                        + bySession, bySession.get("s-held").equals(
                bySession.get("s-written")));
    }

    @Test
    public void aDecisionOnNoStoreValueStaysOnTheZooKeeperChain()
            throws Exception {
        LocationId stored = LocationId.of(LocationKind.STORE, "HBASE_ZK",
                "/hbase/keys/1");
        LocationId held = LocationId.of(LocationKind.MAP, "7", "-3");
        Object[][] rows = {
            {"a constant", "(not (= 3 4))", true},
            {"a store value off the chain", "(= zk_key 1)", false},
            {"a map the store's value was put in", "(= map_key 1)", true},
            {"both", "(= (+ zk_key map_key) 2)", true},
        };
        int at = 0;
        for (Object[] row : rows) {
            Path iteration = tree.newFolder("zk-keys-" + at++).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            seed.read(at(TARGET, "Zk#getData#3:READ", "Zk#getData#3"),
                    stored, 0L, "zk_key", "1");
            seed.read(at(TARGET, "Keys#get#5:READ", "Keys#get#5"), held, 2L,
                    "map_key", "1");
            seed.decision(TARGET, "Keys#u9", 1, true, (String) row[1]);
            seed.flush();
            Corpus corpus = Corpus.read(iteration, null);
            JsonObject chained = new JsonObject();
            chained.addProperty("kind", ZkChain.OCCURRENCE);
            chained.addProperty("occurrenceId", TARGET.render());
            ZkKeys keys = ZkKeys.of(ZkChain.of(
                    Collections.singletonList(chained)));
            DecisionRow decision = corpus.path("s-seed", TARGET).decisions
                    .get(0);
            assertEquals(row[0] + "", row[2],
                    keys.flippable(corpus, "s-seed", decision));
        }
    }

    private static List<String> focused(ClosurePlanner.Plan plan) {
        List<String> focused = new ArrayList<String>();
        for (Task task : plan.tasks) focused.add(task.focused().render());
        return focused;
    }

    private static Map<String, String> why(ClosurePlanner.Plan plan) {
        Map<String, String> reasons = new LinkedHashMap<String, String>();
        for (Task task : plan.tasks) {
            reasons.put(task.focused().render(),
                    plan.why.get(task.taskId()));
        }
        return reasons;
    }

    private Path scopeMap(Path iteration, String... sites)
            throws IOException {
        List<String> lines = new ArrayList<String>(Arrays.asList(sites));
        Path file = iteration.resolve(StaticScopeMap.FILE);
        Files.write(file, (String.join(System.lineSeparator(), lines)
                + System.lineSeparator()).getBytes("UTF-8"));
        return file;
    }

    private static String scopeSite(String role, String regionId,
                                    String siteId, String vmSite,
                                    String cell, String carrier,
                                    String portId, String... guards) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", StaticScopeMap.SITE_KIND);
        row.addProperty("role", role);
        row.addProperty("regionId", regionId);
        row.addProperty("siteId", siteId);
        row.addProperty("vmSite", vmSite);
        row.addProperty("cell", cell);
        row.addProperty("carrier", carrier);
        row.addProperty("portId", portId);
        JsonArray stated = new JsonArray();
        for (String guard : guards) stated.add(guard);
        row.add("guards", stated);
        return row.toString();
    }

    private static String put(String row) {
        JsonObject site = com.google.gson.JsonParser.parseString(row)
                .getAsJsonObject();
        site.addProperty("declaredCallee", "<java.util.Map: java.lang.Object"
                + " put(java.lang.Object,java.lang.Object)>");
        return site.toString();
    }

    private static String targetSite(String regionId, String siteId,
                                     String... guards) {
        return scopeSite(StaticScopeMap.TARGET_SITE, regionId, siteId, "",
                "", "", "", guards);
    }

    private static final class Worker {
        private final Verdict verdict;
        private final Obligation obligation;
        private final Path directory;

        private Worker(Verdict verdict, Obligation obligation,
                       Path directory) {
            this.verdict = verdict;
            this.obligation = obligation;
            this.directory = directory;
        }
    }

    @Test
    public void theHardLaneAnswersOverItsFirstAsksQueryAlone()
            throws Exception {
        String sat = "(declare-const x Int)\n(assert (> x 41))\n";
        String unsat = "(declare-const x Int)\n(assert (and (> x 1) (< x 0)))\n";
        String slow = "(declare-const x Int)\n(declare-const y Int)\n"
                + "(declare-const z Int)\n(assert (and (> x 2) (> y 2) "
                + "(> z 2) (= (+ (* x x x) (* y y y)) (* z z z))))\n";
        Object[][] rows = {
                {unsat, 60_000L, "UNSAT",
                        "no world of this corpus takes the other arm at s#1"},
                {slow, 1L, "NOT_ADMITTED", "SOLVER_TIMEOUT after 1ms"},
                {sat, 60_000L, "MODEL", ""},
        };
        int at = 0;
        for (Object[] row : rows) {
            Path worker = tree.newFolder("hard" + at++).toPath();
            Path obligations = worker.resolve("obligations.jsonl");
            RowCodec.writeAll(obligations, Collections.singletonList(
                    Obligation.of("OB.1", "T", "P", "s", 1, true,
                            Collections.<String, String>emptyMap(),
                            Collections.<String, String>emptyMap(),
                            Collections.<String>emptyList())),
                    ExploreCodec::writeObligation);
            List<String> symbols = Collections.singletonList("x");
            String query = Z3.modelQuery((String) row[0], symbols);
            Files.write(worker.resolve(ObligationSolverMain.QUERY),
                    ArtifactIO.gzip(query.getBytes(StandardCharsets.UTF_8)));
            GapRow built = GapRow.of("S", GapKind.ADMISSION_GAP,
                    GapClass.DIAGNOSTIC, "OB.1", "built");
            String sha = edu.uva.liftlab.graphchecker.smt.ArtifactIO
                    .sha256(query);
            Solved.Key key = Solved.Key.of(query);
            Path solved = worker.resolve(Solved.DIR);
            new HardAsk("OB.1", "S", "the question",
                    "no world of this corpus takes the other arm at s#1",
                    Collections.singletonList(built), symbols, sha,
                    key.of(symbols), solved)
                    .write(worker.resolve(HardAsk.FILE));
            ObligationSolverMain.decide(obligations, "OB.1", worker,
                    Paths.get("z3"), (Long) row[1], 1152);
            String says = Arrays.toString(row);
            Path kept = solved.resolve(key.sha256 + ".json");
            assertEquals(says, !"NOT_ADMITTED".equals(row[2]),
                    Files.exists(kept));
            if (Files.exists(kept)) {
                for (String file : new String[] {ObligationDir.RESULT,
                        HardAsk.Model.FILE, ObligationDir.QUESTION}) {
                    Files.deleteIfExists(worker.resolve(file));
                }
                ObligationSolverMain.decide(obligations, "OB.1", worker,
                        Paths.get("no-z3-here"), (Long) row[1], 1152);
            }
            if ("MODEL".equals(row[2])) {
                assertFalse(says, Files.exists(
                        worker.resolve(ObligationDir.RESULT)));
                assertEquals(says, "42", HardAsk.Model.read(worker.resolve(
                        HardAsk.Model.FILE)).values.get("x"));
                continue;
            }
            ObligationResult result = RowCodec.readAll(
                    worker.resolve(ObligationDir.RESULT),
                    RowCodec::readObligationResult).get(0);
            assertEquals(says, row[2], result.verdict().name());
            assertTrue(says + result.detail(),
                    result.detail().startsWith((String) row[3]));
            assertTrue(says, anyGap(worker, gap -> "built".equals(
                    gap.detail())));
            assertEquals(says, "UNSAT".equals(row[2]), Files.exists(
                    worker.resolve(ObligationDir.QUESTION)));
        }
    }

    private Worker solve(Path iteration, Path waveDir, Obligation proposal,
                         Path out, String name) throws IOException {
        return solve(iteration, null, waveDir, proposal, out, name);
    }

    private Worker solve(Path iteration, Path domains, Path waveDir,
                         Obligation proposal, Path out, String name)
            throws IOException {
        Path worker = out.resolve(name);
        ObligationSolverMain.solve(Corpus.read(iteration, domains),
                iteration, waveDir.resolve("obligations.jsonl"),
                proposal.obligationId(), worker, Paths.get("z3"), 10_000L,
                1152, null);
        List<ObligationResult> rows = RowCodec.readAll(
                worker.resolve("obligation_result.jsonl"),
                RowCodec::readObligationResult);
        assertEquals(1, rows.size());
        List<Obligation> solved = RowCodec.readAll(
                worker.resolve("obligation.jsonl"),
                ExploreCodec::readObligation);
        assertEquals(1, solved.size());
        assertTrue("the query is published whatever the verdict",
                !queryText(worker).isEmpty());
        return new Worker(rows.get(0).verdict(), solved.get(0), worker);
    }

    private static boolean anyGap(Path dir,
            java.util.function.Predicate<GapRow> named) throws IOException {
        return RowCodec.readAll(dir.resolve(ExploreMain.GAPS_FILE),
                        RowCodec::readGap)
                .stream().anyMatch(named);
    }

    private static Path results(Path out) throws IOException {
        Path results = out.resolve("obligation_results.jsonl");
        Files.write(results, new byte[0]);
        return results;
    }

    private static void record(Path results, ObligationResult result)
            throws IOException {
        Files.write(results, (RowCodec.toLine(
                        RowCodec.writeObligationResult(result))
                        + System.lineSeparator()).getBytes("UTF-8"),
                StandardOpenOption.CREATE, StandardOpenOption.APPEND);
    }

    private static List<Obligation> obligations(Path waveDir)
            throws IOException {
        return RowCodec.readAll(waveDir.resolve("obligations.jsonl"),
                ExploreCodec::readObligation);
    }

    @Test
    public void aDoorEarlierInItsOwnTurnIsAControlProducerOfTheOccurrence()
            throws IOException {
        CausalContext started = CausalContext.of("m-create", "HBASE_RPC");
        OccurrenceAddress client = occurrence("hb/client0", "REGION.door",
                CausalContext.of(Role.of("CLIENT"), "test", 1), "Admin#create#1");
        OccurrenceAddress writer = occurrence("hb/master0", "REGION.cached",
                started, "Manager#addOrUpdate#4");
        OccurrenceAddress before = occurrence("hb/master0", "REGION.door",
                started, "Table#put#2");
        OccurrenceAddress after = occurrence("hb/master0", "REGION.door",
                started, "Table#put#9");
        Object[][] table = {
            {"seed", "seed", "[" + before.render() + "]", 1, 1},
            {"seed", "s-other", "[]", 0, 2},
        };
        for (Object[] row : table) {
            Path iteration = tree.newFolder().toPath();
            Map<String, Session> sessions = new LinkedHashMap<>();
            for (String id : new String[] {"seed", "s-other"}) {
                sessions.put(id, new Session(iteration, id));
            }
            Session own = sessions.get((String) row[0]);
            Session door = sessions.get((String) row[1]);
            own.activation(client, false);
            door.activation(before, false);
            door.decision(before, "AbstractRpcClient#u66", 1, false, "");
            own.activation(writer, false);
            own.decision(writer, "Manager#u3", 1, true, "");
            own.activation(after, false);
            own.decision(after, "AbstractRpcClient#u66", 1, false, "");
            for (Session session : sessions.values()) session.flush();
            RowCodec.writeJsonl(SessionDir.of(iteration, "seed").schedule(),
                    Arrays.asList(RowCodec.writeScheduleEvent(ScheduleEvent.of(
                            1L, ScheduleEvent.Kind.SEND, client.node().render()
                                    + "|" + client.context().render(),
                            "HBASE_RPC#REQUEST:MasterService.CreateNamespace",
                            0, client.id(), "m-create")),
                            RowCodec.writeScheduleEvent(ScheduleEvent.of(2L,
                                    ScheduleEvent.Kind.RECV, writer.node()
                                            .render() + "|"
                                            + started.render(),
                                    "HBASE_RPC#REQUEST", 0, "", ""))));
            Map<String, Integer> cut = new LinkedHashMap<String, Integer>();
            List<OccurrenceAddress> earlier =
                    new ArrayList<OccurrenceAddress>();
            List<OccurrenceAddress> doors = Corpus.read(iteration, null)
                    .doorsOf("m-create", writer, cut, earlier);
            List<String> said = new ArrayList<String>();
            for (OccurrenceAddress each : earlier) said.add(each.render());
            String label = "door ran in " + row[1];
            assertEquals(label, "[" + client.render() + "]",
                    renders(doors));
            assertEquals(label, row[2], said.toString());
            assertEquals(label, row[3], cut.getOrDefault(
                    Corpus.EARLIER_IN_TURN, 0));
            assertEquals(label, row[4], cut.getOrDefault(Corpus.OWN_TURN,
                    0));
        }
    }

    private static String renders(List<OccurrenceAddress> occurrences) {
        List<String> rendered = new ArrayList<String>();
        for (OccurrenceAddress each : occurrences) {
            rendered.add(each.render());
        }
        return rendered.toString();
    }

    private static Obligation named(List<Obligation> obligations,
                                    String site) {
        for (Obligation obligation : obligations) {
            if (obligation.siteId().equals(site)) return obligation;
        }
        return null;
    }

    @Test
    public void aClientFaultCutStopsTheCatalogsOwnDoorsAsWellAsAHooksDoors()
            throws Exception {
        OccurrenceAddress client = occurrence("auto0/client0", "REGION.c",
                CausalContext.of(Role.CLIENT, "test", 1), "<a.T: void t()>#u1");
        String create = "<org.apache.zookeeper.ZooKeeper: java.lang.String "
                + "create(java.lang.String,byte[],java.util.List,org.apache."
                + "zookeeper.CreateMode)>#u9";
        String sync = "<org.apache.zookeeper.server.quorum.Learner: void "
                + "readSyncPacket(org.apache.zookeeper.server.quorum."
                + "QuorumPacket)>#u3";
        Path doors = Paths.get("experiments", "zookeeper", "doors.jsonl");
        Object[][] rows = {
            {"ZK_QUORUM", false, true},
            {"ZOOKEEPER", true, false},
        };
        for (Object[] row : rows) {
            ClientFaults cut = ClientFaults.read(doors,
                    Collections.singleton((String) row[0]));
            assertEquals(row[0] + " create", row[1], cut.fails(client, create));
            assertEquals(row[0] + " sync", row[2], cut.fails(client, sync));
        }
    }

    private static OccurrenceAddress occurrence(String node, String region,
                                                CausalContext context,
                                                String callSite) {
        return OccurrenceAddress.of(NodeId.of(node, 0), region, context,
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of(callSite, 0))));
    }

    private static Endpoint at(OccurrenceAddress occurrence, String site,
                               String callSite) {
        return Endpoint.of(occurrence, site, ExecutionIndex.of(
                Collections.singletonList(Frame.of(callSite, 0))), 0);
    }

    private static String exportedId() {
        return at(occurrence("hdfs-case/nn0", "REGION.rotate",
                        CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", 1),
                        "o.a.h.h.s.b.BlockManager#run#8"),
                "XCH.resp.block-key-id", "PBHelper#convert#9").id();
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (IOException | InterruptedException unavailable) {
            return false;
        }
    }

    @Test
    public void anAnchorStoreReadOfAChainWritersVersionIsDemandedWithoutAScopeSite()
            throws Exception {
        LocationId snapshot = LocationId.of(LocationKind.STORE,
                "ZK_SNAPSHOT", "snapshot/peer1");
        OccurrenceAddress restart = occurrence("zk-case/peer1",
                "REGION.target", CausalContext.of(Role.of("TEST"), "", 1),
                "Main#runFromConfig#1");
        OccurrenceAddress sync = occurrence("zk-case/peer1",
                "REGION.sync", CausalContext.of(Role.of("TEST"), "", 1),
                "Peer#run#1");
        Object[][] cases = {{true, true}, {false, false}};
        for (int at = 0; at < cases.length; at++) {
            Path iteration = tree.newFolder("chain-store-" + at).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(restart, false);
            seed.activation(sync, false, true, "peer");
            seed.write(at(sync, "ZK_SNAPSHOT#WRITE:snapshot.peer1",
                    "Peer#syncWithLeader#4"), snapshot, 7L, "", "[B");
            seed.read(at(restart, "ZK_SNAPSHOT#READ:snapshot.peer1",
                    "Main#loadDataBase#2"), snapshot, 7L, "S_snap7", null);
            seed.target(restart, "Guard#u8#1", "false");
            seed.flush();
            List<JsonObject> chain = new ArrayList<JsonObject>();
            if ((Boolean) cases[at][0]) {
                JsonObject held = new JsonObject();
                held.addProperty("kind", ZkChain.OCCURRENCE);
                held.addProperty("occurrenceId", sync.render());
                chain.add(held);
            }
            JsonObject path = new JsonObject();
            path.addProperty("kind", ZkChain.PATH);
            path.addProperty("transport", "ZK_SNAPSHOT");
            path.addProperty("location", "snapshot/peer1");
            path.addProperty("slot", "snapshot/peer1");
            chain.add(path);
            RowCodec.writeJsonl(iteration.resolve(ZkChain.FILE), chain);
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Guard#u8"));
            Path out = tree.newFolder("chain-store-" + at + "-out").toPath();
            JsonObject manifest = plan(iteration,
                    "zk-case/peer1#epoch0/region/REGION.target#1", null,
                    results(out), out.resolve("obligations-0000"), 0);
            Set<String> focused = new LinkedHashSet<String>();
            for (JsonElement task : manifest.getAsJsonArray("taskRows")) {
                focused.add(task.getAsJsonObject().get("focused")
                        .getAsString());
            }
            assertEquals("case " + at + ": " + focused, cases[at][1],
                    focused.contains(sync.render()));
        }
    }

    @Test
    public void aWriterWhoseRecordedArmLeftTheWriteHoldsNoOwnerEvidence() {
        String guard = "<o.a.z.s.SessionTrackerImpl: void run()>#u14";
        String other = "<o.a.z.s.SessionTrackerImpl: void run()>#u2";
        List<String> guards = Arrays.asList(other, guard);
        Object[][] table = {
            {"no decision at a guard", Arrays.asList(false, false),
                    other + "@nothing", false, false},
            {"decided toward the write", Arrays.asList(false, false),
                    guard, false, false},
            {"decided away from the write", Arrays.asList(false, false),
                    guard, true, true},
            {"direction unknown", Arrays.asList(false, null),
                    guard, true, true},
        };
        for (Object[] row : table) {
            @SuppressWarnings("unchecked")
            List<Boolean> outcomes = (List<Boolean>) row[1];
            DecisionRow decision = DecisionRow.of("s", 1, PRODUCER,
                    (String) row[2], 1, (Boolean) row[3], "EXPR.t",
                    Collections.<String, Long>emptyMap());
            assertEquals((String) row[0], row[4], ClosurePlanner.decidedAway(
                    Collections.singletonList(decision), guards, outcomes));
        }
    }

    @Test
    public void aStoreVersionRestsOnEveryWriteOfItsLocationAndTheirItems()
            throws Exception {
        LocationId state = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/collections/t/state.json");
        OccurrenceAddress client = occurrence("solr-case/client0",
                "REGION.target", CausalContext.of(Role.of("TEST"), "", 1),
                "Client#add#1");
        OccurrenceAddress first = occurrence("solr-case/node0",
                "REGION.update", CausalContext.of(
                        Role.of("OVERSEER_STATE_UPDATE"), "", 1),
                "Overseer#run#1");
        OccurrenceAddress last = occurrence("solr-case/node0",
                "REGION.update", CausalContext.of(
                        Role.of("OVERSEER_STATE_UPDATE"), "", 2),
                "Overseer#run#2");
        OccurrenceAddress restore = occurrence("solr-case/node0",
                "REGION.restore", CausalContext.of(Role.of("OVERSEER_TASK"),
                        "", 1), "Restore#run#1");
        Object[][] cases = {
            {true, true, Arrays.asList(true, true, true), "false"},
            {true, false, Arrays.asList(true, true, false), "false"},
            {false, true, Arrays.asList(false, false, false), "false"},
            {true, true, Arrays.asList(true, true, true), "(= M_OTHER 0)"},
        };
        for (int at = 0; at < cases.length; at++) {
            boolean provenance = (Boolean) cases[at][0];
            boolean taken = (Boolean) cases[at][1];
            String phi = (String) cases[at][3];
            Path iteration = tree.newFolder("store-" + at).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(client, false);
            seed.activation(first, false, true, "updater");
            seed.activation(last, false, true, "updater");
            seed.activation(restore, false, true, "runner");
            seed.marker(restore, "CASE.DOOR", "M_DOOR", "false");
            seed.decision(restore, "Door#u3", 1, false, "M_DOOR");
            seed.write(at(first, "SOLR_ZK#WRITE:.collections.t.state.json",
                    "Overseer#run#1"), state, 1L, "", "[B");
            seed.write(at(last, "SOLR_ZK#WRITE:.collections.t.state.json",
                    "Overseer#run#2"), state, 2L, "", "[B");
            seed.integral(client, "CASE.OTHER", "M_OTHER", "1", "0", "9");
            seed.read(at(client, "Router#hash#u2", "Router#hash#2"), state,
                    2L, "S_state2", null);
            seed.target(client, "Guard#u8#1", phi);
            seed.flush();
            List<JsonObject> schedule = new ArrayList<JsonObject>();
            schedule.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                    ScheduleEvent.Kind.SEND, ContextShape.Stance.of(restore)
                            .render(), "SOLR_ZK#REQUEST", 0, restore.id(),
                    "e-item")));
            schedule.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                    ScheduleEvent.Kind.PUBLISH, restore.node().render()
                            + "|" + ContextShape.Stance.VIEW_STANCE,
                    ScheduleEvent.published("SOLR_ZK",
                            "/collections/t/state.json", 2L), 0, "", "")));
            if (taken) {
                schedule.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(1L,
                        ScheduleEvent.Kind.RECV, ContextShape.Stance.of(
                                first).render(), "SOLR_ZK#REQUEST", 0,
                        first.id(), "e-item")));
            }
            RowCodec.writeJsonl(SessionDir.of(iteration, "s-seed").schedule(),
                    schedule);
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Guard#u8"), scopeSite(provenance
                            ? StaticScopeMap.PROVENANCE_SITE
                            : StaticScopeMap.READ_SITE, "",
                    "Router#hash#u2", "Router#hash",
                    "<D: Slice[] active>", "<D: Slice[] active>", ""));
            Path out = tree.newFolder("store-" + at + "-out").toPath();
            Path results = results(out);
            Path wave = out.resolve("obligations-0000");
            JsonObject manifest = plan(iteration,
                    "solr-case/client0#epoch0/region/REGION.target#1", null,
                    results, wave, 0);
            Set<String> focused = new LinkedHashSet<String>();
            for (JsonElement task : manifest.getAsJsonArray("taskRows")) {
                focused.add(task.getAsJsonObject().get("focused")
                        .getAsString());
            }
            String label = "case " + at + ": " + focused;
            assertEquals(label, cases[at][2], Arrays.asList(
                    focused.contains(last.render()),
                    focused.contains(first.render()),
                    focused.contains(restore.render())));
            assertEquals(label, (Boolean) ((List<?>) cases[at][2]).get(2),
                    named(obligations(wave), "Door#u3") != null);
        }
    }

    private static final class Session {
        private final SessionDir dir;
        private final String sessionId;
        private final List<ActivationRow> activations = new ArrayList<>();
        private final List<DecisionRow> decisions = new ArrayList<>();
        private final List<ExportRow> exports = new ArrayList<>();
        private final List<AttachRow> attaches = new ArrayList<>();
        private final List<WriteRow> writes = new ArrayList<>();
        private final List<ReadRow> reads = new ArrayList<>();
        private final List<RootMintRow> roots = new ArrayList<>();
        private final List<TargetRow> targets = new ArrayList<>();
        private final List<GapRow> gaps = new ArrayList<>();
        private final List<ObligationResult> answered = new ArrayList<>();
        private boolean forced;
        private final Map<String, String> spelled =
                new LinkedHashMap<String, String>();
        private final Set<String> doorsOnly = new TreeSet<String>();
        private final Set<String> clients = new TreeSet<String>();
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<>();
        private long seq;

        private Session(Path iteration, String sessionId) {
            this.dir = SessionDir.of(iteration, sessionId);
            this.sessionId = sessionId;
        }

        private void activation(OccurrenceAddress occurrence,
                                boolean focused) {
            activation(occurrence, focused, true);
        }

        private void activation(OccurrenceAddress occurrence, boolean focused,
                                boolean instrumented) {
            activation(occurrence, focused, instrumented,
                    "fixture#" + occurrence.node().node());
        }

        private void activation(OccurrenceAddress occurrence, boolean focused,
                                boolean instrumented, String thread) {
            activations.add(ActivationRow.of(sessionId, occurrence,
                    "task-" + occurrence.regionId(), focused, instrumented,
                    thread, ActivationRow.ClaimKind.NONE, null));
        }

        private void activations(boolean focused,
                                 OccurrenceAddress... occurrences) {
            for (OccurrenceAddress occurrence : occurrences) {
                activation(occurrence, focused);
            }
        }

        private void spelled(String node, String spelling) {
            spelled.put(spelling, node);
        }

        private void decision(OccurrenceAddress occurrence, String site,
                              int ordinal, boolean outcome, String term) {
            decisions.add(DecisionRow.of(sessionId, ++seq, occurrence, site,
                    ordinal, outcome, term,
                    Collections.<String, Long>emptyMap()));
        }

        private void target(OccurrenceAddress occurrence, String site,
                            String phi) {
            targets.add(TargetRow.of(sessionId, ++seq, occurrence, site, phi,
                    false, true, null));
        }

        private void anchored(OccurrenceAddress occurrence) {
            target(occurrence, "BlockTokenSecretManager"
                    + "#retrieveDataEncryptionKey#8", "(= M_READ_KEY 0)");
        }

        private void fatal(OccurrenceAddress occurrence, String site,
                           String phi) {
            targets.add(TargetRow.of(sessionId, ++seq, occurrence, site, phi,
                    true, true, null));
        }

        private void root(OccurrenceAddress occurrence, String rootId,
                          String symbol, RootKind kind, String recorded,
                          String min, String max, boolean declared) {
            roots.add(RootMintRow.of(sessionId, ++seq, occurrence, rootId,
                    symbol, kind, kind == RootKind.CLOCK ? RootCategory.CLOCK
                            : kind == RootKind.MARKER ? RootCategory.FAULT
                            : RootCategory.HOOK, recorded, min, max, declared,
                    kind == RootKind.CLOCK
                ? Clock.of(1_000_000L, Clock.WALL) : null, 0L));
        }

        private void marker(OccurrenceAddress at, String rootId,
                            String symbol, String recorded) {
            root(at, rootId, symbol, RootKind.MARKER, recorded, null, null,
                    true);
        }

        private void integral(OccurrenceAddress at, String rootId,
                              String symbol, String recorded, String min,
                              String max) {
            root(at, rootId, symbol, RootKind.INTEGRAL, recorded, min, max,
                    true);
        }

        private void export(Endpoint endpoint, String ref, long handle,
                            String recorded) {
            exports.add(ExportRow.of(sessionId, ++seq, endpoint, ref, "I",
                    handle, recorded));
        }

        private void attach(Endpoint endpoint, String symbol, String arrival,
                            Endpoint producer) {
            attaches.add(AttachRow.of(sessionId, ++seq, endpoint, symbol, "I",
                    arrival, false, null, producer,
                    "corr-" + endpoint.siteIndex().hash(),
                    producer == null ? "" : "HANDLE"));
        }

        private void write(Endpoint endpoint, LocationId location,
                           long version, String ref) {
            write(endpoint, location, version, ref, "I");
        }

        private void write(Endpoint endpoint, LocationId location,
                           long version, String ref, String javaType) {
            writes.add(WriteRow.of(sessionId, ++seq, endpoint, location,
                    version, ref, javaType));
        }

        private long read(Endpoint endpoint, LocationId location,
                          long version, String symbol, String concrete) {
            reads.add(ReadRow.of(sessionId, ++seq, endpoint, location, version,
                    symbol, "I", concrete));
            return seq;
        }

        private void initial(Endpoint endpoint, LocationId location,
                             long version, String ref) {
            writes.add(WriteRow.initial(sessionId, ++seq, endpoint, location,
                    version, ref, "Z"));
        }

        private void mint(Endpoint endpoint, LocationId location,
                          long version, String symbol, String concrete) {
            reads.add(ReadRow.of(sessionId, ++seq, endpoint, location, version,
                    symbol, "J", concrete, version));
        }

        private void keyChain() {
            activation(WRITER, false);
            activation(PRODUCER, false);
            constant("e.119992", "119992");
            symbolic("e.stored", "M_HOFF_KEY");
            export(ROTATED, "e.119992", 11L, "119992");
            attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
            write(STORED, ALL_KEYS, 5L, "e.stored");
            read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        }

        private void symbolic(String ref, String symbol) {
            symbolic(ref, symbol, "I");
        }

        private void symbolic(String ref, String symbol, String javaType) {
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "SymbolExpression");
            expression.addProperty("_exp", symbol);
            expression.addProperty("_java_type", javaType);
            expressions.put(ref, expression);
        }

        private void expression(String ref, JsonObject node) {
            expressions.put(ref, node);
        }

        private void constant(String ref, String value) {
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("_exp", "C_I_" + value);
            expression.addProperty("_java_type", "I");
            expressions.put(ref, expression);
        }

        private void answered(ObligationResult result) {
            answered.add(result);
        }

        private void gap(GapRow gap) {
            gaps.add(gap);
        }

        private void flush() throws IOException {
            dir.create();
            RowCodec.writeAll(dir.obligations(), answered,
                    RowCodec::writeObligationResult);
            RowCodec.writeAll(dir.activations(), activations,
                    RowCodec::writeActivation);
            RowCodec.writeAll(dir.decisions(), decisions,
                    RowCodec::writeDecision);
            RowCodec.writeAll(dir.exports(), exports, RowCodec::writeExport);
            RowCodec.writeAll(dir.attaches(), attaches, RowCodec::writeAttach);
            RowCodec.writeAll(dir.writes(), writes, RowCodec::writeWrite);
            RowCodec.writeAll(dir.reads(), reads, RowCodec::writeRead);
            RowCodec.writeAll(dir.roots(), roots, RowCodec::writeRootMint);
            RowCodec.writeAll(dir.targets(), targets, RowCodec::writeTarget);
            RowCodec.writeAll(dir.gaps(), gaps, RowCodec::writeGap);
            ExpressionLogs.write(dir.expressions(), expressions);
            boolean focused = false;
            for (ActivationRow activation : activations) {
                if (activation.focused()) focused = true;
            }
            List<String> ran = new ArrayList<String>();
            for (ObligationResult result : answered) {
                ran.add(result.obligationId());
            }
            RowCodec.writeManifest(dir.manifest(),
                    SessionManifest.of(sessionId,
                            forced ? SessionManifest.Role.FORCED
                                    : focused ? SessionManifest.Role.FOCUSED
                                    : SessionManifest.Role.SEED,
                            forced ? ran : focused
                                    ? Collections.singletonList(
                                    "OBL." + sessionId)
                                    : Collections.<String>emptyList())
                            .atClose(null, null, null, spelled, doorsOnly,
                                    null, clients));
        }
    }

    @Test
    public void aModelsWorldIsWhatItPlantsNotThePathItWasAskedFrom() {
        String base = "{\"focusedOccurrenceId\":\"occ1\",\"obligationId\":"
                + "\"OB.%s\",\"pathId\":\"%s\",\"pathSessionId\":\"%s\","
                + "\"flip\":{\"siteId\":\"%s\",\"ordinal\":1,"
                + "\"outcome\":true},\"inheritedFlips\":[],"
                + "\"rootAssignments\":{\"%s\":\"true\"},\"clockDeltas\":{},"
                + "\"answers\":{},\"pairings\":{},\"schedulePrefix\":"
                + "{\"sessionId\":\"%s\",\"events\":%d}}";
        String seed = String.format(base, "a", "p1", "seed", "a.C#u61",
                "ROOT.door.IOE", "seed", 1612);
        Object[][] table = {
                {"asked from a re-run's path", String.format(base, "b", "p2",
                        "rerun1", "a.C#u61", "ROOT.door.IOE", "rerun1", 2405),
                        true},
                {"another fault kind", String.format(base, "c", "p2",
                        "rerun1", "a.C#u66", "ROOT.door.CCE", "rerun1", 2405),
                        false},
                {"the same root at another decision", String.format(base, "d",
                        "p1", "seed", "a.C#u70", "ROOT.door.IOE", "seed",
                        1612), false},
        };
        String world = ObligationFactory.wholeWorldDigest(ExploreCodec.readWorld(
                JsonParser.parseString(seed).getAsJsonObject()));
        for (Object[] row : table) {
            String other = ObligationFactory.wholeWorldDigest(
                    ExploreCodec.readWorld(JsonParser.parseString(
                            (String) row[1]).getAsJsonObject()));
            assertEquals((String) row[0], row[2], world.equals(other));
        }
    }

}
