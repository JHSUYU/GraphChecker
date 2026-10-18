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
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
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
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * Exploration, checked on the five things a corpus can say to it.
 *
 * <p>Each case is a synthetic corpus in the contract's own file layout, driven
 * exactly as the campaign drives the stage: one planner invocation per wave
 * ({@link ExploreMain}), one solver per obligation
 * ({@link ObligationSolverMain}), verdicts appended to the results file the
 * next wave reads.  The queries are solved by the same z3 the campaign uses,
 * so an assertion about SAT or UNSAT is an assertion about the query.</p>
 */
public class ExploreTest {
    /** The bounds a round runs with when the case states none. */
    private static final ObligationFactory.Bounds DEFAULT_BOUNDS =
            new ObligationFactory.Bounds(
                    ObligationFactory.DEFAULT_MAX_PATHS_PER_TASK,
                    ObligationFactory.DEFAULT_MAX_FLIPS_PER_PATH,
                    ObligationFactory.DEFAULT_MAX_WORLD_DEPTH);

    /** What a case declares: a v1 selector, resolved against the seed. */
    private static final String TARGET_SELECTOR =
            "hdfs-case/dn0#epoch0/region/REGION.target#1";
    /** The NameNode's key rotation: a daemon tick, nobody's request. */
    private static final OccurrenceAddress PRODUCER = occurrence("hdfs-case/nn0",
            "REGION.rotate", CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", 1),
            "o.a.h.h.s.b.BlockManager#run#8");
    /** The data node's fatal read: its own DataXceiver op. */
    private static final OccurrenceAddress TARGET = occurrence("hdfs-case/dn0",
            "REGION.target", CausalContext.of(Role.of("DATA_XCEIVER"), "", 1),
            "o.a.h.h.s.d.DataXceiver#run#12");
    /** addKeys on the same node: started by the rotation's own delivery. */
    private static final OccurrenceAddress WRITER = occurrence("hdfs-case/dn0",
            "REGION.addkeys", CausalContext.of(exportedId(),
                    "DatanodeProtocol#registerDatanode"),
            "o.a.h.h.s.d.BPServiceActor#offerService#41");
    /** A node of its own, whose flips reach neither of the two above. */
    private static final OccurrenceAddress BALANCER =
            occurrence("hdfs-case/balancer", "REGION.balance",
                    CausalContext.of(Role.of("BALANCER"), "", 1),
                    "o.a.h.h.b.Balancer#run#3");
    /** The map addKeys writes and the target reads: one location, one node. */
    /** No roots, no clock deltas. */
    private static final Map<String, String> NONE = Collections.emptyMap();
    /** {@code Corpus#inputShape} of a guard stating no handoff. */
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
    /**
     * A second reader of that map on the target's node, started by a
     * message of its own.
     *
     * <p>It is a member of the target's factor -- it touches the location
     * the target reads -- and it is NOT upstream of the target: it reads
     * what the target reads and writes nothing for it.  So what reaches
     * IT reaches the task only through the factor, which is what a
     * reaching set seeded from the focused occurrence alone would lose.
     * dn1's SASL handler is this occurrence on hdfs-11741: it sits beside
     * {@code addKeys} on the map, and the Balancer's token arrives at
     * it.</p>
     */
    private static final OccurrenceAddress READER =
            occurrence("hdfs-case/dn0", "REGION.reader",
                    CausalContext.of(Role.of("DATA_XCEIVER"), "", 2),
                    "o.a.h.h.s.d.DataXceiver#run#44");
    /** The node whose message that second reader is started by. */
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

    /** A system declaring Solr's published views (PUBLISHED_VIEW): a
     *  pairing flip of a view no hook publishes is never asked. */
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

    /**
     * A FORCE RUN KILLED PAST ITS BOUND ANSWERED NOTHING (PIPELINE §7.10,
     * §7.6), as a flip's killed replay does ({@link Frontier#consume}, by
     * the flip its row states, {@link ForcedFlip#flip}): it is asked again;
     * killed twice with no forced session landed it is held unasked, its
     * state BOUNDED and named in the round's {@code boundedFlips}
     * (campaign_bounds' {@code replay_timeout_s}), so no UNSAT rests on a
     * forced replay that ran nothing.  A replay that decided it (here
     * FORCE_DIVERGED) answers it, under the same flip.
     */
    @Test
    public void aKilledForceRunIsAskedAgainThenHeldBounded() throws Exception {
        String killed = ObligationResult.REPLAY_BOUNDED + ": replay exceeded"
                + " replay_timeout_s=2400";
        String diverged = "FORCE_DIVERGED: the occurrence closed first";
        Object[][] rows = {
            // its replays' details, in the order they landed; whether the
            // next round asks it again; its state there; the round's
            // boundedFlips
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
                // Its worker, in the iteration as the pool places it: the
                // solver's question, then what its replay came to.
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

    // ---- (1) depth: one decision per wave -----------------------------

    @Test
    public void nestedGuardChainDeepensOneDecisionPerWave() throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("depth").toPath();
        OccurrenceAddress target = TARGET;
        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, false);
        seed.marker(target, "CASE.MARKER", "M_MARKER", "false");
        seed.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        // Three more declared roots the recording minted, none of them named
        // by any predicate of the seed's own path: the rotation's tick,
        // whose guard a LATER session flips; a clock; and one root no term
        // ever reaches.  A world is inherited whole, so the wave that
        // extends one has to find every root of it minted here -- an
        // assignment is planted at the recording's mint and nowhere else.
        seed.integral(PRODUCER, "CASE.TICK", "M_TICK", "1", "0", "10");
        seed.clock(target, "CASE.NOW", "M_NOW", "1000");
        seed.integral(target, "CASE.SPARE", "M_SPARE", "3", "0", "10");
        // if (a) if (b) throw: the recording took not-a and never reached b.
        // The predicate is published the way the VM publishes one over a
        // propagated value: a REFERENCE into the session's expression
        // table, which the one lowering resolves for the flip query too.
        seed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        seed.decision(target, "Guard#u8", 1, false, "EXPR.0000000000000001");
        // A CONCRETE branch beside it: no predicate, so nothing to flip.
        seed.decision(target, "Concrete#u3", 1, false, "");
        // One PLANNED task, run at two addresses.  That is the one thing
        // that can split an owed arm in two -- the arms answered at the
        // first address settle nothing at the second -- so every wave names
        // it, and the repair is upstream of any wave.
        seed.activation(occurrence("hdfs-case/dn0", "REGION.spare",
                CausalContext.of(Role.of("SPARE"), "", 1),
                "o.a.h.Spare#run#1"), false);
        seed.activation(occurrence("hdfs-case/dn0", "REGION.spare",
                CausalContext.of(Role.of("SPARE"), "", 1),
                "o.a.h.Spare#run#2"), false);
        // The state edge the last part of this case rests on: addKeys on the
        // same node writes the map the target reads, so it is a
        // STATE-CONNECTED member of the target's factor -- one symbolic unit,
        // and what it received is what the target reads.
        seed.keyChain();
        seed.flush();
        // What the wave may flip in the anchor is the guard set of the
        // declared target, and nothing else (PIPELINE §7.2).  The target's
        // region reads the key map addKeys stores (a READ_SITE): what the
        // writer delivers is part of every arm's world, whichever arm read
        // it (Corpus#inputShape).
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8", "Guard#u19"),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", "")),
                scopeSite(StaticScopeMap.READ_SITE, "REGION.target",
                        "BlockTokenSecretManager#u8",
                        "BlockTokenSecretManager#retrieveDataEncryptionKey",
                        "<example.Manager: example.Keys allKeys>",
                        "<example.Manager: example.Keys allKeys>", ""));

        // M3c: the recorded symbols of a term are the ones REACHABLE from
        // it -- the tokens the text shows are only the first hop.  The one
        // lowering answers that question, and the closure is what gives a
        // handoff inside a shared subterm its family, its control and its
        // answer.
        Corpus reading = Corpus.read(iteration, null);
        SmtLowering lowering = reading.lowering("s-seed");
        SmtLowering.Lowered phi = lowering.lower("EXPR.0000000000000001");
        assertTrue("the reference lowers", phi.ok());
        boolean reaches = false;
        for (SmtLowering.Declaration declaration
                : lowering.reachedBy(Collections.singletonList(phi.text()))) {
            reaches |= declaration.body.isEmpty()
                    && "M_MARKER".equals(declaration.name);
        }
        assertTrue("and the query states exactly what it reaches", reaches);

        Path out = tree.newFolder("depth-out").toPath();
        Path results = results(out);

        Path wave0 = out.resolve("obligations-0000");
        JsonObject first = plan(iteration, TARGET_SELECTOR, null, results, wave0, 0);
        assertEquals("OBLIGATIONS_PROPOSED", first.get("state").getAsString());
        List<Obligation> proposed = obligations(wave0);
        assertEquals(1, proposed.size());
        assertEquals("Guard#u8", proposed.get(0).siteId());
        assertTrue(proposed.get(0).flippedOutcome());
        for (Obligation obligation : proposed) {
            assertFalse("a branch the recording states no predicate for is "
                            + "not a flip: there is nothing to negate",
                    "Concrete#u3".equals(obligation.siteId()));
        }
        Worker worker = solve(iteration, wave0, proposed.get(0), out, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, worker.verdict);
        assertEquals("true",
                worker.obligation.rootAssignments().get("CASE.MARKER"));
        // THE HARD LANE'S MODEL, FINISHED BY THE CORPUS: a first ask out of
        // budget leaves its record, the hard lane decides it with no corpus,
        // and its model is planted as it is: the same world the corpus's own
        // ask planted.  (w0's answer is kept by its text, Solved: the first
        // ask is of a store without it, or no budget would run out.)
        deleteTree(iteration.resolve(Solved.DIR));
        Path hard = out.resolve("hard");
        ObligationSolverMain.solve(Corpus.read(iteration, null), iteration,
                wave0.resolve("obligations.jsonl"),
                proposed.get(0).obligationId(), hard, Paths.get("z3"), 1L,
                1152, null);
        ObligationSolverMain.decide(wave0.resolve("obligations.jsonl"),
                proposed.get(0).obligationId(), hard, Paths.get("z3"),
                10_000L, 1152);
        HardAsk.Model model = HardAsk.Model.read(
                hard.resolve(HardAsk.Model.FILE));
        Path finish = out.resolve("finish");
        ObligationSolverMain.solve(Corpus.read(iteration, null), iteration,
                wave0.resolve("obligations.jsonl"),
                proposed.get(0).obligationId(), finish, Paths.get("z3"),
                10_000L, 1152, model);
        assertEquals(worker.obligation, RowCodec.readAll(finish.resolve(
                ObligationDir.OBLIGATION), ExploreCodec::readObligation)
                .get(0));
        // A model over another query than the corpus builds now is refused
        // by name: no replay is owed (no focus row), no re-ask.
        Path stale = out.resolve("stale");
        ObligationSolverMain.solve(Corpus.read(iteration, null), iteration,
                wave0.resolve("obligations.jsonl"),
                proposed.get(0).obligationId(), stale, Paths.get("z3"),
                10_000L, 1152, new HardAsk.Model("another", model.values,
                        10_000L, 1152));
        ObligationResult staleAnswer = RowCodec.readAll(stale.resolve(
                ObligationDir.RESULT), RowCodec::readObligationResult).get(0);
        assertEquals(Verdict.NOT_ADMITTED, staleAnswer.verdict());
        assertTrue(staleAnswer.detail(), staleAnswer.detail().startsWith(
                ObligationFactory.HARD_MODEL_STALE + ":"));
        assertEquals(0L, Files.size(stale.resolve(
                ObligationDir.FOCUSED_TASK)));
        // SEATS: questions asked of one corpus at once, each in a state of
        // its own (Corpus#asking), write the files a corpus read for each
        // alone writes, whichever ran beside or before them.
        Path alone = out.resolve("alone");
        ObligationSolverMain.solve(Corpus.read(iteration, null), iteration,
                wave0.resolve("obligations.jsonl"),
                proposed.get(0).obligationId(), alone, Paths.get("z3"),
                10_000L, 1152, null);
        // Every seat's z3 runs beside the others': none kept yet.
        deleteTree(iteration.resolve(Solved.DIR));
        Corpus shared = Corpus.read(iteration, null);
        List<Thread> seats = new ArrayList<>();
        List<Throwable> failed = Collections.synchronizedList(
                new ArrayList<>());
        for (int seat = 0; seat < 4; seat++) {
            Path beside = out.resolve("beside-" + seat);
            Thread thread = new Thread(() -> {
                try {
                    ObligationSolverMain.solve(shared, iteration,
                            wave0.resolve("obligations.jsonl"),
                            proposed.get(0).obligationId(), beside,
                            Paths.get("z3"), 10_000L, 1152, null);
                } catch (Throwable thrown) {
                    failed.add(thrown);
                }
            });
            seats.add(thread);
            thread.start();
        }
        for (Thread thread : seats) thread.join();
        assertEquals("the seats' questions failed: " + failed, 0,
                failed.size());
        List<Path> written = new ArrayList<>();
        try (java.util.stream.Stream<Path> files = Files.list(alone)) {
            files.sorted().forEach(written::add);
        }
        assertFalse(written.isEmpty());
        for (int seat = 0; seat < 4; seat++) {
            for (Path file : written) {
                assertTrue("seat " + seat + ": " + file.getFileName(),
                        java.util.Arrays.equals(Files.readAllBytes(file),
                                Files.readAllBytes(out.resolve("beside-"
                                        + seat).resolve(file.getFileName()))));
            }
        }
        // The focus row is its own file.  execution_task_plan.jsonl is the
        // PLAN's name, and the workload session opener decodes whatever
        // stands under it, so a focus row written there killed every
        // obligation replay with "execution task requires sourceKey".
        assertFalse("the solver writes no plan",
                Files.exists(worker.directory.resolve(
                        "execution_task_plan.jsonl")));
        JsonObject focus = RowCodec.readJsonl(worker.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        assertEquals("FOCUSED_TASK", focus.get("kind").getAsString());
        assertEquals("the row states WHICH occurrence it focuses",
                target.render(), focus.get("focused").getAsString());
        assertEquals(target.id(),
                focus.get("focusedOccurrenceId").getAsString());
        assertEquals("s-seed", focus.get("seedSessionId").getAsString());
        assertEquals("Guard#u8",
                focus.getAsJsonObject("flip").get("siteId").getAsString());

        // Polarity, asked exactly once.  The recorded conjunct is
        // outcome ? term : (not term) and the obligation asserts its
        // negation, so a MODEL of the query makes the published term equal
        // to the flipped outcome -- whatever polarity the term itself
        // carries.  The last row below is 17960's own shape: a "!=" term,
        // which lowers with a (not ...) of its own, and where one extra
        // negation made the flip ask for the seed's own value.
        flipAsksTheOtherArmOnce("(= M_MARKER false)", false, "true", "false");
        flipAsksTheOtherArmOnce("(= M_MARKER false)", true, "false", "true");
        flipAsksTheOtherArmOnce("(not (= M_MARKER false))", true, "true",
                "false");
        // And a model that hands the root back the recording's own value
        // asks for the seed replay: refused by name, never run.
        flipAsksTheOtherArmOnce("(not (= M_MARKER false))", false, "true",
                null);

        // The campaign replayed it: the flip took the first guard and
        // recorded the second one, which had never executed before.
        Session flipped = new Session(iteration, "s-flip");
        flipped.activation(target, true);
        flipped.marker(target, "CASE.MARKER", "M_MARKER", "true");
        flipped.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        flipped.decision(target, "Guard#u8", 1, true, "M_MARKER");
        flipped.decision(target, "Guard#u19", 1, false, "(> M_COUNT 5)");
        // A replay records every instrumented occurrence it ran, so what the
        // target's factor received and wrote is here as it was in the seed:
        // the flip changed nothing the target received.
        flipped.keyChain();
        // The replay states its own verdict: only an ADMITTED session's
        // path is cut from.
        flipped.answered(ObligationResult.of(proposed.get(0).obligationId(),
                Verdict.ADMITTED, "s-flip", "the flip ran"));
        flipped.flush();
        record(results, ObligationResult.of(proposed.get(0).obligationId(),
                Verdict.ADMITTED, "s-flip", "the flip ran"));

        Path wave1 = out.resolve("obligations-0001");
        plan(iteration, TARGET_SELECTOR, null, results, wave1, 1);
        List<Obligation> next = obligations(wave1);
        List<String> sites = new ArrayList<String>();
        for (Obligation obligation : next) sites.add(obligation.siteId());
        assertTrue("the deeper guard is a first-class obligation: " + sites,
                sites.contains("Guard#u19"));
        for (Obligation obligation : next) {
            assertFalse("a query answered by an earlier wave is never re-asked",
                    obligation.obligationId().equals(
                            proposed.get(0).obligationId()));
            // An arm SOME session of the epoch already took under what its
            // guard depends on is not asked for again, whichever session
            // holds the row: the seed took Guard#u8 false and the flip
            // replay took it true, both on the EMPTY prefix and the seed's
            // inputs, so both arms of that site are attested there and a
            // replay of either collects nothing the corpus lacks.  On laneA6
            // wave 1 this was the marker decision flipped BACK to true out
            // of the wave-0 replays: nine minutes each.  The same arm in a
            // DIFFERENT world is another obligation, and the last part of
            // this case is that one.
            assertFalse("an arm the corpus already holds is not re-flipped: "
                            + sites, "Guard#u8".equals(obligation.siteId()));
        }
        assertTrue("and the wave says which session holds it",
                anyGap(wave1, gap -> gap.cls() == GapClass.DIAGNOSTIC
                        && gap.subject().startsWith("Guard#u8#1 -> ")
                        && gap.detail().contains("arm already recorded by")));
        // The deeper obligation carries the earlier wave's answer in its own
        // prefix: it needs the marker true AND the count above five.
        Obligation deeper = named(next, "Guard#u19");
        assertNotNull(deeper);
        Worker second = solve(iteration, wave1, deeper, out, "w1");
        assertEquals(Verdict.SAT_MODEL_READY, second.verdict);
        // The marker's arm shares nothing with the count: held as s-flip
        // ran it, not asked again (FlipQuery#cone).
        assertTrue(Integer.parseInt(
                second.obligation.rootAssignments().get("CASE.COUNT")) > 5);

        // An arm is owed ONCE per PLANNED OCCURRENCE, not once per session.
        // The deeper guard's flip is answered NOT_ADMITTED -- and a replay
        // that is not admitted records no arm, so no DecisionRow of it
        // exists anywhere -- and then another session runs the same
        // occurrence and records another path of it.  A second path is a
        // second pathId, and while the obligation id carried one, the next
        // wave re-proposed the answered arm out of it: on the 11741 corpus
        // (81 sessions) wave 0's 36 answers left 30 arms unrecorded and
        // wave 1 asked those same 30 facts as 706 obligations.
        record(results, ObligationResult.of(deeper.obligationId(),
                Verdict.NOT_ADMITTED, "", ObligationResult.WORLD_RAN
                + ": the focused occurrence ran its world and never reached"
                + " Guard#u19"));
        Session other = new Session(iteration, "s-flip-2");
        other.activation(target, true);
        other.marker(target, "CASE.MARKER", "M_MARKER", "true");
        other.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        other.decision(target, "Guard#u8", 1, true, "M_MARKER");
        other.decision(target, "Guard#u19", 1, false, "(> M_COUNT 5)");
        other.flush();
        List<Corpus.RecordedPath> grown =
                Corpus.read(iteration, null).pathsOf(target);
        assertEquals("three sessions ran the occurrence", 3, grown.size());
        assertFalse("and each of them minted its own pathId",
                grown.get(1).pathId.equals(grown.get(2).pathId));

        Path wave2 = out.resolve("obligations-0002");
        JsonObject third = plan(iteration, TARGET_SELECTOR, null, results,
                wave2, 2);
        assertEquals("every arm of this occurrence is settled -- recorded by "
                        + "some session, or answered by some wave -- so the "
                        + "frontier closes however many sessions hold a path "
                        + "of it", "FIXED_POINT",
                third.get("state").getAsString());
        assertTrue("an answered arm is never re-proposed out of a new "
                        + "session's path: " + obligations(wave2),
                obligations(wave2).isEmpty());
        assertTrue("and the wave says which answer settled it",
                anyGap(wave2, gap -> gap.cls() == GapClass.DIAGNOSTIC
                        && gap.subject().equals("Guard#u19#1 -> true")
                        && gap.detail().contains("already answered "
                                + "NOT_ADMITTED") && gap.detail().contains(
                                "owed once per planned occurrence")));
        assertTrue("and a planned task answered at two addresses is named",
                anyGap(wave2, gap -> gap.kind() == GapKind.ADDRESS_UNSTABLE
                        && gap.cls() == GapClass.DIAGNOSTIC
                        && gap.subject().equals("task-REGION.spare")
                        && gap.detail().contains("answered at 2 addresses")));

        // ---- the same arm, another world --------------------------------
        //
        // A NESTED obligation extends its parent's world.  s-other-prefix
        // reaches Guard#u19 after flipping the ROTATION's own guard, under
        // root values and a clock skew of its own, and in its world addKeys
        // never ran: the target's unit received something no session of
        // this corpus delivered.  (Its extra concrete decision is not what
        // makes the arm owed: the guard does not depend on it.)  Three
        // things follow, and this is 11741's shape: the arm is owed again in
        // THAT world, the obligation cut from that path inherits the world
        // its path exists in, and the parent's flipped conjunct holds by
        // that world's roots wherever it shares nothing with the flip.
        Session world = new Session(iteration, "s-other-prefix");
        world.activations(true, target, PRODUCER);
        world.marker(target, "CASE.MARKER", "M_MARKER", "true");
        world.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        world.integral(PRODUCER, "CASE.TICK", "M_TICK", "7", "0", "10");
        world.decision(PRODUCER, "Rotate#u5", 1, true, "(> M_TICK 3)");
        world.decision(target, "Concrete#u3", 1, true, "");
        world.decision(target, "Guard#u8", 1, true, "M_MARKER");
        world.decision(target, "Guard#u19", 1, false, "(> M_COUNT 5)");
        world.answered(ObligationResult.of("OBL.other", Verdict.ADMITTED,
                "s-other-prefix", "the focused prefix reproduced"));
        world.flush();
        // Its own focus row, where the campaign writes one: this is what
        // the corpus reads a session's WORLD off.
        Map<String, String> assigned = new LinkedHashMap<String, String>();
        assigned.put("CASE.MARKER", "true");
        assigned.put("CASE.TICK", "7");
        assigned.put("CASE.SPARE", "9");
        Map<String, String> skew = new LinkedHashMap<String, String>();
        skew.put("CASE.NOW", "-4200");
        worker(iteration, "obligations-0000", "ob-other", "OBL.other",
                "s-other-prefix", PRODUCER, "Rotate#u5", assigned, skew);

        // And a session whose replay REFUSED its own obligation: its rows
        // still attest the arms it took, and no wave cuts a flip from its
        // paths, because a world is only a world if the replay that ran it
        // was admitted.
        Session refused = new Session(iteration, "s-refused");
        refused.activation(target, true);
        refused.marker(target, "CASE.MARKER", "M_MARKER", "true");
        refused.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        refused.decision(target, "Concrete#u3", 1, false, "");
        refused.decision(target, "Concrete#u7", 1, true, "");
        refused.decision(target, "Guard#u8", 1, true, "M_MARKER");
        refused.decision(target, "Guard#u19", 1, false, "(> M_COUNT 5)");
        refused.answered(ObligationResult.of("OBL.refused",
                Verdict.NOT_ADMITTED, "s-refused",
                "the focused occurrence's own prefix did not match"));
        refused.flush();

        Path wave3 = out.resolve("obligations-0003");
        JsonObject fourth = plan(iteration, TARGET_SELECTOR, null, results,
                wave3, 3);
        assertEquals("OBLIGATIONS_PROPOSED", fourth.get("state").getAsString());
        List<Obligation> deepened = new ArrayList<Obligation>();
        for (Obligation obligation : obligations(wave3)) {
            if ("Guard#u19".equals(obligation.siteId())) {
                deepened.add(obligation);
            }
        }
        assertEquals("the settled arm is owed again in the world no "
                        + "session has taken it in, and exactly once: "
                        + obligations(wave3), 1, deepened.size());
        assertEquals("cut from the admitted session's path",
                Corpus.pathId("s-other-prefix", target),
                deepened.get(0).pathId());
        for (Obligation obligation : obligations(wave3)) {
            assertFalse("a NOT_ADMITTED session's path is not cut from: "
                            + obligation,
                    Corpus.pathId("s-refused", target)
                            .equals(obligation.pathId()));
        }

        Worker nested = solve(iteration, wave3, deepened.get(0), out, "w3");
        assertEquals(Verdict.SAT_MODEL_READY, nested.verdict);
        JsonObject inherited = RowCodec.readJsonl(nested.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        assertEquals("the world's clock skew is carried whole: nothing in "
                        + "this model moves that clock, and the path only "
                        + "exists under it", "-4200",
                inherited.getAsJsonObject("clockDeltas")
                        .get("CASE.NOW").getAsString());
        assertEquals("and so is a root this query never reaches", "9",
                inherited.getAsJsonObject("rootAssignments")
                        .get("CASE.SPARE").getAsString());
        assertEquals("and the ask states the merged valuation too", "9",
                nested.obligation.rootAssignments().get("CASE.SPARE"));
        assertEquals("the parent's own flip travels with it", 1,
                inherited.getAsJsonArray("inheritedFlips").size());
        JsonObject carried = inherited.getAsJsonArray("inheritedFlips")
                .get(0).getAsJsonObject();
        assertEquals(PRODUCER.id(),
                carried.get("focusedOccurrenceId").getAsString());
        assertEquals("Rotate#u5", carried.get("siteId").getAsString());
        assertTrue(carried.get("outcome").getAsBoolean());
        assertEquals("named by the obligation that first asked for it",
                "OBL.other", carried.get("obligationId").getAsString());
        String query = new String(Files.readAllBytes(
                nested.directory.resolve("obligation_query.smt2")), "UTF-8");
        // The parent's flipped conjunct shares nothing with this guard
        // (FlipQuery#cone): it holds as the world ran it, its root carried
        // whole, so the query need not state it.
        assertFalse("the parent's flip is out of this guard's cone: " + query,
                query.contains("r_CASE_TICK"));
        assertEquals("and held by the world's own root", "7",
                nested.obligation.rootAssignments().get("CASE.TICK"));

        // ---- the same LOCAL path, in a world that changed what the region
        //      received ---------------------------------------------------
        //
        // An unexplored local path of a known region is still work, and so is
        // a KNOWN local path in a world that changed what the region
        // received -- never the same path in a world that changed nothing for
        // it.  11741's missing obligation is the second of those.  dn1's
        // expiry scan runs over the DataNode's own old map BEFORE the put
        // loop, so its own decisions are letter for letter the seed's in
        // every world; what nn0's second rotation changed is the addKeys
        // occurrence beside it, which writes the very map the scan reads and
        // is therefore a member of its factor.  Three admitted sessions, each
        // with a world of its own, say the whole rule.
        //
        // Z: the target's OWN earlier flip, and otherwise the seed's rows.
        Session zed = new Session(iteration, "s-world-z");
        zed.activation(target, true);
        zed.activation(WRITER, false);
        zed.marker(target, "CASE.MARKER", "M_MARKER", "true");
        zed.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        zed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        zed.symbolic("e.stored", "M_HOFF_KEY");
        zed.constant("e.119992", "119992");
        zed.decision(target, "Guard#u8", 1, true, "EXPR.0000000000000001");
        zed.decision(target, "Concrete#u3", 1, false, "");
        zed.export(ROTATED, "e.119992", 11L, "119992");
        zed.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        zed.write(STORED, ALL_KEYS, 5L, "e.stored");
        zed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        zed.answered(ObligationResult.of("OBL.world-z", Verdict.ADMITTED,
                "s-world-z", "the focused prefix reproduced"));
        zed.flush();
        worker(iteration, "obligations-0001", "ob-world-z", "OBL.world-z",
                "s-world-z", target, "Guard#u8",
                Collections.singletonMap("CASE.MARKER", "true"), NONE);

        // Y: nn0's rotation flipped.  Its rows AT THE TARGET are the seed's,
        // letter for letter; what its world changed is the STRUCTURE of what
        // addKeys received -- one handoff more, because the rotation it was
        // held to delivered one key more -- and addKeys writes what the
        // target reads.  (11741: four attaches instead of five.  A member
        // that received nothing at all and wrote nothing the guard reads is
        // no line: it is no conjunct of the guard's query.)
        Session wye = new Session(iteration, "s-world-y");
        wye.activation(PRODUCER, true);
        wye.activations(false, target, WRITER);
        wye.integral(PRODUCER, "CASE.TICK", "M_TICK", "7", "0", "10");
        wye.marker(target, "CASE.MARKER", "M_MARKER", "false");
        wye.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        wye.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        wye.constant("e.kept", "119992");
        wye.decision(PRODUCER, "Rotate#u5", 1, true, "(> M_TICK 3)");
        wye.decision(target, "Guard#u8", 1, false, "EXPR.0000000000000001");
        wye.decision(target, "Concrete#u3", 1, false, "");
        // Two keys, two exports: a key read twice would be one delivery.
        Endpoint secondKey = Endpoint.of(PRODUCER, "XCH.resp.block-key-id",
                ExecutionIndex.of(Collections.singletonList(Frame.of(
                        "PBHelper#convert#9", 1))), 0);
        wye.export(ROTATED, "e.kept", 11L, "119992");
        wye.export(secondKey, "e.kept", 12L, "119992");
        wye.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        wye.attach(DELIVERED, "M_HOFF_KEY", "119992", secondKey);
        wye.write(STORED, ALL_KEYS, 5L, "e.kept");
        wye.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        wye.answered(ObligationResult.of("OBL.world-y", Verdict.ADMITTED,
                "s-world-y", "the focused prefix reproduced"));
        wye.flush();
        worker(iteration, "obligations-0001", "ob-world-y", "OBL.world-y",
                "s-world-y", PRODUCER, "Rotate#u5",
                Collections.singletonMap("CASE.TICK", "7"), NONE);

        // W: a world all the same -- a flip on a node of its own -- that
        // changed nothing this region received.  Its rows at the target and
        // at the target's factor have the seed's SHAPE: the same decisions,
        // the same handoffs from the same producer, the same reads and
        // writes.  The one thing that differs is a delivered VALUE, and a
        // value is not a difference: the families carry values
        // symbolically, and a clock-valued handoff is a different value in
        // every run for reasons no flip caused.
        Session unmoved = new Session(iteration, "s-world-w");
        unmoved.activation(BALANCER, true);
        unmoved.activations(false, target, WRITER);
        unmoved.integral(BALANCER, "CASE.MOVE", "M_MOVE", "2", "0", "10");
        unmoved.marker(target, "CASE.MARKER", "M_MARKER", "false");
        unmoved.integral(target, "CASE.COUNT", "M_COUNT", "0", "0", "10");
        unmoved.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        unmoved.symbolic("e.stored", "M_HOFF_KEY");
        unmoved.constant("e.887766", "887766");
        unmoved.decision(BALANCER, "Balance#u2", 1, true, "(> M_MOVE 1)");
        unmoved.decision(target, "Guard#u8", 1, false, "EXPR.0000000000000001");
        unmoved.decision(target, "Concrete#u3", 1, false, "");
        unmoved.export(ROTATED, "e.887766", 11L, "887766");
        unmoved.attach(DELIVERED, "M_HOFF_KEY", "887766", ROTATED);
        unmoved.write(STORED, ALL_KEYS, 5L, "e.stored");
        unmoved.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "887766");
        unmoved.answered(ObligationResult.of("OBL.world-w", Verdict.ADMITTED,
                "s-world-w", "the focused prefix reproduced"));
        unmoved.flush();
        worker(iteration, "obligations-0001", "ob-world-w", "OBL.world-w",
                "s-world-w", BALANCER, "Balance#u2", NONE, NONE);

        Corpus worlds = Corpus.read(iteration, null);
        Task anchored = ClosurePlanner.taskOf(worlds,
                ClosurePlanner.taskId(target));
        assertNotNull(anchored);
        assertTrue("addKeys writes the map the target reads, so it is a "
                        + "state-connected member of its factor: "
                        + anchored.factor(),
                anchored.factor().contains(WRITER));
        assertEquals("and s-world-y's own rows at the target are the seed's",
                worlds.decisionsOf("s-seed", target).size(),
                worlds.decisionsOf("s-world-y", target).size());
        assertEquals("what its world changed is the STRUCTURE of what the "
                        + "factor member received: one handoff more",
                worlds.attachesOn("s-seed", WRITER).size() + 1,
                worlds.attachesOn("s-world-y", WRITER).size());
        String seedInputs = dependence(worlds, anchored, "s-seed",
                "Guard#u8");
        assertFalse("so what its world delivered differs, through that "
                        + "member", seedInputs.equals(dependence(worlds,
                anchored, "s-world-y", "Guard#u8")));
        assertEquals("while the balancer's world changed nothing this region "
                        + "received", seedInputs, dependence(worlds,
                anchored, "s-world-w", "Guard#u8"));
        assertEquals("though every value it delivered differs -- a VALUE is "
                        + "not a difference, because the families carry "
                        + "values symbolically and a clock-valued handoff "
                        + "is a different value in every run",
                worlds.attachesOn("s-seed", WRITER).size(),
                worlds.attachesOn("s-world-w", WRITER).size());
        assertFalse("the delivered values really do differ",
                worlds.attachesOn("s-world-w", WRITER).get(0).arrival()
                        .equals(worlds.attachesOn("s-seed", WRITER).get(0)
                                .arrival()));
        assertFalse("and the observed values too",
                worlds.readsOn("s-world-w", target).get(0).concreteValue()
                        .equals(worlds.readsOn("s-seed", target).get(0)
                                .concreteValue()));
        assertFalse("though that session really does have a world",
                ObligationFactory.worldDigest(worlds.world("s-world-w"))
                        .isEmpty());

        Path wave4 = out.resolve("obligations-0004");
        JsonObject fifth = plan(iteration, TARGET_SELECTOR, null, results,
                wave4, 4);
        assertEquals("OBLIGATIONS_PROPOSED", fifth.get("state").getAsString());
        String wyeWorld = dependence(worlds, anchored, "s-world-y",
                "Guard#u8");
        String worldless = ObligationFactory.obligationId(
                ClosurePlanner.taskId(target), "Guard#u8", 1, true,
                seedInputs);
        assertEquals("a flip at the target itself changed nothing the target "
                        + "received, so the arm s-world-z recorded is the "
                        + "arm over the seed's inputs, and it settles that "
                        + "one", worldless, ObligationFactory.obligationId(
                        ClosurePlanner.taskId(target), "Guard#u8", 1, true,
                        dependence(worlds, anchored, "s-world-z",
                                "Guard#u8")));
        List<Obligation> reopened = new ArrayList<Obligation>();
        for (Obligation obligation : obligations(wave4)) {
            if ("Guard#u8".equals(obligation.siteId())
                    && obligation.flippedOutcome()) {
                reopened.add(obligation);
            }
            assertFalse("the same local path in a world that changed nothing "
                            + "for this region is not work, so the world-less "
                            + "arm every unaffected session offers stays "
                            + "settled: " + obligation,
                    worldless.equals(obligation.obligationId()));
            assertFalse("and nothing is cut from that session's path: "
                            + obligation, Corpus.pathId("s-world-w", target)
                            .equals(obligation.pathId()));
        }
        assertEquals("the arm s-world-z already recorded is owed again -- "
                        + "once -- in the world that changed what the region "
                        + "received: " + obligations(wave4),
                1, reopened.size());
        assertEquals("cut from that world's own path",
                Corpus.pathId("s-world-y", target), reopened.get(0).pathId());
        assertEquals("and keyed by it", ObligationFactory.obligationId(
                        ClosurePlanner.taskId(target), "Guard#u8", 1, true,
                        wyeWorld),
                reopened.get(0).obligationId());
        Worker owed = solve(iteration, wave4, reopened.get(0), out, "w4");
        assertEquals(Verdict.SAT_MODEL_READY, owed.verdict);
        JsonObject inWorld = RowCodec.readJsonl(owed.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        assertEquals("and the replay is held to the world it is owed in", 1,
                inWorld.getAsJsonArray("inheritedFlips").size());
        JsonObject rotation = inWorld.getAsJsonArray("inheritedFlips").get(0)
                .getAsJsonObject();
        assertEquals(PRODUCER.id(),
                rotation.get("focusedOccurrenceId").getAsString());
        assertEquals("Rotate#u5", rotation.get("siteId").getAsString());
        assertTrue(rotation.get("outcome").getAsBoolean());

        // And the gate's own focus-row lookup is what it was: EVERY wave's
        // workers, walked from the iteration directory the gate is handed,
        // so a session an earlier wave focused still states its world.
        Map<String, JsonObject> asked = new LinkedHashMap<String, JsonObject>();
        for (ObligationDir found : ObligationDir.workersIn(iteration)) {
            for (JsonObject row : found.focus()) {
                if (!asked.containsKey(found.sessionId())) {
                    asked.put(found.sessionId(), row);
                }
            }
        }
        assertTrue("an EARLIER wave's focus row is found too: "
                + asked.keySet(), asked.containsKey("s-other-prefix"));
        assertTrue(asked.keySet().containsAll(Arrays.asList(
                "s-world-z", "s-world-y", "s-world-w")));

        // THE NESTING BOUND.  s-world-y stands in a world of one flip, so
        // a wave that nests no deeper than the seed cuts nothing from it --
        // and says how many paths that left unread.
        Path shallow = out.resolve("obligations-0005");
        plan(iteration, results, null, shallow, 5, bounds(
                ObligationFactory.DEFAULT_MAX_PATHS_PER_TASK, 0));
        for (Obligation obligation : obligations(shallow)) {
            assertFalse("no obligation is cut from a world deeper than the "
                            + "bound: " + obligation,
                    Corpus.pathId("s-world-y", target)
                            .equals(obligation.pathId()));
        }
        assertTrue("and the bound states what it left unread",
                anyGap(shallow, gap -> gap.kind() == GapKind.ADMISSION_GAP
                        && gap.cls() == GapClass.DIAGNOSTIC
                        && gap.subject().endsWith("max-world-depth=0")));

        // THE PATH BOUND counts new work, never repetition: a path whose
        // arms are all settled or offered by a path before it is skipped
        // uncounted, so a bound of one cuts from the first path that offers
        // an owed arm and names only the others that do.
        Path every = out.resolve("obligations-0006");
        plan(iteration, TARGET_SELECTOR, null, results, every, 6);
        Set<String> owedPaths = new LinkedHashSet<String>();
        for (Obligation obligation : obligations(every)) {
            if (obligation.taskId().equals(ClosurePlanner.taskId(target))) {
                owedPaths.add(obligation.pathId());
            }
        }
        assertEquals("two of the target's paths offer an owed arm: "
                + owedPaths, 2, owedPaths.size());
        assertEquals("of eight", 8,
                Corpus.read(iteration, null).pathsOf(target).size());
        Path one = out.resolve("obligations-0007");
        plan(iteration, results, null, one, 7, bounds(1,
                ObligationFactory.DEFAULT_MAX_WORLD_DEPTH));
        Set<String> cut = new LinkedHashSet<String>();
        for (Obligation obligation : obligations(one)) {
            if (obligation.taskId().equals(ClosurePlanner.taskId(target))) {
                cut.add(obligation.pathId());
            }
        }
        assertEquals("one path cut from, the first that offers an owed arm",
                1, cut.size());
        String named = "";
        for (GapRow gap : RowCodec.readAll(one.resolve(ExploreMain.GAPS_FILE),
                RowCodec::readGap)) {
            if (gap.subject().equals(ClosurePlanner.taskId(target)
                    + " max-paths-per-region=1")) {
                named = gap.detail();
            }
        }
        assertTrue("and the bound names only the two that offer an owed "
                        + "arm: " + named, named.startsWith("this task has 2 "
                + "recorded path(s) that offer an owed arm"));
        // It defers, never drops: with that path's arms in flight, the next
        // round cuts from the path it left.
        Path flying = out.resolve("in_flight-0008.jsonl");
        RowCodec.writeAll(flying, obligations(one),
                ExploreCodec::writeObligation);
        Path later = out.resolve("obligations-0008");
        plan(iteration, results, flying, later, 8, bounds(1,
                ObligationFactory.DEFAULT_MAX_WORLD_DEPTH));
        Set<String> deferred = new LinkedHashSet<String>();
        for (Obligation obligation : obligations(later)) {
            if (obligation.taskId().equals(ClosurePlanner.taskId(target))) {
                deferred.add(obligation.pathId());
            }
        }
        Set<String> left = new LinkedHashSet<String>(owedPaths);
        left.removeAll(cut);
        assertEquals("the next round cuts from the path the bound left: "
                + deferred, left, deferred);
    }

    /**
     * ONE PLANNER SERVES THE ROUNDS (PIPELINE §7.1): what it read for a round
     * it keeps for the next -- the sessions' rows, the static map, the slot
     * table it changed -- and each round's files are the ones a planner of
     * its own writes over the iteration as it stood, while sessions land
     * and one leaves (a GROW swap).  The slot table on disk is the rounds'
     * changes: a slot a world opened, then dropped once its session left.
     * A served round reads the corpus its question names (PIPELINE §7.9):
     * a session that lands once the round's corpus is frozen is no session
     * of that round.
     */
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
        // round -> what lands before it: a world's session, its leaving,
        // another world's; and one that lands after the round's corpus was
        // frozen, while it plans.
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
            // What the round reads, by which its room is judged: the files
            // of the sessions the planner does not hold yet, as they decode.
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

    /**
     * A ROUND ON ONE CORE IS A ROUND ON MANY ({@code contract.Parallel}):
     * the frontier's keys and the candidates, one session's in order to a
     * thread, the sessions side by side, and every file read and written by
     * blocks -- byte for byte the files one thread writes.
     */
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

    /** A world's admitted session of the served planner's iteration: the
     *  target's guard flipped by the marker, the rotated key delivered. */
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

    /** A directory and everything under it, gone (a session GROW moved
     *  aside). */
    private static void deleteTree(Path dir) throws IOException {
        List<Path> all = new ArrayList<Path>();
        try (java.util.stream.Stream<Path> walked = Files.walk(dir)) {
            walked.forEach(all::add);
        }
        Collections.reverse(all);
        for (Path path : all) Files.delete(path);
    }

    /**
     * One obligation worker of the iteration: the FOCUS ROW its replay was
     * driven by, and the result row that names the session it published.
     *
     * <p>The world a session ran in is read off this row and nowhere else
     * ({@link Corpus#world}), so a fixture that wants a session to have one
     * writes the row the campaign writes.</p>
     */
    private static void worker(Path iteration, String wave, String dir,
                               String obligationId, String sessionId,
                               OccurrenceAddress focused, String siteId,
                               Map<String, String> roots,
                               Map<String, String> clockDeltas)
            throws IOException {
        worker(iteration, wave, dir, obligationId, sessionId, focused, siteId,
                roots, clockDeltas, Collections.<Corpus.Flip>emptyList());
    }

    /** The same, for a replay that INHERITED a world as well as its own. */
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

    /**
     * THE ROUND STATES, THE CAMPAIGN STOPS (PIPELINE §7.9).  A round names
     * every admitted replay that observed the fatal at the declared
     * occurrence and keeps proposing -- whether the exploration ends there
     * is the campaign's, once COMPOSE has judged the corpus.  It never
     * proposes an obligation the campaign has in flight, under its id or
     * under the question its row asks (an id moves as sessions land), and
     * its wave is one past the deepest wave a landed session came from.
     */
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

        // In flight under its own id, and under another id for the same
        // question: neither is proposed again, and the round says so.
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

    /**
     * A BRANCH WITHOUT THE DECLARED REGION UNDER ITS CONTEXT STOPS
     * (PIPELINE §7.4).  An admitted replay that ran the declared region
     * under the declared context at another index -- a window index a retry
     * moved -- parents obligations; one that ran it only under another
     * context does not, and is named; a refused replay parents nothing
     * either way.  A sender no row names is unknown, never a difference.
     */
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

    /**
     * WHAT A GUARD DEPENDS ON is its arm's key ({@link
     * ObligationFactory#dependence}): a prefix decision sharing no variable
     * with the guard, and a factor member's writes to state the guard does
     * not read, never split one question in two; a prefix decision over the
     * guard's own root, and another value written where it reads, do.
     * (hdfs-11741 v79: 4984 candidates, 2422 keys by the whole prefix and
     * every write of the factor, 499 by what the guard depends on.)
     */
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
        // session, Near#u2, Far#u4, writes of the map, writes of the qop,
        // handoffs to a co-reader of the map; s-idle also runs the late
        // feeder, which delivers it nothing
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
        // A world whose flip stands later in the task's own occurrence (a
        // fault after the guard: solr-adhoc-07's makePath): its prefix is
        // asserted, never keyed.
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
        // Feeders that wrote other terms where the guard reads (a member
        // flip writing M_A-1 where the seed wrote M_A+10; requests writing
        // 5 or 7; a term reading a location another writer wrote).
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
        // session, written term, the inner location's writer (or none)
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
        // A member's replies from two producers, in either arrival order.
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
        // A session that runs a feeder no earlier session ran: the seed never
        // ran it, so what the seed's guard depends on is unmoved.
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
        // The wave names an obligation once: a solver reading the corpus
        // mid-wave (a larger factor, another dependence) keeps that id.
        ObligationFactory.Candidate located = ObligationFactory.locate(corpus,
                Obligation.of("OBL.as-the-wave-named-it", task.taskId(),
                        Corpus.pathId("s-seed", TARGET), "Guard#u8", 1, true,
                        NONE,
                        NONE,
                        Collections.<String>emptyList()));
        assertEquals("OBL.as-the-wave-named-it", located.obligationId);
    }

    /**
     * GROWTH IS THE CLOSURE'S (PIPELINE §7.2, §7.8). A
     * demanded occurrence no session CAPTURED -- the hooks ran it and its
     * runtime identity is in a session's rows, but no planned task admitted
     * it -- is grown from the admitted focused session that names it; named
     * by the seed replay alone it waits for one (DIAGNOSTIC); a lost role is
     * no region, so nothing grows it; a captured one is a task.  hdfs-17899:
     * a DataNode's periodic heartbeat sends through the woven IPC door under
     * no task, and the closure demands that sender.
     */
    @Test
    public void theClosureGrowsWhatItDemandsAndNoSessionCaptured()
            throws Exception {
        OccurrenceAddress lost = occurrence("hdfs-case/nn0",
                "ROLE.IPC_HANDLER", CausalContext.of(Role.of("IPC_HANDLER")),
                "o.a.h.ipc.Server$Handler#run#1");
        // Started by nn0's KEY_MANAGER_TICK #3 through a message its tick
        // root sent in no region (the heartbeats of hdfs-11741).
        OccurrenceAddress anchored = occurrence("hdfs-case/nn0",
                "REGION.rotate", CausalContext.of("e-tick", "HADOOP_IPC"),
                "o.a.h.h.s.b.BlockManager#run#8");
        // producer, whether the seed captures it, whether a focused replay
        // names it, the last tick of its role the recording ran (-1: no
        // recorded schedule), whether it began past that tick
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
                // PRODUCER is nn0's KEY_MANAGER_TICK #1.
                List<JsonObject> ticks = new ArrayList<JsonObject>();
                // A view's publication stands at its node's |VIEW stance,
                // which no tick reading parses (ScheduleEvent.Kind#PUBLISH).
                ticks.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                        ScheduleEvent.Kind.PUBLISH, producer.node().render()
                                + "|VIEW", ScheduleEvent.published("SOLR_ZK",
                                "/collections/c/state.json", 3L), 0, "")));
                if (recorded > 0) {
                    ticks.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                            ScheduleEvent.Kind.WAKE, producer.node().render()
                                    + "|" + CausalContext.of(Role.of(
                                    "KEY_MANAGER_TICK"), "", recorded)
                                    .render(), "tick.KEY_MANAGER_TICK", 0,
                            "")));
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
                // A tick the recording never ran: only a slower replay ran
                // it (hdfs-11741 v86, heartbeats #44-#100 against #5).
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
                // Once planned, an address is not grown again: whether it
                // runs is the replays' timing (hdfs-17897 v83).
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
                // This corpus flips nothing, so its first wave is the
                // fixpoint: no focused replay will ever run it.
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

    /**
     * A MEMBER IS NAMED BY ITS CLASS AND WHAT THE QUERY READS OF IT ({@link
     * Corpus#inputShape}): node, region and context shape, never its
     * address; semantic counts only -- the same value written k or k' times,
     * or by a member under renumbered ids, is one world (solr-adhoc-07/21:
     * polls and watcher callbacks re-keyed every arm) -- while another value
     * written where a read of the task looks, or another pinned value its
     * read observed of a write the query cannot state, is another; and a
     * member that wrote only state the region reads elsewhere is no line
     * (no conjunct of the query: solr-adhoc-21 RX4).  What another
     * occurrence's read observed is no input of the task's query.
     */
    @Test
    public void aMemberIsNamedByItsClassAndWhatTheQueryReads()
            throws Exception {
        Path iteration = tree.newFolder("member-class").toPath();
        List<OccurrenceAddress> polls = new ArrayList<OccurrenceAddress>();
        for (int k : new int[] {1, 2, 3, 7}) {
            polls.add(occurrence("hdfs-case/dn0", "REGION.addkeys",
                    CausalContext.of(Role.of("POLL"), "", k),
                    "o.a.h.h.s.d.Poller#poll#" + k));
        }
        JsonObject mystery = new JsonObject();
        mystery.addProperty("_type", "NoSuchExpression");
        mystery.addProperty("_java_type", "I");
        // session, the polls that ran (each writing the map once), what they
        // wrote (a constant, or "?" a term that does not lower), what the
        // task's read of the first write observed ("-": none read it), and
        // whether another occurrence's read observed it
        Object[][] sessions = {
            {"s-one", new int[] {0}, "7", "7", false},
            {"s-three", new int[] {0, 1, 2}, "7", "7", false},
            {"s-renumbered", new int[] {3}, "7", "7", false},
            {"s-nine", new int[] {0}, "9", "9", false},
            {"s-none", new int[] {}, "7", "-", false},
            {"s-u7", new int[] {0}, "?", "7", false},
            {"s-u9", new int[] {0}, "?", "9", false},
            {"s-u-other", new int[] {0}, "?", "-", true},
            {"s-u-unread", new int[] {0}, "?", "-", false},
        };
        for (Object[] row : sessions) {
            Session session = new Session(iteration, (String) row[0]);
            session.activation(TARGET, false);
            if ("?".equals(row[2])) {
                session.expression("EXPR.00000000000000e7", mystery);
            } else {
                session.constant("EXPR.00000000000000e7", (String) row[2]);
            }
            for (int at : (int[]) row[1]) {
                session.activation(polls.get(at), false);
                session.write(at(polls.get(at), Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true),
                        "BlockTokenSecretManager#addKeys#12"), ALL_KEYS,
                        5L + at, "EXPR.00000000000000e7");
            }
            if (!"-".equals(row[3])) {
                session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY",
                        (String) row[3]);
            }
            if ((Boolean) row[4]) {
                session.activation(READER, false);
                session.read(CONSULTED, ALL_KEYS, 5L, "M_SEEN_KEY", "7");
            }
            session.flush();
        }
        Corpus corpus = Corpus.read(iteration, null);
        Set<String> guard = Collections.singleton(
                SmtLowering.locationKey(ALL_KEYS));
        Set<String> none = Collections.<String>emptySet();
        String once = corpus.inputShape("s-one", TARGET, polls, guard,
                NONE_STATED);
        Object[][] rows = {
            // session, with location set, same key as s-one under it, why
            {"s-three", guard, true, "the same value three times"},
            {"s-renumbered", guard, true, "under another index"},
            {"s-nine", guard, false,
                    "another value a read of the task observed"},
            {"s-none", guard, false, "no writer of what the guard reads"},
            {"s-none", none, true,
                    "a member that only fed the region is no line"},
        };
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            Set<String> locations = (Set<String>) row[1];
            assertEquals((String) row[3], row[2], corpus.inputShape(
                    "s-one", TARGET, polls, locations, NONE_STATED).equals(
                    corpus.inputShape((String) row[0], TARGET, polls,
                            locations, NONE_STATED)));
        }
        assertEquals("the polls of s-one as s-one", once,
                corpus.inputShape("s-one", TARGET, polls, guard, NONE_STATED));
        Object[][] unlowered = {
            {"s-u7", "s-u9", false,
                    "a term the query cannot state, pinned to 7 against 9"},
            {"s-u7", "s-u-other", false,
                    "pinned by the task's read against read by no one's"},
            {"s-u-other", "s-u-unread", true,
                    "another occurrence's read is no input of the query"},
        };
        for (Object[] row : unlowered) {
            assertEquals((String) row[3], row[2], corpus.inputShape(
                    (String) row[0], TARGET, polls, guard, NONE_STATED).equals(
                    corpus.inputShape((String) row[1], TARGET, polls,
                            guard, NONE_STATED)));
        }
        // Members started by messages no row names: their shape has an
        // unknown hop, which tells nothing apart, so each keeps its address.
        Path unknown = tree.newFolder("member-unknown-hop").toPath();
        List<OccurrenceAddress> unnamed = new ArrayList<OccurrenceAddress>();
        for (int k : new int[] {1, 2}) {
            unnamed.add(occurrence("hdfs-case/dn0", "REGION.addkeys",
                    CausalContext.of("E-unnamed-" + k, "Poller#poll"),
                    "o.a.h.h.s.d.Poller#poll#" + k));
        }
        for (Object[] row : new Object[][] {{"s-one", new int[] {0}},
                {"s-two", new int[] {0, 1}}}) {
            Session session = new Session(unknown, (String) row[0]);
            session.activation(TARGET, false);
            session.constant("e.stored", "7");
            for (int at : (int[]) row[1]) {
                session.activation(unnamed.get(at), false);
                session.write(at(unnamed.get(at), Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true),
                        "BlockTokenSecretManager#addKeys#12"), ALL_KEYS,
                        5L + at, "e.stored");
            }
            session.flush();
        }
        Corpus unknownCorpus = Corpus.read(unknown, null);
        assertFalse("two members of an unknown hop are not one class",
                unknownCorpus.inputShape("s-one", TARGET, unnamed, guard,
                        NONE_STATED)
                        .equals(unknownCorpus.inputShape("s-two", TARGET,
                                unnamed, guard, NONE_STATED)));
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

    /**
     * WORLD_REFUTED: a replay of an open arm's flip that refuted its world
     * answers nothing of the arm.  The arm is asked again with exactly that
     * world excluded, the round names the refuted world on the arm's row
     * (digest, conditions, the workload's exception), and the arm closes
     * UNSAT once no other world of the corpus takes it -- an UNSAT that says
     * it rests on the refuted world.
     */
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
        // Its replay refuted that world: the worker's answer, as the head
        // lands it in the iteration.
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
        String query = new String(Files.readAllBytes(second.directory
                .resolve("obligation_query.smt2")), StandardCharsets.UTF_8);
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

    /** One symbolic leaf, as the VM serializes it ({@code "N"} is null). */
    private static JsonObject leaf(String symbol, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", symbol);
        node.addProperty("_java_type", javaType);
        return node;
    }

    /** One int literal, as the VM serializes it. */
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

    /**
     * One guarded read: the location, the version it observed, and the
     * PROJECTION the execution performed on that version.
     *
     * <p>The shape 11741's anchor guard has -- the map state the write log
     * covers, and the one entry this read took out of it.</p>
     */
    private static JsonObject guardedRead(LocationId location, long version,
                                          String javaType,
                                          JsonObject projection) {
        return guardedRead(location, version, javaType, projection, -1L);
    }

    /**
     * The same, stating the EVENT the read happened at.
     *
     * <p>Which is what makes the node a statement about shared state a
     * closure can follow (E2): the location says WHICH cell and the event
     * id says AS OF WHEN, so the version the producer had in hand is the
     * latest write of that location at or before it.</p>
     */
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

    /**
     * A KEPT ANSWER IS ALL ITS TEXT SAYS ({@link Solved#whole}): unsat, or
     * sat with a value of every symbol the text asks the model of -- a sat
     * whose model's run was cut short is answered, never kept, so the next
     * ask of the text runs z3 again; and a store that cannot be written
     * leaves the answer answered.  Per row: the verdict, the symbols its
     * model valued, whether the next ask is answered as kept.
     */
    @Test
    public void onlyAWholeAnswerIsKept() throws Exception {
        List<String> asks = Arrays.asList("x", "y");
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
            assertSame(z3, solved.answer("q", asks, () -> z3));
            int[] runs = {0};
            solved.answer("q", asks, () -> {
                runs[0]++;
                return z3;
            });
            assertEquals(Arrays.toString(row), row[2], runs[0] == 0);
        }
        Z3.Answer unsat = Z3.Answer.decided("unsat",
                Collections.<String, String>emptyMap());
        Solved unwritable = Solved.at(tree.newFile("a-file").toPath()
                .resolve(Solved.DIR));
        assertSame(unsat, unwritable.answer("q", asks, () -> unsat));
    }

    /**
     * THE SOLVER KEY ({@link Solved}): z3's decided answer is a fact of its
     * query's text alone, kept by it, and an ask of the same text under
     * another question -- another plan generation, world, task -- runs no
     * z3 and comes to the outcome a z3 run deciding the same comes to; the
     * question stays its own (SOLR-18413 b05: 312 of 519 solver-decided asks
     * asked a text asked before).  An undecided answer is kept nowhere.  Per
     * row: the flipped term, its verdict.
     */
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
            Path kept = solved.dir().resolve(edu.uva.liftlab.graphchecker
                    .smt.ArtifactIO.sha256(asked.smt2) + ".json");
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
            // Undecided at its budget: no answer of the text, none kept.
            Files.delete(kept);
            ObligationFactory.Outcome timedOut = corpus.asking(() ->
                    ObligationFactory.solve(corpus, candidate, new Z3(
                            Paths.get("z3"), 1L, 1152), solved, "plan C",
                            none, null));
            assertTrue(name + ": " + timedOut.result.detail(),
                    timedOut.result.detail().startsWith("SOLVER_TIMEOUT"));
            assertFalse(name, Files.exists(kept));
        }
    }

    /**
     * ONLY A FAITHFUL VERDICT SETTLES AN ARM ({@link Frontier#consume},
     * {@code ObligationResult#settlesArm}): a NOT_ADMITTED whose replay ran
     * its world as asked and never reached the decision ({@code WORLD_RAN})
     * settles the arm for every world, as today; one whose replay did not
     * run its world (an inherited root not minted, a refusal, a stall) is a
     * fact about that world only -- the arm stays owed for any other world,
     * the flip itself asked once more and settled by a second such answer
     * (solr-bugs-tra-start-overwrite SG3A: the one pairing flip's world never
     * minted its inherited root, and its NOT_ADMITTED closed the arm).  A
     * replay killed past its bound ({@code REPLAY_BOUNDED}) answered
     * nothing: it is no world-only answer, the flip is asked once more, and
     * killed twice it is held BOUNDED and named, never settled
     * (solr-adhoc-38 EXZ1: 24 flips killed twice read as world-only
     * answers, and the run closed UNSAT).
     */
    @Test
    public void onlyAFaithfulNotAdmittedSettlesTheArm() throws Exception {
        String ran = ObligationResult.WORLD_RAN + ": occurrence o never"
                + " reached Lookup#u8#1 in this replay, and the world it ran"
                + " was the one asked";
        String unrun = "occurrence o never reached Lookup#u8#1 in this"
                + " replay; its world did not run: the inherited root R was"
                + " never minted";
        // A refusal whose cause is in what the key names (the flipped
        // predicate, the versions it read that no row wrote) is the arm's;
        // one resting on the world (an inherited flip) is its own flip's.
        String atArm = ObligationResult.ARM_REFUSED + ": the query was"
                + " refused: ADMISSION_GAP:Lookup#u8#1";
        String inWorld = "the query was refused: ADMISSION_GAP:Rotate#u5#1";
        String killed = ObligationResult.REPLAY_BOUNDED + ": replay exceeded"
                + " replay_timeout_s=2400";
        // At its z3s' cap: undecided by name, as a timeout is -- no fact
        // about the arm.
        String memout = "SOLVER_MEMOUT at 1984 MB";
        Object[][] rows = {
            // its answers' details (the k-th landing takes the k-th, the
            // last repeating), how many of them landed on its flip,
            // whether the arm is settled for every world, whether the next
            // round asks the flip again from the same path, whether the flip
            // is held BOUNDED
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
                // What it asked, which a bounded flip is named by.
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

    /** Each bounded flip row's site (FORCE for the FORCE run) and how many
     *  killed replays it names. */
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

    /** One earlier worker of this iteration: its question file and the
     *  answer it wrote. */
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

    /** A target read of a map two concurrent addKeys wrote, recorded taking
     *  the first write, and {@code Lookup#u8} deciding {@code term} over it
     *  (and over root {@code CASE.LIMIT}, recorded {@code limit}, when one
     *  is given). */
    /** {@link #twoWriters}' lookup over the read node the VM writes. */
    private static final String VM_LOOKUP = "EXPR.0000000000000002";
    /** The key id both of {@link #twoWriters}' writers store: a field. */
    private static final LocationId KEY_ID =
            LocationId.of(LocationKind.INSTANCE, "21", "40");

    private Path twoWriters(String name, String term, String limit)
            throws IOException {
        return twoWriters(name, term, limit, "I");
    }

    /** {@link #twoWriters}, the second writer storing an int, or with
     *  {@code "Z"} a comparison's boolean. */
    private Path twoWriters(String name, String term, String limit,
                            String secondType) throws IOException {
        return twoWriters(name, term, limit, secondType, 6L);
    }

    /** {@link #twoWriters}, the lookup again seeing version {@code seen}:
     *  the second writer's 6, or one no row wrote. */
    private Path twoWriters(String name, String term, String limit,
                            String secondType, long seen)
            throws IOException {
        Path iteration = tree.newFolder(name).toPath();
        // A second addKeys, started by a request of its own.
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
        // The lookup again, after the second write: the same occurrence's
        // read of the same field.
        seed.read(at(TARGET, Endpoint.stateSite("BlockTokenSecretManager",
                "retrieveDataEncryptionKey", 9, false),
                "BlockTokenSecretManager#retrieveDataEncryptionKey#9"),
                KEY_ID, seen, "M_READ_AGAIN", "2");
        // The lookup as the VM states it: the guarded read, joined to the
        // write it observed, compared.
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

    /** Why a worker said what it said, for a failure message. */
    private static String detail(Worker worker) throws IOException {
        List<ObligationResult> rows = RowCodec.readAll(
                worker.directory.resolve("obligation_result.jsonl"),
                RowCodec::readObligationResult);
        return rows.isEmpty() ? "" : rows.get(0).detail();
    }

    private static String query(Worker worker) throws IOException {
        return new String(Files.readAllBytes(
                worker.directory.resolve("obligation_query.smt2")),
                java.nio.charset.StandardCharsets.UTF_8);
    }

    // ---- driving the stage the way the campaign drives it -------------

    /**
     * One round, planned from the case's own selector as the stage does,
     * over the static map the epoch published beside its sessions, with
     * nothing in flight.
     */
    private JsonObject plan(Path iteration, String selector, Path domains,
                            Path results, Path roundDir, int round)
            throws IOException {
        return ExploreMain.plan(iteration, selector, domains, results, null,
                iteration.resolve(StaticScopeMap.FILE), roundDir, round,
                "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                DEFAULT_BOUNDS);
    }

    /** The same, of the case's target, with {@code inFlight} held and
     *  {@code bounds} its round's. */
    private static JsonObject plan(Path iteration, Path results,
            Path inFlight, Path roundDir, int round,
            ObligationFactory.Bounds bounds) throws IOException {
        return ExploreMain.plan(iteration, TARGET_SELECTOR, null, results,
                inFlight, iteration.resolve(StaticScopeMap.FILE), roundDir,
                round, "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS, bounds);
    }

    /** A round's bounds: {@code maxPaths} per task, {@code maxDepth} deep. */
    private static ObligationFactory.Bounds bounds(int maxPaths,
                                                   int maxDepth) {
        return new ObligationFactory.Bounds(maxPaths,
                ObligationFactory.DEFAULT_MAX_FLIPS_PER_PATH, maxDepth);
    }

    /**
     * The walk's steps run ahead on the planner's cores ({@code
     * ClosurePlanner#CORES}), and its plan is the one-at-a-time walk's: each
     * step computed ahead is the walk of its demand's state, and is taken in
     * queue order only while it still is; what only that order gives -- the
     * leaves of the anchor's two reads at one seq, held once, the first
     * asked ({@code Corpus#readLeaves}) -- is computed in it.  Here a
     * producer whose every delivery a session attached, and a writer each
     * session's anchor read, over seventy sessions: planned on one core --
     * the walk one step at a time -- on four and on the host's, the three
     * plans are one.
     */
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
            // The next read at the same seq (a store read and its view's).
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

    /**
     * A step computed ahead whose demand an earlier step grew, or whose
     * walk claimed the leaves of a seq another row asked first in the
     * order, is not the walk of its demand there ({@code
     * ClosurePlanner.Walk#take}): W1's delivery is W4's
     * handoff, so W1's step grows W4, which then reads e, W5's; W1 and W2
     * read a and b at one seq ({@code Corpus#readLeaves}: the first row
     * asked holds it), a holding W8's handoff through W7's write, so in
     * the order W2's delivery rests on a's leaves -- which name f, W6's --
     * not on b's; over seventy sessions.  On one core -- the walk one step
     * at a time -- on four and on the host's, one plan.
     */
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
            // a's version 1 is W8's handoff, which moves: a and b's seq
            // holds a's leaves where W1 asked it first.
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

    /**
     * A step reads its group's index; it never builds one: groups are
     * indexed on the planner's thread as the steps that walk them start
     * ({@code ClosurePlanner.Walk#reads}).  Here the anchor's step demands
     * twelve producers, so the steps started next index the thirteenth
     * group -- the insert after which a JDK 8 HashMap resizes at its next
     * computeIfAbsent, whatever its key -- and the walk, planned two hundred
     * times on the host's cores, is the one-core walk each time.
     */
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

    /** The plans of {@code iteration}'s corpus, each read anew, on one
     *  core -- the walk one step at a time -- on four, and on the host's
     *  ({@code ClosurePlanner#CORES}). */
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

    /** {@link #closure} of {@link #TARGET}, its steps on {@code
     *  cores}. */
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
                SystemView.of(""), cores, said::add), said);
    }

    /** Everything a plan states, as text. */
    private static String rendered(ClosurePlanner.Plan plan) {
        return plan.tasks + "\n" + plan.why + "\n" + plan.flipSites + "\n"
                + gapsOf(plan) + "\n" + plan.exposed + "\n" + plan.waiting
                + "\n" + plan.truncated + "\n" + plan.unpaused + "\n"
                + plan.runWhole + "\n" + plan.ceilingCut;
    }

    /** One write of a store version at an occurrence, and one leaf of the
     *  document it exported. */
    private static void written(Session session, OccurrenceAddress at,
                                LocationId store, long version, String leaf) {
        session.write(at(at, "SOLR_ZK#WRITE:" + store.slot(),
                "ZkStateWriter#write#3"), store, version, "");
        session.export(at(at, ContentPort.of("SOLR_ZK", store.slot(), leaf),
                "Utils#toJSON#7"), "", 0L, "0");
    }

    /** One anchor's closure, every admitted session a parent of growth but
     *  those whose branch stopped ({@link Branches}). */
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

    /** The gaps each plan's walk said, each once, as a round writes them
     *  ({@code RoundGaps}). */
    private static final Map<ClosurePlanner.Plan, List<GapRow>> SAID =
            Collections.synchronizedMap(new java.util.IdentityHashMap<
                    ClosurePlanner.Plan, List<GapRow>>());

    /** {@code plan}, whose walk said {@code said}. */
    private static ClosurePlanner.Plan saying(ClosurePlanner.Plan plan,
                                              Set<GapRow> said) {
        SAID.put(plan, new ArrayList<GapRow>(said));
        return plan;
    }

    /** The gaps {@code plan}'s walk said ({@link #saying}). */
    private static List<GapRow> gapsOf(ClosurePlanner.Plan plan) {
        return SAID.get(plan);
    }

    /**
     * The task bound counts static candidates only ({@code
     * ClosurePlanner.Candidates}): a candidate the rows later connect -- here
     * the producer of what the anchor's writer attached, found first as a
     * static writer of the map -- is planned whatever the bound, and the
     * candidates left take turns by class, so a bound of two plans one of
     * each class before a second of either.
     */
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
        // Per bound: the static candidates planned, and those cut.
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
        // Past a ceiling of two occurrences the rows connect, the producer
        // the writer's attach names is cut and named, and no static
        // candidate stays planned whatever the bound.
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

    /** The occurrences one plan's tasks focus, in its order. */
    private static List<String> focused(ClosurePlanner.Plan plan) {
        List<String> focused = new ArrayList<String>();
        for (Task task : plan.tasks) focused.add(task.focused().render());
        return focused;
    }

    /** Which rule proposed each task of one plan, by focused occurrence. */
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

    /** One site row of that map, in the artifact's one shape. */
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

    /** The same WRITE_SITE row, stated as a mutator call on the container
     *  its carrier holds: a store of that container's state, the MAP
     *  location the fixture's key map is ({@code StaticScopeMap#stores}). */
    private static String put(String row) {
        JsonObject site = com.google.gson.JsonParser.parseString(row)
                .getAsJsonObject();
        site.addProperty("declaredCallee", "<java.util.Map: java.lang.Object"
                + " put(java.lang.Object,java.lang.Object)>");
        return site.toString();
    }

    /** The declared target and the branches it is control-dependent on. */
    private static String targetSite(String regionId, String siteId,
                                     String... guards) {
        return scopeSite(StaticScopeMap.TARGET_SITE, regionId, siteId, "",
                "", "", "", guards);
    }

    /**
     * One decision, one flip, one polarity.
     *
     * @param term     the predicate as the runtime publishes it, polarity-free
     * @param outcome  whether that term HELD in the recording (CONTRACT-SPEC
     *                 §2.2), which is what makes the conjunct
     * @param recorded what the session minted for the marker
     * @param expected the value the model must assign, or null when the wave
     *                 must refuse because the model would BE the recording
     */
    private void flipAsksTheOtherArmOnce(String term, boolean outcome,
                                         String recorded, String expected)
            throws IOException {
        Assume.assumeTrue(z3Available());
        String name = "polarity-" + Math.abs((term + outcome).hashCode());
        Path iteration = tree.newFolder(name).toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.marker(TARGET, "CASE.MARKER", "M_MARKER", recorded);
        seed.decision(TARGET, "Guard#u8", 1, outcome, term);
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"));
        Path out = tree.newFolder(name + "-out").toPath();
        Path results = results(out);
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null, results, wave, 0);
        List<Obligation> proposed = obligations(wave);
        assertEquals("one flippable decision, one obligation: " + proposed,
                1, proposed.size());
        assertEquals("the flip asks for the arm the recording did not take",
                !outcome, proposed.get(0).flippedOutcome());
        Worker solved = solve(iteration, wave, proposed.get(0), out, "w");
        if (expected == null) {
            assertEquals("a model that is the recording is not an arm the "
                    + "seed lacks", Verdict.NOT_ADMITTED, solved.verdict);
            // THE WAVE'S, and DIAGNOSTIC.  "This flip does not depend on the
            // declared roots on this prefix" is a fact about the question
            // the wave asked and about no execution, so it is not a blocking
            // defect and it is not filed under the session whose path the
            // flip was cut from -- which for a wave-0 flip is the SEED,
            // whose ledger then said the recording had a blocking defect
            // and made campaign_write_gaps exit 3.
            assertTrue("and the refusal is named, as the wave's own "
                    + "diagnostic", anyGap(solved.directory, gap ->
                    gap.cls() == GapClass.DIAGNOSTIC
                            && ExploreCodec.EXPLORATION.equals(gap.sessionId())
                            && gap.detail().contains(
                                    "the model is the valuation")));
            return;
        }
        assertEquals(Verdict.SAT_MODEL_READY, solved.verdict);
        assertEquals("the model makes the published term take the flipped "
                        + "outcome's truth value", expected,
                solved.obligation.rootAssignments().get("CASE.MARKER"));
    }

    /** One obligation worker: the verdict row and the completed obligation. */
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

    /**
     * THE HARD LANE READS NO CORPUS ({@code ObligationSolverMain#decide}): z3
     * alone over the query a first ask published and its record ({@code
     * HardAsk}), answered as the corpus's ask maps an answer ({@code
     * ObligationFactory#settled}): UNSAT with the record's detail, gaps and
     * question, settling it; the budget spent a named SOLVER_TIMEOUT, never
     * UNSAT; a model left for the host's solver to finish, no answer
     * (SGF7-adhoc-39: each hard ask was a corpus JVM of 18-21 GB, one per
     * host).  Per row: the body, the budget, and the verdict and detail
     * published (MODEL: a model, no answer).
     */
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
                    query.getBytes(StandardCharsets.UTF_8));
            GapRow built = GapRow.of("S", GapKind.ADMISSION_GAP,
                    GapClass.DIAGNOSTIC, "OB.1", "built");
            String sha = edu.uva.liftlab.graphchecker.smt.ArtifactIO
                    .sha256(query);
            Path solved = worker.resolve(Solved.DIR);
            new HardAsk("OB.1", "S", "the question",
                    "no world of this corpus takes the other arm at s#1",
                    Collections.singletonList(built), symbols, sha, solved)
                    .write(worker.resolve(HardAsk.FILE));
            ObligationSolverMain.decide(obligations, "OB.1", worker,
                    Paths.get("z3"), (Long) row[1], 1152);
            String says = Arrays.toString(row);
            // Its decided answer is kept by its text, an undecided one
            // nowhere; asked again, a kept one is the answer, no z3 run.
            Path kept = solved.resolve(sha + ".json");
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

    /** One worker, given the same case declaration the wave was planned under. */
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
                Files.size(worker.resolve("obligation_query.smt2")) > 0);
        return new Worker(rows.get(0).verdict(), solved.get(0), worker);
    }

    /** Whether a directory's gap rows hold one {@code named} matches: a
     *  round's ({@link ExploreMain#GAPS_FILE}) or a worker's. */
    private static boolean anyGap(Path dir,
            java.util.function.Predicate<GapRow> named) throws IOException {
        Path round = dir.resolve(ExploreMain.GAPS_FILE);
        return RowCodec.readAll(Files.isRegularFile(round) ? round
                        : dir.resolve("gaps.jsonl"), RowCodec::readGap)
                .stream().anyMatch(named);
    }

    /** The results file of a case's rounds, empty. */
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

    private static Obligation named(List<Obligation> obligations,
                                    String site) {
        for (Obligation obligation : obligations) {
            if (obligation.siteId().equals(site)) return obligation;
        }
        return null;
    }

    /** One occurrence: a component, a region, why it ran, and where. */
    private static OccurrenceAddress occurrence(String node, String region,
                                                CausalContext context,
                                                String callSite) {
        return OccurrenceAddress.of(NodeId.of(node, 0), region, context,
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of(callSite, 0))));
    }

    /** One endpoint of an occurrence, at the first execution of its site. */
    private static Endpoint at(OccurrenceAddress occurrence, String site,
                               String callSite) {
        return Endpoint.of(occurrence, site, ExecutionIndex.of(
                Collections.singletonList(Frame.of(callSite, 0))), 0);
    }

    /**
     * The rotation's export endpoint, which the writer's causal anchor names.
     *
     * <p>Built the long way because it is a static initialiser that the
     * writer's own address depends on: the anchor IS the producer's endpoint
     * id, so the consumer's identity contains the producer's.</p>
     */
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

    /**
     * IDENTITY §7.2: a store version the concrete anchor read through a
     * decoded object -- a STORE read at its PROVENANCE_SITE, before it
     * decided -- rests on the write that made it and on every earlier
     * version of its location, whatever node wrote them, and each writer on
     * the queue item it took in: the item's sender decided a fault, so it is
     * a control producer and its door is asked
     * (solr-bugs-restore-construction: the client's view of state.json,
     * the Overseer's state writes, the item RestoreCmd offered).  Rows:
     * whether the read is on the anchor's provenance site, whether the
     * earlier writer took in the item, and what is then planned.
     */
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
        // Per row: the read on the anchor's provenance site, the earlier
        // writer took the item in, the anchor's phi (a symbolic one demands
        // the store version too: its content is no value a term names).
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
            // A node's view publication: its stance is no causal context,
            // and the corpus reads past it (review B1: every schedule
            // holding one crashed the planner).
            schedule.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                    ScheduleEvent.Kind.PUBLISH, restore.node().render()
                            + "|" + ContextShape.Stance.VIEW_STANCE,
                    ScheduleEvent.published("SOLR_ZK",
                            "/collections/t/state.json", 2L), 0, "")));
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
        /** What this replay SETTLED, as its own obligations.jsonl states. */
        private final List<ObligationResult> answered = new ArrayList<>();
        /** A FORCE run's session ({@code SessionManifest.Role#FORCED}). */
        private boolean forced;
        /** The names its nodes had only in this run, spelling -> node
         *  ({@code SessionManifest#runSpellings}). */
        private final Map<String, String> spelled =
                new LinkedHashMap<String, String>();
        /** The occurrences it ran for their doors alone. */
        private final Set<String> doorsOnly = new TreeSet<String>();
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<>();
        /** The session's own event order: every row takes the next one. */
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

        /** The same, on a thread of its own. */
        private void activation(OccurrenceAddress occurrence, boolean focused,
                                boolean instrumented, String thread) {
            activations.add(ActivationRow.of(sessionId, occurrence,
                    "task-" + occurrence.regionId(), focused, instrumented,
                    thread));
        }

        /** Several occurrences, each its own activation. */
        private void activations(boolean focused,
                                 OccurrenceAddress... occurrences) {
            for (OccurrenceAddress occurrence : occurrences) {
                activation(occurrence, focused);
            }
        }

        /** {@code spelling} is node {@code node}'s in this run. */
        private void spelled(String node, String spelling) {
            spelled.put(spelling, node);
        }

        private void decision(OccurrenceAddress occurrence, String site,
                              int ordinal, boolean outcome, String term) {
            decisions.add(DecisionRow.of(sessionId, ++seq, occurrence, site,
                    ordinal, outcome, term,
                    Collections.<String, Long>emptyMap()));
        }

        /**
         * One root minted, at the point of the session where it is minted:
         * before every decision that can mention it, because a value is read
         * before it is branched on.
         */
        /** The anchor's own predicate, in the fatal polarity. */
        private void target(OccurrenceAddress occurrence, String site,
                            String phi) {
            targets.add(TargetRow.of(sessionId, ++seq, occurrence, site, phi,
                    false, true));
        }

        /** The key lookup's anchor: fatal where the key read was 0. */
        private void anchored(OccurrenceAddress occurrence) {
            target(occurrence, "BlockTokenSecretManager"
                    + "#retrieveDataEncryptionKey#8", "(= M_READ_KEY 0)");
        }

        /** The anchor, where this replay observed the fatal. */
        private void fatal(OccurrenceAddress occurrence, String site,
                           String phi) {
            targets.add(TargetRow.of(sessionId, ++seq, occurrence, site, phi,
                    true, true));
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

        /** A declared fault marker the recording minted as {@code recorded}. */
        private void marker(OccurrenceAddress at, String rootId,
                            String symbol, String recorded) {
            root(at, rootId, symbol, RootKind.MARKER, recorded, null, null,
                    true);
        }

        /** A declared integral root, its recorded value and its domain. */
        private void integral(OccurrenceAddress at, String rootId,
                              String symbol, String recorded, String min,
                              String max) {
            root(at, rootId, symbol, RootKind.INTEGRAL, recorded, min, max,
                    true);
        }

        /** A declared clock reading. */
        private void clock(OccurrenceAddress at, String rootId,
                           String symbol, String recorded) {
            root(at, rootId, symbol, RootKind.CLOCK, recorded, null, null,
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

        /** The same, at the Java type the runtime states for the value. */
        private void write(Endpoint endpoint, LocationId location,
                           long version, String ref, String javaType) {
            writes.add(WriteRow.of(sessionId, ++seq, endpoint, location,
                    version, ref, javaType));
        }

        private void read(Endpoint endpoint, LocationId location,
                          long version, String symbol, String concrete) {
            reads.add(ReadRow.of(sessionId, ++seq, endpoint, location, version,
                    symbol, "I", concrete));
        }

        /**
         * The key chain as every session of the target's factor records it:
         * the rotation exports a key, addKeys receives it as M_HOFF_KEY and
         * stores it in the map, the target reads it back.
         */
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

        /** The value a handoff minted, as the VM propagated it. */
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

        /** One expression of the session's table, as the VM built it. */
        private void expression(String ref, JsonObject node) {
            expressions.put(ref, node);
        }

        /** One literal the VM recorded as a delivered constant. */
        private void constant(String ref, String value) {
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("_exp", "C_I_" + value);
            expression.addProperty("_java_type", "I");
            expressions.put(ref, expression);
        }

        /**
         * One verdict this replay published for itself.
         *
         * <p>The replay owns whether its obligation was admitted, and a
         * wave cuts a new flip only from a session that says ADMITTED of
         * every one of them -- so the fixture states it where the runtime
         * does, in the session's own file.</p>
         */
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
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
            // The fixture STATES the role, as a campaign's own session
            // manifest does.
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
                                    null));
        }
    }
}
