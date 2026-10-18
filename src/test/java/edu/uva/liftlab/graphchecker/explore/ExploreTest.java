package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
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
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
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
import edu.uva.liftlab.graphchecker.contract.UnplannedInput;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.plan.SystemView;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;

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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
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

    /** A leaf set as a session keeps it (Corpus.HeldLeaves): the names in
     *  the order computed, each name one instance across the sets,
     *  read-only. */
    @Test
    public void aHeldLeafSetKeepsItsOrderAndOneInstancePerName() {
        Set<String> first = new Corpus.HeldLeaves(new LinkedHashSet<String>(
                Arrays.asList(new String("loc:MAP/o#s"), "M_A", "b")));
        Set<String> second = new Corpus.HeldLeaves(new LinkedHashSet<String>(
                Arrays.asList("b", new String("loc:MAP/o#s"))));
        assertEquals(Arrays.asList("loc:MAP/o#s", "M_A", "b"),
                new ArrayList<String>(first));
        assertEquals(Arrays.asList("b", "loc:MAP/o#s"),
                new ArrayList<String>(second));
        assertTrue(first.iterator().next() == second.toArray()[1]);
        java.util.Iterator<String> names = first.iterator();
        names.next();
        try {
            names.remove();
            throw new AssertionError("a held leaf set changed");
        } catch (UnsupportedOperationException kept) {
            assertEquals(3, first.size());
        }
    }

    // ---- (0) the forced replay: the whole way to the throw first -------

    /**
     * PIPELINE §7.10: {@code if (a) { if (b) throw }}, the recording took
     * not-a.  The first round asks ONE FORCE run of the anchor, first, the
     * seed's flip of a beside it; once the forced session lands -- held
     * apart, no path of the corpus-wide views -- its forced flip asks a and
     * b at once.  Its verdict is read by the flip it asks, whatever id it
     * was answered under (an id moves as sessions land).
     */
    @Test
    public void theForcedRunIsAskedFirstAndItsPathAsksTheWholeWay()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("forced").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.marker(TARGET, "CASE.A", "M_A", "false");
        seed.integral(TARGET, "CASE.B", "M_B", "0", "0", "10");
        seed.decision(TARGET, "Guard#u8", 1, false, "M_A");
        seed.flush();
        JsonObject target = com.google.gson.JsonParser.parseString(
                targetSite("REGION.target", "Throw#u30", "Guard#u19"))
                .getAsJsonObject();
        target.add("force", com.google.gson.JsonParser.parseString(
                "[{\"siteId\":\"Guard#u19\",\"arm\":true},"
                        + "{\"siteId\":\"Guard#u8\",\"arm\":true}]"));
        target.add("chain", com.google.gson.JsonParser.parseString(
                "[{\"siteId\":\"Guard#u8\",\"outcome\":true}]"));
        scopeMap(iteration, target.toString());
        Path out = tree.newFolder("forced-out").toPath();
        Path results = results(out);

        // Round 0: the FORCE run first, the seed's flip of a beside it.
        Path wave0 = out.resolve("obligations-0000");
        JsonObject first = plan(iteration, TARGET_SELECTOR, null, results,
                wave0, 0);
        List<Obligation> proposed = obligations(wave0);
        assertEquals("the FORCE run, then the seed's flip: " + proposed, 2,
                proposed.size());
        Obligation force = proposed.get(0);
        assertTrue(force.force() && !force.flips());
        assertEquals(Corpus.pathId("s-seed", TARGET), force.pathId());
        Obligation seedFlip = proposed.get(1);
        assertEquals("Guard#u8", seedFlip.siteId());
        assertEquals("PROPOSED",
                first.getAsJsonObject("force").get("state").getAsString());
        // Its worker asks no solver: the seed's world, the anchor forced.
        Worker forcing = solve(iteration, wave0, force, out, "force");
        assertEquals(Verdict.SAT_MODEL_READY, forcing.verdict);
        JsonObject focus = RowCodec.readJsonl(forcing.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        assertTrue(focus.get("force").getAsBoolean());
        assertTrue(focus.get("flip").isJsonNull());
        assertEquals(TARGET.render(),
                focus.get("declaredTarget").getAsString());
        // In flight, neither is asked again.
        Path flying = out.resolve("in_flight.jsonl");
        RowCodec.writeAll(flying, Arrays.asList(force, seedFlip),
                ExploreCodec::writeObligation);
        Path again = out.resolve("obligations-0000b");
        JsonObject waiting = plan(iteration, results, flying, again, 1,
                DEFAULT_BOUNDS);
        assertTrue(obligations(again).isEmpty());
        assertEquals("IN_FLIGHT",
                waiting.getAsJsonObject("force").get("state").getAsString());

        // The forced session lands: a and b forced off their arms, its
        // target standing at a with the whole way to the throw as phi.
        Session forced = new Session(iteration, "s-forced");
        forced.activation(TARGET, true);
        forced.marker(TARGET, "CASE.A", "M_A", "false");
        forced.integral(TARGET, "CASE.B", "M_B", "0", "0", "10");
        forced.forcedDecision(TARGET, "Guard#u8", 1, true, "M_A");
        forced.forcedDecision(TARGET, "Guard#u19", 1, true, "(> M_B 5)");
        forced.forcedTarget(TARGET, "Guard#u19", 3L,
                "(and M_A (> M_B 5))");
        forced.answered(ObligationResult.of(force.obligationId(),
                Verdict.ADMITTED, "s-forced", "FORCED_TARGET: reached"));
        forced.flush();
        record(results, ObligationResult.of(force.obligationId(),
                Verdict.ADMITTED, "s-forced", "FORCED_TARGET: reached"));
        Corpus corpus = Corpus.read(iteration, null);
        assertEquals("held apart from every corpus-wide view", 1,
                corpus.sessions().size());
        assertTrue(corpus.targetsOn(TARGET).isEmpty()
                && corpus.pathsOf(TARGET).size() == 1);
        assertEquals(1, corpus.forcedPaths(TARGET).size());
        assertEquals(3L, corpus.forcedFrom("s-forced"));

        // Round 1: the forced flip, at a's forced arm; the seed's flies.
        RowCodec.writeAll(flying, Collections.singletonList(seedFlip),
                ExploreCodec::writeObligation);
        Path wave1 = out.resolve("obligations-0001");
        JsonObject asking = plan(iteration, results, flying, wave1, 1,
                DEFAULT_BOUNDS);
        List<Obligation> next = obligations(wave1);
        assertEquals("the forced flip alone: " + next, 1, next.size());
        Obligation whole = next.get(0);
        assertEquals("Guard#u8", whole.siteId());
        assertTrue(whole.flippedOutcome());
        assertEquals(Corpus.pathId("s-forced", TARGET), whole.pathId());
        assertEquals("OPEN", asking.getAsJsonObject("force")
                .get("forcedFlipVerdict").getAsString());
        Worker asked = solve(iteration, wave1, whole, out, "forced-flip");
        assertEquals(Verdict.SAT_MODEL_READY, asked.verdict);
        assertEquals("a holds", "true",
                asked.obligation.rootAssignments().get("CASE.A"));
        assertTrue("and so does b, nested behind it, in the same world",
                Integer.parseInt(asked.obligation.rootAssignments()
                        .get("CASE.B")) > 5);

        // Answered under an id the flip has since left: read by its flip,
        // and the seed's flip of a, asked again, counts after it.
        land(iteration, "obligations-0001", whole, ObligationResult.of(
                "drifted00000000", Verdict.UNSAT, "", "no world"));
        Files.delete(flying);
        Path wave2 = out.resolve("obligations-0002");
        JsonObject after = plan(iteration, TARGET_SELECTOR, null, results,
                wave2, 2);
        JsonObject view = after.getAsJsonObject("force");
        assertEquals("UNSAT", view.get("forcedFlipVerdict").getAsString());
        assertEquals(1, view.get("seedFlipsAfterForcedFlip").getAsInt());
        assertTrue(obligations(wave2).stream().anyMatch(o ->
                o.pathId().equals(Corpus.pathId("s-seed", TARGET))));
    }

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

    /**
     * The fence (PIPELINE §7.10): a FORCED session with no forced target --
     * a FORCE run that diverged or never closed, published anyway -- is no
     * session: none of its messages is a sender, its interaction none, its
     * write no writer.  One at its forced target keeps its messages from
     * before its forced world for its own path alone.
     */
    @Test
    public void aForcedSessionReachesNoOtherPath() throws Exception {
        Path iteration = tree.newFolder("fence").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, WRITER, PRODUCER);
        seed.constant("e.seed", "1");
        seed.export(ROTATED, "e.seed", 11L, "1");
        seed.attach(DELIVERED, "M_HOFF_KEY", "1", ROTATED);
        seed.flush();
        Session stray = new Session(iteration, "s-stray");
        stray.activations(false, WRITER, PRODUCER);
        stray.constant("e.stray", "2");
        stray.export(ROTATED, "e.stray", 12L, "2");
        stray.attach(DELIVERED, "M_HOFF_KEY", "2", ROTATED);
        stray.write(STORED, ALL_KEYS, 5L, "e.stray");
        stray.forcedDecision(TARGET, "Guard#u8", 1, true, "M_A");
        stray.flush();
        Session forced = new Session(iteration, "s-forced");
        forced.activations(false, WRITER, PRODUCER);
        forced.constant("e.before", "3");
        forced.constant("e.after", "4");
        forced.export(ROTATED, "e.before", 13L, "3");
        forced.attach(DELIVERED, "M_HOFF_KEY", "3", ROTATED);
        forced.forcedDecision(TARGET, "Guard#u8", 1, true, "M_A");
        forced.forcedTarget(TARGET, "Guard#u8", forced.seq, "M_A");
        forced.export(ROTATED, "e.after", 14L, "4");
        forced.answered(ObligationResult.of("force", Verdict.ADMITTED,
                "s-forced", "FORCED_TARGET: reached"));
        forced.flush();

        Corpus corpus = Corpus.read(iteration, null);
        Interaction slot = Interaction.of(InteractionKind.WIRE, ROTATED,
                DELIVERED);
        assertNull("no forced target: no session", corpus.session("s-stray"));
        assertTrue(corpus.writesOf("s-stray",
                SmtLowering.locationKey(ALL_KEYS)).isEmpty());
        Object[][] views = {
                {"senders", sessionsOf(corpus.exportsOf(ROTATED))},
                {"deliveries", sessionsOf(corpus.attachesOf(slot))},
                {"interactions", corpus.interactions().containsKey(slot.id())
                        ? Collections.singleton("s-seed")
                        : Collections.<String>emptySet()}};
        for (Object[] view : views) {
            assertEquals((String) view[0], Collections.singleton("s-seed"),
                    view[1]);
        }
        List<ExportRow> own = corpus.ownExportsOf("s-forced", ROTATED);
        assertEquals("its own sender, from before its forced world", 1,
                own.size());
        assertTrue(own.get(0).seq() < corpus.forcedFrom("s-forced"));
        assertTrue(corpus.ownExportsOf("s-seed", ROTATED).isEmpty());
        Object[][] scopes = {
                {"the seed's path", "s-seed",
                        Collections.singleton("s-seed")},
                {"the forced path", "s-forced", new LinkedHashSet<String>(
                        Arrays.asList("s-seed", "s-forced"))}};
        for (Object[] scope : scopes) {
            Set<String> sessions = new LinkedHashSet<String>();
            for (Arms.Arm arm : corpus.arms().armsAt(slot, "M_HOFF_KEY",
                    (String) scope[1])) {
                sessions.add(arm.sessionId());
            }
            assertEquals((String) scope[0], scope[2], sessions);
        }
    }

    /**
     * A session's own arms of a slot ({@code Arms#ownArmsAt}: what a
     * handoff's name in an arm's key states) are its arms among every
     * session's ({@code Arms#armsAt}), in order, each guarded by its own
     * symbols on the roots its session ran: an arm naming a root its session
     * never ran is refused, its sibling naming none is not, and a minted
     * root no session varied guards only the arm that names it -- asked
     * once or again (the guards are held per session).
     */
    @Test
    public void aSessionsOwnArmsAreGuardedByTheirOwnSymbols()
            throws Exception {
        Path iteration = tree.newFolder("own-arms").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, WRITER, PRODUCER);
        seed.integral(PRODUCER, "CASE.A", "M_A", "1", "0", "10");
        seed.constant("e.seed.const", "1");
        seed.symbolic("e.seed.named", "M_A");
        seed.export(ROTATED, "e.seed.const", 11L, "1");
        seed.export(ROTATED, "e.seed.named", 12L, "1");
        seed.attach(DELIVERED, "M_HOFF_KEY", "1", ROTATED);
        seed.flush();
        Session other = new Session(iteration, "s-other");
        other.activations(false, WRITER, PRODUCER);
        other.constant("e.other.const", "2");
        other.symbolic("e.other.named", "M_A");
        other.export(ROTATED, "e.other.const", 13L, "2");
        other.export(ROTATED, "e.other.named", 14L, "2");
        other.attach(DELIVERED, "M_HOFF_KEY", "2", ROTATED);
        other.flush();

        Corpus corpus = Corpus.read(iteration, null);
        Arms arms = corpus.arms();
        Interaction slot = Interaction.of(InteractionKind.WIRE, ROTATED,
                DELIVERED);
        List<String> expected = Arrays.asList("s-other e.other.const {}",
                "s-seed e.seed.const {}", "s-seed e.seed.named {M_A=1}");
        for (int ask = 0; ask < 2; ask++) {
            List<String> all = new ArrayList<String>();
            for (Arms.Arm arm : arms.armsAt(slot, "M_HOFF_KEY", "s-seed")) {
                all.add(arm.sessionId() + " " + arm.expressionRef() + " "
                        + arm.guard());
            }
            assertEquals("ask " + ask, expected, all);
            assertEquals("ask " + ask, Collections.singleton(slot.id()
                    + "|s-other|CASE.A"), arms.drainRefusals());
            for (String session : Arrays.asList("s-seed", "s-other")) {
                List<String> own = new ArrayList<String>();
                for (Arms.Arm arm : arms.ownArmsAt(slot, "M_HOFF_KEY",
                        session)) {
                    own.add(arm.sessionId() + " " + arm.expressionRef()
                            + " " + arm.guard());
                }
                List<String> its = new ArrayList<String>();
                for (String arm : all) {
                    if (arm.startsWith(session + " ")) its.add(arm);
                }
                assertEquals(session + ", ask " + ask, its, own);
            }
            assertEquals("ask " + ask, Collections.singleton(slot.id()
                    + "|s-other|CASE.A"), arms.drainRefusals());
        }
    }

    private static Set<String> sessionsOf(List<? extends Object> rows) {
        Set<String> sessions = new LinkedHashSet<String>();
        for (Object row : rows) {
            sessions.add(row instanceof ExportRow
                    ? ((ExportRow) row).sessionId()
                    : ((AttachRow) row).sessionId());
        }
        return sessions;
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
        String query = queryText(nested.directory);
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

    // ---- (1b) a world is what it DELIVERED to the arm's task -----------

    /**
     * AN ARM'S WORLD IS WHAT THE SESSION'S WORLD DELIVERED TO ITS TASK.
     *
     * <p>Two worlds that delivered a task the same structure ask its arms
     * the same question, whatever flips produced it.  Keyed by the CAUSE --
     * the flips of the world, or those of them that reach the task over the
     * corpus's causal graph -- one question was asked once per combination
     * of flips: of hdfs-11741 round v37's 641 obligations, 561 were distinct
     * (task, arm, prefix, delivered structure).</p>
     *
     * <p>Five sessions over one corpus.  The seed, and four admitted
     * replays whose factor member got one handoff fewer, each for its own
     * reason: the producer's rotation, which the member attaches from; a
     * balancer flip on a node of its own; both at once; and a sidecar's
     * flip, which reaches the task only through the map's second reader.
     * The four delivered the same structure, so they are ONE world here,
     * and the wave asks the arm twice: over the seed's inputs and over
     * theirs, the latter cut from the smallest world that offers it.</p>
     */
    @Test
    public void anArmIsKeyedByWhatTheWorldDeliveredAndByNoFlip()
            throws Exception {
        Path iteration = tree.newFolder("reaching").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, WRITER, PRODUCER, BALANCER, READER,
                SIDECAR);
        seed.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        seed.integral(PRODUCER, "CASE.TICK", "M_TICK", "1", "0", "10");
        seed.integral(BALANCER, "CASE.MOVE", "M_MOVE", "1", "0", "10");
        seed.integral(SIDECAR, "CASE.SEND", "M_SEND", "1", "0", "10");
        seed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.symbolic("e.token", "M_HOFF_TOKEN");
        seed.constant("e.119992", "119992");
        seed.constant("e.554433", "554433");
        seed.decision(TARGET, "Guard#u8", 1, false, "EXPR.0000000000000001");
        seed.decision(PRODUCER, "Rotate#u5", 1, false, "(> M_TICK 3)");
        seed.decision(BALANCER, "Balance#u2", 1, false, "(> M_MOVE 1)");
        seed.decision(SIDECAR, "Send#u4", 1, false, "(> M_SEND 0)");
        // The wire: the rotation exports the key, addKeys on the target's
        // node attaches it and writes it into the map the target reads.
        seed.export(ROTATED, "e.119992", 11L, "119992");
        seed.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        seed.write(STORED, ALL_KEYS, 5L, "e.stored");
        seed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        // And a second reader of the same map, started by a message of its
        // own: state-connected to the target, upstream of nothing it reads.
        seed.export(SENT, "e.554433", 12L, "554433");
        seed.attach(RECEIVED, "M_HOFF_TOKEN", "554433", SENT);
        seed.read(CONSULTED, ALL_KEYS, 5L, "M_SEEN_KEY", "119992");
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"));

        // Four admitted replays, whose rows AT THE TARGET are the seed's
        // and whose factor member received one handoff fewer: four causes,
        // one delivered structure.
        heldTo(iteration, "s-up", PRODUCER);
        heldTo(iteration, "s-aside", BALANCER);
        heldTo(iteration, "s-up-and-aside", PRODUCER);
        heldTo(iteration, "s-through-factor", SIDECAR);
        worker(iteration, "obligations-0000", "ob-up", "OBL.up", "s-up",
                PRODUCER, "Rotate#u5",
                Collections.singletonMap("CASE.TICK", "7"), NONE);
        worker(iteration, "obligations-0000", "ob-aside", "OBL.aside",
                "s-aside", BALANCER, "Balance#u2",
                Collections.singletonMap("CASE.MOVE", "2"), NONE);
        worker(iteration, "obligations-0000", "ob-both", "OBL.both",
                "s-up-and-aside", PRODUCER, "Rotate#u5",
                Collections.singletonMap("CASE.TICK", "7"),
                NONE,
                Collections.singletonList(new Corpus.Flip(BALANCER.id(),
                        "Balance#u2", 1, true, "OBL.aside")));
        worker(iteration, "obligations-0000", "ob-factor", "OBL.factor",
                "s-through-factor", SIDECAR, "Send#u4",
                Collections.singletonMap("CASE.SEND", "0"), NONE);

        Corpus corpus = Corpus.read(iteration, null);
        Task task = ClosurePlanner.taskOf(corpus,
                ClosurePlanner.taskId(TARGET));
        assertNotNull(task);
        assertTrue("addKeys writes the map the target reads, so it is a "
                        + "state-connected member of its factor: "
                        + task.factor(), task.factor().contains(WRITER));
        assertTrue("and so is the second reader of that map: "
                + task.factor(), task.factor().contains(READER));

        // ---- what each world delivered to this task ------------------
        String seedInputs = dependence(corpus, task, "s-seed", "Guard#u8");
        String delivered = dependence(corpus, task, "s-up", "Guard#u8");
        assertFalse("the rotation's world delivered the factor member one "
                + "handoff fewer", seedInputs.equals(delivered));
        for (String sessionId : Arrays.asList("s-aside", "s-up-and-aside",
                "s-through-factor")) {
            assertEquals(sessionId + " delivered the same structure, so it "
                            + "is the same world here, whatever its flips",
                    delivered, dependence(corpus, task, sessionId,
                            "Guard#u8"));
        }
        assertFalse("which the flips alone do not say: they differ",
                ObligationFactory.worldDigest(corpus.world("s-up")).equals(
                        ObligationFactory.worldDigest(
                                corpus.world("s-aside"))));

        // ---- so the wave asks the arm once per delivered structure -----
        Path out = tree.newFolder("reaching-out").toPath();
        Path results = results(out);
        Path wave = out.resolve("obligations-0001");
        JsonObject manifest = plan(iteration, TARGET_SELECTOR, null, results,
                wave, 1);
        assertEquals("OBLIGATIONS_PROPOSED",
                manifest.get("state").getAsString());
        List<Obligation> proposed = obligations(wave);
        assertEquals("one arm, two structures -- the seed's and the one four "
                + "worlds delivered alike: " + proposed, 2, proposed.size());
        String taskId = ClosurePlanner.taskId(TARGET);
        Map<String, Obligation> byId = new LinkedHashMap<String, Obligation>();
        for (Obligation obligation : proposed) {
            assertEquals("Guard#u8", obligation.siteId());
            assertTrue(obligation.flippedOutcome());
            byId.put(obligation.obligationId(), obligation);
        }
        assertTrue("the arm over the seed's inputs: " + proposed,
                byId.containsKey(ObligationFactory.obligationId(taskId,
                        "Guard#u8", 1, true, seedInputs)));
        Obligation shared = byId.get(ObligationFactory.obligationId(taskId,
                "Guard#u8", 1, true, delivered));
        assertNotNull("and the same arm over what the four delivered, which "
                + "is the nested flip the 11741 witness needs: " + proposed,
                shared);
        assertFalse("cut from a world of one flip, never from the world of "
                        + "two that delivered the same: " + shared,
                Corpus.pathId("s-up-and-aside", TARGET)
                        .equals(shared.pathId()));
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
     * WHAT A FEEDER WROTE WHERE THE GUARD READS is named by what binds it in
     * the flip query ({@code Corpus#written}): a handoff it wrote by its own
     * run's wire arms (the producer's class, export site, canonical term),
     * else by its arrival; a read inside its term by every writer the query
     * offers it, else by its value; a term that does not lower by the values
     * observed; no depth bound, a cycle by its graph (each unit named once,
     * whichever the walk entered first).  Each
     * by the query's own conditions: an arm or a writer's value the query
     * drops (a name it cannot declare, a value of another sort) binds
     * nothing; a name a node has only in one run by the node, an identity
     * hash and an object the VM named by its class and where the key first
     * meets it (two values aliased otherwise name apart).  Each row: two
     * worlds, and whether they share the arm's key.
     */
    @Test(timeout = 120000)
    public void aWrittenTermIsNamedByWhatBindsItInTheQuery()
            throws Exception {
        Path iteration = tree.newFolder("written-binds").toPath();
        JsonObject symbolA = leaf("M_A", "I");
        LocationId[] chain = new LocationId[4];
        OccurrenceAddress[] writers = new OccurrenceAddress[4];
        for (int at = 0; at < 4; at++) {
            chain[at] = LocationId.of(LocationKind.INSTANCE, "50", "" + at);
            writers[at] = occurrence("hdfs-case/dn0", "REGION.chain" + at,
                    CausalContext.of(Role.of("CHAIN" + at), "", 1),
                    "o.a.h.h.s.d.Chain" + at + "#run#1");
        }
        OccurrenceAddress concurrent = occurrence("hdfs-case/dn0",
                "REGION.extra", CausalContext.of(Role.of("EXTRA"), "", 1),
                "o.a.h.h.s.d.Extra#run#1");
        OccurrenceAddress innerReader = occurrence("hdfs-case/dn0",
                "REGION.innerReader", CausalContext.of(Role.of("INNER"), "",
                        1), "o.a.h.h.s.d.InnerReader#run#1");
        JsonObject mystery = new JsonObject();
        mystery.addProperty("_type", "NoSuchExpression");
        mystery.addProperty("_java_type", "I");
        LocationId cycledOne = LocationId.of(LocationKind.INSTANCE, "60", "1");
        LocationId cycledTwo = LocationId.of(LocationKind.INSTANCE, "60", "2");
        OccurrenceAddress[] cycled = new OccurrenceAddress[2];
        for (int at = 0; at < 2; at++) {
            cycled[at] = occurrence("hdfs-case/dn0", "REGION.cycle",
                    CausalContext.of(Role.of("CYCLE"), "", at + 1),
                    "o.a.h.h.s.d.Cycle#run#" + (at + 1));
        }
        int ringSize = 40;
        OccurrenceAddress[] ring = new OccurrenceAddress[ringSize];
        LocationId[] ringed = new LocationId[ringSize];
        for (int at = 0; at < ringSize; at++) {
            ring[at] = occurrence("hdfs-case/dn0", "REGION.ring",
                    CausalContext.of(Role.of("RING"), "", at + 1),
                    "o.a.h.h.s.d.Ring#run#" + (at + 1));
            ringed[at] = LocationId.of(LocationKind.INSTANCE, "70", "" + at);
        }
        // session -> what WRITER writes at the guard's location
        String[] names = {"s-seed", "h-plus", "h-minus", "h-plus-again",
            "p-five", "p-seven", "i-one", "i-two", "u-five", "u-seven",
            "u-five-again", "u-unstated", "d-one", "d-two", "c-up",
            "c-self", "g-eleven", "g-eleven-minus", "g-twelve", "r-three",
            "r-four", "b-three", "b-four", "n-one", "n-one-again", "n-two",
            "y-hash", "y-hash-again", "y-other", "v-doc", "v-doc-again",
            "v-other", "w-alias", "w-alias-again", "w-apart", "k-ring",
            "k-ring-again", "k-ring-deep"};
        for (String name : names) {
            Session session = new Session(iteration, name);
            session.activation(TARGET, !name.equals("s-seed"));
            session.activation(WRITER, false);
            session.integral(TARGET, "CASE.A", "M_A", "0", "0", "10");
            String guardValue = "0";
            if (name.startsWith("h-")) {
                session.activation(PRODUCER, false);
                // Its path decided on an unsupported subterm first: that
                // conjunct marks no delivered term unsupported.
                session.expression("EXPR.00000000000000f5", mystery);
                session.decision(PRODUCER, "Rotate#u3", 1, true,
                        "(> (+ M_A EXPR.00000000000000f5) 0)");
                session.expression("EXPR.00000000000000f1", binary(
                        name.equals("h-minus") ? "-" : "+", symbolA,
                        literal(name.equals("h-minus") ? 1 : 10)));
                session.export(ROTATED, "EXPR.00000000000000f1", 11L, "11");
                session.attach(DELIVERED, "M_HOFF_KEY", "11", ROTATED);
                session.symbolic("EXPR.00000000000000f2", "M_HOFF_KEY", "I");
            } else if (name.startsWith("g-")) {
                // A producer arm naming what no row declares: the query
                // drops it and pins the handoff to its arrival.
                session.activation(PRODUCER, false);
                session.expression("EXPR.00000000000000f1", binary(
                        name.endsWith("minus") ? "-" : "+", leaf("M_GHOST", "I"),
                        literal(name.endsWith("minus") ? 1 : 10)));
                String arrival = name.equals("g-twelve") ? "12" : "11";
                session.export(ROTATED, "EXPR.00000000000000f1", 11L, arrival);
                session.attach(DELIVERED, "M_HOFF_KEY", arrival, ROTATED);
                session.symbolic("EXPR.00000000000000f2", "M_HOFF_KEY", "I");
            } else if (name.startsWith("r-") || name.startsWith("b-")) {
                // An inner read whose one writer the query takes nothing
                // from -- its value names what no row declares, or is a
                // Bool where the read is an int -- is pinned to its value.
                session.activation(innerReader, false, true, "inner");
                session.activation(writers[0], false, true, "chain0");
                session.expression("EXPR.00000000000000f3",
                        name.startsWith("r-") ? binary("+",
                                leaf("M_GHOST", "I"), literal(1))
                                : binary(">", symbolA, literal(3)));
                session.write(at(writers[0], "Chain0#u1:WRITE", "Chain0#u1"),
                        chain[0], 7L, "EXPR.00000000000000f3");
                session.read(at(innerReader, "Inner#u2:READ", "Inner#u2"),
                        chain[0], 7L, "M_INNER",
                        name.endsWith("three") ? "3" : "4");
                session.symbolic("EXPR.00000000000000f2", "M_INNER", "I");
            } else if (name.startsWith("y-")) {
                // A searcher's name, which spells its identity hash.
                session.expression("EXPR.00000000000000f2",
                        VmExpressionIr.stringConstant("Searcher@"
                                + (name.equals("y-hash") ? "4d4eeaac"
                                : "2a3146e9") + "["
                                + (name.equals("y-other") ? "other" : "core")
                                + "] main"));
            } else if (name.startsWith("w-")) {
                // Two searchers' names: one searcher twice, or two.
                String first = name.equals("w-alias-again") ? "11aa22bb"
                        : "4d4eeaac";
                session.expression("EXPR.00000000000000f2",
                        VmExpressionIr.stringConstant("Searcher@" + first
                                + " Searcher@" + (name.equals("w-apart")
                                ? "2a3146e9" : first)));
            } else if (name.startsWith("v-")) {
                // A term that does not lower, whose reader observed an
                // object the VM named, by its run's rid.
                session.expression("EXPR.00000000000000f2", mystery);
                guardValue = name.equals("v-doc") ? "M_L'org/x/Doc'_6574"
                        : name.equals("v-doc-again") ? "M_L'org/x/Doc'_6601"
                        : "M_L'org/x/Other'_6574";
            } else if (name.startsWith("n-")) {
                // A node's URL, at the port this run gave it: node1 at 46805
                // (n-one) or 36143 (n-one-again), node2 at 41111 (n-two).
                session.spelled("auto0/node1", name.equals("n-one")
                        ? "127.0.0.1:46805_solr" : "127.0.0.1:36143_solr");
                session.spelled("auto0/node2", "127.0.0.1:41111_solr");
                session.expression("EXPR.00000000000000f2",
                        VmExpressionIr.stringConstant("http://127.0.0.1:"
                                + (name.equals("n-one") ? "46805"
                                : name.equals("n-two") ? "41111" : "36143")
                                + "/solr"));
            } else if (name.startsWith("c-")) {
                // A cycle of two writers of one class and site: the second
                // one's read takes the first one's write (c-up) or its own
                // (c-self).
                for (OccurrenceAddress writer : cycled) {
                    session.activation(writer, false);
                }
                session.expression("EXPR.00000000000000c1",
                        binary("+", leaf("M_CYCLE_A", "I"), literal(1)));
                session.expression("EXPR.00000000000000c2",
                        binary("+", leaf("M_CYCLE_B", "I"), literal(1)));
                session.write(at(cycled[0], "Cycle#u1:WRITE", "Cycle#u1"),
                        cycledOne, 7L, "EXPR.00000000000000c1");
                session.write(at(cycled[1], "Cycle#u1:WRITE", "Cycle#u1"),
                        cycledTwo, 8L, "EXPR.00000000000000c2");
                session.write(at(cycled[1], "Cycle#u1:WRITE", "Cycle#u1"),
                        cycledOne, 9L, "EXPR.00000000000000c2");
                session.read(at(cycled[0], "Cycle#u2:READ", "Cycle#u2"),
                        cycledTwo, 8L, "M_CYCLE_A", "2");
                session.read(at(cycled[1], "Cycle#u2:READ", "Cycle#u2"),
                        cycledOne, name.equals("c-up") ? 7L : 9L,
                        "M_CYCLE_B", "1");
                session.read(at(WRITER, "Inner#u2:READ", "Inner#u2"),
                        cycledOne, 7L, "M_CYCLED", "3");
                session.symbolic("EXPR.00000000000000f2", "M_CYCLED", "I");
            } else if (name.startsWith("k-")) {
                // A ring of forty writers: each one's term reads the next
                // location, which the next two wrote -- a cycle met from
                // every one of 2^40 paths (solr-adhoc-09 SC7: naming it
                // anew from every entry never ended).  k-ring-deep adds 2
                // instead of 1 twenty writers deep.
                for (int at = 0; at < ringSize; at++) {
                    session.activation(ring[at], false, true, "ring" + at);
                    String ref = String.format("EXPR.%016x", 0x100 + at);
                    session.expression(ref, binary("+", leaf("M_RING" + at,
                            "I"), literal(name.equals("k-ring-deep")
                            && at == ringSize / 2 ? 2 : 1)));
                    session.write(at(ring[at], "Ring#u1:WRITE", "Ring#u1"),
                            ringed[at], 100L + 2 * at, ref);
                    session.write(at(ring[at], "Ring#u1:WRITE", "Ring#u1"),
                            ringed[(at + ringSize - 1) % ringSize],
                            101L + 2 * ((at + ringSize - 1) % ringSize), ref);
                    int next = (at + 1) % ringSize;
                    session.read(at(ring[at], "Ring#u2:READ", "Ring#u2"),
                            ringed[next], 100L + 2 * next, "M_RING" + at, "1");
                }
                session.read(at(WRITER, "Inner#u2:READ", "Inner#u2"),
                        ringed[0], 100L, "M_RINGED",
                        name.equals("k-ring-again") ? "4" : "3");
                session.symbolic("EXPR.00000000000000f2", "M_RINGED", "I");
            } else if (name.startsWith("p-")) {
                session.attach(DELIVERED, "M_HOFF_KEY",
                        name.equals("p-five") ? "5" : "7", null);
                session.symbolic("EXPR.00000000000000f2", "M_HOFF_KEY", "I");
            } else if (name.startsWith("i-")) {
                // An inner read by a turn of its own, which a concurrent
                // writer (its own thread, instrumented) may have fed.
                session.activation(innerReader, false, true, "inner");
                session.activation(writers[0], false, true, "chain0");
                session.constant("EXPR.00000000000000f3", "3");
                session.write(at(writers[0], "Chain0#u1:WRITE", "Chain0#u1"),
                        chain[0], 7L, "EXPR.00000000000000f3");
                if (name.equals("i-two")) {
                    session.activation(concurrent, false, true, "extra");
                    session.constant("EXPR.00000000000000f4", "9");
                    session.write(at(concurrent, "Extra#u1:WRITE", "Extra#u1"),
                            chain[0], 8L, "EXPR.00000000000000f4");
                }
                session.read(at(innerReader, "Inner#u2:READ", "Inner#u2"),
                        chain[0], 7L, "M_INNER", "3");
                session.symbolic("EXPR.00000000000000f2", "M_INNER", "I");
            } else if (name.startsWith("u-")) {
                session.expression("EXPR.00000000000000f2", mystery);
                guardValue = name.startsWith("u-five") ? "5"
                        : name.equals("u-unstated") ? null : "7";
            } else if (name.equals("s-seed")) {
                session.constant("EXPR.00000000000000f2", "4");
            } else {
                // A chain four writers deep: WRITER's term reads chain[0],
                // written by writers[0] from chain[1], ... chain[3] holds
                // a constant, 1 or 2.
                for (int at = 0; at < 4; at++) {
                    session.activation(writers[at], false);
                    String ref = String.format("EXPR.00000000000000%02x",
                            0xa0 + at);
                    if (at == 3) {
                        session.constant(ref, name.equals("d-one") ? "1" : "2");
                    } else {
                        session.symbolic(ref, "M_CHAIN" + (at + 1), "I");
                        session.read(at(writers[at], "Chain" + at
                                        + "#u2:READ", "Chain" + at + "#u2"),
                                chain[at + 1], 5L, "M_CHAIN" + (at + 1), "1");
                    }
                    session.write(at(writers[at], "Chain" + at + "#u1:WRITE",
                            "Chain" + at + "#u1"), chain[at], 5L, ref);
                }
                session.read(at(WRITER, "Inner#u2:READ", "Inner#u2"),
                        chain[0], 5L, "M_CHAIN0", "1");
                session.symbolic("EXPR.00000000000000f2", "M_CHAIN0", "I");
            }
            session.write(STORED, ALL_KEYS, 5L, "EXPR.00000000000000f2");
            session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", guardValue);
            session.decision(TARGET, "Guard#u8", 1, false,
                    "(> (+ M_A M_READ_KEY) 3)");
            session.flush();
        }
        Corpus corpus = Corpus.read(iteration, null);
        Task task = ClosurePlanner.taskOf(corpus,
                ClosurePlanner.taskId(TARGET));
        Object[][] rows = {
            {"h-plus", "h-minus", false,
                    "a producer sending M_A-1 after its flip, not M_A+10"},
            {"h-plus", "h-plus-again", true, "the same arm in another run"},
            {"p-five", "p-seven", false, "a pinned payload 5 against 7"},
            {"i-one", "i-two", false,
                    "a concurrent writer the inner read may take"},
            {"u-five", "u-seven", false,
                    "a term that does not lower, observed 5 against 7"},
            {"u-five", "u-five-again", true,
                    "the same observed value of such a term"},
            {"u-five", "u-unstated", false,
                    "a read that states no value is another one"},
            {"d-one", "d-two", false,
                    "a constant four writers deep (no depth bound)"},
            {"c-up", "c-self", false,
                    "a back-edge to the writer above against to itself"},
            {"g-eleven", "g-twelve", false,
                    "an arm the query drops: pinned to 11 against 12"},
            {"g-eleven", "g-eleven-minus", true,
                    "whatever the dropped arm delivered"},
            {"r-three", "r-four", false,
                    "a writer's value naming what no row declares"},
            {"b-three", "b-four", false,
                    "a writer's value of another sort than the read"},
            {"n-one", "n-one-again", true,
                    "one node's URL at the port each run gave it"},
            {"n-one", "n-two", false, "another node's URL"},
            {"y-hash", "y-hash-again", true,
                    "one name at another identity hash"},
            {"y-hash", "y-other", false, "another name"},
            {"v-doc", "v-doc-again", true,
                    "an observed object of one class at another rid"},
            {"v-doc", "v-other", false, "an object of another class"},
            {"w-alias", "w-alias-again", true,
                    "one object twice, at another identity hash"},
            {"w-alias", "w-apart", false, "one object twice against two"},
            {"k-ring", "k-ring-again", true,
                    "a ring of forty writers, each unit named once"},
            {"k-ring", "k-ring-deep", false,
                    "another constant twenty writers deep in the ring"},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[3], row[2], dependence(corpus, task,
                    (String) row[0], "Guard#u8").equals(dependence(corpus,
                    task, (String) row[1], "Guard#u8")));
        }
    }

    /**
     * A RUN'S HANDLE IS NUMBERED BY WHERE THE KEY FIRST MEETS IT ({@code
     * Corpus#numbered}): an object at another rid in every place names
     * alike, an object that two places shared in one world and not in the
     * other names apart, whatever spelling (an observed rid, a minted
     * identity) names it.
     */
    @Test
    public void aRunsHandleIsNumberedByWhereTheKeyFirstMeetsIt() {
        String[][] rows = {
            // three handles' rids, the numbered text
            {"5 7 5", "f(M_L'Doc'_1 M_L'Doc'_2 identity__1)"},
            {"9 3 9", "f(M_L'Doc'_1 M_L'Doc'_2 identity__1)"},
            {"5 5 7", "f(M_L'Doc'_1 M_L'Doc'_1 identity__2)"},
        };
        for (String[] row : rows) {
            String[] rid = row[0].split(" ");
            String text = "f(" + Corpus.handle("M_L'Doc'_", "rid:" + rid[0])
                    + " " + Corpus.handle("M_L'Doc'_", "rid:" + rid[1]) + " "
                    + Corpus.handle("identity__", "rid:" + rid[2]) + ")";
            Map<String, String> order = new LinkedHashMap<String, String>();
            assertEquals(row[0], row[1], Corpus.numbered(text, order));
            assertEquals(row[0], new HashSet<String>(Arrays.asList(rid))
                    .size(), order.size());
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

    /**
     * WHAT FED A MEMBER, BY SEMANTIC COUNTS ({@code Corpus#handoffs}): each
     * distinct (handoff site, producer) once -- hdfs-11741's five keys
     * against four are five distinct exports against four to addKeys, the
     * writer of the map the guard reads, while a content field read again
     * four or three times is one delivery, and a queue's first item is one
     * whatever its sequential counter (solr-adhoc-19 SC6: qn-0000000000 in
     * one world, qn-0000000001 in another); two producers of one site are
     * two.  And WHOSE: a member is a line where it wrote where the query
     * reads or a MESSAGE fed it (what the arm consumes after the flip:
     * hdfs-11741); what it read of a store (a content port) is a read,
     * named wherever it reaches the query -- a member that only read the
     * store and wrote nothing the guard reads, present in one world only,
     * keys alike (solr-adhoc-19 SC6) -- while a handoff the guard states is
     * named by what binds it, so a member delivering the task another value
     * there re-keys through it.
     */
    @Test
    public void aMemberIsFedByDistinctSitesAndProducers() throws Exception {
        Path iteration = tree.newFolder("fed-by").toPath();
        String queue = "SOLR_ZK#CONTENT:|overseer|queue|qn-000000000";
        String props = "SOLR_ZK#CONTENT:|clusterprops.json#|legacyCloud";
        Endpoint told = at(TARGET, "XCH.resp.told", "Told#1");
        // session, the exports of PRODUCER WRITER takes in (by index; -1 a
        // SIDECAR one), the content site it reads (null: none) and how
        // often, what PRODUCER told the task (null: nothing), and how READER
        // ran ("": not at all, "store": reading the store, "message": fed
        // by SIDECAR)
        Object[][] sessions = {
            {"s-five", new int[] {0, 1, 2, 3, 4}, null, 0, null, ""},
            {"s-four", new int[] {0, 1, 2, 3}, null, 0, null, ""},
            {"s-again-4", new int[] {0, 0, 0, 0}, null, 0, null, ""},
            {"s-again-3", new int[] {0, 0, 0}, null, 0, null, ""},
            {"s-qn0", new int[] {}, queue + "0#|name", 1, null, ""},
            {"s-qn1", new int[] {}, queue + "1#|name", 2, null, ""},
            {"s-one", new int[] {0}, null, 0, null, ""},
            {"s-two", new int[] {0, -1}, null, 0, null, ""},
            {"s-five-store", new int[] {0, 1, 2, 3, 4}, null, 0, null,
                    "store"},
            {"s-five-message", new int[] {0, 1, 2, 3, 4}, null, 0, null,
                    "message"},
            {"s-told-5", new int[] {0}, null, 0, "5", ""},
            {"s-told-5-store", new int[] {0}, null, 0, "5", "store"},
            {"s-told-7", new int[] {0}, null, 0, "7", ""},
            {"s-task-store-1", new int[] {0}, null, 0, null, "", 1},
            {"s-task-store-2", new int[] {0}, null, 0, null, "", 2},
        };
        for (Object[] row : sessions) {
            Session session = new Session(iteration, (String) row[0]);
            session.activations(false, TARGET, WRITER);
            session.constant("e.stored", "1");
            session.write(STORED, ALL_KEYS, 5L, "e.stored");
            for (int k : (int[]) row[1]) {
                Endpoint producer = k < 0 ? SENT : Endpoint.of(PRODUCER,
                        "XCH.resp.block-key-id", ExecutionIndex.of(
                                Collections.singletonList(Frame.of(
                                        "PBHelper#convert#9", k))), 0);
                session.attach(DELIVERED, "M_HOFF_" + k, "1", producer);
            }
            for (int read = 0; read < (Integer) row[3]; read++) {
                session.attach(at(WRITER, (String) row[2], "ZkRead#3"),
                        "M_CONTENT_" + read, "x", null);
            }
            if (row[4] != null) {
                // PRODUCER, which read the store and writes nothing the
                // guard reads, tells the task a value its guard reads.
                session.activation(PRODUCER, false);
                session.attach(at(PRODUCER, props, "ZkRead#3"), "M_FED",
                        "3", null);
                session.attach(told, "M_TOLD", (String) row[4], ROTATED);
            }
            // The task's own reads of the store, from one export or two.
            for (int read = 0; row.length > 6 && read < (Integer) row[6];
                 read++) {
                session.attach(at(TARGET, props, "ZkRead#7"),
                        "M_PROPS_" + read, "x", Endpoint.of(PRODUCER,
                                props, ExecutionIndex.of(
                                        Collections.singletonList(Frame.of(
                                                "ZkWrite#2", read))), 0));
            }
            if (!"".equals(row[5])) {
                // READER, writing nothing the guard reads: it read the
                // store, or SIDECAR's message fed it.
                session.activation(READER, false);
                if ("store".equals(row[5])) {
                    session.attach(at(READER, props, "ZkRead#3"),
                            "M_TOKEN", "9", null);
                } else {
                    session.attach(RECEIVED, "M_TOKEN", "9", SENT);
                }
            }
            session.flush();
        }
        Corpus corpus = Corpus.read(iteration, null);
        List<OccurrenceAddress> factor = Arrays.asList(WRITER, PRODUCER,
                READER);
        Set<String> guard = Collections.singleton(
                SmtLowering.locationKey(ALL_KEYS));
        List<String> stated = Collections.singletonList("(> M_TOLD 3)");
        Object[][] rows = {
            {"s-five", "s-four", false,
                    "five distinct exports against four to the writer"},
            {"s-again-4", "s-again-3", true,
                    "one export read four times against three"},
            {"s-again-4", "s-one", true, "read again against read once"},
            {"s-qn0", "s-qn1", true,
                    "the first queue item at another counter, read again"},
            {"s-one", "s-two", false, "two producers of one site"},
            {"s-five", "s-five-store", true,
                    "a member in one world only that read the store and "
                            + "writes nothing the guard reads"},
            {"s-five", "s-five-message", false,
                    "a member in one world only that a message fed"},
            {"s-told-5", "s-told-5-store", true,
                    "the store reader beside a value the guard states"},
            {"s-told-5", "s-told-7", false,
                    "a store reader writing nothing the guard reads, "
                            + "telling the task 5 against 7 where the "
                            + "guard reads"},
            {"s-task-store-1", "s-task-store-2", true,
                    "the task's own store read of one version against two, "
                            + "the guard stating neither"},
            {"s-one", "s-task-store-1", true,
                    "the task's own store read the guard does not state"},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[3], row[2], corpus.inputShape(
                    (String) row[0], TARGET, factor, guard, stated).equals(
                    corpus.inputShape((String) row[1], TARGET, factor,
                            guard, stated)));
        }
    }

    /**
     * A HANDOFF IS NAMED BY A DIGEST ({@code Corpus#tokenName}): its name
     * holds its producer's arms and their conditions, which name the
     * handoffs they read, so a chain whose every level reads the one before
     * twice would be text 3^n long held whole (solr-adhoc-40 SL1: one name
     * outgrew an 8 GB heap).  Rows: a constant at the chain's head 24 levels
     * up re-keys, the same constant again does not.
     */
    @Test(timeout = 60000)
    public void aHandoffChainIsNamedByDigests() throws Exception {
        Path iteration = tree.newFolder("handoff-chain").toPath();
        int depth = 24;
        OccurrenceAddress[] chain = new OccurrenceAddress[depth + 1];
        for (int at = 0; at <= depth; at++) {
            chain[at] = occurrence("hdfs-case/dn" + (at % 3), "REGION.chain",
                    CausalContext.of(Role.of("CHAIN"), "", at + 1),
                    "o.a.h.Chain#run#" + (at + 1));
        }
        Endpoint told = at(TARGET, "XCH.chain", "Chain#told");
        for (String name : new String[] {"s-one", "s-one-again", "s-two"}) {
            Session session = new Session(iteration, name);
            session.activation(TARGET, false);
            session.constant("e.head", name.equals("s-two") ? "2" : "1");
            session.activation(chain[0], false);
            session.export(at(chain[0], "XCH.chain", "Chain#0"), "e.head",
                    1L, "1");
            for (int at = 1; at <= depth; at++) {
                // Each level reads the one before, decides on it twice and
                // passes it on.
                session.activation(chain[at], false);
                String symbol = "M_CHAIN_" + at;
                session.attach(at(chain[at], "XCH.chain", "Chain#in"),
                        symbol, "1", at(chain[at - 1], "XCH.chain",
                                "Chain#" + (at - 1)));
                session.decision(chain[at], "Chain#u1", 1, true,
                        "(> " + symbol + " 0)");
                session.decision(chain[at], "Chain#u2", 1, true,
                        "(< " + symbol + " 9)");
                session.symbolic("e.pass" + at, symbol);
                session.export(at(chain[at], "XCH.chain", "Chain#" + at),
                        "e.pass" + at, 1L + at, "1");
            }
            session.attach(told, "M_TOLD", "1", at(chain[depth],
                    "XCH.chain", "Chain#" + depth));
            session.flush();
        }
        Corpus corpus = Corpus.read(iteration, null);
        List<String> stated = Collections.singletonList("(> M_TOLD 3)");
        List<OccurrenceAddress> none = Collections.emptyList();
        Set<String> nowhere = Collections.emptySet();
        String one = corpus.inputShape("s-one", TARGET, none, nowhere, stated);
        assertEquals("the same chain again", one, corpus.inputShape(
                "s-one-again", TARGET, none, nowhere, stated));
        assertFalse("another constant at the head, 24 levels up",
                one.equals(corpus.inputShape("s-two", TARGET, none, nowhere,
                        stated)));
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
     * One admitted replay of this corpus: the target's own rows as the seed
     * recorded them, and one handoff fewer at the factor member.
     *
     * <p>The rotation it was held to delivered nothing, so {@code addKeys}
     * stored what it already had: the STRUCTURE of what the member received
     * differs from the recording's and {@link Corpus#inputShape} says so,
     * while the target's own decisions are letter for letter the seed's --
     * which is hdfs-11741's shape, and the reason the world is part of the
     * key at all.</p>
     */
    private void heldTo(Path iteration, String sessionId,
                        OccurrenceAddress focused) throws IOException {
        Session session = new Session(iteration, sessionId);
        session.activation(focused, true);
        session.activations(false, TARGET, WRITER);
        session.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        session.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        session.constant("e.kept", "119992");
        session.decision(TARGET, "Guard#u8", 1, false, "EXPR.0000000000000001");
        session.write(STORED, ALL_KEYS, 5L, "e.kept");
        session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        session.answered(ObligationResult.of("OBL." + sessionId,
                Verdict.ADMITTED, sessionId, "the focused prefix reproduced"));
        session.flush();
    }

    /**
     * Whether a decision is a fault decision, and what a term rests on, are
     * asked of the expressions' shared nodes, never of their lowered text:
     * a chain each of whose 64 nodes names the one below twice is 64 nodes,
     * and its text 2^64 leaves (hdfs-17960 rr1's wave planner).
     */
    @Test
    public void aTermReachesWhatItsSharedExpressionNamesUnrendered()
            throws Exception {
        Path iteration = tree.newFolder("dag").toPath();
        Session session = new Session(iteration, "s-dag");
        session.activation(TARGET, false);
        session.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        JsonObject marked = leaf("M_MARKER", "I");
        JsonObject unmarked = leaf("M_OTHER", "I");
        for (int depth = 0; depth < 64; depth++) {
            marked = binary("+", marked, marked);
            unmarked = binary("+", unmarked, unmarked);
        }
        session.expression("EXPR.00000000000000d1",
                binary("==", marked, literal(0)));
        session.expression("EXPR.00000000000000d2",
                binary("==", unmarked, literal(0)));
        session.decision(TARGET, "Guard#u8", 1, false, "EXPR.00000000000000d1");
        session.decision(TARGET, "Guard#u9", 1, false, "EXPR.00000000000000d2");
        session.flush();
        Corpus corpus = Corpus.read(iteration, null);
        assertEquals(Collections.singleton("Guard#u8"),
                corpus.faultSites(TARGET));
        assertEquals(Collections.singleton("M_OTHER"),
                corpus.termSymbols("s-dag", "(not EXPR.00000000000000d2)"));
    }

    // ---- (2) a handoff is answered only with what a producer delivers --

    @Test
    public void handoffIsAnsweredWithAValueSomeProducerDelivers()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("family").toPath();
        OccurrenceAddress target = TARGET;
        OccurrenceAddress producer = PRODUCER;
        Endpoint exported = at(producer, "XCH.resp.block-key-id",
                "PBHelper#convert#9");
        Endpoint attached = at(target, "XCH.resp.block-key-id",
                "PBHelper#convert#9");

        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, target, producer);
        // The recording mints the producer's own root: every instrumented
        // region of the seed runs symbolically ({@code Arms#attested}), so
        // the rotation that put a serial on the wire minted it.  That row
        // is also where any replay would PLANT a value of it -- the mint's
        // occurrence, which the focused set of an obligation assigning this
        // root has to hold.  Declared, because a serial a rotation moved is
        // the case's whole hypothesis (11741 declares SERIAL_NO +0..+3):
        // undeclared it is pinned to this reading, and then no arm a
        // rotation delivered under another reading is available at all.
        seed.integral(producer, "CASE.SERIAL", "M_SERIAL", "119992", null,
                null);
        seed.constant("e.119992", "119992");
        seed.export(exported, "e.119992", 11L, "119992");
        seed.attach(attached, "M_HOFF_KEY", "119992", exported);
        seed.decision(target, "Lookup#u8", 1, false, "(= M_HOFF_KEY 119995)");
        seed.flush();
        // A second recording of the same interaction delivered another id.
        // Its own prefix is cut at the export: the decision it took AFTER
        // putting the value on the wire is no condition of that delivery, and
        // asserting it would make the arm unsatisfiable.
        Session rotated = new Session(iteration, "s-rot");
        rotated.activation(producer, true);
        rotated.answered(ObligationResult.of("OBL.s-rot", Verdict.ADMITTED,
                "s-rot", "the focused prefix reproduced"));
        // The consumer received it in that replay too, running concretely:
        // an arm comes only from a run whose OWN pairing named this
        // consumer (IDENTITY §4), which is what makes a family the
        // deliveries of one interaction rather than of one port.
        rotated.activation(target, false);
        rotated.root(producer, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "119995", null, null, false);
        rotated.decision(producer, "Rotate#u3", 1, true, "(> M_SERIAL 0)");
        rotated.constant("e.119995", "119995");
        rotated.export(exported, "e.119995", 12L, "119995");
        rotated.attach(attached, "M_HOFF_KEY", "119995", exported);
        rotated.decision(producer, "After#u9", 1, true, "(> M_SERIAL 1000000)");
        rotated.flush();
        scopeMap(iteration,
                targetSite("REGION.target", "Throw#u30", "Lookup#u8"),
                scopeSite(StaticScopeMap.EXPORT_SITE, "REGION.rotate",
                        "PBHelper#convert#9", "PBHelper#convert", "", "",
                        "XCH.resp.block-key-id", "Rotate#u3"));

        Path out = tree.newFolder("family-out").toPath();
        Path results = out.resolve("obligation_results.jsonl");
        Path wave0 = out.resolve("obligations-0000");
        // The case's own declaration, in the spelling a case writes: three
        // rotations' worth of serial, relative to what the recording read.
        Path serialDomain = iteration.resolve("root-domains.jsonl");
        Files.write(serialDomain, Collections.singletonList(
                "{\"sourceId\":\"CASE.SERIAL\","
                        + "\"declaredDomainMin\":\"+0\","
                        + "\"declaredDomainMax\":\"+3\"}"),
                java.nio.charset.StandardCharsets.UTF_8);
        plan(iteration, TARGET_SELECTOR, serialDomain, results, wave0, 0);
        List<Obligation> proposed = obligations(wave0);
        // The producer ran symbolically in the rotated session, so it is a
        // task of its own -- the NN rotation is explored as a worker, not as
        // the consumer's companion.  What it may flip is the guard set of the
        // EXPORT it is in the closure for: the rotation decision that decides
        // the delivery, and not the decision it took AFTER putting the value
        // on the wire, which no delivery can depend on (PIPELINE §7.2).
        List<String> sites = new ArrayList<String>();
        for (Obligation obligation : proposed) sites.add(obligation.siteId());
        assertTrue("the export's own guard is an obligation: " + sites,
                sites.contains("Rotate#u3"));
        assertFalse("a decision after the export is no guard of it: " + sites,
                sites.contains("After#u9"));
        Obligation consumerFlip = named(proposed, "Lookup#u8");
        assertNotNull("the consumer's own flip is proposed", consumerFlip);
        Worker worker = solve(iteration, serialDomain, wave0, consumerFlip,
                out, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, worker.verdict);
        assertTrue("the control is producible",
                worker.obligation.unproducible().isEmpty());
        assertEquals("119995", worker.obligation.answers().get(attached.id()));
        // And the value that answer rests on is planted where the RECORDING
        // mints it, which is the NameNode's rotation and not the consumer
        // occurrence this obligation flips: the focused set holds both, so
        // one replay of the whole workload runs the rotation that mints the
        // serial and the consumer whose guard is flipped.
        JsonObject answered = RowCodec.readJsonl(worker.directory
                .resolve(ObligationDir.FOCUSED_TASK)).get(0);
        assertEquals("119995",
                worker.obligation.rootAssignments().get("CASE.SERIAL"));
        assertEquals(producer.render(), answered.getAsJsonObject("rootMints")
                .get("CASE.SERIAL").getAsString());
        assertEquals(target.render(), answered.get("focused").getAsString());

        // The negative control: a flip that needs a value no producer of this
        // corpus delivers is UNSAT, not answered out of the family.
        Path other = tree.newFolder("family-unsat").toPath();
        Session lone = new Session(other, "s-seed");
        lone.activations(false, target, producer);
        lone.constant("e.119992", "119992");
        lone.export(exported, "e.119992", 11L, "119992");
        lone.attach(attached, "M_HOFF_KEY", "119992", exported);
        lone.decision(target, "Lookup#u8", 1, false, "(= M_HOFF_KEY 7)");
        lone.flush();
        scopeMap(other, targetSite("REGION.target", "Throw#u30",
                "Lookup#u8"));
        Path unsatOut = tree.newFolder("family-unsat-out").toPath();
        Path unsatWave = unsatOut.resolve("obligations-0000");
        plan(other, TARGET_SELECTOR, null,
                unsatOut.resolve("results.jsonl"), unsatWave, 0);
        Worker refused = solve(other, unsatWave,
                named(obligations(unsatWave), "Lookup#u8"), unsatOut, "w0");
        assertEquals(Verdict.UNSAT, refused.verdict);
    }

    // ---- (3) a handoff no producer delivers is named ------------------

    @Test
    public void controlWithNoArmIsUnproducible() throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("unproducible").toPath();
        OccurrenceAddress target = TARGET;
        Endpoint attached = at(target, "XCH.req.key-id",
                "DataXceiver#readBlock#22");
        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, false);
        // Unpaired: the value arrived from outside this corpus.
        seed.attach(attached, "M_HOFF_REQ", "119992", null);
        seed.decision(target, "Lookup#u8", 1, false, "(= M_HOFF_REQ 5)");
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Lookup#u8"));

        Path out = tree.newFolder("unproducible-out").toPath();
        Path wave0 = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null, out.resolve("results.jsonl"), wave0, 0);
        List<Obligation> proposed = obligations(wave0);
        assertEquals(1, proposed.size());
        Worker worker = solve(iteration, wave0, proposed.get(0), out, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, worker.verdict);
        assertEquals(Collections.singletonList(attached.id()),
                worker.obligation.unproducible());
        assertEquals("5", worker.obligation.answers().get(attached.id()));
        assertTrue("the obligation announces the control it invented",
                anyGap(worker.directory, gap -> gap.kind()
                        == GapKind.UNPRODUCIBLE_ANSWER
                        && gap.subject().contains("XCH.req.key-id")));
    }

    // ---- an open decider arm: asked at one decision, named until closed --

    /**
     * A reached anchor whose phi left out an open decider arm
     * (TargetRow.OpenArm, causynth.BooleanReturns) asks the ONE decision
     * the row names -- the call of the helper that fed the guard, never
     * every call of its method -- and the round's manifest names the arm
     * until a flip closes it: PENDING while asked, UNANSWERED once its only
     * replay never reached the decision, UNSAT once no world takes it --
     * under whatever obligation id the answer landed, since a flip is judged
     * by itself, not by the id the corpus now computes (hdfs-adhoc-39 WD2:
     * the UNSAT landed under another id); an arm with no decision to ask is
     * NOT_FLIPPABLE.
     */
    @Test
    public void anOpenDeciderArmIsAskedAtTheCallThatFedTheGuard()
            throws Exception {
        String helper = "State#u2";
        Object[][] rows = {
            // the arm's asked decision, the answer, the arm's state, the id
            // the answer landed under (null: the one proposed), how many of
            // its replays did not run their world (WORLD_UNREFUTED)
            {helper, null, "PENDING", null, 0},
            {helper, Verdict.NOT_ADMITTED, "UNANSWERED", null, 0},
            {helper, Verdict.UNSAT, "UNSAT", null, 0},
            {helper, Verdict.UNSAT, "UNSAT", "drifted-id", 0},
            // its own world refuted, the arm its id names answered UNSAT by
            // a sibling path's flip
            {helper, Verdict.UNSAT, "UNSAT", "shared", 0},
            // never asked itself, its id answered NOT_ADMITTED by a sibling
            // path's flip whose replay ran its world (an arm keyed by its
            // effect at the task: a reduced world's answer stands for it) --
            // still unanswered; one whose replay did not run its world
            // stands for no other world: the arm is asked in its own
            {helper, Verdict.NOT_ADMITTED, "UNANSWERED", "shared-only", 0},
            {helper, Verdict.NOT_ADMITTED, "PENDING", "shared-only-unrun",
                0},
            {helper, Verdict.NOT_ADMITTED, "PENDING", "unrun-once", 1},
            {helper, Verdict.NOT_ADMITTED, "UNANSWERED", "unrun-twice", 2},
            {"", null, "NOT_FLIPPABLE", null, 0}};
        for (Object[] row : rows) {
            String asked = (String) row[0];
            Path iteration = tree.newFolder("open-arm-" + row[2]
                    + (row[3] == null ? "" : "-" + row[3])).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            seed.integral(TARGET, "CASE.SERIAL", "M_SERIAL", "7", null, null);
            // An earlier call of the helper, and the one that fed the guard.
            seed.decision(TARGET, helper, 1, true, "(> M_SERIAL 3)");
            seed.decision(TARGET, helper, 2, false, "(> M_SERIAL 10)");
            seed.targets.add(TargetRow.of("s-seed", 99L, TARGET, "Throw#u30",
                    "false", false, true, TargetRow.OpenArm.of(helper, 2,
                            true, asked, 2)));
            seed.flush();
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Guard#u9"));
            Path out = tree.newFolder("open-arm-out-" + row[2]
                    + (row[3] == null ? "" : "-" + row[3])).toPath();
            Path results = out.resolve("results.jsonl");
            Files.createDirectories(out);
            Files.write(results, new byte[0]);
            JsonObject first = plan(iteration, TARGET_SELECTOR, null, results,
                    out.resolve("obligations-0000"), 0);
            List<Obligation> proposed = obligations(
                    out.resolve("obligations-0000"));
            if (asked.isEmpty()) {
                assertTrue("nothing to ask: " + proposed, proposed.isEmpty());
            } else {
                assertEquals("one flip, of the call that fed the guard: "
                        + proposed, 1, proposed.size());
                assertEquals(2, proposed.get(0).ordinal());
            }
            JsonObject named = first;
            int unrun = (Integer) row[4];
            if (String.valueOf(row[3]).startsWith("shared-only")) {
                Obligation flip = proposed.get(0);
                ObligationResult sibling = ObligationResult.of(
                        flip.obligationId(), Verdict.NOT_ADMITTED, "",
                        "shared-only".equals(row[3])
                                ? ObligationResult.WORLD_RAN + ": sibling"
                                : "sibling; its world did not run: (a)");
                record(results, sibling);
                Path worker = iteration.resolve("obligations-0000")
                        .resolve(flip.obligationId());
                Files.createDirectories(worker);
                Files.write(worker.resolve(ObligationDir.QUESTION),
                        "siblingflip:asked".getBytes(StandardCharsets.UTF_8));
                record(worker.resolve(ObligationDir.RESULT), sibling);
                named = plan(iteration, TARGET_SELECTOR, null, results,
                        out.resolve("obligations-0001"), 1);
            } else if ("shared".equals(row[3])) {
                Obligation flip = proposed.get(0);
                ObligationResult own = ObligationResult.of(
                        flip.obligationId(), Verdict.NOT_ADMITTED, "s-flip",
                        "WORLD_REFUTED: never entered",
                        edu.uva.liftlab.graphchecker.contract.WorldRefutation
                                .of(Arrays.asList("(a)", "(b)", "(c)", "(d)"),
                                        "", "", ""));
                record(results, own);
                land(iteration, "obligations-0000", flip, own);
                ObligationResult sibling = ObligationResult.of(
                        flip.obligationId(), Verdict.UNSAT, "", "sibling");
                record(results, sibling);
                Path worker = iteration.resolve("obligations-0001")
                        .resolve(flip.obligationId());
                Files.createDirectories(worker);
                Files.write(worker.resolve(ObligationDir.QUESTION),
                        "siblingflip:asked".getBytes(StandardCharsets.UTF_8));
                record(worker.resolve(ObligationDir.RESULT), sibling);
                named = plan(iteration, TARGET_SELECTOR, null, results,
                        out.resolve("obligations-0001"), 1);
            } else if (row[1] != null) {
                Obligation flip = proposed.get(0);
                for (int run = 0; run < Math.max(1, unrun); run++) {
                    ObligationResult answer = ObligationResult.of(
                            row[3] == null || unrun > 0 ? flip.obligationId()
                                    : (String) row[3], (Verdict) row[1],
                            "s-flip" + run, unrun == 0
                                    ? (row[1] == Verdict.NOT_ADMITTED
                                    ? ObligationResult.WORLD_RAN
                                    + ": never reached" : "answered")
                                    : ObligationResult.WORLD_UNREFUTED
                                    + ": never reached; its world is not"
                                    + " refuted: (a) no root mint row");
                    record(results, answer);
                    land(iteration, "obligations-000" + run, flip, answer);
                }
                named = plan(iteration, TARGET_SELECTOR, null, results,
                        out.resolve("obligations-0001"), 1);
                if (unrun > 0) {
                    assertEquals("asked once more, never a third time",
                            unrun == 1 ? 1 : 0, obligations(
                                    out.resolve("obligations-0001")).size());
                }
            }
            JsonArray arms = named.getAsJsonArray("openArms");
            assertEquals("the arm is named: " + arms, 1, arms.size());
            JsonObject arm = arms.get(0).getAsJsonObject();
            assertEquals(helper, arm.get("siteId").getAsString());
            assertTrue(arm.get("outcome").getAsBoolean());
            assertEquals("its state: " + arm, row[2],
                    arm.get("state").getAsString());
            assertEquals("its unrun worlds named: " + arm, unrun,
                    arm.getAsJsonArray("unrunWorlds").size());
        }
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

    // ---- (4) a root with no domain is pinned, here as in the composer --

    @Test
    public void rootWithoutADomainCannotBeMoved() throws Exception {
        Assume.assumeTrue(z3Available());
        OccurrenceAddress target = TARGET;
        Path pinned = tree.newFolder("pinned").toPath();
        Session seed = new Session(pinned, "s-seed");
        seed.activation(target, false);
        seed.root(target, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL, "7",
                null, null, false);
        seed.decision(target, "Arrival#u8", 1, false, "(> M_SERIAL 10)");
        seed.flush();
        scopeMap(pinned, targetSite("REGION.target", "Throw#u30",
                "Arrival#u8"));
        Path pinnedOut = tree.newFolder("pinned-out").toPath();
        Path pinnedWave = pinnedOut.resolve("obligations-0000");
        plan(pinned, TARGET_SELECTOR, null,
                pinnedOut.resolve("results.jsonl"), pinnedWave, 0);
        Worker refused = solve(pinned, pinnedWave,
                obligations(pinnedWave).get(0), pinnedOut, "w0");
        assertEquals(Verdict.UNSAT, refused.verdict);

        // Declared, the same flip is satisfiable inside the declared domain,
        // whose bounds the case states RELATIVE to the recording.
        Path declared = tree.newFolder("declared").toPath();
        Session open = new Session(declared, "s-seed");
        open.activation(target, false);
        open.integral(target, "CASE.SERIAL", "M_SERIAL", "7", null, null);
        open.decision(target, "Arrival#u8", 1, false, "(> M_SERIAL 10)");
        open.flush();
        scopeMap(declared, targetSite("REGION.target", "Throw#u30",
                "Arrival#u8"));
        // The case's own file, in the one spelling a case writes it in:
        // sourceId and two bounds RELATIVE to the recording.
        Path domains = declared.resolve("root-domains.jsonl");
        Files.write(domains, Collections.singletonList(
                "{\"sourceId\":\"CASE.SERIAL\","
                        + "\"declaredDomainMin\":\"+4\","
                        + "\"declaredDomainMax\":\"+5\"}"),
                java.nio.charset.StandardCharsets.UTF_8);
        Path declaredOut = tree.newFolder("declared-out").toPath();
        Path declaredWave = declaredOut.resolve("obligations-0000");
        plan(declared, TARGET_SELECTOR, domains,
                declaredOut.resolve("results.jsonl"), declaredWave, 0);
        // The worker is handed the same declaration the wave was planned
        // under, exactly as the campaign hands it.
        Worker moved = solve(declared, domains, declaredWave,
                obligations(declaredWave).get(0), declaredOut, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, moved.verdict);
        String value = moved.obligation.rootAssignments().get("CASE.SERIAL");
        assertTrue("free inside [11, 12], and nowhere else: " + value,
                "11".equals(value) || "12".equals(value));

        // A root the flip depends on is not always minted where the flip
        // is.  11741's SERIAL_NO is the NameNode's, read by the balancer,
        // so the FOCUSED SET holds the MINT's occurrence too: an assignment
        // is planted where the run mints it and nowhere else, and a mint
        // running unfocused reads the recording's value under an obligation
        // asking for another one.
        Path elsewhere = tree.newFolder("minted-elsewhere").toPath();
        Session across = new Session(elsewhere, "s-seed");
        across.activations(false, target, PRODUCER);
        across.integral(PRODUCER, "CASE.SERIAL", "M_SERIAL", "7", null, null);
        across.decision(target, "Arrival#u8", 1, false, "(> M_SERIAL 10)");
        across.flush();
        scopeMap(elsewhere, targetSite("REGION.target", "Throw#u30",
                "Arrival#u8"));
        Path elsewhereOut = tree.newFolder("elsewhere-out").toPath();
        Path elsewhereWave = elsewhereOut.resolve("obligations-0000");
        Path elsewhereDomains = elsewhere.resolve("root-domains.jsonl");
        Files.copy(domains, elsewhereDomains);
        plan(elsewhere, TARGET_SELECTOR, elsewhereDomains,
                elsewhereOut.resolve("results.jsonl"), elsewhereWave, 0);
        Worker planted = solve(elsewhere, elsewhereDomains, elsewhereWave,
                named(obligations(elsewhereWave), "Arrival#u8"),
                elsewhereOut, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, planted.verdict);
        JsonObject plantedRow = RowCodec.readJsonl(planted.directory
                .resolve(ObligationDir.FOCUSED_TASK)).get(0);
        assertEquals("the focus row states where the assignment is planted",
                PRODUCER.render(), plantedRow.getAsJsonObject("rootMints")
                        .get("CASE.SERIAL").getAsString());
        assertEquals("which is not the occurrence the flip is about",
                TARGET.render(), plantedRow.get("focused").getAsString());
        assertFalse("nor a member of its state-connected factor",
                plantedRow.getAsJsonArray("factor").toString()
                        .contains(PRODUCER.render()));

        // And a root the RECORDING minted nowhere names no occurrence any
        // replay could be focused on, so the obligation is refused by name
        // rather than run on the recording's own value.
        Path unminted = tree.newFolder("unminted").toPath();
        Session recording = new Session(unminted, "s-seed");
        recording.activation(target, false);
        recording.flush();
        Session replayed = new Session(unminted, "s-flip");
        replayed.activation(target, true);
        replayed.integral(target, "CASE.SERIAL", "M_SERIAL", "7", null, null);
        replayed.decision(target, "Arrival#u8", 1, false, "(> M_SERIAL 10)");
        replayed.answered(ObligationResult.of("OBL.s-flip", Verdict.ADMITTED,
                "s-flip", "the focused prefix reproduced"));
        replayed.flush();
        scopeMap(unminted, targetSite("REGION.target", "Throw#u30",
                "Arrival#u8"));
        Path unmintedOut = tree.newFolder("unminted-out").toPath();
        Path unmintedWave = unmintedOut.resolve("obligations-0000");
        Path unmintedDomains = unminted.resolve("root-domains.jsonl");
        Files.copy(domains, unmintedDomains);
        plan(unminted, TARGET_SELECTOR, unmintedDomains,
                unmintedOut.resolve("results.jsonl"), unmintedWave, 0);
        Obligation orphan = named(obligations(unmintedWave), "Arrival#u8");
        assertNotNull("the flip is proposed before anyone knows the model",
                orphan);
        Worker unmintable = solve(unminted, unmintedDomains, unmintedWave,
                orphan, unmintedOut, "w0");
        assertEquals(Verdict.NOT_ADMITTED, unmintable.verdict);
        assertTrue("and no focus row is written for it",
                RowCodec.readJsonl(unmintable.directory
                        .resolve(ObligationDir.FOCUSED_TASK)).isEmpty());
        assertTrue("the obligation is named, and so is the root",
                anyGap(unmintable.directory, gap -> gap.kind()
                        == GapKind.ASSIGNMENT_UNMINTABLE
                        && gap.cls() == GapClass.DIAGNOSTIC
                        && gap.subject().equals(orphan.obligationId())
                        && gap.detail().equals("CASE.SERIAL")));

        // A clock has no domain either, and is not pinned for it: it is free
        // with a floor.  What the focus row states for one is the SKEW the
        // replay adds to the instant it reads for itself -- never the
        // recording's instant, which no other execution ever reads -- so it
        // is written apart from the values a mint writes.
        Path ticking = tree.newFolder("clock").toPath();
        Session ticks = new Session(ticking, "s-seed");
        ticks.activation(target, false);
        ticks.clock(target, "CASE.NOW", "M_NOW", "700");
        ticks.decision(target, "Arrival#u8", 1, false, "(> M_NOW 1000)");
        ticks.flush();
        scopeMap(ticking, targetSite("REGION.target", "Throw#u30",
                "Arrival#u8"));
        Path clockOut = tree.newFolder("clock-out").toPath();
        Path clockWave = clockOut.resolve("obligations-0000");
        plan(ticking, TARGET_SELECTOR, null,
                clockOut.resolve("results.jsonl"), clockWave, 0);
        Worker ticked = solve(ticking, clockWave,
                obligations(clockWave).get(0), clockOut, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, ticked.verdict);
        assertTrue("a clock is not a value written at a mint",
                ticked.obligation.rootAssignments().isEmpty());
        JsonObject focus = RowCodec.readJsonl(ticked.directory
                .resolve(ObligationDir.FOCUSED_TASK)).get(0);
        String skew = focus.getAsJsonObject("clockDeltas")
                .get("CASE.NOW").getAsString();
        // A CLOCK IS A MILLISECOND COUNT IN A JAVA long.  The query's clock
        // variable carries the ceiling beside the floor, so the instant the
        // model hands back is one an execution could read and the difference
        // is a skew the replay can APPLY: FocusedReplay.clockSkew parses it
        // with Long.valueOf, and hdfs-11741 campaign #2 handed it
        // 18446742283726387588 -- a negative difference printed unsigned,
        // because the query stated only (>= v 0) and z3 answered past 2^63.
        long applied = Long.parseLong(skew);
        assertEquals("the focus row states the skew as a Java long, which is"
                        + " the only thing a replay can apply", skew,
                Long.toString(applied));
        assertTrue("and the instant it asks for is a Java long too: " + skew,
                applied <= Long.MAX_VALUE - 700L);
        assertTrue("the skew carries a reading of 700 past 1000: " + skew,
                applied > 300L);
        String tickedQuery = queryText(ticked.directory);
        assertTrue("because the query ceilings the clock a window above the"
                        + " reading, so no model can overflow the long the"
                        + " workload adds to it: " + tickedQuery,
                tickedQuery.contains(" 2592000700))"));
        assertFalse("and the Java long ceiling is not the domain any more",
                tickedQuery.contains(" 9223372036854775807))"));

        // AND A PINNED ROOT BESIDE THE CLOCK IS STILL A CLOCK-DRIVEN FLIP.
        // The query reaches a root with no domain, so the query pins it and
        // the model hands it back where the recording minted it -- which is
        // what a pinned root DOES, and says nothing about whether this world
        // is one the seed already ran.  A moved clock says that, and says it
        // first: #recordedValuation is asked the skews too, and a non-zero
        // one answers before the root comparison.  nn0's second-rotation
        // removeExpiredKeys#u15 flips of the 11741 campaign of 2026-09-20
        // were refused as "the model is the recording's own valuation
        // (HDFS.BLOCK_KEY.SERIAL_NO=182907) and answers no handoff" while
        // the same model moved two CLOCK variables.
        Path pinnedClock = tree.newFolder("clock-pinned").toPath();
        Session both = new Session(pinnedClock, "s-seed");
        both.activation(target, false);
        both.clock(target, "CASE.NOW", "M_NOW", "700");
        both.integral(target, "CASE.SERIAL", "M_SERIAL", "182907", null, null);
        both.decision(target, "Arrival#u8", 1, false,
                "(and (> M_NOW 1000) (= M_SERIAL 182907))");
        both.flush();
        scopeMap(pinnedClock, targetSite("REGION.target", "Throw#u30",
                "Arrival#u8"));
        Path bothOut = tree.newFolder("clock-pinned-out").toPath();
        Path bothWave = bothOut.resolve("obligations-0000");
        plan(pinnedClock, TARGET_SELECTOR, null,
                bothOut.resolve("results.jsonl"), bothWave, 0);
        Worker driven = solve(pinnedClock, bothWave,
                obligations(bothWave).get(0), bothOut, "w0");
        assertEquals("a clock skew is a counterfactual of its own",
                Verdict.SAT_MODEL_READY, driven.verdict);
        assertEquals("and the pinned root is where it was minted",
                "182907",
                driven.obligation.rootAssignments().get("CASE.SERIAL"));
        JsonObject drivenFocus = RowCodec.readJsonl(driven.directory
                .resolve(ObligationDir.FOCUSED_TASK)).get(0);
        JsonObject drivenSkews = drivenFocus.getAsJsonObject("clockDeltas");
        assertNotNull("the obligation carries the skew it is owed",
                drivenSkews);
        assertFalse("which is what makes it a world the seed did not run: "
                        + drivenSkews, drivenSkews.entrySet().isEmpty());
        assertTrue("past the instant the recording read: " + drivenSkews,
                Long.parseLong(drivenSkews.get("CASE.NOW").getAsString())
                        > 300L);
    }

    // ---- (5) the closure holds the writer of every version read -------

    /**
     * A read of a reference rests on the container its store delivered: the
     * closure demands the writer of each state of it the read could have
     * seen through that store ({@code Corpus#referentStates}, the rule
     * COMPOSE answers a query by) -- here a mutation after the store, live
     * at the read, by an occurrence no row of the anchor joins -- and a
     * store that states no container demands none.
     */
    @Test
    public void aReferenceReadDemandsTheStateItsStoreDelivered()
            throws Exception {
        OccurrenceAddress builder = occurrence("hdfs-case/dn0",
                "REGION.build", CausalContext.of(Role.of("BUILDER"), "", 1),
                "o.a.h.Builder#run#2");
        OccurrenceAddress cleaner = occurrence("hdfs-case/dn0",
                "REGION.clean", CausalContext.of(Role.of("CLEANER"), "", 1),
                "o.a.h.Cleaner#run#2");
        LocationId reference = LocationId.of(LocationKind.INSTANCE, "8",
                "16");
        LocationId map = LocationId.of(LocationKind.MAP, "20", "-3");
        for (boolean referent : new boolean[]{true, false}) {
            Path iteration = tree.newFolder("referent-" + referent).toPath();
            Session seed = new Session(iteration, "s-seed");
            for (OccurrenceAddress at : Arrays.asList(TARGET, WRITER,
                    builder, cleaner)) {
                seed.activation(at, false);
            }
            seed.symbolic("e.put", "M_PUT");
            seed.symbolic("e.map", "M_MAP");
            seed.symbolic("e.removed", "M_REMOVED");
            seed.write(at(builder, "Map#put#1:WRITE", "Builder#build#1"),
                    map, 1L, "e.put");
            seed.writes.add(WriteRow.of("s-seed", ++seed.seq, at(WRITER,
                    "Policy#update#2:WRITE", "Policy#update#2"), reference,
                    2L, "e.map", "L", referent ? WriteRow.Referent.of(map,
                            1L) : null, null));
            seed.write(at(cleaner, "Map#remove#3:WRITE", "Cleaner#clean#3"),
                    map, 3L, "e.removed");
            seed.read(at(TARGET, "Handler#get#4:READ", "Handler#get#4"),
                    reference, 2L, "M_KC", "0");
            seed.target(TARGET, "Handler#get#5", "(= M_KC 0)");
            seed.flush();

            ClosurePlanner.Plan plan = closure(Corpus.read(iteration, null),
                    TARGET, StaticScopeMap.empty());
            List<String> focused = focused(plan);
            assertTrue("the store's writer: " + focused,
                    focused.contains(WRITER.render()));
            assertEquals("the state the read saw through the store: "
                    + focused, referent, focused.contains(cleaner.render()));
        }
    }

    /**
     * A container's state read rests on the reference read that returned
     * the container, whether or not the VM states it as the relation's
     * owner: the reference's writer is in the closure (hdfs-bugs
     * slowdisk-zero: chooseVolume's filter asks {@code contains} of the list
     * getSlowDisksToExclude() returned, inside the lambda that captured it).
     */
    @Test
    public void aContainerReadRestsOnTheReadThatReturnedItsObject()
            throws Exception {
        Path iteration = tree.newFolder("holder").toPath();
        LocationId reference = LocationId.of(LocationKind.INSTANCE, "8",
                "88");
        LocationId list = LocationId.of(LocationKind.MAP, "20", "-3");
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, WRITER);
        seed.symbolic("e.list", "M_LIST");
        seed.write(at(WRITER, "Metrics#run#2:WRITE", "Metrics#run#2"),
                reference, 2L, "e.list");
        seed.read(at(TARGET, "Metrics#getList#15:READ", "Metrics#getList#15"),
                reference, 2L, "M_REF", "M_L'java/util/ArrayList'_20");
        seed.read(at(TARGET, "Chooser#test#40:READ", "Chooser#test#40"),
                list, 1L, "M_HAS", "0");
        seed.target(TARGET, "Chooser#choose#5", "(= M_HAS 0)");
        seed.flush();

        ClosurePlanner.Plan plan = closure(Corpus.read(iteration, null),
                TARGET, StaticScopeMap.empty());
        List<String> focused = focused(plan);
        assertTrue("the writer of the reference that returned the list: "
                + focused, focused.contains(WRITER.render()));
        assertTrue(plan.unpaused.isEmpty());

        // The same writer run for its doors alone is no capture of the
        // value it is demanded for: GROW is asked to run it whole (no
        // focused replay ran it, so none is re-run), and it is named.
        seed.doorsOnly.add(WRITER.render());
        seed.flush();
        Set<GapRow> doorsSaid = new LinkedHashSet<GapRow>();
        ClosurePlanner.Plan doors = saying(ClosurePlanner.plan(
                Corpus.read(iteration, null), TARGET,
                ClosurePlanner.DEFAULT_MAX_TASKS, StaticScopeMap.empty(),
                Branches.of(Corpus.read(iteration, null),
                        Collections.singletonList(TARGET),
                        new ArrayList<GapRow>()),
                Collections.singleton(WRITER.render()),
                Collections.<String>emptySet(), ClientFaults.NONE,
                SystemView.of(""), doorsSaid::add), doorsSaid);
        assertEquals(Collections.singletonMap(WRITER, ""), doors.unpaused);
        assertEquals("no focused replay ran it: the fixed point names it",
                Collections.singleton(WRITER), doors.runWhole);
        boolean named = false;
        for (GapRow gap : gapsOf(doors)) {
            named |= gap.subject().equals(WRITER.render())
                    && gap.detail().contains("doors alone");
        }
        assertTrue("the unpaused writer is named", named);
    }

    @Test
    public void closureHoldsTheWriterOfAReadVersionAndTheWireProducer()
            throws Exception {
        Path iteration = tree.newFolder("closure").toPath();
        OccurrenceAddress target = TARGET;
        OccurrenceAddress writer = WRITER;
        OccurrenceAddress producer = PRODUCER;
        // The map, owned the way the runtime writes an owner: the VM's
        // symbolic rid of the object whose state this is.
        LocationId allKeys = LocationId.of(LocationKind.MAP, "21",
                "allKeys");
        Endpoint exported = at(producer, "XCH.resp.block-key-id",
                "PBHelper#convert#9");
        Endpoint attached = at(writer, "XCH.resp.block-key-id",
                "PBHelper#convert#9");

        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, target, writer, producer);
        seed.constant("e.119992", "119992");
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.export(exported, "e.119992", 11L, "119992");
        seed.attach(attached, "M_HOFF_KEY", "119992", exported);
        seed.write(stored(writer), allKeys, 5L, "e.stored");
        seed.read(lookedUp(target), allKeys, 5L, "M_READ_KEY", "119992");
        // What makes this occurrence an anchor: the predicate whose fatal arm
        // the composition asks about, over the value it read.
        seed.anchored(target);
        seed.flush();
        Path mapFile = scopeMap(iteration,
                targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""));
        StaticScopeMap map = StaticScopeMap.read(mapFile);

        Corpus corpus = Corpus.read(iteration, null);
        ClosurePlanner.Plan plan = closure(corpus, target, map);
        List<String> focused = focused(plan);
        assertTrue("the writer of the version the anchor read is in the "
                + "closure: " + focused, focused.contains(writer.render()));
        assertTrue("and so is the producer of what that writer attached: "
                + focused, focused.contains(producer.render()));
        Task anchor = plan.tasks.get(0);
        assertEquals(target.render(), anchor.focused().render());
        assertTrue("the writer replays with it as a state-connected factor",
                anchor.factor().contains(writer));
        for (Task task : plan.tasks) {
            assertFalse("a wire producer is never another task's factor",
                    task.factor().contains(producer));
        }
        // A task is recovered from its id alone, which is how the worker that
        // executes an obligation knows what to replay.
        Task recovered = ClosurePlanner.taskOf(corpus, anchor.taskId());
        assertNotNull(recovered);
        assertEquals(anchor.focused(), recovered.focused());
        // The recorded pairing and the consumer's own causal anchor agree
        // here, so there is nothing to tell anybody.
        for (GapRow gap : gapsOf(plan)) {
            assertFalse(gap.kind() == GapKind.TOPOLOGY_DIVERGENCE);
        }

        // N1/N2: A STATIC CANDIDATE LIVES IN ONE PROCESS.  A carrier is a
        // CLASS field -- BlockTokenSecretManager.allKeys -- so its write
        // sites exist in every JVM that loaded the class; the location the
        // anchor read is a CONCRETE object in the reader's own heap
        // (IDENTITY §4), and no other JVM can have written it.  The same
        // for a port: the message this attach records was put on the wire by
        // the PAIRED producer's process.  Admitting the rest gave hdfs-11741
        // campaign #4 (2026-09-20) a wave 1 of 246 obligations, 124 of them
        // the Balancer's own removeExpiredKeys flips in worlds where nothing
        // on the Balancer's path to the target changed.
        Path perNode = tree.newFolder("closure-node-scope").toPath();
        // A second addKeys occurrence ON THE READER'S NODE that no row pairs
        // with this read: the static map is the only thing naming it.
        OccurrenceAddress sibling = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.CLIENT, "", 9),
                "o.a.h.h.s.d.BPServiceActor#offerService#41");
        // The same two regions on a node of their own: another JVM's
        // allKeys, and another JVM's wire.
        OccurrenceAddress foreignWriter = occurrence("hdfs-case/balancer",
                "REGION.addkeys",
                CausalContext.of(Role.of("BALANCER"), "", 2),
                "o.a.h.h.b.KeyManager#setKeys#7");
        OccurrenceAddress foreignExporter = occurrence("hdfs-case/balancer",
                "REGION.rotate",
                CausalContext.of(Role.of("BALANCER"), "", 3),
                "o.a.h.h.b.KeyManager#run#8");
        // A write site of the SAME carrier whose region ONLY the balancer
        // ran: on the reader's node there is no occurrence to focus, and
        // that -- not the balancer's -- is what the retained set would have
        // to grow by.
        OccurrenceAddress elsewhereOnly = occurrence("hdfs-case/balancer",
                "REGION.refresh",
                CausalContext.of(Role.of("BALANCER"), "", 4),
                "o.a.h.h.b.KeyManager#refresh#2");
        // On the reader's node too, but seen holding another key map only:
        // a store reaches only an object its occurrence holds.
        OccurrenceAddress otherMap = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.CLIENT, "", 10),
                "o.a.h.h.s.d.BPServiceActor#offerService#42");
        // A second reader of the anchor's map: state-connected to it, and
        // passing it nothing.
        OccurrenceAddress coReader = occurrence("hdfs-case/dn0",
                "REGION.target", CausalContext.of(Role.of("DATA_XCEIVER"),
                        "", 2), "o.a.h.h.s.d.DataXceiver#run#13");
        Session spread = new Session(perNode, "s-seed");
        spread.activations(false, target, writer, producer, sibling,
                foreignWriter, foreignExporter, elsewhereOnly, otherMap,
                coReader);
        spread.constant("e.other", "7");
        spread.write(stored(otherMap), LocationId.of(LocationKind.MAP, "34",
                "allKeys"), 6L, "e.other");
        spread.read(lookedUp(coReader), allKeys, 5L, "M_READ_KEY_2", "119992");
        spread.constant("e.119992", "119992");
        spread.symbolic("e.stored", "M_HOFF_KEY");
        spread.export(exported, "e.119992", 11L, "119992");
        spread.attach(attached, "M_HOFF_KEY", "119992", exported);
        spread.write(stored(writer), allKeys, 5L, "e.stored");
        spread.read(lookedUp(target), allKeys, 5L, "M_READ_KEY", "119992");
        spread.anchored(target);
        spread.flush();
        StaticScopeMap spreadMap = StaticScopeMap.read(scopeMap(perNode,
                targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", "")),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.refresh",
                        "KeyManager#u4", "KeyManager#refresh",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", "")),
                scopeSite(StaticScopeMap.EXPORT_SITE, "REGION.rotate",
                        "PBHelper#convert#9", "PBHelper#convert", "", "",
                        "XCH.resp.block-key-id")));
        ClosurePlanner.Plan scoped = closure(Corpus.read(perNode, null),
                target, spreadMap);
        Map<String, String> scopedWhy = why(scoped);
        assertEquals("a static write site of the read's carrier is a "
                        + "candidate on the READER'S node: " + scopedWhy,
                ClosurePlanner.STATIC_CANDIDATE_WRITER,
                scopedWhy.get(sibling.render()));
        assertFalse("the same site on another node's occurrence is not a "
                        + "task -- that JVM's heap holds another allKeys: "
                        + scopedWhy,
                scopedWhy.containsKey(foreignWriter.render()));
        assertFalse("nor is a write site of the carrier whose region only "
                        + "that other node ran: " + scopedWhy,
                scopedWhy.containsKey(elsewhereOnly.render()));
        assertFalse("nor an occurrence on the reader's node the session saw "
                        + "hold another map only: " + scopedWhy,
                scopedWhy.containsKey(otherMap.render()));
        assertFalse("and a co-reader of the map is no task: " + scopedWhy,
                scopedWhy.containsKey(coReader.render()));
        assertTrue("though it replays with the anchor, its factor",
                scoped.tasks.get(0).factor().contains(coReader));
        assertFalse("and neither is a static export site of the port on a "
                        + "node other than the PAIRED producer's: "
                        + scopedWhy,
                scopedWhy.containsKey(foreignExporter.render()));
        // The task bound counts static candidates only: whatever it is, the
        // occurrences the rows connect are planned, however late the walk
        // finds them (the sibling is found with the writer, the producer
        // only through the writer's attach); past it a candidate is cut
        // (REGION_PATH_CLOSURE_TRUNCATED, ClosurePlanner#Candidates).
        Corpus spreadCorpus = Corpus.read(perNode, null);
        for (int bound : new int[] {0, 1}) {
            ClosurePlanner.Plan cut = ClosurePlanner.plan(spreadCorpus,
                    target, bound, spreadMap, Branches.of(spreadCorpus,
                            Collections.singletonList(target),
                            new ArrayList<GapRow>()),
                Collections.<String>emptySet(),
                Collections.<String>emptySet(), ClientFaults.NONE,
                SystemView.of(""), gap -> { });
            List<String> kept = focused(cut);
            List<String> expected = new ArrayList<String>(Arrays.asList(
                    target.render(), writer.render(), producer.render()));
            if (bound > 0) expected.add(sibling.render());
            assertEquals("bound " + bound + ": " + kept, expected, kept);
            assertEquals(bound > 0 ? Collections.<String>emptySet()
                    : Collections.singleton(sibling.render()), cut.truncated);
            assertTrue(cut.ceilingCut.isEmpty());
        }
        // The round says how much it did not plan, and its own truncation
        // row is DIAGNOSTIC: whether it blocks a claim is the exploration's
        // end's to say (PIPELINE §7.9).
        Path cutWave = tree.newFolder("spread-cut").toPath();
        JsonObject truncated = ExploreMain.plan(perNode, TARGET_SELECTOR,
                null, perNode.resolve("results.jsonl"), null,
                perNode.resolve(StaticScopeMap.FILE), cutWave, 0, "epoch0", 0,
                DEFAULT_BOUNDS);
        assertEquals(1, truncated.get("truncated").getAsInt());
        assertEquals(0, truncated.get("ceilingCut").getAsInt());
        boolean recorded = false;
        for (GapRow gap : RowCodec.readAll(cutWave.resolve(ExploreMain.GAPS_FILE),
                RowCodec::readGap)) {
            if (!gap.detail().startsWith("REGION_PATH_CLOSURE_TRUNCATED")) {
                continue;
            }
            assertEquals(GapClass.DIAGNOSTIC, gap.cls());
            recorded = true;
        }
        assertTrue("the round records its truncation", recorded);
        assertEquals("while the producer the rows paired stays a member: "
                        + scopedWhy, ClosurePlanner.CLOSURE_MEMBER,
                scopedWhy.get(producer.render()));
        boolean saidNeverRan = false;
        boolean saidNotHere = false;
        for (GapRow gap : gapsOf(scoped)) {
            if (gap.kind() != GapKind.ADMISSION_GAP
                    || gap.cls() != GapClass.DIAGNOSTIC) {
                continue;
            }
            saidNeverRan |= gap.subject().equals("REGION.addkeys")
                    && gap.detail().contains("activated that region");
            saidNotHere |= gap.subject().equals("REGION.refresh")
                    && gap.detail().contains("activated that region on "
                            + target.node().render());
        }
        assertFalse("a region the reader's own node DID run is never "
                + "reported as one no session activated", saidNeverRan);
        assertTrue("and the one only the other node ran is -- naming the "
                + "node whose activations were asked about", saidNotHere);

        // E2: A DEMANDED EXPORT STATES THE SHARED STATE IT RESTS ON.  The
        // producer's delivered value is projected out of its own key map,
        // and the VM publishes THAT read only inside the expression -- a
        // ReadFromExpression carrying the location and the event id -- so no
        // ReadRow of the rotation names it and writers() is never asked.
        // Without this edge the removal scan the export rests on is in no
        // closure and the clock it read is declared nowhere: on hdfs-11741
        // campaign #4 (2026-09-20) nn0's export region records 1324 instance
        // reads and not one map read, so once the cross-node fan-out of N1
        // was gone nn0's removeExpiredKeys#u15 sat in no flip set at all.
        Path restsOnState = tree.newFolder("closure-stated-read").toPath();
        LocationId nnKeys = LocationId.of(LocationKind.MAP, "77", "allKeys");
        // The rotation's own earlier tick, which wrote the map it exports.
        OccurrenceAddress scanning = occurrence("hdfs-case/nn0",
                "REGION.expiry",
                CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", 2),
                "o.a.h.h.s.b.BlockManager#run#19");
        // The SAME region on a node of its own: another JVM's key map, so
        // no occurrence of it could have written the version nn0 exported.
        OccurrenceAddress farExpiry = occurrence("hdfs-case/dn0",
                "REGION.expiry", CausalContext.of(Role.CLIENT, "", 5),
                "o.a.h.h.s.d.BPServiceActor#offerService#77");
        Endpoint scanned = at(scanning, Endpoint.stateSite(
                "BlockTokenSecretManager", "removeExpiredKeys", 16, true),
                "BlockTokenSecretManager#removeExpiredKeys#16");
        Session rests = new Session(restsOnState, "s-seed");
        rests.activations(false, target, writer, producer, scanning, farExpiry);
        rests.symbolic("e.scan", "M_SCANNED", "L");
        rests.symbolic("e.stored", "M_HOFF_KEY");
        // What the rotation DELIVERED: a projection out of the map, over
        // the version the scan left it at, as the VM publishes it.
        rests.expression("e.exported", guardedRead(nnKeys, 25L, "L",
                leaf("M_HOFF_KEY", "I"), 30L));
        rests.write(scanned, nnKeys, 25L, "e.scan", "L");
        rests.export(exported, "e.exported", 11L, "119992");
        rests.attach(attached, "M_HOFF_KEY", "119992", exported);
        rests.write(stored(writer), allKeys, 5L, "e.stored");
        rests.read(lookedUp(target), allKeys, 5L, "M_READ_KEY", "119992");
        rests.anchored(target);
        rests.flush();
        StaticScopeMap restsMap = StaticScopeMap.read(scopeMap(restsOnState,
                targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.expiry",
                        "BlockTokenSecretManager#u16",
                        "BlockTokenSecretManager#removeExpiredKeys",
                        "<example.Manager: java.util.Map allKeys>",
                        "<example.Manager: java.util.Map allKeys>", "",
                        "BlockTokenSecretManager#u15"),
                scopeSite(StaticScopeMap.EXPORT_SITE, "REGION.rotate",
                        "PBHelper#convert#9", "PBHelper#convert", "", "",
                        "XCH.resp.block-key-id")));
        ClosurePlanner.Plan viaState = closure(
                Corpus.read(restsOnState, null), target, restsMap);
        Map<String, Set<String>> statedFlips =
                new LinkedHashMap<String, Set<String>>();
        for (Task task : viaState.tasks) {
            statedFlips.put(task.focused().render(),
                    viaState.flipSites.get(task.taskId()));
        }
        assertTrue("the occurrence that wrote the version the export rests "
                        + "on is in the closure, although no read row of "
                        + "the exporter names that map: " + statedFlips,
                statedFlips.containsKey(scanning.render()));
        assertTrue("with the guard of its write as the branch a wave may "
                        + "flip there -- the rotation flip 11741 needs: "
                        + statedFlips,
                statedFlips.get(scanning.render())
                        .contains("BlockTokenSecretManager#u15"));
        assertFalse("and the same write site on another node is still not a "
                        + "task: a concrete map lives in one heap (N1): "
                        + statedFlips,
                statedFlips.containsKey(farExpiry.render()));

        // Where they disagree, the closure follows the ROW and the reader is
        // told: the writer below was started by some other delivery than the
        // one its attach row names.
        Path split = tree.newFolder("closure-split").toPath();
        OccurrenceAddress confused = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(at(producer,
                                "XCH.resp.block-key-expiry", "PBHelper#convert#12")
                                .id(), "DatanodeProtocol#registerDatanode"),
                "o.a.h.h.s.d.BPServiceActor#offerService#41");
        Session other = new Session(split, "s-seed");
        other.activations(false, target, confused, producer);
        other.constant("e.119992", "119992");
        other.symbolic("e.stored", "M_HOFF_KEY");
        other.export(exported, "e.119992", 11L, "119992");
        other.attach(at(confused, "XCH.resp.block-key-id",
                "PBHelper#convert#9"), "M_HOFF_KEY", "119992", exported);
        other.write(stored(confused), allKeys, 5L, "e.stored");
        other.read(at(confused, Endpoint.stateSite("BlockTokenSecretManager",
                        "get", 3, false), "BlockTokenSecretManager#get#3"),
                allKeys, 5L, "M_READ_KEY", "119992");
        other.target(confused, "BlockTokenSecretManager#get#3",
                "(= M_READ_KEY 0)");
        other.flush();
        ClosurePlanner.Plan divergent = closure(Corpus.read(split, null),
                confused, map);
        List<String> divergentFocused = focused(divergent);
        assertTrue("the closure follows the recorded pairing: "
                        + divergentFocused,
                divergentFocused.contains(producer.render()));
        boolean told = false;
        for (GapRow gap : gapsOf(divergent)) {
            told |= gap.kind() == GapKind.TOPOLOGY_DIVERGENCE
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.detail().contains(exported.id());
        }
        assertTrue("and the disagreement is named", told);

        // The epoch's skeleton, over the same corpus: a pair no slot covers
        // OPENS one (growth, and the producer is a task of this same wave);
        // the same pair from any later replay FILLS it; and a consumer
        // endpoint paired with a different producer REPLACES -- which is the
        // only one of the three that forks an epoch.
        Set<String> members = new LinkedHashSet<String>();
        members.add(target.id());
        members.add(writer.id());
        SlotTable table = new SlotTable();
        SlotTable.Reconciliation first = table.reconcile(corpus, members, 0);
        assertFalse("growth is not a divergence", first.replaced);
        assertTrue("the wire delivery and the state edge both open slots: "
                + first.opened.size(), first.opened.size() >= 2);
        SlotTable.Reconciliation again = table.reconcile(corpus, members, 1);
        assertTrue("the same pairs fill the slots they opened",
                again.opened.isEmpty() && again.filled >= 2);
        assertFalse(again.replaced);

        // A REPLACEMENT is one consumer endpoint pairing with a DIFFERENT
        // producer: the two pairings cannot both be this epoch's.
        Path twoWays = tree.newFolder("closure-replaced").toPath();
        Endpoint otherPort = at(producer, "XCH.resp.block-key-expiry",
                "PBHelper#convert#12");
        Session paired = new Session(twoWays, "s-seed");
        paired.activations(false, target, writer, producer);
        paired.constant("e.119992", "119992");
        paired.export(exported, "e.119992", 11L, "119992");
        paired.attach(attached, "M_HOFF_KEY", "119992", exported);
        paired.flush();
        Session repaired = new Session(twoWays, "s-two");
        repaired.activations(false, writer, producer);
        repaired.constant("e.119993", "119993");
        repaired.export(otherPort, "e.119993", 13L, "119993");
        repaired.attach(attached, "M_HOFF_KEY", "119993", otherPort);
        repaired.flush();
        Set<String> pairedMembers = new LinkedHashSet<String>();
        pairedMembers.add(writer.id());
        SlotTable.Reconciliation contradiction = new SlotTable()
                .reconcile(Corpus.read(twoWays, null), pairedMembers, 2);
        assertTrue("a LATER SESSION pairing one consumer with another "
                        + "producer than the catalog's is a replacement",
                contradiction.replaced);
        boolean blocking = false;
        for (GapRow gap : contradiction.gaps) {
            blocking |= gap.kind() == GapKind.TOPOLOGY_DIVERGENCE
                    && gap.cls() == GapClass.BLOCKING
                    && gap.detail().contains("the catalog pairs this consumer")
                    && gap.detail().contains("opened by s-seed");
        }
        assertTrue("and it is BLOCKING: the campaign opens an epoch",
                blocking);

        // A slot stands on the session that opened it.  GROW withdraws the
        // replay that exposed a region and re-runs it under the grown plan
        // (hdfs-11741 V4): the re-run's pairing replaces nothing, since the
        // session the old slot stood on is no longer the corpus's.
        Path before = tree.newFolder("closure-before-grow").toPath();
        Session exposing = new Session(before, "s-seed");
        exposing.activations(false, writer, producer);
        exposing.constant("e.119992", "119992");
        exposing.export(exported, "e.119992", 11L, "119992");
        exposing.attach(attached, "M_HOFF_KEY", "119992", exported);
        exposing.flush();
        Path after = tree.newFolder("closure-after-grow").toPath();
        Session rerun = new Session(after, "s-two");
        rerun.activations(false, writer, producer);
        rerun.constant("e.119993", "119993");
        rerun.export(otherPort, "e.119993", 13L, "119993");
        rerun.attach(attached, "M_HOFF_KEY", "119993", otherPort);
        rerun.flush();
        SlotTable grown = new SlotTable();
        grown.reconcile(Corpus.read(before, null), pairedMembers, 1);
        SlotTable.Reconciliation reopened = grown.reconcile(
                Corpus.read(after, null), pairedMembers, 2);
        assertFalse("a withdrawn session's slot contradicts nothing",
                reopened.replaced);
        assertEquals("the session in its place opens the slot again",
                otherPort.id(), slotsOf(reopened).get(0).producer.id());

        // An occurrence a replay answered by its question (IDENTITY §9)
        // stands at the declared address under another chain: its pairing
        // is that chain's, a slot beside the declared one's, no replacement
        // -- whichever session lands first, and through the slot file too,
        // since which slots are answered is read off their opening sessions.
        String[][] chains = {{"s-seed", "119992", "11"},
                {"s-two", "119993", "13"}};
        Path answeredRun = tree.newFolder("closure-answered").toPath();
        for (String[] chain : chains) {
            chainOf(answeredRun, chain, writer, producer, attached,
                    chain[0].equals("s-seed") ? exported : otherPort);
        }
        SlotTable.Reconciliation ownChain = new SlotTable().reconcile(
                Corpus.read(answeredRun, null), pairedMembers, 2);
        assertFalse("an answered occurrence's pairing replaces nothing",
                ownChain.replaced);
        assertEquals("and opens its own slot beside the declared one's", 2,
                slotsOf(ownChain).size());
        for (String[] landing : new String[][] {{"0", "table"},
                {"1", "table"}, {"0", "file"}, {"1", "file"}}) {
            String[] chain = chains[Integer.parseInt(landing[0])];
            Path alone = tree.newFolder("closure-landed-" + chain[0] + "-"
                    + landing[1]).toPath();
            chainOf(alone, chain, writer, producer, attached,
                    chain[0].equals("s-seed") ? exported : otherPort);
            SlotTable landed = new SlotTable();
            landed.reconcile(Corpus.read(alone, null), pairedMembers, 1);
            if (landing[1].equals("file")) {
                landed.write(Files.createDirectories(
                        alone.resolve("obligations-0001")));
                landed = SlotTable.read(alone);
            }
            SlotTable.Reconciliation both = landed.reconcile(
                    Corpus.read(answeredRun, null), pairedMembers, 2);
            assertFalse(chain[0] + " landing first by " + landing[1]
                    + " makes no replacement", both.replaced);
            assertEquals(chain[0] + " landing first by " + landing[1]
                    + " holds both chains' slots", 2, landed.size());
        }

        // ONLY AN ADMITTED REPLAY STATES A TOPOLOGY.  The same foreign
        // pairing, from a replay whose own result row says NOT_ADMITTED, is
        // a replay that did not run the world it was asked for: it states
        // no topology at all, so the skeleton is untouched, the wave is not
        // emptied, and the pairing is REPORTED.  hdfs-11741 campaign #2:
        // one such session -- its mint had planted no clock skew -- paired
        // eight consumers with producers the skeleton does not carry, and
        // wave 1 opened with zero candidates.
        Path unadmitted = tree.newFolder("closure-replaced-unadmitted")
                .toPath();
        Session held = new Session(unadmitted, "s-seed");
        held.activations(false, target, writer, producer);
        held.constant("e.119992", "119992");
        held.export(exported, "e.119992", 11L, "119992");
        held.attach(attached, "M_HOFF_KEY", "119992", exported);
        held.flush();
        Session wrongWorld = new Session(unadmitted, "s-unadmitted");
        wrongWorld.activations(true, writer, producer);
        wrongWorld.constant("e.119993", "119993");
        wrongWorld.export(otherPort, "e.119993", 13L, "119993");
        wrongWorld.attach(attached, "M_HOFF_KEY", "119993", otherPort);
        wrongWorld.answered(ObligationResult.of("OBL.s-unadmitted",
                Verdict.NOT_ADMITTED, "s-unadmitted",
                "the obligation assigns a root no mint of this replay "
                        + "planted"));
        wrongWorld.flush();
        SlotTable.Reconciliation stands = new SlotTable()
                .reconcile(Corpus.read(unadmitted, null), pairedMembers, 2);
        assertFalse("a replay that was not admitted states no topology, so "
                        + "it contradicts none and the next wave keeps its "
                        + "candidates", stands.replaced);
        boolean reported = false;
        for (GapRow gap : stands.gaps) {
            if (gap.kind() != GapKind.TOPOLOGY_DIVERGENCE) continue;
            assertFalse("and nothing it says is BLOCKING: " + gap.detail(),
                    gap.cls() == GapClass.BLOCKING);
            reported |= gap.sessionId().equals("s-unadmitted")
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.detail().contains("the catalog pairs this consumer")
                    && gap.detail().endsWith("(this replay was not admitted, "
                            + "so it states no topology)");
        }
        assertTrue("the pairing is still REPORTED, naming why nothing was "
                + "done about it", reported);

        // PIPELINE §7.1 step 4: a STATE reader that joined ANOTHER writer in
        // another session is not a replacement, it is that family's second
        // arm.  A flip is expected to change which writer delivers -- that
        // is what the flip is for -- so reading it as a contradiction forked
        // an epoch over the arm the wave had just asked for.  "Opened by
        // another session" means nothing for a state slot.
        Path arms = tree.newFolder("closure-state-arms").toPath();
        OccurrenceAddress otherWriter = occurrence("hdfs-case/dn0",
                "REGION.deletekeys", CausalContext.of(Role.CLIENT, "", 4),
                "o.a.h.h.s.d.BPServiceActor#offerService#77");
        Endpoint reader = at(target, Endpoint.stateSite(
                "BlockTokenSecretManager", "get", 3, false),
                "BlockTokenSecretManager#get#3");
        Session firstArm = new Session(arms, "s-seed");
        firstArm.activations(false, target, writer);
        firstArm.symbolic("e.a", "M_A");
        firstArm.write(stored(writer), allKeys, 5L, "e.a");
        firstArm.read(reader, allKeys, 5L, "M_READ_KEY", "119992");
        firstArm.flush();
        Session flipping = new Session(arms, "s-flip");
        flipping.activations(true, target, otherWriter);
        flipping.symbolic("e.b", "M_B");
        flipping.write(at(otherWriter, Endpoint.stateSite(
                        "BlockTokenSecretManager", "removeKeys", 19, true),
                        "BlockTokenSecretManager#removeKeys#19"), allKeys,
                9L, "e.b");
        flipping.read(reader, allKeys, 9L, "M_READ_KEY_2", "0");
        // AND IT WAS ADMITTED: only a replay that ran the world it was asked
        // for states a topology, so a second arm is an arm because the
        // session says its obligation reproduced.
        flipping.answered(ObligationResult.of("OBL.s-flip", Verdict.ADMITTED,
                "s-flip", "the focused prefix reproduced"));
        flipping.flush();
        Set<String> readers = new LinkedHashSet<String>();
        readers.add(target.id());
        readers.add(writer.id());
        readers.add(otherWriter.id());
        SlotTable.Reconciliation grew2 = new SlotTable().reconcile(
                Corpus.read(arms, null), readers, 8);
        assertFalse("a state pairing another session states is growth",
                grew2.replaced);
        assertTrue("both writers are arms of that reader's family: "
                        + grew2.opened.size(), grew2.opened.size() >= 2);
        for (GapRow gap : grew2.gaps) {
            assertFalse("and nothing is refused over it: " + gap.detail(),
                    gap.kind() == GapKind.TOPOLOGY_DIVERGENCE
                            && gap.cls() == GapClass.BLOCKING);
        }

        // Two occurrences of ONE code point that a replay ran BOTH are
        // two requests -- growth.  A REPLACEMENT is the closure's member
        // ABSENT from a replay that ran the same code point under another
        // context.
        Path requests = tree.newFolder("closure-two-requests").toPath();
        OccurrenceAddress firstRequest = occurrence("hdfs-case/dn0",
                "REGION.checksum",
                CausalContext.of("a1b2c3d4e5f60718", "HDFS_SASL/checksum"),
                "o.a.h.h.s.d.DataXceiver#run#44");
        OccurrenceAddress secondRequest = occurrence("hdfs-case/dn0",
                "REGION.checksum",
                CausalContext.of("00112233445566aa", "HDFS_SASL/checksum"),
                "o.a.h.h.s.d.DataXceiver#run#44");
        Session bothRan = new Session(requests, "s-seed");
        bothRan.activations(false, firstRequest, secondRequest);
        bothRan.flush();
        assertFalse("two requests at one code point are growth",
                new SlotTable().reconcile(Corpus.read(requests, null),
                        Collections.singleton(firstRequest.id()), 5)
                        .replaced);

        // Contexts compare by their shape (Corpus#contextShape): a replay
        // that ran the code point under the member's shape ran the member,
        // whatever it counted (solr-adhoc-05: a poll's k-th wake is another
        // k in every run); one that ran it only under another shape -- a
        // client's root in place of a poll's wake -- replaced it.  A hop
        // whose sender no row names is no known difference (two requests
        // here, their senders unnamed).
        OccurrenceAddress otherShape = occurrence("hdfs-case/dn0",
                "REGION.checksum", CausalContext.of(Role.CLIENT, "", 1),
                "o.a.h.h.s.d.DataXceiver#run#44");
        OccurrenceAddress wake12 = occurrence("hdfs-case/dn0",
                "REGION.checksum", CausalContext.of(Role.of("WAKE"),
                        "ZkDistributedQueue.peekElements", 12),
                "o.a.h.h.s.d.DataXceiver#run#44");
        OccurrenceAddress wake1 = occurrence("hdfs-case/dn0",
                "REGION.checksum", CausalContext.of(Role.of("WAKE"),
                        "ZkDistributedQueue.peekElements", 1),
                "o.a.h.h.s.d.DataXceiver#run#44");
        // member, what the replay ran, whether it replaced the member
        Object[][] instead = {
                {otherShape, wake1, true},
                {firstRequest, secondRequest, false},
                {wake12, wake1, false},
                {wake12, otherShape, true},
        };
        for (Object[] row : instead) {
            OccurrenceAddress member = (OccurrenceAddress) row[0];
            OccurrenceAddress ran = (OccurrenceAddress) row[1];
            Path dir = tree.newFolder("closure-instead-"
                    + member.context().render().hashCode() + "-"
                    + ran.context().render().hashCode()).toPath();
            Session ranIt = new Session(dir, "s-seed");
            ranIt.activation(member, false);
            ranIt.flush();
            Session ranOther = new Session(dir, "s-flip");
            ranOther.activation(ran, true);
            ranOther.answered(ObligationResult.of("OBL.s-flip",
                    Verdict.ADMITTED, "s-flip",
                    "the focused prefix reproduced"));
            ranOther.flush();
            assertEquals(member.context().render() + " held, "
                            + ran.context().render() + " ran",
                    row[2], new SlotTable().reconcile(Corpus.read(dir, null),
                            Collections.singleton(member.id()), 6).replaced);
        }

        // A member this replay ran under its own context on another node
        // MOVED (solr-bugs-snapshot-no-active Z2K: a setData fault made node1
        // the Overseer, and the update node1 had served ran on node0, beside
        // node1's new autoscaling write at setData's code point): named,
        // DIAGNOSTIC, never a replacement -- unless all it ran elsewhere is
        // a Lost context, which names no shape.
        OccurrenceAddress served = occurrence("hdfs-case/dn0",
                "REGION.checksum", CausalContext.of(Role.CLIENT, "update", 1),
                "o.a.h.h.s.d.DataXceiver#run#44");
        OccurrenceAddress lost = occurrence("hdfs-case/dn0",
                "REGION.checksum", CausalContext.of(Role.UNKNOWN),
                "o.a.h.h.s.d.DataXceiver#run#44");
        OccurrenceAddress movedRequest = occurrence("hdfs-case/dn1",
                "REGION.checksum", served.context(),
                "o.a.h.h.s.d.DataXceiver#run#44");
        OccurrenceAddress lostThere = occurrence("hdfs-case/dn1",
                "REGION.checksum", CausalContext.of(Role.UNKNOWN),
                "o.a.h.h.s.d.DataXceiver#run#44");
        // what else the replay ran, whether it replaced the member, the
        // moved rows
        Object[][] movedRows = {
                {movedRequest, false, 1},
                {lostThere, true, 0},
        };
        for (Object[] row : movedRows) {
            Path dir = tree.newFolder("closure-moved-" + ((OccurrenceAddress)
                    row[0]).node().render().hashCode() + "-" + row[2])
                    .toPath();
            Session ranIt = new Session(dir, "s-seed");
            ranIt.activation(served, false);
            ranIt.flush();
            Session ranThere = new Session(dir, "s-flip");
            ranThere.activation(lost, true);
            ranThere.activation((OccurrenceAddress) row[0], false);
            ranThere.answered(ObligationResult.of("OBL.s-flip",
                    Verdict.ADMITTED, "s-flip",
                    "the focused prefix reproduced"));
            ranThere.flush();
            SlotTable.Reconciliation reconciled = new SlotTable().reconcile(
                    Corpus.read(dir, null),
                    Collections.singleton(served.id()), 6);
            assertEquals(row[0] + " elsewhere", row[1], reconciled.replaced);
            int named = 0;
            for (GapRow gap : reconciled.gaps) {
                if (gap.kind() != GapKind.ADDRESS_UNSTABLE) continue;
                assertEquals(GapClass.DIAGNOSTIC, gap.cls());
                assertEquals(served.render(), gap.subject());
                assertTrue(gap.detail(), gap.detail().contains("hdfs-case/dn1"));
                named++;
            }
            assertEquals(row[0] + " elsewhere", row[2], named);
        }

        // The closure may hold TWO occurrences of one code point: hdfs-17897's
        // dn0 serves the client's SASL handshake and the checksum leader's
        // own at one callback, and the leader's co-reads the key map the
        // client's reads.  A replay that ran one member and not the other
        // ran that code point under a context the closure holds -- nothing
        // stands in the absent one's place.  Each order is asked, because a
        // table that kept one member per code point read exactly one of
        // them as a replacement.
        Set<String> bothMembers = new LinkedHashSet<String>(Arrays.asList(
                firstRequest.id(), secondRequest.id()));
        for (OccurrenceAddress alone
                : Arrays.asList(firstRequest, secondRequest)) {
            Path oneMember = tree.newFolder("closure-one-member-"
                    + alone.context().render().hashCode()).toPath();
            Session seedBoth = new Session(oneMember, "s-seed");
            seedBoth.activations(false, firstRequest, secondRequest);
            seedBoth.flush();
            Session ranOne = new Session(oneMember, "s-flip");
            ranOne.activation(alone, true);
            ranOne.answered(ObligationResult.of("OBL.s-flip",
                    Verdict.ADMITTED, "s-flip",
                    "the focused prefix reproduced"));
            ranOne.flush();
            assertFalse("a closure member is never another member's "
                            + "replacement",
                    new SlotTable().reconcile(Corpus.read(oneMember, null),
                            bothMembers, 7).replaced);
        }
        // With two members held there, a context of a shape the closure does
        // NOT hold there is still a replacement when it ran the code point
        // alone, and still growth beside a member that ran.
        OccurrenceAddress firstCall = occurrence("hdfs-case/dn0",
                "REGION.checksum", CausalContext.of(Role.CLIENT, "checksum", 1),
                "o.a.h.h.s.d.DataXceiver#run#44");
        OccurrenceAddress secondCall = occurrence("hdfs-case/dn0",
                "REGION.checksum", CausalContext.of(Role.CLIENT, "checksum", 2),
                "o.a.h.h.s.d.DataXceiver#run#44");
        Set<String> twoCalls = new LinkedHashSet<String>(Arrays.asList(
                firstCall.id(), secondCall.id()));
        OccurrenceAddress stranger = wake1;
        Path strangerAlone = tree.newFolder("closure-stranger-alone").toPath();
        Session seedTwo = new Session(strangerAlone, "s-seed");
        seedTwo.activations(false, firstCall, secondCall);
        seedTwo.flush();
        Session ranStranger = new Session(strangerAlone, "s-flip");
        ranStranger.activation(stranger, true);
        ranStranger.answered(ObligationResult.of("OBL.s-flip",
                Verdict.ADMITTED, "s-flip", "the focused prefix reproduced"));
        ranStranger.flush();
        assertTrue("a code point the closure holds, run under no shape it "
                        + "holds there, IS a replacement",
                new SlotTable().reconcile(Corpus.read(strangerAlone, null),
                        twoCalls, 8).replaced);
        Path strangerBeside = tree.newFolder("closure-stranger-beside")
                .toPath();
        Session seedThree = new Session(strangerBeside, "s-seed");
        seedThree.activations(false, firstCall, secondCall);
        seedThree.flush();
        Session ranBeside = new Session(strangerBeside, "s-flip");
        ranBeside.activation(secondCall, true);
        ranBeside.activation(stranger, false);
        ranBeside.answered(ObligationResult.of("OBL.s-flip",
                Verdict.ADMITTED, "s-flip", "the focused prefix reproduced"));
        ranBeside.flush();
        assertFalse("beside a member that ran, another context is a second "
                        + "request",
                new SlotTable().reconcile(Corpus.read(strangerBeside, null),
                        twoCalls, 9).replaced);

        // An occurrence the corpus names ONLY in a write row -- no
        // activation, no decision -- cannot be a task: there is no recorded
        // run to focus a replay on.  It used to reach Task.of with an empty
        // seedSessionId and abort the whole wave with
        // "seedSessionId is required"; the seed replay alone ran it, so it
        // WAITS for a focused replay to expose it.
        Path unrun = tree.newFolder("closure-unrun").toPath();
        OccurrenceAddress ghost = occurrence("hdfs-case/dn0",
                "REGION.unrun", CausalContext.of(Role.of("DATA_XCEIVER"), "", 7),
                "o.a.h.h.s.d.DataXceiver#run#88");
        Session partialRun = new Session(unrun, "s-seed");
        partialRun.activation(target, false);
        partialRun.symbolic("e.ghost", "M_GHOST");
        partialRun.write(at(ghost, Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true),
                        "BlockTokenSecretManager#addKeys#12"), allKeys, 9L,
                "e.ghost");
        partialRun.read(at(target, Endpoint.stateSite(
                        "BlockTokenSecretManager", "get", 3, false),
                        "BlockTokenSecretManager#get#3"), allKeys, 9L,
                "M_READ_KEY", "119992");
        partialRun.target(target, "BlockTokenSecretManager#get#3",
                "(= M_READ_KEY 0)");
        partialRun.flush();
        ClosurePlanner.Plan withGhost = closure(Corpus.read(unrun, null),
                target, map);
        for (Task task : withGhost.tasks) {
            assertFalse("an occurrence no session ran is not a task",
                    task.focused().id().equals(ghost.id()));
            assertFalse("and a task always names the recording it was "
                    + "planned from", task.seedSessionId().isEmpty());
        }
        assertTrue("and it waits by name: " + withGhost.waiting,
                withGhost.waiting.contains(ghost));

        // A fatal predicate published as a REFERENCE into the session's
        // expression table names the read it rests on, through the one
        // lowering the composer and the flip query also use.  Reading the
        // token as a name admitted nothing, so the closure said "no
        // admitted path reads this" about the anchor's own read.
        Path viaRef = tree.newFolder("closure-phi-ref").toPath();
        Endpoint refRead = at(target, Endpoint.stateSite(
                "BlockTokenSecretManager", "get", 3, false),
                "BlockTokenSecretManager#get#3");
        Session stated = new Session(viaRef, "s-seed");
        stated.activations(false, target, writer);
        stated.symbolic("e.stored", "M_HOFF_KEY");
        stated.symbolic("EXPR.0000000000000002", "M_READ_KEY");
        stated.write(at(writer, Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true),
                        "BlockTokenSecretManager#addKeys#12"), allKeys, 5L,
                "e.stored");
        stated.read(refRead, allKeys, 5L, "M_READ_KEY", "119992");
        stated.target(target, "BlockTokenSecretManager#get#3",
                "(not EXPR.0000000000000002)");
        stated.flush();
        ClosurePlanner.Plan lowered = closure(Corpus.read(viaRef, null),
                target, map);
        for (GapRow gap : gapsOf(lowered)) {
            assertFalse("the anchor's own read is what its phi rests on: "
                            + gap.detail(),
                    gap.subject().equals(refRead.toString())
                            && gap.detail().contains("no admitted path"));
        }

        theClosureHasOneRoot(iteration, writer);

        // PIPELINE §7.2: the closure grows by the STATIC write sites of the
        // locations it demands, and not only by the writers some row paired.
        // On 17960 the seed runs the marker's true arm, where deleteSnapshot
        // defers and the counter decrement never executes, so NO row of any
        // session can put the deletion region in the anchor's closure -- and
        // that region's marker branch is the flip the wave exists to ask for.
        // What the map states is the site (region, method#unit, the cell it
        // stores into) and its guard set; which occurrences ran it is the
        // recording's to say.
        Path aside = tree.newFolder("closure-static-writer").toPath();
        OccurrenceAddress deferring = occurrence("hdfs-case/dn0",
                "REGION.deferring", CausalContext.of(Role.CLIENT, "", 1),
                "o.a.h.h.s.n.SnapshotManager#deleteSnapshot#7");
        OccurrenceAddress undeclared = occurrence("hdfs-case/dn0",
                "REGION.undeclared", CausalContext.of(Role.CLIENT, "", 2),
                "o.a.h.h.s.n.SnapshotManager#renameSnapshot#7");
        LocationId counter = LocationId.of(LocationKind.INSTANCE, "2",
                "24");
        Session apart = new Session(aside, "s-seed");
        apart.activations(false, target, writer, deferring, undeclared);
        apart.symbolic("e.count", "M_COUNT_IN");
        apart.symbolic("EXPR.0000000000000003", "M_MARKER", "Z");
        apart.symbolic("EXPR.0000000000000004", "M_READ_COUNT");
        apart.marker(deferring, "CASE.MARKER", "M_MARKER", "true");
        // The increment the seed DID run, and the anchor's read of it.
        apart.write(at(writer, Endpoint.stateSite("SnapshotManager",
                        "createSnapshot", 621, true),
                        "SnapshotManager#createSnapshot#621"), counter, 61L,
                "e.count");
        apart.read(at(target, Endpoint.stateSite("SnapshotManager",
                        "getNumSnapshots", 2, false),
                        "SnapshotManager#getNumSnapshots#2"), counter, 61L,
                "M_READ_COUNT", "2");
        apart.target(target, "SnapshotManager#getNumSnapshots#2",
                "(not EXPR.0000000000000004)");
        apart.decision(target, "Section#u61", 1, true, "EXPR.0000000000000004");
        // The deletion region decided the marker and wrote NOTHING.
        apart.decision(deferring, "SnapshotManager#u7", 1, false,
                "EXPR.0000000000000003");
        // A second symbolic decision of that same occurrence, at a site no
        // guard set names: it decides nothing about the write.
        apart.decision(deferring, "SnapshotManager#u90", 1, false,
                "M_ELSEWHERE");
        // And an occurrence the closure does not hold at all.
        apart.decision(undeclared, "SnapshotManager#u7", 1, false,
                "M_UNDECLARED");
        apart.flush();
        scopeMap(aside,
                targetSite("REGION.target", "SnapshotManager#u64",
                        "Section#u61"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "SnapshotManager#u27",
                        "SnapshotManager#createSnapshot",
                        "<java.util.concurrent.atomic.AtomicInteger: int"
                                + " value>",
                        "<SnapshotManager: AtomicInteger numSnapshots>", "",
                        "SnapshotManager#u9"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.deferring",
                        "SnapshotManager#u35",
                        "SnapshotManager#deleteSnapshot",
                        "<java.util.concurrent.atomic.AtomicInteger: int"
                                + " value>",
                        "<SnapshotManager: AtomicInteger numSnapshots>", "",
                        "SnapshotManager#u7"),
                // A region of the program that no session of this corpus ran.
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.neverran",
                        "SnapshotManager#u3",
                        "SnapshotManager#setNumSnapshots",
                        "<java.util.concurrent.atomic.AtomicInteger: int"
                                + " value>",
                        "<SnapshotManager: AtomicInteger numSnapshots>", ""));
        Path asideWave = tree.newFolder("closure-static-writer-wave")
                .toPath();
        JsonObject beside = plan(aside, TARGET_SELECTOR, null,
                aside.resolve("results.jsonl"), asideWave, 0);
        Map<String, String> whyTask = new LinkedHashMap<String, String>();
        for (JsonElement element : beside.getAsJsonArray("taskRows")) {
            JsonObject taskRow = element.getAsJsonObject();
            whyTask.put(taskRow.get("focused").getAsString(),
                    taskRow.get("why").getAsString());
        }
        assertEquals("the anchor is a closure member",
                ClosurePlanner.CLOSURE_MEMBER, whyTask.get(target.render()));
        assertEquals("the writer the rows paired is one too",
                ClosurePlanner.CLOSURE_MEMBER, whyTask.get(writer.render()));
        assertEquals("and the region that COULD have written the location is "
                        + "in the closure through the static map, with the "
                        + "manifest saying which: " + whyTask,
                ClosurePlanner.STATIC_CANDIDATE_WRITER,
                whyTask.get(deferring.render()));
        assertFalse("an occurrence no demanded value reaches is not a task: "
                + whyTask, whyTask.containsKey(undeclared.render()));
        // A candidate region no session ran is NAMED and is not a task:
        // there is no run to focus (PIPELINE §7.2).
        assertTrue("the unrun candidate region is named",
                anyGap(asideWave, gap -> gap.kind() == GapKind.ADMISSION_GAP
                        && gap.cls() == GapClass.DIAGNOSTIC
                        && gap.subject().equals("REGION.neverran")
                        && gap.detail().contains(
                                "retained set would have to grow")));

        List<Obligation> beyond = obligations(asideWave);
        List<String> flips = new ArrayList<String>();
        for (Obligation flip : beyond) {
            flips.add(flip.siteId());
            assertTrue("a wave proposes no model: the worker solves it",
                    flip.rootAssignments().isEmpty());
        }
        assertEquals("the target's guard and the deletion region's own guard "
                        + "of the write, and nothing else: " + flips,
                Arrays.asList("Section#u61", "SnapshotManager#u7"), flips);
        assertEquals("one flip from the anchor, one from the writer the seed "
                        + "never ran", 1,
                obligationsOf(beyond, ClosurePlanner.taskId(deferring))
                        .size());
        for (Obligation flip : beyond) {
            assertFalse("a symbolic decision at a site no guard set names is "
                            + "not a candidate: " + flips,
                    "SnapshotManager#u90".equals(flip.siteId()));
            assertFalse("and neither is one of an occurrence outside the "
                            + "closure: " + flips,
                    ClosurePlanner.taskId(undeclared).equals(flip.taskId()));
        }

        // PIPELINE §7.2: the same growth where the demanded read
        // is a CONTAINER.  The join INLINES the version a read observed, and
        // a container version is lowered once and NAMED, so an anchor guard
        // `allKeys.get(id) == null` stands in the text as one
        // container_dag__ name.  Behind it is the chain of PUTs, whose base
        // is the empty map; the read's OWN symbol is in neither.  Matching
        // rows against the names the text SAYS therefore demanded nothing of
        // the anchor's map, writers() was never asked about it, and on 11741
        // no NameNode occurrence could enter the closure at all -- wave 0
        // had the anchor's own guard to flip and nothing else.  What a term
        // RESTS ON includes the state the subterm is the value of.
        Path inlined = tree.newFolder("closure-container-demand").toPath();
        // The expiry tick ON THE READER'S OWN NODE: the map this anchor read
        // is an object in this JVM's heap (N1), so the occurrence that could
        // have expired a key OUT OF IT is the data node's own tick -- which
        // on 11741 is dn1's removeExpiredKeys#u15.  The NameNode's tick
        // reaches this closure through the WIRE, as the producer of the key
        // id the data node attached, and not through this read.
        OccurrenceAddress expiring = occurrence("hdfs-case/dn0",
                "REGION.expiry", CausalContext.of(
                        Role.of("KEY_MANAGER_TICK"), "", 2),
                "o.a.h.h.s.b.BlockManager#run#19");
        Endpoint mapRead = at(target, Endpoint.stateSite(
                        "BlockTokenSecretManager", "retrieveDataEncryptionKey",
                        437, false),
                "BlockTokenSecretManager#retrieveDataEncryptionKey#437");
        String mapState = "MAP_STATE/" + allKeys.owner() + "#allKeys@v5";
        JsonObject chain = relation("ASSOCIATIVE", "PUT", "java/util/HashMap",
                relation("ASSOCIATIVE", "SNAPSHOT_BASE", "java/util/HashMap",
                        relation("ASSOCIATIVE", "STATE", "java/util/HashMap",
                                leaf("M_L'java/util/HashMap'_3",
                                        "java/util/HashMap"))),
                literal(119992), leaf("M_HOFF_KEY", "I"));
        Session container = new Session(inlined, "s-seed");
        container.activations(false, target, writer, expiring);
        container.expression("e.map", chain);
        container.expression("EXPR.0000000000000005", binary("==",
                guardedRead(allKeys, 5L, "L", relation("ASSOCIATIVE", "READ",
                        "L", chain, literal(119992))),
                leaf("N", "")));
        container.write(at(writer, Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true),
                        "BlockTokenSecretManager#addKeys#12"), allKeys, 5L,
                "e.map", "L");
        container.read(mapRead, allKeys, 5L, mapState, "119992");
        // The predicate every key case's fatal arm is: is the reference
        // this execution read null?  Published over the VM's own identity
        // leaf, which the lowering mints an opaque name for -- and states
        // a fact about.
        container.expression("EXPR.0000000000000006", binary("==",
                leaf("M_L'org/apache/Held'_9", "org/apache/Held"),
                leaf("N", "")));
        container.target(target, "BlockTokenSecretManager#u120",
                "EXPR.0000000000000005");
        container.flush();
        StaticScopeMap ofAllKeys = StaticScopeMap.read(scopeMap(inlined,
                targetSite("REGION.target", "BlockTokenSecretManager#u120",
                        "BlockTokenSecretManager#u8"),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u27",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Manager: java.util.Map allKeys>",
                        "<example.Manager: java.util.Map allKeys>", "",
                        "BlockTokenSecretManager#u21")),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.expiry",
                        "BlockTokenSecretManager#u16",
                        "BlockTokenSecretManager#removeExpiredKeys",
                        "<example.Manager: java.util.Map allKeys>",
                        "<example.Manager: java.util.Map allKeys>", "",
                        "BlockTokenSecretManager#u15"))));
        Corpus vC = Corpus.read(inlined, null);
        SmtLowering lowering = vC.lowering("s-seed");
        String mapGuard = lowering.statedTerm("EXPR.0000000000000005",
                "test");
        assertTrue("the container version stands in the text as one name: "
                + mapGuard, mapGuard.contains("container_dag__"));
        Set<String> says = lowering.reachedSymbols(
                Collections.singletonList(mapGuard));
        assertFalse("and the text does not SAY the read behind it, which is "
                        + "what a query binds its variables by: " + says,
                says.contains(mapState));
        Set<String> restsOn = vC.termSymbols("s-seed",
                "EXPR.0000000000000005");
        assertTrue("its expression RESTS ON it, which is what the closure "
                + "demands: " + restsOn, restsOn.contains(mapState));
        // THE FACTS: what the recording states about the names the guard
        // rests on travels with them.  The map read lowered to an opaque
        // identity, and the recording states that identity was not null --
        // the execution read fields off the object.  Unstated, a flip of
        // `x == null` is satisfied by freeing that boundary (PIPELINE §7.5),
        // which is how 18 of hdfs-11741's 36 wave-0 obligations came
        // back SAT with no variable declared at all.
        String nullTest = lowering.statedTerm("EXPR.0000000000000006",
                "test");
        List<String> states = lowering.facts(
                Arrays.asList(mapGuard, nullTest));
        boolean notNull = false;
        for (String fact : states) {
            notNull |= fact.startsWith("(not (= identity__")
                    && fact.endsWith("nullRef))");
        }
        assertTrue("the identity the guard rests on is stated non-null: "
                + states, notNull);
        ClosurePlanner.Plan demanded = closure(vC, target, ofAllKeys);
        Map<String, String> whyMap = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flipsOf =
                new LinkedHashMap<String, Set<String>>();
        for (Task task : demanded.tasks) {
            whyMap.put(task.focused().render(),
                    demanded.why.get(task.taskId()));
            flipsOf.put(task.focused().render(),
                    demanded.flipSites.get(task.taskId()));
        }
        assertEquals("the writer of the version the map read observed is a "
                        + "closure member: " + whyMap,
                ClosurePlanner.CLOSURE_MEMBER, whyMap.get(writer.render()));
        assertEquals("and the region that COULD have expired a key out of "
                        + "that same map joins through the static map -- the "
                        + "flip 11741 needs, and no row connects it: "
                        + whyMap, ClosurePlanner.STATIC_CANDIDATE_WRITER,
                whyMap.get(expiring.render()));
        assertTrue("with the guard of its write as the branch a wave may "
                        + "flip there: " + flipsOf,
                flipsOf.get(expiring.render())
                        .contains("BlockTokenSecretManager#u15"));
        for (GapRow gap : gapsOf(demanded)) {
            // The row states the value it wrote as a bare reference and the
            // map states the field's descriptor; read as equality, every
            // container write row disagreed with its own cell and the
            // location had no carrier at all.
            assertFalse("and the cell's carrier is named: " + gap.detail(),
                    gap.kind() == GapKind.DECLARATION_MISSING);
        }

        // Two reads of ONE location at one endpoint id that observed
        // DIFFERENT versions are two events the identity cannot separate --
        // a read the runtime does not stand at carries no site index.  That
        // is not a replacement (a run does not contradict itself): no slot
        // for either, one DIAGNOSTIC, and the wave still asks its questions.
        Path collided = tree.newFolder("closure-no-site-index").toPath();
        Endpoint twice = at(target, Endpoint.stateSite(
                "BlockTokenSecretManager", "get", 3, false),
                "BlockTokenSecretManager#get#3");
        Session loop = new Session(collided, "s-seed");
        loop.activations(false, target, writer);
        loop.symbolic("e.first", "M_FIRST");
        loop.symbolic("e.second", "M_SECOND");
        loop.write(stored(writer), allKeys, 5L, "e.first");
        loop.write(at(writer, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 13, true), "BlockTokenSecretManager"
                        + "#addKeys#13"), allKeys, 6L, "e.second");
        loop.read(twice, allKeys, 5L, "M_READ_KEY", "119992");
        loop.read(twice, allKeys, 6L, "M_READ_KEY", "119993");
        loop.target(target, "BlockTokenSecretManager#get#3",
                "(= M_READ_KEY 0)");
        loop.flush();
        Set<String> both = new LinkedHashSet<String>();
        both.add(target.id());
        both.add(writer.id());
        SlotTable.Reconciliation ambiguous = new SlotTable().reconcile(
                Corpus.read(collided, null), both, 7);
        assertFalse("one session does not contradict itself",
                ambiguous.replaced);
        boolean unsayable = false;
        for (GapRow gap : ambiguous.gaps) {
            unsayable |= gap.kind() == GapKind.LINEAGE_LOST
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.detail().contains("site index missing")
                    && gap.detail().contains("observe v5 and v6");
        }
        assertTrue("and the missing site index is named", unsayable);
        for (SlotTable.Slot slot : slotsOf(ambiguous)) {
            assertFalse("neither read opens a slot",
                    slot.consumer.id().equals(twice.id()));
        }
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

    /** One container relation, as the VM serializes it. */
    private static JsonObject relation(String shape, String operation,
                                       String javaType, JsonObject receiver,
                                       JsonObject... arguments) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ContainerRelation");
        node.addProperty("shape", shape);
        node.addProperty("operation", operation);
        node.addProperty("_java_type", javaType);
        if (receiver != null) node.add("receiver", receiver);
        JsonArray list = new JsonArray();
        for (JsonObject argument : arguments) list.add(argument);
        node.add("arguments", list);
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

    /** The slots one reconciliation opened, for an assertion to look at. */
    /** One session pairing {@code attached} with {@code port}'s key
     *  {@code chain[1]}: the declared one ({@code s-seed}) or one that
     *  answered the consumer's occurrence by its question. */
    private static void chainOf(Path iteration, String[] chain,
                                OccurrenceAddress writer,
                                OccurrenceAddress producer, Endpoint attached,
                                Endpoint port) throws IOException {
        Session session = new Session(iteration, chain[0]);
        session.activations(false, writer, producer);
        session.constant("e." + chain[1], chain[1]);
        session.export(port, "e." + chain[1], Long.parseLong(chain[2]),
                chain[1]);
        session.attach(attached, "M_HOFF_KEY", chain[1], port);
        if (!chain[0].equals("s-seed")) {
            session.gap(GapRow.of(chain[0], GapKind.ADDRESS_UNSTABLE,
                    GapClass.DIAGNOSTIC, attached.occurrence().render(),
                    "the declared occurrence ran at another address"));
        }
        session.flush();
    }

    private static List<SlotTable.Slot> slotsOf(
            SlotTable.Reconciliation reconciliation) {
        return new ArrayList<SlotTable.Slot>(reconciliation.opened);
    }

    // ---- (5b) the closure has ONE root: the case's declared anchor -------

    /**
     * Folded into the closure case: a wave's roots are the anchor and nothing
     * else (PIPELINE §7.1).  The seed replay's task plan was a second source
     * of them, and a plan row is the PLAN side's own address for a region: in
     * the first real 17960 wave 43 of its 45 rows named an address no row of
     * the recording published, each became a closure root, and the wave died
     * on the empty {@code Task.seedSessionId} that follows from one.  An
     * address the seed did run is still not a root unless the case declared
     * it, and a declared anchor the seed did NOT run is refused by name.
     */
    private void theClosureHasOneRoot(Path iteration, OccurrenceAddress ran)
            throws IOException {
        Path waveDir = tree.newFolder("roots-wave").toPath();
        JsonObject manifest = ExploreMain.plan(iteration, TARGET_SELECTOR,
                null, iteration.resolve("results.jsonl"), null,
                iteration.resolve(StaticScopeMap.FILE), waveDir, 0, "epoch0",
                ClosurePlanner.DEFAULT_MAX_TASKS,
                DEFAULT_BOUNDS);
        List<String> anchors = new ArrayList<String>();
        for (JsonElement element : manifest.getAsJsonArray("anchors")) {
            anchors.add(element.getAsString());
        }
        assertEquals("one declaration, one root: " + anchors, 1,
                anchors.size());
        assertEquals(TARGET.render(), anchors.get(0));
        // The writer IS in the closure -- as the anchor's reach, not as a
        // root of its own; nothing outside that reach is planned.
        assertTrue("the closure still reaches the writer",
                manifest.get("tasks").getAsInt() >= 2);
        assertFalse("and a run's own address is not a second root: " + anchors,
                anchors.contains(ran.render()));
        // A task bound of none cuts nothing the rows connect: the writer and
        // the producer are planned whatever --max-tasks says, and the round
        // records no truncation.
        Path cut = tree.newFolder("roots-cut").toPath();
        JsonObject uncut = ExploreMain.plan(iteration, TARGET_SELECTOR,
                null, iteration.resolve("results.jsonl"), null,
                iteration.resolve(StaticScopeMap.FILE), cut, 0, "epoch0", 0,
                DEFAULT_BOUNDS);
        assertEquals(manifest.get("tasks").getAsInt(),
                uncut.get("tasks").getAsInt());
        assertEquals(0, uncut.get("truncated").getAsInt());
        assertEquals(0, uncut.get("ceilingCut").getAsInt());

        // A declared anchor the seed session never ran: BLOCKING, and the
        // refusal names the address rather than leaving "no tasks".
        Path elsewhere = tree.newFolder("roots-absent").toPath();
        Session only = new Session(elsewhere, "s-seed");
        only.activation(WRITER, false);
        only.flush();
        Path absentWave = tree.newFolder("roots-absent-wave").toPath();
        ExploreMain.plan(elsewhere, TARGET.render(), null,
                elsewhere.resolve("results.jsonl"), null,
                elsewhere.resolve(StaticScopeMap.FILE), absentWave, 0,
                "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                DEFAULT_BOUNDS);
        assertTrue("the anchor's absence is BLOCKING and named",
                anyGap(absentWave, gap -> gap.kind() == GapKind.ADMISSION_GAP
                        && gap.cls() == GapClass.BLOCKING
                        && gap.subject().equals(TARGET.render())
                        && gap.detail().contains("published no activation")));
    }

    // ---- (6) a demanded clock comparison is asked with room to spare ----

    /**
     * THE MARGIN, as a rewriting rule: every operator, both polarities.
     *
     * <p>A demanded atom is the proposition the QUERY asserts, so a demanded
     * FALSE is read off the assertion the negation makes: {@code (not (>= a
     * b))} strengthened is {@code (not (>= (+ a eps) b))}, which says
     * {@code a + eps < b}.</p>
     */
    @Test
    public void everyDemandedClockComparisonCarriesTheMargin() {
        Map<String, Long> clocks = Collections.singletonMap("clk_now", 5L);
        // Demanded true: the margin goes on the side that has to be cleared.
        assertEquals("(>= a (+ clk_now 5))",
                strengthened("(>= a clk_now)", clocks));
        assertEquals("(> a (+ clk_now 5))",
                strengthened("(> a clk_now)", clocks));
        assertEquals("(<= (+ a 5) clk_now)",
                strengthened("(<= a clk_now)", clocks));
        assertEquals("(< (+ a 5) clk_now)",
                strengthened("(< a clk_now)", clocks));
        // Demanded false: the same proposition, read through the negation.
        assertEquals("(not (>= (+ a 5) clk_now))",
                strengthened("(not (>= a clk_now))", clocks));
        assertEquals("(not (> (+ a 5) clk_now))",
                strengthened("(not (> a clk_now))", clocks));
        assertEquals("(not (<= a (+ clk_now 5)))",
                strengthened("(not (<= a clk_now))", clocks));
        assertEquals("(not (< a (+ clk_now 5)))",
                strengthened("(not (< a clk_now))", clocks));
        // Pushed through the connectives a conjunct is built from, and
        // through a double negation.
        assertEquals("(and (< (+ a 5) clk_now) (or (> b (+ clk_now 5))"
                        + " (not (>= (+ c 5) clk_now))))",
                strengthened("(and (< a clk_now) (or (> b clk_now)"
                        + " (not (>= c clk_now))))", clocks));
        assertEquals("(not (not (< (+ a 5) clk_now)))",
                strengthened("(not (not (< a clk_now)))", clocks));
        // An atom no clock cell reaches is not this rule's business.
        assertEquals("(< a b)", strengthened("(< a b)", clocks));
        assertEquals("(< M_COUNT 5)", strengthened("(< M_COUNT 5)", clocks));
        // THE JVM'S OWN COMPARE.  Two longs are compared with lcmp and
        // branched on, so the atom is (>= (ite ...) 0) -- read back as the
        // comparison the lowering says it is, and strengthened there.  The
        // margin on the 0 would have made it unsatisfiable.
        String compare = edu.uva.liftlab.graphchecker.smt
                .JavaPrimitiveSmtSemantics.integralCompareResult("1500",
                        "clk_now");
        assertEquals("(not (>= (+ 1500 5) clk_now))",
                strengthened("(not (>= " + compare + " 0))", clocks));
        assertEquals("(>= 1500 (+ clk_now 5))",
                strengthened("(>= " + compare + " 0)", clocks));
        assertEquals("the mirrored spelling states the same comparison: "
                        + "(<= 0 lcmp(a, b)) IS a >= b",
                "(>= 1500 (+ clk_now 5))",
                strengthened("(<= 0 " + compare + ")", clocks));
        // An ite that is NOT that compare decides no polarity for what is
        // under it, and its operands are not a millisecond count either.
        String branch = "(>= (ite (< clk_now 3) 1 0) 0)";
        assertEquals(branch, strengthened(branch, clocks));
        assertEquals("(= (ite (< clk_now 3) 1 0) 1)",
                strengthened("(= (ite (< clk_now 3) 1 0) 1)", clocks));
        // And the caller is told which atom it was, once per atom.
        assertEquals("the atom named is the one the rule stopped at",
                Collections.singletonList(branch),
                ClockMargin.strengthen(branch, clocks).unstrengthened);
        assertEquals("and under an = it is the comparison itself",
                Collections.singletonList("(< clk_now 3)"),
                ClockMargin.strengthen("(= (ite (< clk_now 3) 1 0) 1)",
                        clocks).unstrengthened);
        assertTrue("an atom the margin DID reach is not reported",
                ClockMargin.strengthen("(< a clk_now)", clocks)
                        .unstrengthened.isEmpty());
        // A MINUTE IN EACH CLOCK'S OWN TICKS: currentTimeMillis counts ms,
        // nanoTime ns (SOLR-18406's reservation); an atom comparing the two
        // has no one margin and is left alone, named.
        assertEquals(60_000L, ClockMargin.margin(1_000_000L));
        assertEquals(60_000_000_000L, ClockMargin.margin(1L));
        Map<String, Long> two = new LinkedHashMap<String, Long>();
        two.put("clk_ms", ClockMargin.margin(1_000_000L));
        two.put("clk_ns", ClockMargin.margin(1L));
        assertEquals("(< (+ clk_ms 60000000000) clk_ns)",
                ClockMargin.strengthen("(< clk_ms clk_ns)",
                        Collections.singletonMap("clk_ns",
                                ClockMargin.margin(1L))).text);
        assertEquals(Collections.singletonList("(< clk_ms clk_ns)"),
                ClockMargin.strengthen("(< clk_ms clk_ns)", two)
                        .unstrengthened);
    }

    private static String strengthened(String term,
                                       Map<String, Long> clocks) {
        return ClockMargin.strengthen(term, clocks).text;
    }

    /**
     * The same rule where it is spent: a flip over a clock, solved.
     *
     * <p>hdfs-11741 campaign #4's 35 refusals in one fixture -- the guard is
     * {@code expiryDate >= now} over a wall-clock literal, the flip asks for
     * the other arm, and the model has to clear the literal by the margin
     * rather than by the one millisecond z3 would otherwise answer with.</p>
     *
     * <p>THE INHERITED FLIP IS DEMANDED TOO, and the prefix around it is not.
     * The path a child is cut from exists only in the world its parent's
     * replay ran ({@link Corpus.World}), so the query re-asserts that flip --
     * and a flip over a clock is a flip over a clock whoever asked for it
     * first.  The decisions the parent's occurrence took BEFORE it, and the
     * flipped path's own prefix, are the recording's own arms and are asked
     * for exactly as recorded.</p>
     */
    @Test
    public void anInheritedClockFlipCarriesTheMarginAndItsPrefixDoesNot()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path margin = tree.newFolder("margin").toPath();
        Session clocked = new Session(margin, "s-seed");
        clocked.activation(TARGET, false);
        clocked.clock(TARGET, "CASE.NOW", "M_NOW", "1000");
        clocked.decision(TARGET, "Expiry#u15", 1, true,
                notBefore("1500", "M_NOW"));
        clocked.flush();
        scopeMap(margin, targetSite("REGION.target", "Throw#u30",
                "Expiry#u15"));
        Path marginOut = tree.newFolder("margin-out").toPath();
        Path marginWave = marginOut.resolve("obligations-0000");
        plan(margin, TARGET_SELECTOR, null,
                marginOut.resolve("results.jsonl"), marginWave, 0);
        List<Obligation> proposed = obligations(marginWave);
        assertEquals(1, proposed.size());
        Worker direct = solve(margin, marginWave, proposed.get(0), marginOut,
                "w0");
        assertEquals(detail(direct), Verdict.SAT_MODEL_READY, direct.verdict);
        assertTrue("the demanded atom carries the margin: " + query(direct),
                query(direct).contains("(not (>= (+ 1500 "
                        + ClockMargin.margin(1_000_000L) + ") clk_"));
        long owed = Long.parseLong(RowCodec.readJsonl(direct.directory
                .resolve(ObligationDir.FOCUSED_TASK)).get(0)
                .getAsJsonObject("clockDeltas").get("CASE.NOW")
                .getAsString());
        assertTrue("and the replay is owed a skew that clears the literal by "
                        + "it, not by one millisecond: " + owed,
                owed >= 1500L + ClockMargin.margin(1_000_000L) - 1000L);

        // An atom whose polarity no connective of the query resolves is
        // left exactly as it was, and named once.
        Path branched = tree.newFolder("margin-ite").toPath();
        Session other = new Session(branched, "s-seed");
        other.activation(TARGET, false);
        other.clock(TARGET, "CASE.NOW", "M_NOW", "1000");
        other.decision(TARGET, "Expiry#u15", 1, false,
                "(= (ite (< 1500 M_NOW) 1 0) 1)");
        other.flush();
        scopeMap(branched, targetSite("REGION.target", "Throw#u30",
                "Expiry#u15"));
        Path branchedOut = tree.newFolder("margin-ite-out").toPath();
        Path branchedWave = branchedOut.resolve("obligations-0000");
        plan(branched, TARGET_SELECTOR, null,
                branchedOut.resolve("results.jsonl"), branchedWave, 0);
        Worker asIs = solve(branched, branchedWave,
                obligations(branchedWave).get(0), branchedOut, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, asIs.verdict);
        assertFalse("no margin is invented for it: " + query(asIs),
                query(asIs).contains("(+ "));
        assertTrue("and the wave says which atom it could not reach",
                anyGap(asIs.directory, gap -> gap.kind()
                        == GapKind.ADMISSION_GAP
                        && gap.cls() == GapClass.DIAGNOSTIC
                        && ExploreCodec.EXPLORATION.equals(gap.sessionId())
                        && gap.detail().contains("clock margin")
                        && gap.detail().contains("(< 1500 clk_")));

        // The inherited flip.
        Path iteration = tree.newFolder("inherited-margin").toPath();
        // The recording: the rotation read its clock and took neither arm
        // the child was later held to, and the target never reached the
        // guard this obligation flips.
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, PRODUCER);
        seed.clock(PRODUCER, "CASE.NOW", "M_NOW", "1000");
        seed.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        seed.marker(TARGET, "CASE.OTHER", "M_OTHER", "false");
        seed.decision(PRODUCER, "Before#u3", 1, true,
                notBefore("200000", "M_NOW"));
        seed.decision(PRODUCER, "Rotate#u5", 1, false,
                notBefore("100000", "M_NOW"));
        seed.decision(TARGET, "Guard#u8", 1, false, "M_MARKER");
        seed.flush();
        // The child: the rotation's compare flipped, and on THAT path the
        // target reached a guard the seed never did.
        Session child = new Session(iteration, "s-inherit");
        child.activation(PRODUCER, true);
        child.activation(TARGET, false);
        child.clock(PRODUCER, "CASE.NOW", "M_NOW", "1000");
        child.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        child.marker(TARGET, "CASE.OTHER", "M_OTHER", "false");
        child.decision(PRODUCER, "Before#u3", 1, true,
                notBefore("200000", "M_NOW"));
        child.decision(PRODUCER, "Rotate#u5", 1, true,
                notBefore("100000", "M_NOW"));
        child.decision(TARGET, "Guard#u8", 1, false, "M_MARKER");
        // Its predicate reads the clock too, so the inherited flip shares
        // it (FlipQuery#cone).
        child.decision(TARGET, "Deeper#u9", 1, false, "(and M_OTHER "
                + notBefore("300000", "M_NOW") + ")");
        child.answered(ObligationResult.of("OBL.inherit", Verdict.ADMITTED,
                "s-inherit", "the focused prefix reproduced"));
        child.flush();
        worker(iteration, "obligations-0000", "ob-inherit", "OBL.inherit",
                "s-inherit", PRODUCER, "Rotate#u5", NONE,
                Collections.singletonMap("CASE.NOW", "0"));
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8", "Deeper#u9"));

        Path out = tree.newFolder("inherited-margin-out").toPath();
        Path wave = out.resolve("obligations-0001");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 1);
        Obligation deeper = named(obligations(wave), "Deeper#u9");
        assertNotNull("the arm only the child's path offers is proposed",
                deeper);
        assertEquals("and it is cut from that child's path",
                Corpus.pathId("s-inherit", TARGET), deeper.pathId());
        Worker worker = solve(iteration, wave, deeper, out, "w1");
        assertEquals(detail(worker), Verdict.SAT_MODEL_READY, worker.verdict);
        String query = query(worker);
        assertTrue("the flip the child inherited is demanded, so it carries "
                        + "the margin: " + query,
                query.contains("(>= 100000 (+ clk_CASE_NOW_s_inherit "
                        + ClockMargin.margin(1_000_000L) + "))"));
        assertTrue("while the decision that occurrence took BEFORE it is the "
                        + "recording's own arm, asked for as recorded: "
                        + query,
                query.contains(notBefore("200000",
                        "clk_CASE_NOW_s_inherit")));
        assertFalse("nothing is strengthened around it",
                query.contains("(+ 200000"));
        JsonObject focus = RowCodec.readJsonl(worker.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        long skew = Long.parseLong(focus.getAsJsonObject("clockDeltas")
                .get("CASE.NOW").getAsString());
        assertTrue("and the model clears the inherited literal by the margin"
                        + " too: " + skew,
                skew + 1000L <= 100000L - ClockMargin.margin(1_000_000L));
    }

    // ---- (6a) a flip only another writer takes plants that pairing -----

    /**
     * A model that takes the other arm only through which writer a read
     * observes plants that pairing: the focus row states it, and the replay
     * is held to it by CONFIRM's rows (SOLR-18413 r5: 67 such focused
     * replays ran the world they were cut from again, each NOT_ADMITTED).
     * The read is the VM's guarded read, joined to the write it observed: a
     * read another writer could have answered is its own symbol, or no
     * choice could move it.
     */
    @Test
    public void aFlipOnlyAnotherWriterTakesPlantsThatPairing()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = twoWriters("paired-world", VM_LOOKUP, null);
        Path out = tree.newFolder("paired-world-out").toPath();
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 0);
        Obligation lookup = named(obligations(wave), "Lookup#u8");
        assertNotNull(lookup);
        Worker worker = solve(iteration, wave, lookup, out, "w0");
        assertTrue("the other writer is the flip's only way: "
                + query(worker), query(worker).contains("wchoice_"));
        assertEquals(detail(worker), Verdict.SAT_MODEL_READY, worker.verdict);
        assertTrue(detail(worker),
                detail(worker).contains("1 planted pairing(s)"));
        JsonObject pairings = RowCodec.readJsonl(worker.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0)
                .getAsJsonObject("pairings");
        String reader = Confirmation.id(LOOKED_UP);
        assertEquals(pairings.toString(), 1, pairings.size());
        String writer = pairings.get(reader).getAsString();
        assertFalse("another writer than the one the read observed",
                writer.equals(Confirmation.id(STORED)));
        List<String> state = new ArrayList<String>();
        for (JsonObject edge : RowCodec.readJsonl(
                worker.directory.resolve(Confirmation.FILE))) {
            if ("STATE".equals(edge.get("kind").getAsString())) {
                state.add(edge.get("reader").getAsString() + " -> "
                        + edge.get("writer").getAsString());
            }
        }
        assertEquals(Collections.singletonList(reader + " -> " + writer),
                state);
    }

    /**
     * A writer whose store is of another sort than the read (an array
     * cell's whole array, a narrower cell) delivers nothing the read could
     * be: no model takes it, so a flip only it could take plants nothing.
     */
    @Test
    public void anArmOfAnotherSortIsNoModelsChoice() throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = twoWriters("other-sort", VM_LOOKUP, null, "Z");
        Path out = tree.newFolder("other-sort-out").toPath();
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 0);
        Worker worker = solve(iteration, wave,
                named(obligations(wave), "Lookup#u8"), out, "w0");
        assertFalse(detail(worker),
                detail(worker).contains("planted pairing"));
        assertTrue(query(worker), query(worker).matches(
                "(?s).*\\(not wchoice_\\S+\\).*"));
    }

    /**
     * A model that moves a writer choice is asked again with every choice
     * held to the recorded writer; one that then plants a root is the one
     * run, and no pairing is.  The nearest-world objective keeps the root
     * at its recording and lets the other writer take the arm; held, only
     * the root can.
     */
    @Test
    public void aModelHeldToTheRecordedWriterPlantsTheRootInstead()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = twoWriters("held-writer",
                "(or (= M_READ_KEY 2) (= M_LIMIT 5))", "0");
        Path out = tree.newFolder("held-writer-out").toPath();
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 0);
        Worker worker = solve(iteration, wave,
                named(obligations(wave), "Lookup#u8"), out, "w0");
        assertEquals(detail(worker), Verdict.SAT_MODEL_READY,
                worker.verdict);
        assertEquals("5", worker.obligation.rootAssignments()
                .get("CASE.LIMIT"));
        assertTrue("the query run is the one held to the recording: "
                + query(worker), query(worker).matches(
                "(?s).*\\(assert wchoice_\\S+\\)\\n\\(check-sat\\).*"));
    }

    /**
     * One question, one answer.  An obligation's id drifts as sessions land
     * (its dependence's factor grows); its question -- the query as asked
     * and all its replay is given -- does not, and a solver answers a
     * question a worker settled with that answer (SOLR-18413 r5: 185
     * questions asked 717 times).  A question only asked, whose replay
     * decided nothing, settles nothing.
     */
    @Test
    public void aSettledQuestionIsAnsweredWithoutItsSolver()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = twoWriters("asked-once", "(= M_READ_KEY 2)", null);
        Path out = tree.newFolder("asked-once-out").toPath();
        Path wave0 = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null, out.resolve("results.jsonl"),
                wave0, 0);
        Obligation lookup = named(obligations(wave0), "Lookup#u8");
        Worker first = solve(iteration, wave0, lookup, out, "w0");
        String asked = new String(Files.readAllBytes(first.directory
                .resolve(ObligationDir.QUESTION_ASKED)),
                StandardCharsets.UTF_8).trim();
        assertEquals("the question's first half is the flip a round holds "
                        + "in flight (Frontier#inFlight)",
                ObligationFactory.flip(lookup.taskId(), lookup.pathId(),
                        lookup.siteId(), lookup.ordinal(),
                        lookup.flippedOutcome()),
                asked.substring(0, asked.indexOf(':')));
        // Asked by a worker whose replay was killed: nothing settled.  And
        // an ADMITTED answer whose session left the corpus stands on
        // nothing.
        answer(iteration, "OB.killed", ObligationDir.QUESTION_ASKED, asked,
                Verdict.NOT_ADMITTED, "",
                "replay exceeded replay_timeout_s=2400");
        answer(iteration, "OB.admitted", ObligationDir.QUESTION, asked,
                Verdict.ADMITTED, "S.gone", "flipped");
        Worker again = solve(iteration, wave0, lookup, out, "w1");
        assertEquals(detail(again), Verdict.SAT_MODEL_READY, again.verdict);
        // Settled under an id that has since drifted: its answer, no solver.
        answer(iteration, "OB.drifted", ObligationDir.QUESTION, asked,
                Verdict.NOT_ADMITTED, "", "refused");
        Worker settled = solve(iteration, wave0, lookup, out, "w2");
        assertEquals(Verdict.NOT_ADMITTED, settled.verdict);
        assertEquals(detail(settled), "question " + asked + " was settled "
                + "NOT_ADMITTED by obligation OB.drifted, which asked the "
                + "same flip and query of the same world, focus, factor, "
                + "seed session, declared occurrence and plan generation: "
                + "refused", detail(settled));
        assertFalse("a reuse settles nothing itself: its source does",
                Files.exists(settled.directory.resolve(
                        ObligationDir.QUESTION)));
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
     * An ADMITTED replay settles its flip whatever id the arm has since
     * ({@link Frontier#consume}): sessions landing after it move the
     * dependence, and the same flip of the same path would plant the same
     * world again (solr-adhoc-07 IB1: 59 answered flips re-keyed, 25 of them
     * ADMITTED).  A NOT_ADMITTED or UNSAT answer under another id stays
     * owed: it answered another question.
     */
    @Test
    public void anAdmittedFlipIsSettledUnderAnyId() throws Exception {
        for (Verdict verdict : new Verdict[] {Verdict.ADMITTED,
                Verdict.NOT_ADMITTED, Verdict.UNSAT}) {
            Path iteration = twoWriters("flip-" + verdict, "(= M_READ_KEY 2)",
                    null);
            Path out = tree.newFolder("flip-" + verdict + "-out").toPath();
            Path wave0 = out.resolve("obligations-0000");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave0, 0);
            Obligation lookup = named(obligations(wave0), "Lookup#u8");
            answer(iteration, "OB.rekeyed", ObligationDir.QUESTION,
                    ObligationFactory.flip(lookup.taskId(), lookup.pathId(),
                            lookup.siteId(), lookup.ordinal(),
                            lookup.flippedOutcome()) + ":content", verdict,
                    "", "answered");
            Path wave1 = out.resolve("obligations-0001");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave1, 1);
            assertEquals(verdict.name(), verdict != Verdict.ADMITTED,
                    named(obligations(wave1), "Lookup#u8") != null);
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

    /**
     * A read of a version no write row states (a store outside every
     * activation, named UNATTRIBUTED_STORE) is, in a flip query, its own
     * symbol wherever a write row states its location -- the run's own
     * choice holds it to what it read, beside each eligible writer -- so a
     * flip can move it as it moves a read whose writer is known
     * (hdfs-adhoc-39 OA4: the append's read of BlockInfo.uc saw the
     * completion, stored in no activation, and the VM's guarded read
     * lowered to the null it returned: the open arm's flip had no
     * variable).  The same read of a location no row writes stays the
     * value it returned.
     */
    @Test
    public void aReadOfAStoreOutsideEveryActivationIsMovedLikeAnyRead()
            throws Exception {
        Assume.assumeTrue(z3Available());
        for (boolean written : new boolean[] {true, false}) {
            String name = "outside-" + written;
            Path iteration = tree.newFolder(name).toPath();
            OccurrenceAddress again = occurrence("hdfs-case/dn0",
                    "REGION.addkeys", CausalContext.of(Role.of("KEY_UPDATE"),
                            "", 2), "o.a.h.h.s.d.BPServiceActor#offerService#41");
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            seed.activation(again, false, true, "fixture#key-updater");
            seed.constant("e.2", "2");
            if (written) {
                seed.write(at(again, Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true),
                        "BlockTokenSecretManager#addKeys#12"), KEY_ID, 6L,
                        "e.2");
            }
            // The lookup saw version 9, which no row of the session wrote.
            seed.read(LOOKED_UP, KEY_ID, 9L, "M_READ_KEY", "1");
            // As the VM states it: an exact read of the value it returned.
            JsonObject read = readNode(KEY_ID, 9L, "I", literal(1));
            read.addProperty("observedExact", true);
            seed.expression(VM_LOOKUP, binary("==", read, literal(2)));
            seed.decision(TARGET, "Lookup#u8", 1, false, VM_LOOKUP);
            seed.flush();
            scopeMap(iteration,
                    targetSite("REGION.target", "Throw#u30", "Lookup#u8"),
                    scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                            "BlockTokenSecretManager#u12",
                            "BlockTokenSecretManager#addKeys",
                            "<example.Keys: int value>",
                            "<example.Manager: example.Keys allKeys>", ""));
            Path out = tree.newFolder(name + "-out").toPath();
            Path wave = out.resolve("obligations-0000");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave, 0);
            Worker worker = solve(iteration, wave,
                    named(obligations(wave), "Lookup#u8"), out, "w0");
            String detail = name + ": " + detail(worker) + "\n"
                    + query(worker);
            if (written) {
                assertEquals(detail, Verdict.SAT_MODEL_READY,
                        worker.verdict);
                assertTrue(detail, query(worker).contains("wchoice_"));
                assertTrue(detail, detail(worker).contains(
                        "1 planted pairing(s)"));
            } else {
                // No writer to choose: the read is the value it returned,
                // and the flip has no variable of its own -- refused at the
                // arm, for a version no row wrote is the same in every
                // world under its key.
                assertEquals(detail, Verdict.NOT_ADMITTED, worker.verdict);
                assertTrue(detail, detail(worker).startsWith(
                        ObligationResult.ARM_REFUSED + ": the query was "
                                + "refused: ADMISSION_GAP"));
            }
        }
    }

    /**
     * One writer choice binds every read one occurrence made of a location
     * (IDENTITY §4), so where its reads saw two writes, or a version no row
     * wrote, no writer's choice is the run: the run's own choice holds each
     * read to the value it read, as COMPOSE's observed arm does, and is the
     * recorded pairing, never the two reads forced equal.  A model moving
     * both to the other writer plants that pairing for each; a writer whose
     * store is of another sort than a read is no choice, the recorded one
     * included once the run's choice is (its row's value holds that read),
     * so the model takes the run and plants nothing.
     */
    @Test
    public void readsNoOneWriterExplainsKeepTheRunsOwnChoice()
            throws Exception {
        Assume.assumeTrue(z3Available());
        // the lookup again's version, the second writer's type, the
        // flipped term, the pairings the model plants
        Object[][] table = {
                {6L, "I", "(and (= M_READ_KEY 2) (= M_READ_AGAIN 2))", 2},
                {9L, "I", "(and (= M_READ_KEY 2) (= M_READ_AGAIN 2))", 2},
                {6L, "Z", "(and (= M_READ_AGAIN 2) (= M_READ_KEY 1))", 0},
        };
        for (Object[] row : table) {
            String name = "two-writes-" + row[0] + row[1];
            Path iteration = twoWriters(name, (String) row[2], null,
                    (String) row[1], (Long) row[0]);
            Path out = tree.newFolder(name + "-out").toPath();
            Path wave = out.resolve("obligations-0000");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave, 0);
            Worker worker = solve(iteration, wave,
                    named(obligations(wave), "Lookup#u8"), out, "w0");
            String detail = name + ": " + detail(worker) + "\n"
                    + query(worker);
            assertTrue(detail, query(worker).matches(
                    "(?s).*\\(=> wchoice_\\S+_run \\(= \\S+ 1\\)\\).*"));
            if ((Integer) row[3] > 0) {
                assertEquals(detail, Verdict.SAT_MODEL_READY,
                        worker.verdict);
                assertTrue(detail, detail(worker).contains(row[3]
                        + " planted pairing(s)"));
            } else {
                assertTrue(detail, query(worker).matches(
                        "(?s).*\\(not wchoice_\\S+\\).*"));
                assertFalse(detail, detail(worker).contains(
                        "planted pairing"));
            }
        }
    }

    /**
     * A flip is asked only where its own predicate reaches a variable: a
     * movable read a PREFIX decision names binds nothing the flipped
     * predicate rests on, and a predicate over a read only one writer wrote
     * is the recording's arm whatever the prefix does -- by the owner's
     * ruling (only SAT or UNSAT; a concrete value is a constant), UNSAT on
     * this path, named NOT_FLIPPABLE.  A read of a version no row wrote keeps
     * the refusal ({@link #aReadOfAStoreOutsideEveryActivationIsMovedLikeAnyRead}).
     */
    @Test
    public void aFlipWhosePredicateReachesNoVariableIsNotAsked()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("prefix-only").toPath();
        OccurrenceAddress again = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.of("KEY_UPDATE"), "",
                        2), "o.a.h.h.s.d.BPServiceActor#offerService#41");
        LocationId other = LocationId.of(LocationKind.INSTANCE, "21", "41");
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, WRITER);
        seed.activation(again, false, true, "fixture#key-updater");
        seed.constant("e.1", "1");
        seed.constant("e.2", "2");
        seed.constant("e.3", "3");
        seed.write(STORED, KEY_ID, 5L, "e.1");
        seed.write(at(again, Endpoint.stateSite("BlockTokenSecretManager",
                "addKeys", 12, true), "BlockTokenSecretManager#addKeys#12"),
                KEY_ID, 6L, "e.2");
        seed.write(STORED, other, 7L, "e.3");
        seed.read(LOOKED_UP, KEY_ID, 5L, "M_READ_KEY", "1");
        seed.read(at(TARGET, Endpoint.stateSite("BlockTokenSecretManager",
                "retrieveDataEncryptionKey", 9, false),
                "BlockTokenSecretManager#retrieveDataEncryptionKey#9"),
                other, 7L, "M_OTHER", "3");
        seed.expression(VM_LOOKUP, binary("==", readNode(other, 7L, "I",
                literal(3)), literal(4)));
        seed.decision(TARGET, "Prefix#u7", 1, false, "(= M_READ_KEY 2)");
        seed.decision(TARGET, "Lookup#u8", 1, false, VM_LOOKUP);
        seed.flush();
        scopeMap(iteration,
                targetSite("REGION.target", "Throw#u30", "Lookup#u8"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""));
        Path out = tree.newFolder("prefix-only-out").toPath();
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 0);
        Worker worker = solve(iteration, wave,
                named(obligations(wave), "Lookup#u8"), out, "w0");
        assertEquals(detail(worker), Verdict.UNSAT, worker.verdict);
        assertTrue(detail(worker), detail(worker).contains(
                "NOT_FLIPPABLE:Lookup#u8#1"));
    }

    // ---- (6b) a handoff nobody can answer moves only with its own run --

    /**
     * A handoff that is not a CONTROL is held to what its own run's producer
     * computed it from.
     *
     * <p>An obligation's answers are applied at the attaches of the occurrence
     * it flips and nowhere else, so another run's arrival is freedom the
     * replay does not have: the model picks one of the recorded arrivals,
     * nothing plants it, and the replay receives whatever its own run
     * produces.  hdfs-11741 campaign #4 has three of those -- the block-key
     * expiry date of a balance-block delivery, free over an OR of 20
     * arrivals, answered with the minimum and 105291 to 203751ms below what
     * the replay then got.  Its own run's arm moves only with roots and
     * clocks the replay plants: SOLR-18413's leader parses a routing rule's
     * expiry in its state watcher, not in the update that checks it, and the
     * expiry is the Overseer's clock plus the timeout.  The handoff of the
     * occurrence this obligation DOES flip is still answered out of its
     * family (case 2).</p>
     */
    @Test
    public void aHandoffThisObligationCannotAnswerMovesOnlyWithItsOwnRun()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("pinned-handoff").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, WRITER, PRODUCER);
        seed.integral(PRODUCER, "CASE.SERIAL", "M_SERIAL", "119992", null,
                null);
        seed.constant("e.119992", "119992");
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.export(ROTATED, "e.119992", 11L, "119992");
        // The delivery is received by addKeys -- a member of the target's
        // factor, and NOT the occurrence the flip is about.
        seed.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        seed.write(STORED, ALL_KEYS, 5L, "e.stored");
        seed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        seed.decision(TARGET, "Lookup#u8", 1, false, "(= M_READ_KEY 119995)");
        seed.flush();
        // A second recording of the same interaction delivered 119995.
        Session rotated = new Session(iteration, "s-rot");
        rotated.activation(PRODUCER, true);
        rotated.activations(false, WRITER, TARGET);
        rotated.answered(ObligationResult.of("OBL.s-rot", Verdict.ADMITTED,
                "s-rot", "the focused prefix reproduced"));
        rotated.root(PRODUCER, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "119995", null, null, false);
        rotated.decision(PRODUCER, "Rotate#u3", 1, true, "(> M_SERIAL 0)");
        rotated.constant("e.119995", "119995");
        rotated.export(ROTATED, "e.119995", 12L, "119995");
        rotated.attach(DELIVERED, "M_HOFF_KEY", "119995", ROTATED);
        rotated.flush();
        scopeMap(iteration,
                targetSite("REGION.target", "Throw#u30", "Lookup#u8"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""),
                scopeSite(StaticScopeMap.EXPORT_SITE, "REGION.rotate",
                        "PBHelper#convert#9", "PBHelper#convert", "", "",
                        "XCH.resp.block-key-id", "Rotate#u3"));
        Path out = tree.newFolder("pinned-handoff-out").toPath();
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 0);
        Obligation lookup = named(obligations(wave), "Lookup#u8");
        assertNotNull(lookup);
        Worker worker = solve(iteration, wave, lookup, out, "w0");
        String query = query(worker);
        List<String> aboutTheDelivery = new ArrayList<String>();
        for (String line : query.split("\n")) {
            if (line.startsWith("(assert") && line.contains("vH_")) {
                aboutTheDelivery.add(line);
            }
        }
        assertEquals("one assertion binds the delivery, and it is the arm of "
                        + "this path's own run: " + aboutTheDelivery, 1,
                aboutTheDelivery.size() - countOf(aboutTheDelivery,
                        "wchoice_"));
        boolean own = false;
        for (String line : aboutTheDelivery) {
            if (line.contains("wchoice_")) continue;
            own = line.matches(".*\\(= vH_\\S+ 119992\\).*");
            assertFalse("no other recorded arrival of that slot binds it: "
                    + line, line.contains("119995"));
        }
        assertTrue("and what it binds it to is what that run's producer "
                + "sent: " + aboutTheDelivery, own);
        assertEquals("so a flip that needs another delivery is refused, "
                        + "rather than answered with a value nothing would "
                        + "plant", Verdict.UNSAT, worker.verdict);

        // The same delivery, sent as the producer's clock reading: its own
        // run's arm moves with that clock, which the replay plants.
        Path clocked = tree.newFolder("own-run-clock").toPath();
        Session timed = new Session(clocked, "s-seed");
        timed.activations(false, TARGET, WRITER, PRODUCER);
        timed.clock(PRODUCER, "CASE.NOW", "M_NOW", "119992");
        timed.symbolic("e.now", "M_NOW");
        timed.symbolic("e.stored", "M_HOFF_KEY");
        timed.export(ROTATED, "e.now", 11L, "119992");
        timed.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        timed.write(STORED, ALL_KEYS, 5L, "e.stored");
        timed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        timed.decision(TARGET, "Lookup#u8", 1, false, "(= M_READ_KEY 119995)");
        timed.flush();
        scopeMap(clocked,
                targetSite("REGION.target", "Throw#u30", "Lookup#u8"),
                scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""),
                scopeSite(StaticScopeMap.EXPORT_SITE, "REGION.rotate",
                        "PBHelper#convert#9", "PBHelper#convert", "", "",
                        "XCH.resp.block-key-id", "Rotate#u3"));
        Path timedOut = tree.newFolder("own-run-clock-out").toPath();
        Path timedWave = timedOut.resolve("obligations-0000");
        plan(clocked, TARGET_SELECTOR, null, timedOut.resolve("results.jsonl"),
                timedWave, 0);
        Worker moved = solve(clocked, timedWave,
                named(obligations(timedWave), "Lookup#u8"), timedOut, "w0");
        assertEquals(detail(moved), Verdict.SAT_MODEL_READY, moved.verdict);
        JsonObject focus = RowCodec.readJsonl(moved.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        assertEquals("the flip moves the producer's clock by what the "
                        + "delivery needs: " + focus, "3",
                focus.getAsJsonObject("clockDeltas").get("CASE.NOW")
                        .getAsString());
        assertEquals("and answers nothing at the delivery it does not "
                + "flip: " + focus, 0, focus.getAsJsonObject("answers")
                .size());
    }

    /** How many of these lines mention this name. */
    private static int countOf(List<String> lines, String name) {
        int found = 0;
        for (String line : lines) {
            if (line.contains(name)) found++;
        }
        return found;
    }

    /**
     * THE CONE (FlipQuery#cone): a flip query asks only the conjuncts its
     * flipped predicate shares a name with.  A prefix decision over a fault
     * marker the expiry never reads is dropped, so a z3 that cannot decide
     * it (here: one that answers unknown whenever the marker is in the
     * query) still decides the flip, and the marker is neither read back
     * nor planted (SOLR-18413 b616891a77d1afb8: ZkStateReader's map
     * bookkeeping left z3 "incomplete (theory array)" on a clock flip it
     * shared nothing with).
     */
    @Test
    public void aFlipQueryAsksOnlyWhatItsPredicateShares() throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("cone").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.clock(TARGET, "CASE.NOW", "M_NOW", "1000");
        seed.marker(TARGET, "CASE.HARD", "M_HARD", "false");
        seed.decision(TARGET, "Hard#u7", 1, false, "M_HARD");
        seed.decision(TARGET, "Expiry#u15", 1, true,
                notBefore("200000", "M_NOW"));
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Expiry#u15"));
        Path out = tree.newFolder("cone-out").toPath();
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 0);
        Path z3 = out.resolve("z3-undecided-on-the-marker.sh");
        Files.write(z3, Arrays.asList("#!/bin/bash",
                "input=$(cat)",
                "case $input in",
                "  *HARD*) echo unknown;"
                        + " echo '(:reason-unknown \"incomplete\")' ;;",
                "  *) printf '%s\\n' \"$input\" | exec z3 \"$@\" ;;",
                "esac"), StandardCharsets.UTF_8);
        assertTrue(z3.toFile().setExecutable(true));
        Path worker = out.resolve("w0");
        ObligationSolverMain.solve(Corpus.read(iteration, null), iteration,
                wave.resolve("obligations.jsonl"),
                named(obligations(wave), "Expiry#u15").obligationId(),
                worker, z3, 10_000L, 1152, null);
        String query = queryText(worker);
        assertFalse("the marker's decision shares nothing with the expiry: "
                + query, query.contains("HARD"));
        assertEquals(query, Verdict.SAT_MODEL_READY, RowCodec.readAll(
                worker.resolve("obligation_result.jsonl"),
                RowCodec::readObligationResult).get(0).verdict());
        JsonObject focus = RowCodec.readJsonl(worker.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        assertTrue("the clock moves: " + focus, focus.getAsJsonObject(
                "clockDeltas").has("CASE.NOW"));
        assertFalse("and the marker outside the cone is not planted: "
                + focus, focus.getAsJsonObject("rootAssignments")
                .has("CASE.HARD"));
    }

    /**
     * The cone's split and closure (FlipQuery#conjuncts, #cone): {@code
     * (and)}, {@code (not (not))} and {@code (not (or))} split; a
     * conjunct naming a container definition shares what that definition
     * reaches, never what only reaches it; a preamble function
     * ({@code assoc_has}) shares nothing; a conjunct naming no variable or
     * declaration is kept.
     */
    @Test
    public void aConeKeepsWhatAContainerDefinitionShares() {
        assertEquals(Arrays.asList("(< x 3)", "(not (= j 1))", "(= k x)"),
                FlipQuery.conjuncts("(and (< x 3) (not (or (= j 1) "
                        + "(not (not (not (= k x)))))))"));
        Map<String, String> declarations = new LinkedHashMap<String, String>();
        declarations.put("c1",
                "(define-fun c1 () AssocState (assoc_put c0 k x))");
        declarations.put("c2",
                "(define-fun c2 () AssocState (assoc_put c3 j x))");
        declarations.put("c0", "(declare-fun c0 () AssocState)");
        declarations.put("c3", "(declare-fun c3 () AssocState)");
        List<String> conjuncts = Arrays.asList("(< x 3)",
                "(assoc_has c1 7)", "(= k 2)", "(= j 1)",
                "(assoc_has c3 7)", "(= \"a\" \"a\")");
        Set<String> names = new LinkedHashSet<String>();
        boolean[] kept = FlipQuery.cone(conjuncts, "(< x 3)",
                new LinkedHashSet<String>(Arrays.asList("x", "k", "j")),
                declarations, names);
        assertEquals("c1 reaches x, so its conjunct joins, and k with it; "
                        + "c2 reaches x too, but nothing names c2, so "
                        + "neither j nor c3 joins: " + names,
                "[true, true, true, false, false, true]",
                Arrays.toString(kept));
        assertEquals("[x, c1, c0, k]", names.toString());
    }

    // ---- (7) a clock moves forward only ------------------------------

    /**
     * The floor of a flip query's clock is what that session READ.
     *
     * <p>Not 0: exploration asks for a run that lasted longer or a node
     * whose clock is ahead, and a clock turned back to 1970 is no run --
     * the replay is handed {@code model - reading} and adds it to the
     * instant it reads for itself, so a model below the reading tells it to
     * read an instant its own execution had already passed.  The reading is
     * the one the session the path was CUT FROM states, which is the world
     * that session ran in: its mint recorded what it used, plant and
     * all.</p>
     */
    @Test
    public void aFlipQueryFloorsEveryClockAtTheReadingItWasCutFrom()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("clock-floor").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.clock(TARGET, "CASE.NOW", "M_NOW", "1000");
        seed.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        seed.marker(TARGET, "CASE.OTHER", "M_OTHER", "false");
        seed.decision(TARGET, "Expiry#u15", 1, true,
                notBefore("200000", "M_NOW"));
        seed.decision(TARGET, "Guard#u8", 1, false, "M_MARKER");
        seed.flush();
        // The child ran in a world that had already moved this clock: its
        // own mint states 5000, which is the seed's 1000 plus the 4000ms
        // its obligation asked for, because a mint plants the skew and
        // records what it then read.
        Session child = new Session(iteration, "s-later");
        child.activation(TARGET, true);
        child.clock(TARGET, "CASE.NOW", "M_NOW", "5000");
        child.marker(TARGET, "CASE.MARKER", "M_MARKER", "false");
        child.marker(TARGET, "CASE.OTHER", "M_OTHER", "false");
        child.decision(TARGET, "Expiry#u15", 1, true,
                notBefore("200000", "M_NOW"));
        child.decision(TARGET, "Guard#u8", 1, false, "M_MARKER");
        // Its predicate reads the clock too, so the clock's domain is in
        // its cone (FlipQuery#cone).
        child.decision(TARGET, "Deeper#u9", 1, false, "(and M_OTHER "
                + notBefore("300000", "M_NOW") + ")");
        child.answered(ObligationResult.of("OBL.later", Verdict.ADMITTED,
                "s-later", "the focused prefix reproduced"));
        child.flush();
        worker(iteration, "obligations-0000", "ob-later", "OBL.later",
                "s-later", TARGET, "Expiry#u15", NONE,
                Collections.singletonMap("CASE.NOW", "4000"));
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8", "Deeper#u9"));
        Path out = tree.newFolder("clock-floor-out").toPath();
        Path wave = out.resolve("obligations-0001");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 1);
        Obligation deeper = named(obligations(wave), "Deeper#u9");
        assertNotNull("the arm only the child's path offers is proposed",
                deeper);
        Worker worker = solve(iteration, wave, deeper, out, "w1");
        assertEquals(detail(worker), Verdict.SAT_MODEL_READY,
                worker.verdict);
        String query = query(worker);
        // FLOOR AND CEILING, both from THIS session's reading: 5000, and
        // 5000 + the stated 30-day window.  A ceiling of Long.MAX is not a
        // ceiling -- it lets a model satisfy "this expired" by pushing the
        // clock close enough to the top that the workload's own
        // `clock + interval` overflows to a negative instant, which the
        // replay then ADMITS (hdfs-11741 campaign #5b, obligation
        // 5ad106c42fcf45f6).
        assertTrue("the cell is floored at what THIS session read, not at "
                        + "0, and ceilinged a window above it: " + query,
                query.contains("(assert (>= clk_CASE_NOW_s_later 5000))")
                        && query.contains("(assert (<= clk_CASE_NOW_s_later "
                        + "2592005000))"));
        assertFalse("so the Java long ceiling is no longer the domain: "
                        + query,
                query.contains("clk_CASE_NOW_s_later 9223372036854775807"));
        assertFalse("and the seed's own earlier reading is not the floor",
                query.contains("clk_CASE_NOW_s_later 1000)"));
        // The scan's own compare holds it below 200000 and nothing else
        // bounds it, so a floor of 0 would let the model answer 1970.
        JsonObject focus = RowCodec.readJsonl(worker.directory.resolve(
                ObligationDir.FOCUSED_TASK)).get(0);
        long skew = Long.parseLong(focus.getAsJsonObject("clockDeltas")
                .get("CASE.NOW").getAsString());
        assertTrue("so no replay is owed a NEGATIVE skew: " + skew,
                skew >= 0L);

        // And a flip that needs the clock EARLIER than its session read it
        // is refused: the floor talking.
        {
            Path back = tree.newFolder("clock-back").toPath();
            Session only = new Session(back, "s-seed");
            only.activation(TARGET, false);
            only.clock(TARGET, "CASE.NOW", "M_NOW", "5000");
            only.decision(TARGET, "Early#u7", 1, false,
                    notBefore("4000", "M_NOW"));
            only.flush();
            scopeMap(back, targetSite("REGION.target", "Throw#u30",
                    "Early#u7"));
            Path backOut = tree.newFolder("clock-back-out").toPath();
            Path backWave = backOut.resolve("obligations-0000");
            plan(back, TARGET_SELECTOR, null,
                    backOut.resolve("results.jsonl"), backWave, 0);
            Worker refused = solve(back, backWave,
                    obligations(backWave).get(0), backOut, "w0");
            assertEquals("4000 >= now needs a clock this execution had "
                            + "already passed", Verdict.UNSAT,
                    refused.verdict);
        }

        // And one clock of one node runs forward from cell to cell, as
        // COMPOSE orders it: moving the earlier reading past 10000 moves the
        // later one with it, which its own guard keeps under 6000 -- no
        // model jumps the clock forward and back (hdfs-11741 L1).
        {
            Path order = tree.newFolder("clock-order").toPath();
            Session only = new Session(order, "s-seed");
            only.activation(TARGET, false);
            only.clock(TARGET, "CASE.NOW", "M_NOW", "5000");
            only.clock(TARGET, "CASE.LATER", "M_LATER", "5004");
            only.decision(TARGET, "Late#u6", 1, true,
                    notBefore("6000", "M_LATER"));
            only.decision(TARGET, "Now#u7", 1, true,
                    notBefore("10000", "M_NOW"));
            only.flush();
            scopeMap(order, targetSite("REGION.target", "Throw#u30",
                    "Now#u7"));
            Path orderOut = tree.newFolder("clock-order-out").toPath();
            Path orderWave = orderOut.resolve("obligations-0000");
            plan(order, TARGET_SELECTOR, null,
                    orderOut.resolve("results.jsonl"), orderWave, 0);
            Worker ordered = solve(order, orderWave,
                    named(obligations(orderWave), "Now#u7"), orderOut, "w0");
            assertEquals("the later reading may not fall back behind the "
                    + "earlier one: " + detail(ordered), Verdict.UNSAT,
                    ordered.verdict);
        }
    }

    /**
     * {@code expiryDate >= now} as the JVM decides it: {@code lcmp} and a
     * branch on its result, which is the shape every one of hdfs-11741's
     * clock guards is published in.
     */
    private static String notBefore(String left, String right) {
        return "(>= " + edu.uva.liftlab.graphchecker.smt
                .JavaPrimitiveSmtSemantics.integralCompareResult(left, right)
                + " 0)";
    }

    /** Why a worker said what it said, for a failure message. */
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
     * WHAT COMPOSE KEEPS, EXPLORE DEMANDS (compose.RestsOn): a handoff a kept
     * decision of an occurrence some join reaches names is demanded, and its
     * producer planned, whoever received it (hdfs-11741: the balancer's
     * KeyManager decides on the expiry dates of nn0's updateBlockKeys@1
     * response, whose handler no session ran).  Per row: whether nn0's
     * handler, the producer of the value {@code keys} decided on, is planned.
     */
    @Test
    public void whatComposeKeepsIsWhatExploreDemands() throws Exception {
        Object[][] rows = {
                // The anchor reads what keys wrote after deciding on v_H.
                {"kept", true},
                // keys decided on nothing that moves.
                {"unmoved", false},
                // keys decided on v_H only after its write: no prefix of it.
                {"after", false},
                // The anchor's fatal reads nothing keys wrote, but its own
                // prefix does: only the path's closure (ofPath) reaches keys.
                {"anchor-only", true},
                // The anchor's prefix reads w1's write, w1 read keys's
                // before it: two joins from the anchor, and keys in no
                // demand's group (its fatal reads neither).
                {"two-hops", true},
                // The anchor's attach; its producer p read keys's write: only
                // the delivery's closure (ofDelivery) reaches keys.
                {"delivery", true},
                // p's export reads a container keys put: the delivery's
                // closure is seeded by that version's write (seedWrites).
                {"container", true},
                // The anchor-only chain in a replay that refused its
                // obligation: no admitted path, so nothing is demanded.
                {"refused", false},
        };
        for (Object[] row : rows) {
            String kind = (String) row[0];
            Path iteration = tree.newFolder("rests-on-" + kind).toPath();
            ClosurePlanner.Plan plan = closure(restsOnCorpus(iteration, kind),
                    REST_ANCHOR, StaticScopeMap.empty());
            boolean planned = false;
            for (Task task : plan.tasks) {
                planned |= task.focused().id().equals(REST_HANDLER.id());
            }
            assertEquals(kind + ": " + plan.tasks + " " + gapsOf(plan),
                    row[1], planned);
        }
    }

    private static final OccurrenceAddress REST_ANCHOR = occurrence(
            "hdfs-case/bal", "REGION.move", CausalContext.of(Role.CLIENT, "",
                    1), "Dispatcher#move#3");
    private static final OccurrenceAddress REST_KEYS = occurrence(
            "hdfs-case/bal", "REGION.keys", CausalContext.of(Role.CLIENT, "",
                    2), "KeyManager#update#5");
    private static final OccurrenceAddress REST_HANDLER = occurrence(
            "hdfs-case/nn0", "REGION.handler", CausalContext.of(Role.CLIENT,
                    "", 3), "NameNodeRpc#getBlockKeys#9");
    private static final OccurrenceAddress REST_W1 = occurrence(
            "hdfs-case/bal", "REGION.w1", CausalContext.of(Role.CLIENT, "",
                    4), "Dispatcher#plan#7");
    private static final OccurrenceAddress REST_P = occurrence(
            "hdfs-case/bal", "REGION.p", CausalContext.of(Role.CLIENT, "",
                    5), "Dispatcher#source#8");

    /** One row's corpus ({@link #whatComposeKeepsIsWhatExploreDemands}). */
    private static Corpus restsOnCorpus(Path iteration, String kind)
            throws IOException {
        LocationId stored = LocationId.of(LocationKind.INSTANCE, "7", "24");
        LocationId planned = LocationId.of(LocationKind.INSTANCE, "8", "25");
        LocationId map = LocationId.of(LocationKind.MAP, "9", "allKeys");
        boolean refused = "refused".equals(kind);
        Session seed = new Session(iteration, "s-seed");
        Session chain = refused ? new Session(iteration, "s-flip") : seed;
        for (Session session : refused ? new Session[]{seed, chain}
                : new Session[]{seed}) {
            session.activation(REST_ANCHOR, session == chain && refused);
            session.activations(false, REST_KEYS, REST_HANDLER, REST_W1,
                    REST_P);
        }
        Endpoint sent = at(REST_HANDLER, "XCH.resp.expiry-date",
                "PBHelper#convert#9");
        chain.symbolic("e.expiry", "M_EXPIRY_OUT");
        chain.export(sent, "e.expiry", 1L, "600");
        chain.attach(at(REST_KEYS, "XCH.resp.expiry-date",
                "PBHelper#convert#9"), "M_HOFF_EXPIRY", "600", sent);
        chain.symbolic("EXPR.0000000000000001", "unmoved".equals(kind)
                ? "M_UNMOVED" : "M_HOFF_EXPIRY");
        Endpoint keysWrite = at(REST_KEYS, Endpoint.stateSite("KeyManager",
                "update", 12, true), "KeyManager#update#12");
        if (!"after".equals(kind)) {
            chain.decision(REST_KEYS, "KeyManager#u4", 1, true,
                    "EXPR.0000000000000001");
        }
        // keys writes a constant: what moves is only its decision.
        chain.constant("e.key", "7");
        if ("container".equals(kind)) {
            chain.symbolic("e.map", "M_MAPV");
            chain.write(keysWrite, map, 5L, "e.map", "L");
        } else {
            chain.write(keysWrite, "two-hops".equals(kind) ? planned
                    : stored, 5L, "e.key");
        }
        if ("after".equals(kind)) {
            chain.decision(REST_KEYS, "KeyManager#u4", 1, true,
                    "EXPR.0000000000000001");
        }
        chain.symbolic("EXPR.0000000000000002", "M_READ_KEY");
        chain.symbolic("EXPR.0000000000000003", "M_OTHER");
        String phi = "(not EXPR.0000000000000002)";
        switch (kind) {
            case "two-hops":
                // w1 reads keys's write, then writes what the anchor reads.
                chain.read(at(REST_W1, Endpoint.stateSite("Dispatcher",
                        "plan", 2, false), "Dispatcher#plan#2"), planned, 5L,
                        "M_READ_PLANNED", "7");
                chain.constant("e.c", "7");
                chain.write(at(REST_W1, Endpoint.stateSite("Dispatcher",
                        "plan", 6, true), "Dispatcher#plan#6"), stored, 6L,
                        "e.c");
                chain.read(at(REST_ANCHOR, Endpoint.stateSite("Dispatcher",
                        "move", 3, false), "Dispatcher#move#3"), stored, 6L,
                        "M_READ_KEY", "7");
                // Its fatal reads neither: keys is in no demand's group.
                phi = "(not EXPR.0000000000000003)";
                break;
            case "delivery":
            case "container": {
                // The anchor's fatal reads the value p delivered.
                Endpoint delivered = at(REST_P, "XCH.source.value",
                        "Dispatcher#source#8");
                if ("delivery".equals(kind)) {
                    chain.read(at(REST_P, Endpoint.stateSite("Dispatcher",
                            "source", 4, false), "Dispatcher#source#4"),
                            stored, 5L, "M_READ_SOURCE", "7");
                    chain.symbolic("e.p", "M_P_OUT");
                } else {
                    chain.expression("e.p", guardedRead(map, 5L, "I",
                            relation("ASSOCIATIVE", "READ", "I",
                                    leaf("M_L'java/util/HashMap'_1",
                                            "java/util/HashMap"),
                                    literal(1)), 5L));
                }
                chain.export(delivered, "e.p", 2L, "7");
                chain.attach(at(REST_ANCHOR, "XCH.source.value",
                        "Dispatcher#source#8"), "M_HOFF_SOURCE", "7",
                        delivered);
                chain.symbolic("EXPR.0000000000000004", "M_HOFF_SOURCE");
                phi = "(not EXPR.0000000000000004)";
                break;
            }
            case "anchor-only":
            case "refused":
                chain.read(at(REST_ANCHOR, Endpoint.stateSite("Dispatcher",
                        "move", 3, false), "Dispatcher#move#3"), stored, 5L,
                        "M_READ_KEY", "7");
                phi = "(not EXPR.0000000000000003)";
                break;
            default:
                chain.read(at(REST_ANCHOR, Endpoint.stateSite("Dispatcher",
                        "move", 3, false), "Dispatcher#move#3"), stored, 5L,
                        "M_READ_KEY", "7");
        }
        chain.target(REST_ANCHOR, "Dispatcher#move#3", phi);
        if (refused) {
            seed.symbolic("EXPR.0000000000000003", "M_OTHER");
            seed.target(REST_ANCHOR, "Dispatcher#move#3",
                    "(not EXPR.0000000000000003)");
            chain.answered(ObligationResult.of("OBL.refused",
                    Verdict.NOT_ADMITTED, "s-flip",
                    "the focused occurrence's own prefix did not match"));
            seed.flush();
        }
        chain.flush();
        return Corpus.read(iteration, null);
    }

    /**
     * The groups of a closure overlap -- each is an occurrence and its
     * state-connected factor -- and each member's reads are indexed once
     * per walk, every group it is in reading that one index, in group order
     * (solr-adhoc-39 PV7 round 6: indexed per group, the walk passed 14 GB).
     */
    @Test
    public void overlappingGroupsShareTheirMembersReads() throws Exception {
        Path iteration = tree.newFolder("shared-groups").toPath();
        for (String sessionId : Arrays.asList("s-seed", "s-two")) {
            Session session = new Session(iteration, sessionId);
            session.activations(false, TARGET, WRITER, READER);
            session.symbolic("e.stored", "M_HOFF_KEY");
            session.write(STORED, ALL_KEYS, 5L, "e.stored");
            session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "0");
            session.read(CONSULTED, ALL_KEYS, 5L, "M_CHECKED", "0");
            session.anchored(TARGET);
            session.flush();
        }
        ClosurePlanner.Walk walk = new ClosurePlanner.Walk(
                Corpus.read(iteration, null), StaticScopeMap.empty(), TARGET,
                ClosurePlanner.CORES, gap -> { });
        ClosurePlanner.GroupReads target = walk.reads(TARGET);
        ClosurePlanner.GroupReads reader = walk.reads(READER);
        assertEquals("every occurrence on the map is in both groups", 3,
                target.members.size());
        assertEquals(3, reader.members.size());
        for (Object member : reader.members) {
            boolean shared = false;
            for (Object held : target.members) shared |= held == member;
            assertTrue("one index per member, shared by its groups", shared);
        }
        List<String> stated = new ArrayList<String>();
        for (ReadRow row : reader.of("M_READ_KEY")) {
            stated.add(row.sessionId());
        }
        assertEquals("a symbol's rows, every session's, in recorded order",
                Arrays.asList("s-seed", "s-two"), stated);
    }

    /**
     * A diagnostic about a read or a pairing that every replay repeats --
     * the seed's rows again, over objects of its own run -- is said once
     * per endpoint and field, as the first session states it, not once per
     * session and object (solr-adhoc-39 PV7 round 5: 75,333 no-carrier rows
     * of 139,230, a rendered address each).
     */
    @Test
    public void aDiagnosticEveryReplayRepeatsIsSaidOnce() throws Exception {
        Path iteration = tree.newFolder("said-once").toPath();
        // The writer's anchor names ROTATED; its attach row pairs another
        // export: a divergence each session states again.
        Endpoint other = at(PRODUCER, "XCH.resp.block-key-expiry",
                "PBHelper#convert#12");
        Endpoint side = at(TARGET, Endpoint.stateSite(
                "BlockTokenSecretManager", "retrieveDataEncryptionKey", 9,
                false), "BlockTokenSecretManager#retrieveDataEncryptionKey#9");
        int rid = 40;
        for (String sessionId : Arrays.asList("s-seed", "s-two")) {
            Session session = new Session(iteration, sessionId);
            session.activations(false, TARGET, WRITER, PRODUCER);
            session.constant("e.119992", "119992");
            session.symbolic("e.stored", "M_HOFF_KEY");
            session.export(other, "e.119992", 11L, "119992");
            session.attach(DELIVERED, "M_HOFF_KEY", "119992", other);
            session.write(STORED, ALL_KEYS, 5L, "e.stored");
            session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
            // An object of this run's own, which nothing recorded writes.
            session.read(side, LocationId.of(LocationKind.MAP, "" + rid++,
                    "-3"), 0L, "M_SIDE", "0");
            session.target(TARGET, "BlockTokenSecretManager"
                    + "#retrieveDataEncryptionKey#8",
                    "(and (= M_READ_KEY 0) (= M_SIDE 0))");
            session.flush();
        }
        StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                targetSite("REGION.target", "BlockTokenSecretManager#u120")));
        ClosurePlanner.Plan plan = closure(Corpus.read(iteration, null),
                TARGET, map);
        Map<String, Integer> said = new LinkedHashMap<String, Integer>();
        for (GapRow gap : gapsOf(plan)) {
            if (gap.kind() == GapKind.DECLARATION_MISSING
                    || gap.kind() == GapKind.TOPOLOGY_DIVERGENCE) {
                said.merge(gap.kind() + " " + gap.subject(), 1, Integer::sum);
            }
        }
        assertTrue("the divergence is named: " + said.keySet(),
                said.containsKey(GapKind.TOPOLOGY_DIVERGENCE + " "
                        + DELIVERED.render()));
        assertTrue("and the uncarried read of the run's own object: "
                + said.keySet(), said.containsKey(
                GapKind.DECLARATION_MISSING + " " + side.render()));
        for (Map.Entry<String, Integer> gap : said.entrySet()) {
            assertEquals("said once: " + gap.getKey(), 1,
                    gap.getValue().intValue());
        }
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

    /**
     * The ZooKeeper chain grows by its own fields only ({@code ZkEdges},
     * {@code ZkChain#grown}): an off-chain decode or write of a chain path's
     * version a chain occurrence of the same session consumed, whose leaves
     * lie under a key of the chain, is an edge, keyed by those keys -- named
     * by the admitted replay that showed it, or by none where only the seed
     * did.  Not an edge: another node's decode, a version no chain occurrence
     * consumed, a write touching no chain field, work under no region, a read
     * of a path off the chain (solr-18413 SGF7: every such one grown, 1099
     * rows in round 2).
     */
    @Test
    public void theChainGrowsByItsOwnFieldsOnly() throws Exception {
        Path iteration = tree.newFolder("zk-edges").toPath();
        String path = "/collections/c/state.json";
        LocationId state = LocationId.of(LocationKind.STORE, "SOLR_ZK", path);
        LocationId view = LocationId.of(LocationKind.VIEW, "SOLR_ZK@dn0",
                path);
        LocationId otherView = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@dn1", path);
        LocationId aliases = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/aliases.json");
        OccurrenceAddress role = occurrence("hdfs-case/dn0", "ROLE.UNKNOWN",
                CausalContext.of(Role.of("UNKNOWN"), "", 1), "o.a.Pool#run#1");
        OccurrenceAddress router = occurrence("hdfs-case/nn0",
                "REGION.router", CausalContext.of(Role.of("ROUTER"), "", 1),
                "o.a.Router#run#1");
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, SIDECAR);
        seed.read(at(TARGET, "SOLR_ZK#VIEW:|c", "Reader#get#1"), view, 2L,
                "M_V2", "0");
        decoded(seed, SIDECAR, view, 2L, "/c/shards/shard1/state");
        seed.flush();
        Session flip = new Session(iteration, "s-flip");
        flip.activation(TARGET, true);
        flip.activations(false, READER, WRITER, PRODUCER, BALANCER, router);
        flip.answered(ObligationResult.of("OBL.s-flip", Verdict.ADMITTED,
                "s-flip", "the focused prefix reproduced"));
        // The chain consumed version 3: its view on dn0 and the store's.
        flip.read(at(TARGET, "SOLR_ZK#VIEW:|c", "Reader#get#1"), view, 3L,
                "M_V3", "0");
        flip.read(at(TARGET, "SOLR_ZK#READ:|c", "SolrZkClient#getData#2"),
                state, 3L, "M_S3", "0");
        decoded(flip, READER, view, 3L, "/c/shards/shard1/state");
        written(flip, WRITER, state, 3L, "/c/shards/shard1/range");
        written(flip, role, state, 3L, "/c/shards/shard1/range");
        written(flip, router, state, 3L, "/c/router/name");
        written(flip, PRODUCER, state, 4L, "/c/shards/shard1/range");
        decoded(flip, BALANCER, otherView, 3L, "/c/shards/shard1/state");
        flip.read(at(TARGET, "SOLR_ZK#READ:|aliases.json",
                "SolrZkClient#getData#5"), aliases, 7L, "M_ALIASES", "0");
        flip.flush();
        Path chainFile = iteration.resolve(ZkChain.FILE);
        RowCodec.writeJsonl(chainFile, Arrays.asList(
                JsonParser.parseString("{\"schemaVersion\":1,\"kind\":"
                        + "\"ZK_CHAIN_PATH\",\"transport\":\"SOLR_ZK\","
                        + "\"location\":\"" + path + "\",\"slot\":\""
                        + path + "\"}").getAsJsonObject(),
                JsonParser.parseString("{\"schemaVersion\":1,\"kind\":"
                        + "\"ZK_CHAIN_OCCURRENCE\",\"occurrenceId\":\""
                        + TARGET.render() + "\"}").getAsJsonObject(),
                JsonParser.parseString("{\"schemaVersion\":1,\"kind\":"
                        + "\"ZK_CHAIN_KEYS\",\"occurrenceId\":\""
                        + TARGET.render() + "\",\"location\":\"" + path
                        + "\",\"slot\":\"" + path + "\",\"pointers\":"
                        + "[\"|c|shards\"]}").getAsJsonObject()));
        ZkChain chain = ZkChain.read(chainFile);
        List<JsonObject> edges = ZkEdges.of(Corpus.read(iteration, null),
                chain);
        Map<String, String> named = new LinkedHashMap<String, String>();
        for (JsonObject edge : edges) {
            named.put(edge.get("occurrence").getAsString() + " v"
                    + edge.get("version").getAsLong() + " "
                    + edge.get("pointers"), edge.get("sessionId")
                    .getAsString());
        }
        Map<String, String> expected = new LinkedHashMap<String, String>();
        expected.put(SIDECAR.render() + " v2 [\"|c|shards\"]", "");
        expected.put(READER.render() + " v3 [\"|c|shards\"]", "s-flip");
        expected.put(WRITER.render() + " v3 [\"|c|shards\"]", "s-flip");
        assertEquals(expected, named);

        ZkChain grown = chain.grown(edges);
        for (OccurrenceAddress joined : Arrays.asList(SIDECAR, READER,
                WRITER)) {
            assertTrue(grown.holds(joined.render()));
            assertEquals("keyed by the chain's fields it carries",
                    "[{\"location\":\"" + path + "\",\"slot\":\"" + path
                            + "\",\"pointer\":\"|c|shards\"}]",
                    grown.contentKeys(joined.render()).toString());
        }
        assertFalse(grown.holdsPath("SOLR_ZK", "/aliases.json"));
        assertTrue("and never shrinks", grown.rows().containsAll(
                chain.rows()));
    }

    /** One decode of a view's version at an occurrence, and one leaf of
     *  the document it minted. */
    private static void decoded(Session session, OccurrenceAddress at,
                                LocationId view, long version, String leaf) {
        session.write(at(at, "SOLR_ZK#DECODED:" + view.slot(),
                "ZkStateReader#refresh#4"), view, version, "");
        session.attach(at(at, ContentPort.of("SOLR_ZK", view.slot(), leaf),
                "Utils#fromJSON#6"), "M_LEAF" + session.seq, "0", null);
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

    /**
     * A decision is a flip only where it rests on a root, a message's
     * field, a heap read or a chain read ({@code ZkKeys}): not over a leaf
     * of a chain path no key covers, a read of a view of a path off the
     * chain, or nothing it classifies (a decoded container).  One over a
     * covered leaf, or over an off-chain leaf and a root, is; with no
     * chain, every one is.
     */
    @Test
    public void aDecisionOverOffChainStoreValuesAloneIsNoFlip()
            throws Exception {
        Path iteration = tree.newFolder("zk-keys").toPath();
        String state = "/collections/c/state.json";
        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET);
        seed.attach(at(TARGET, ContentPort.of("SOLR_ZK", state,
                "/c/shards/shard1/state"), "Decode#1"), "M_ON", "1", null);
        seed.attach(at(TARGET, ContentPort.of("SOLR_ZK", state,
                "/c/replicas"), "Decode#2"), "M_OFF", "1", null);
        seed.read(at(TARGET, "SOLR_ZK#READ:|aliases.json", "View#3"),
                LocationId.of(LocationKind.VIEW, "SOLR_ZK@nn0",
                        "/aliases.json"), 7L, "M_VIEW", "1");
        seed.integral(TARGET, "CASE.R", "M_ROOT", "1", "0", "9");
        seed.decision(TARGET, "Guard#on", 1, true, "(= M_ON 1)");
        seed.decision(TARGET, "Guard#off", 1, true, "(= M_OFF 1)");
        seed.decision(TARGET, "Guard#view", 1, true, "(= M_VIEW 1)");
        seed.decision(TARGET, "Guard#mixed", 1, true, "(= M_OFF M_ROOT)");
        seed.decision(TARGET, "Guard#container", 1, true,
                "(= container_dag__1 nullRef)");
        seed.flush();
        Path chainFile = iteration.resolve(ZkChain.FILE);
        RowCodec.writeJsonl(chainFile, Arrays.asList(
                JsonParser.parseString("{\"schemaVersion\":1,\"kind\":"
                        + "\"ZK_CHAIN_PATH\",\"transport\":\"SOLR_ZK\","
                        + "\"location\":\"" + state + "\",\"slot\":\""
                        + state + "\"}").getAsJsonObject(),
                JsonParser.parseString("{\"schemaVersion\":1,\"kind\":"
                        + "\"ZK_CHAIN_KEYS\",\"occurrenceId\":\""
                        + TARGET.render() + "\",\"location\":\"" + state
                        + "\",\"slot\":\"" + state + "\",\"pointers\":"
                        + "[\"|c|shards\"]}").getAsJsonObject()));
        Corpus corpus = Corpus.read(iteration, null);
        ZkKeys keys = ZkKeys.of(ZkChain.read(chainFile));
        ZkKeys none = ZkKeys.of(ZkChain.read(null));
        Map<String, Boolean> flips = new TreeMap<String, Boolean>();
        for (DecisionRow decision : corpus.decisionsOf("s-seed", TARGET)) {
            flips.put(decision.siteId(),
                    keys.flippable(corpus, "s-seed", decision));
            assertTrue(none.flippable(corpus, "s-seed", decision));
        }
        Map<String, Boolean> expected = new TreeMap<String, Boolean>();
        expected.put("Guard#on", true);
        expected.put("Guard#off", false);
        expected.put("Guard#view", false);
        expected.put("Guard#mixed", true);
        expected.put("Guard#container", false);
        assertEquals(expected, flips);
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

    /**
     * A static candidate the rows later reach is no longer one ({@code
     * ClosurePlanner.Demand#absorb}): here {@code door}, planned as a static
     * writer of the map, sent the message that started the next candidate
     * and decided a fault of it, so that candidate's expansion reaches it
     * as a control producer -- and when the third candidate's producer
     * meets the ceiling, the static candidates leave the plan and the
     * control producer stays.
     */
    @Test
    public void aStaticCandidateReachedAsAControlProducerIsNoLongerCut()
            throws Exception {
        Path iteration = tree.newFolder("candidate-relabel").toPath();
        LocationId allKeys = LocationId.of(LocationKind.MAP, "21", "allKeys");
        OccurrenceAddress door = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.CLIENT, "", 9),
                "o.a.h.h.s.d.BPServiceActor#offerService#41");
        OccurrenceAddress served = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of("e-door",
                        "HADOOP_IPC/heartbeat"),
                "o.a.h.h.s.d.BPServiceActor#offerService#43");
        OccurrenceAddress guarded = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.CLIENT, "", 11),
                "o.a.h.h.s.d.BPServiceActor#offerService#44");
        OccurrenceAddress producer = occurrence("hdfs-case/dn0",
                "REGION.other", CausalContext.of(Role.of("OTHER"), "", 1),
                "o.a.h.h.s.d.Other#run#1");
        Endpoint exported = at(producer, "XCH.req.guard", "Other#send#2");
        Session seed = new Session(iteration, "s-seed");
        for (OccurrenceAddress at : Arrays.asList(TARGET, WRITER, door,
                served, guarded, producer)) {
            seed.activation(at, false);
        }
        seed.marker(door, "CASE.DOOR", "M_DOOR", "false");
        seed.decision(door, "Client#u7", 1, false, "M_DOOR");
        seed.constant("e.one", "1");
        seed.export(exported, "e.one", 21L, "1");
        seed.attach(at(guarded, "XCH.req.guard", "Other#send#2"), "M_GUARD",
                "1", exported);
        seed.decision(guarded, "Keys#u3", 1, true, "(= M_GUARD 1)");
        seed.constant("e.stored", "7");
        seed.write(STORED, allKeys, 5L, "e.stored");
        seed.read(at(TARGET, Endpoint.stateSite("BlockTokenSecretManager",
                        "retrieveDataEncryptionKey", 8, false),
                        "BlockTokenSecretManager#retrieveDataEncryptionKey#8"),
                allKeys, 5L, "M_READ_KEY", "7");
        seed.anchored(TARGET);
        seed.flush();
        RowCodec.writeJsonl(SessionDir.of(iteration, "s-seed").schedule(),
                Collections.singletonList(RowCodec.writeScheduleEvent(
                        ScheduleEvent.of(0L, ScheduleEvent.Kind.SEND,
                                door.node().render() + "|"
                                        + door.context().render(),
                                "HADOOP_IPC#REQUEST", 0, door.id(),
                                "e-door"))));
        StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.addkeys",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", "",
                        "Keys#u3"))));
        Corpus corpus = Corpus.read(iteration, null);
        ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, TARGET,
                ClosurePlanner.DEFAULT_MAX_TASKS, 2, map, Branches.of(corpus,
                        Collections.singletonList(TARGET),
                        new ArrayList<GapRow>()),
                    Collections.<String>emptySet(),
                Collections.<String>emptySet(), ClientFaults.NONE,
                SystemView.of(""), gap -> { });
        Set<String> planned = new LinkedHashSet<String>();
        for (Task task : plan.tasks) planned.add(task.focused().render());
        assertEquals(new LinkedHashSet<String>(Arrays.asList(TARGET.render(),
                WRITER.render(), door.render())), planned);
        assertEquals(ClosurePlanner.CONTROL_PRODUCER,
                plan.why.get(ClosurePlanner.taskId(door)));
        assertEquals(Collections.singleton(producer.render()),
                plan.ceilingCut);
        assertEquals(new LinkedHashSet<String>(Arrays.asList(
                producer.render(), served.render(), guarded.render())),
                new LinkedHashSet<String>(plan.truncated));
    }

    /**
     * GROW OF AN INVOCATION (PIPELINE §7.8): a marker call only a flipped
     * world made (solr-adhoc-09: the second {@code waitForState} after the
     * first timed out) is exposed by an admitted session that may parent,
     * once, as an UNPLANNED_INPUT growth row naming the session and its
     * obligation; the seed and a stopped branch expose none; one past the
     * declared bound is named, counted as {@code unplanned-input-max}, and
     * not grown; one the plan already holds grows nothing.
     */
    @Test
    public void aMarkerInvocationOnlyAFlippedWorldMadeIsGrownOnce()
            throws Exception {
        Object[][] subjects = {
            {"TASK.t SYM.m#2", "TASK.t", "SYM.m", 2, "SYM.m#2"},
            {"TASK.t SYM.m#3#2", "TASK.t", "SYM.m", 2, "SYM.m#2"},
        };
        for (Object[] subject : subjects) {
            UnplannedInput input = UnplannedInput.parse((String) subject[0]);
            assertEquals(Arrays.asList(subject[1], subject[2], subject[3],
                    subject[4]), Arrays.asList(input.taskId(), input.symbol(),
                    input.k(), input.grown()));
        }
        Path iteration = tree.newFolder("unplanned").toPath();
        Object[][] sessions = {
            // session, focused, its activation, the invocations it names
            {"s-seed", false, TARGET, "SYM.m#2"},
            {"s-flip", true, TARGET, "SYM.m#2 SYM.m#5"},
            {"s-later", true, TARGET, "SYM.m#2"},
            {"s-stopped", true, WRITER, "SYM.x#2"},
        };
        for (Object[] row : sessions) {
            String sessionId = (String) row[0];
            Session session = new Session(iteration, sessionId);
            session.activation((OccurrenceAddress) row[2], (Boolean) row[1]);
            if ((Boolean) row[1]) {
                session.answered(ObligationResult.of("OBL." + sessionId,
                        Verdict.ADMITTED, sessionId, "admitted"));
            }
            for (String grown : ((String) row[3]).split(" ")) {
                session.gap(GapRow.of(sessionId, GapKind.UNPLANNED_INPUT,
                        GapClass.DIAGNOSTIC, "TASK.t " + grown, "concrete"));
            }
            session.flush();
        }
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u19"));
        Path out = tree.newFolder("unplanned-out").toPath();
        Path results = results(out);
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null, results, wave, 0);
        List<String> grown = new ArrayList<String>();
        for (JsonObject row : RowCodec.readJsonl(
                wave.resolve(WaveGraph.GROWTH))) {
            grown.add(row.get("kind").getAsString() + " "
                    + row.get("taskId").getAsString() + " "
                    + row.get("symbol").getAsString() + "#"
                    + row.get("k").getAsInt() + " "
                    + row.get("sessionId").getAsString() + " "
                    + row.get("obligationId").getAsString());
        }
        assertEquals(Collections.singletonList(
                "UNPLANNED_INPUT TASK.t SYM.m#2 s-flip OBL.s-flip"), grown);
        boolean bounded = false;
        for (JsonObject gap : RowCodec.readJsonl(wave.resolve(ExploreMain.GAPS_FILE))) {
            bounded |= gap.get("subject").getAsString().equals(
                    "TASK.t SYM.m#5 unplanned-input-max="
                            + UnplannedInput.MAX);
        }
        assertTrue("the bound is named, counted", bounded);
        // Planned (an earlier generation's), it grows nothing.
        JsonObject planned = new JsonObject();
        planned.addProperty("taskId", "TASK.t");
        JsonArray inputs = new JsonArray();
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "SYM.m#2");
        inputs.add(input);
        planned.add("inputActions", inputs);
        RowCodec.writeJsonl(iteration.resolve("execution_task_plan.jsonl"),
                Collections.singletonList(planned));
        Path next = out.resolve("obligations-0001");
        plan(iteration, TARGET_SELECTOR, null, results, next, 1);
        assertTrue("a planned invocation grows no row",
                RowCodec.readJsonl(next.resolve(WaveGraph.GROWTH)).isEmpty());
    }

    /**
     * F2: a static site is found at the occurrence whose region HOLDS it.
     *
     * <p>A declared region entered synchronously inside another region's
     * occurrence opens none of its own, so a site of region R is recorded
     * under an occurrence of the enclosing R' -- and the static map publishes
     * a site under its INNERMOST holder alone ({@code
     * StaticScopeMap#holders}), so R' never appears beside that site.
     * Matching region ids for equality then found no occurrence at all and
     * the candidate read as "no session activated that region", which is a
     * writer the corpus HAD run, lost.</p>
     */
    @Test
    public void aStaticSiteIsACandidateWhereItsMethodIsHeld()
            throws Exception {
        Path iteration = tree.newFolder("holding").toPath();
        // The writer ran as an occurrence of the ENCLOSING region, which is
        // what a fold leaves in the corpus.
        OccurrenceAddress enclosing = occurrence("hdfs-case/dn0",
                "REGION.outer", CausalContext.of(Role.of("DATA_XCEIVER"), "",
                        2), "o.a.h.h.s.d.BPServiceActor#offerService#41");
        // The occurrence the site's method is held BY, which wrote nothing
        // the anchor read and is therefore no member of the closure yet.
        OccurrenceAddress holder = occurrence("hdfs-case/dn0",
                "REGION.holder", CausalContext.of(Role.of("KEY_MANAGER_TICK"),
                        "", 1), "o.a.h.h.s.b.KeyManager#run#3");
        OccurrenceAddress unrelated = occurrence("hdfs-case/dn0",
                "REGION.elsewhere", CausalContext.of(Role.of("DATA_XCEIVER"),
                        "", 3), "o.a.h.h.s.d.DataXceiver#run#77");
        // Where a port event ran outside every admitted activation: its
        // ambient row names the place, and no activation of its region ran
        // there, so it is no candidate however its region holds the site.
        OccurrenceAddress ambient = occurrence("hdfs-case/dn0",
                "REGION.handler", CausalContext.of(Role.of("IPC_HANDLER"),
                        "", 1), "o.a.h.h.s.b.KeyManager#run#9");
        Endpoint stored = at(enclosing, Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true),
                "BlockTokenSecretManager#addKeys#12");

        Session seed = new Session(iteration, "s-seed");
        seed.activations(false, TARGET, enclosing, holder, unrelated);
        seed.activation(ambient, false, false);
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.write(stored, ALL_KEYS, 5L, "e.stored");
        seed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        seed.anchored(TARGET);
        seed.flush();

        // The map names the carrier at the recorded write's own site, and a
        // SECOND write site of that carrier -- KeyManager#refresh -- under
        // the innermost region that holds it.  No occurrence of REGION.inner
        // is in this corpus; the occurrence that RAN that method is the one
        // addressed as REGION.holder.
        String[] rows = {
                targetSite("REGION.target", "BlockTokenSecretManager#u120"),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.outer",
                        "BlockTokenSecretManager#u12",
                        "BlockTokenSecretManager#addKeys",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", "")),
                put(scopeSite(StaticScopeMap.WRITE_SITE, "REGION.inner",
                        "KeyManager#u4", "KeyManager#refresh",
                        "<example.Keys: int value>",
                        "<example.Manager: example.Keys allKeys>", ""))};
        Path mapFile = scopeMap(iteration, rows);

        // Without the skeletons beside it the map can say nothing about
        // holding, and the join is the region-id equality it always was:
        // nothing runs REGION.inner, so nothing is a candidate.
        Map<String, String> blind = why(closure(Corpus.read(iteration, null),
                TARGET, StaticScopeMap.read(mapFile)));
        assertFalse("with no skeletons, equality finds no occurrence of the"
                        + " region the site is published under: " + blind,
                blind.containsKey(holder.render()));

        // With them, the enclosing region's own method set answers: it holds
        // the site's method, so its occurrence is the candidate writer.
        skeletons(iteration,
                skeleton("REGION.inner", "KeyManager"),
                skeleton("REGION.holder", "KeyManager", "BPServiceActor"),
                skeleton("REGION.handler", "KeyManager"),
                skeleton("REGION.outer", "BlockTokenSecretManager"),
                skeleton("REGION.elsewhere", "DataXceiver"),
                skeleton("REGION.target", "BlockTokenSecretManager"));
        ClosurePlanner.Plan plan = closure(Corpus.read(iteration, null),
                TARGET, StaticScopeMap.read(mapFile));
        Map<String, String> held = why(plan);
        assertEquals("the occurrence whose region holds the site's method is"
                        + " the static candidate writer: " + held,
                ClosurePlanner.STATIC_CANDIDATE_WRITER,
                held.get(holder.render()));
        assertFalse("and an occurrence of a region that does not hold it is"
                        + " not, though it ran on the same node: " + held,
                held.containsKey(unrelated.render()));
        assertFalse("nor is an ambient one, which nothing waits on either: "
                        + plan.waiting, plan.waiting.contains(ambient)
                || plan.exposed.containsKey(ambient));
    }

    /** The occurrences one plan's tasks focus, in its order. */
    private static List<String> focused(ClosurePlanner.Plan plan) {
        List<String> focused = new ArrayList<String>();
        for (Task task : plan.tasks) focused.add(task.focused().render());
        return focused;
    }

    /** addKeys' store of the key map, in {@code occurrence}. */
    private static Endpoint stored(OccurrenceAddress occurrence) {
        return at(occurrence, Endpoint.stateSite("BlockTokenSecretManager",
                "addKeys", 12, true), "BlockTokenSecretManager#addKeys#12");
    }

    /** The key lookup's read of the key map, in {@code occurrence}. */
    private static Endpoint lookedUp(OccurrenceAddress occurrence) {
        return at(occurrence, Endpoint.stateSite("BlockTokenSecretManager",
                "retrieveDataEncryptionKey", 8, false),
                "BlockTokenSecretManager#retrieveDataEncryptionKey#8");
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

    /** The region skeletons PLAN writes beside the static map. */
    private Path skeletons(Path iteration, String... regions)
            throws IOException {
        Path file = iteration.resolve(StaticScopeMap.REGIONS);
        Files.write(file, (String.join(System.lineSeparator(),
                Arrays.asList(regions))
                + System.lineSeparator()).getBytes("UTF-8"));
        return file;
    }

    /** One skeleton row: the region, and the methods it holds. */
    private static String skeleton(String regionId, String... methods) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "REGION_SKELETON");
        row.addProperty("regionId", regionId);
        JsonArray held = new JsonArray();
        for (String method : methods) held.add(method);
        row.add("methods", held);
        return row.toString();
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
                    ArtifactIO.gzip(query.getBytes(StandardCharsets.UTF_8)));
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
                !queryText(worker).isEmpty());
        return new Worker(rows.get(0).verdict(), solved.get(0), worker);
    }

    /** Lands one answer in the iteration as a worker does: its directory
     *  under the obligation id it ran as, the question naming the flip it
     *  asked, its result row. */
    private static void land(Path iteration, String wave, Obligation asked,
                             ObligationResult answer) throws IOException {
        Path worker = iteration.resolve(wave).resolve(answer.obligationId());
        Files.createDirectories(worker);
        Files.write(worker.resolve(ObligationDir.QUESTION), (ObligationFactory
                .flip(asked.taskId(), asked.pathId(), asked.siteId(),
                        asked.ordinal(), asked.flippedOutcome()) + ":asked")
                .getBytes(StandardCharsets.UTF_8));
        record(worker.resolve(ObligationDir.RESULT), answer);
    }

    /** Whether a directory's gap rows hold one {@code named} matches: a
     *  round's ({@link ExploreMain#GAPS_FILE}) or a worker's. */
    private static boolean anyGap(Path dir,
            java.util.function.Predicate<GapRow> named) throws IOException {
        return RowCodec.readAll(dir.resolve(ExploreMain.GAPS_FILE),
                        RowCodec::readGap)
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

    /** The obligations one task offered, for a per-task count. */
    private static List<Obligation> obligationsOf(
            List<Obligation> obligations, String taskId) {
        List<Obligation> found = new ArrayList<Obligation>();
        for (Obligation obligation : obligations) {
            if (obligation.taskId().equals(taskId)) found.add(obligation);
        }
        return found;
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
     * IDENTITY §7.3: a door of the message the anchor served joins its
     * closure as a control producer only where a session recorded a fault
     * decision of it -- what decides whether the message exists, the door
     * PLAN's CONTROL_PRODUCER rule admits.  Any other door, captured with no
     * fault branch or run only by the seed under no planned task
     * (hdfs-adhoc-28's heartbeat tick, its scope holding no IPC client door),
     * is one DIAGNOSTIC row: no task, and nothing waited for.
     */
    @Test
    public void aDoorIsAControlProducerWhereItDecidedAFault()
            throws Exception {
        OccurrenceAddress anchor = occurrence("hdfs-case/dn0",
                "REGION.recovery", CausalContext.of("e-door",
                        "HADOOP_IPC/heartbeat"),
                "o.a.h.h.s.d.BlockRecoveryWorker#run#3");
        OccurrenceAddress door = occurrence("hdfs-case/dn0", "REGION.actor",
                CausalContext.of(Role.of("BP_SERVICE_ACTOR"), "", 3),
                "o.a.h.h.s.d.BPServiceActor#run#1");
        // the door captured (a planned task ran it), it decided a fault
        Object[][] cases = {{true, true}, {true, false}, {false, false}};
        for (Object[] row : cases) {
            boolean captured = (Boolean) row[0];
            boolean faulted = (Boolean) row[1];
            String label = "captured=" + captured + " faulted=" + faulted;
            Path iteration = tree.newFolder().toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(anchor, false);
            // Named by the seed either way; instrumented only if captured.
            seed.activation(door, false, captured);
            if (faulted) {
                seed.marker(door, "CASE.DOOR", "M_DOOR", "false");
                seed.decision(door, "Client#u7", 1, false, "M_DOOR");
            } else if (captured) {
                seed.decision(door, "Actor#u3", 1, true, "");
            }
            seed.target(anchor, "Recovery#u8#1", "false");
            seed.flush();
            RowCodec.writeJsonl(SessionDir.of(iteration, "s-seed").schedule(),
                    Collections.singletonList(RowCodec.writeScheduleEvent(
                            ScheduleEvent.of(0L, ScheduleEvent.Kind.SEND,
                                    door.node().render() + "|"
                                            + door.context().render(),
                                    "HADOOP_IPC#REQUEST", 0, door.id(),
                                    "e-door"))));
            StaticScopeMap map = StaticScopeMap.read(scopeMap(iteration,
                    targetSite("REGION.recovery", "Recovery#u9", "Recovery#u8")));
            ClosurePlanner.Plan plan = closure(Corpus.read(iteration, null),
                    anchor, map);
            boolean task = false;
            for (Task planned : plan.tasks) {
                task |= planned.focused().equals(door);
            }
            int rows = 0;
            for (GapRow gap : gapsOf(plan)) {
                if (gap.subject().equals(door.render())
                        && gap.detail().contains("decided no fault")) {
                    assertEquals(label, GapClass.DIAGNOSTIC, gap.cls());
                    rows++;
                }
            }
            assertEquals(label, faulted, task);
            assertEquals("one row for a door that decided no fault: " + label,
                    faulted ? 0 : 1, rows);
            assertFalse("never waited for: " + label,
                    plan.waiting.contains(door));
        }
    }

    /**
     * D0 (R1-ROOTS §2.3, PIPELINE §7.2): an anchor every admitted path
     * decided on no symbol demands the shared state it read BEFORE it
     * decided on its guards' cone (the scope map's demandDistance,
     * SYMBOL-SCOPE §4.6), so the fault that chose what that state's writer
     * wrote is asked; a read made after the decision, or off the cone,
     * reaches nothing -- unless its predicate names that read (a compound
     * guard's phi stands at its first test, and its later tests read
     * after it: hdfs-adhoc-26's cTime reads).  Each round's manifest
     * states it as information ({@code concreteAnchors}: how many paths
     * decided it, the reads its closure demands, those off the cone),
     * never a gap.  An anchor whose predicate names a symbol, an
     * unreached one with a symbolic decision on the way to the throw, or
     * a run that observed the fatal, plans as before and is no concrete
     * anchor.
     */
    @Test
    public void aConcreteAnchorDemandsWhatItReadBeforeItDecided()
            throws Exception {
        LocationId stored = LocationId.of(LocationKind.INSTANCE, "5", "8");
        // phi (null: unreached), observed fatal, the anchor's read before
        // its decision at its guard, the read on the guards' cone, that
        // decision's term (null: none) -> the writer is a task, and the
        // concrete anchor's {decided, demanded reads, off the cone} (null:
        // no concrete anchor).
        Object[][] cases = {
            {"false", false, true, true, "", true, new int[]{1, 1, 0}},
            {"false", false, false, true, "", false, new int[]{1, 0, 0}},
            {"false", false, true, false, "", false, new int[]{1, 0, 1}},
            {null, false, true, true, "", true, new int[]{1, 1, 0}},
            {null, false, true, true, null, false, new int[]{0, 0, 0}},
            {null, false, true, true, "(= M_OTHER 0)", false, null},
            {"(= M_OTHER 0)", false, true, true, "", false, null},
            {"true", true, true, true, "", false, null},
            // phi names the read it made after the target row, off the cone
            {NAMES_ITS_READ, false, false, false, "", true, new int[]{1, 1, 0}},
        };
        for (int at = 0; at < cases.length; at++) {
            Object[] row = cases[at];
            String phi = (String) row[0];
            boolean before = (Boolean) row[2];
            Path iteration = tree.newFolder("concrete-" + at).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activations(false, TARGET, WRITER);
            seed.marker(WRITER, "CASE.DOOR", "M_DOOR", "false");
            seed.decision(WRITER, "Door#u3", 1, false, "M_DOOR");
            seed.constant("e.wrote", "7");
            seed.write(at(WRITER, "Keys#put#4:WRITE", "Keys#put#4"), stored,
                    1L, "e.wrote");
            seed.integral(TARGET, "CASE.OTHER", "M_OTHER", "1", "0", "9");
            Endpoint read = at(TARGET, "Lookup#get#2:READ", "Lookup#get#2");
            if (before) seed.read(read, stored, 1L, "M_READ", "7");
            if (row[4] != null) {
                seed.decision(TARGET, "Guard#u8", 1, false, (String) row[4]);
            }
            if (phi == null) {
                seed.targets.add(TargetRow.of("s-seed", ++seed.seq, TARGET,
                        "Guard#u8#1", "", false, false));
            } else if ((Boolean) row[1]) {
                seed.fatal(TARGET, "Guard#u8#1", phi);
            } else if (NAMES_ITS_READ.equals(phi)) {
                seed.target(TARGET, "Guard#u8#1", phi);
                // The read the second test makes, joined to a constant.
                seed.expression(phi, readTest(seed.seq + 1, stored));
            } else {
                seed.target(TARGET, "Guard#u8#1", phi);
            }
            if (!before) seed.read(read, stored, 1L, "M_READ", "7");
            seed.flush();
            JsonObject lookup = com.google.gson.JsonParser.parseString(
                    scopeSite(StaticScopeMap.READ_SITE, "REGION.target",
                            "Lookup#get#u2", "Lookup#get", "<L: int stored>",
                            "<L: int stored>", "")).getAsJsonObject();
            if ((Boolean) row[3]) lookup.addProperty("demandDistance", 3);
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Guard#u8"), lookup.toString());

            Path out = tree.newFolder("concrete-" + at + "-out").toPath();
            Path results = results(out);
            Path wave = out.resolve("obligations-0000");
            JsonObject manifest = plan(iteration, TARGET_SELECTOR, null,
                    results, wave, 0);
            List<String> focused = new ArrayList<String>();
            for (JsonElement task : manifest.getAsJsonArray("taskRows")) {
                focused.add(task.getAsJsonObject().get("focused")
                        .getAsString());
            }
            String label = "case " + at + ": " + focused;
            assertEquals(label, row[5], focused.contains(WRITER.render()));
            assertEquals(label, row[5], named(obligations(wave),
                    "Door#u3") != null);
            JsonArray concrete = manifest.getAsJsonArray("concreteAnchors");
            int[] expected = (int[]) row[6];
            assertEquals(label + ": " + concrete, expected == null ? 0 : 1,
                    concrete.size());
            if (expected != null) {
                JsonObject anchor = concrete.get(0).getAsJsonObject();
                assertEquals(label, expected[0],
                        anchor.get("decided").getAsInt());
                assertEquals(label, expected[1],
                        anchor.get("reads").getAsInt());
                assertEquals(label, expected[2],
                        anchor.get("offCone").getAsInt());
            }
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

    /**
     * SYMBOL-SCOPE §4.2: a store version the anchor read through a decoded
     * object rests on the fetches of its location PLAN stated on the
     * target's data flow (the plan's {@code storeFetches}) on the reader's
     * node: a lost reply there registers no watch, so the node reads an
     * older version (solr-adhoc-40: node2's aliases watcher).  They join
     * contributing no value, and their store-read doors are asked.  Rows:
     * the occurrence the plan states (none, node2's, node1's) and whether
     * the read is on the anchor's provenance site.
     */
    @Test
    public void aStoreReadRestsOnItsNodesFetchesOfItsLocation()
            throws Exception {
        LocationId aliases = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/aliases.json");
        OccurrenceAddress processor = occurrence("solr-case/node2",
                "REGION.target", CausalContext.of(Role.of("TEST"), "", 1),
                "Processor#wrap#1");
        OccurrenceAddress fetched = occurrence("solr-case/node2",
                "REGION.watch", CausalContext.of(Role.of("WATCH"), "", 1),
                "Watcher#run#1");
        OccurrenceAddress elsewhere = occurrence("solr-case/node1",
                "REGION.watch", CausalContext.of(Role.of("WATCH"), "", 1),
                "Watcher#run#1");
        Object[][] cases = {
            {fetched, true, true},
            {null, true, false},
            {elsewhere, true, false},
            {fetched, false, false},
        };
        for (int at = 0; at < cases.length; at++) {
            OccurrenceAddress stated = (OccurrenceAddress) cases[at][0];
            boolean provenance = (Boolean) cases[at][1];
            Path iteration = tree.newFolder("fetch-" + at).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(processor, false);
            seed.activation(fetched, false, true, "watch2");
            seed.activation(elsewhere, false, true, "watch1");
            seed.marker(fetched, "CASE.READ2", "M_READ2", "false");
            seed.decision(fetched, "Read#u12", 1, false, "M_READ2");
            seed.marker(elsewhere, "CASE.READ1", "M_READ1", "false");
            seed.decision(elsewhere, "Read#u17", 1, false, "M_READ1");
            seed.read(at(processor, "Aliases#props#u2", "Aliases#props#2"),
                    aliases, 1L, "S_aliases1", null);
            seed.target(processor, "Guard#u8#1", "false");
            seed.flush();
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Guard#u8"), scopeSite(provenance
                            ? StaticScopeMap.PROVENANCE_SITE
                            : StaticScopeMap.READ_SITE, "",
                    "Aliases#props#u2", "Aliases#props",
                    "<A: java.util.Map props>", "<A: java.util.Map props>",
                    ""));
            Files.write(iteration.resolve(ExploreMain.REGION_PLAN),
                    (stated == null ? "" : "{\"kind\":\"CONCOLIC_REGION_PLAN\","
                            + "\"regionId\":\"REGION.watch\",\"occurrenceId\":\""
                            + stated.render() + "\",\"storeFetches\":[{\"siteId\":"
                            + "\"Read#u12\",\"ordinal\":1,\"fetch\":\"PROVENANCE\","
                            + "\"location\":\"SOLR_ZK:/aliases.json\",\"version\":1}]}\n")
                            .getBytes("UTF-8"));
            Path out = tree.newFolder("fetch-" + at + "-out").toPath();
            Path results = results(out);
            Path wave = out.resolve("obligations-0000");
            plan(iteration, "solr-case/node2#epoch0/region/REGION.target#1",
                    null, results, wave, 0);
            assertEquals("case " + at, cases[at][2],
                    named(obligations(wave), "Read#u12") != null);
            assertEquals("case " + at + ": another node's fetch", null,
                    named(obligations(wave), "Read#u17"));
        }
    }

    /**
     * IDENTITY §7.2: a turn that takes a queue item in at its root, before
     * any of its regions opened (the Overseer queue loop's turn), holds a
     * door of that item in every occurrence it runs: the item's other
     * consumer (the task's Runner, which wrote what the anchor read) names
     * it as a control producer, and its door is asked
     * (solr-bugs-overseer-lock-leak: markTaskAsRunning's ZooKeeper write);
     * so does the turn that sent it (RestoreCmd's RESTORECORE requests
     * before its offer); the Runner's own turn is what the item started, no
     * door of it, and a control producer contributes no value, so the doors
     * of its own item are not asked.
     */
    @Test
    public void aTurnThatTookAnItemInAtItsRootHoldsItsDoors()
            throws Exception {
        LocationId state = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/collections/c/state.json");
        OccurrenceAddress client = occurrence("solr-case/node1",
                "REGION.target", CausalContext.of(Role.of("TEST"), "", 1),
                "Processor#add#1");
        CausalContext runnerTurn = CausalContext.of(Role.of("OVERSEER_TASK"),
                "", 1);
        OccurrenceAddress runner = occurrence("solr-case/node0",
                "REGION.task", runnerTurn, "Runner#run#1");
        CausalContext queueTurn = CausalContext.of(
                Role.of("OVERSEER_TASK_QUEUE"), "", 1);
        OccurrenceAddress marking = occurrence("solr-case/node0",
                "REGION.mark", queueTurn, "Queue#mark#1");
        // Another occurrence of the Runner's turn.
        OccurrenceAddress sibling = occurrence("solr-case/node0",
                "REGION.sib", runnerTurn, "Runner#sib#1");
        // Per row: the queue turn's row of the item, at its root (no
        // occurrence) or not: a turn that took it in so or sent it holds a
        // door of it.
        Object[][] cases = {
            {ScheduleEvent.Kind.RECV, true},
            {ScheduleEvent.Kind.RECV, false},
            {ScheduleEvent.Kind.SEND, true},
        };
        for (int at = 0; at < cases.length; at++) {
            ScheduleEvent.Kind kind = (ScheduleEvent.Kind) cases[at][0];
            boolean rooted = (Boolean) cases[at][1];
            Path iteration = tree.newFolder("turn-" + at).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(client, false);
            seed.activation(runner, false, true, "runner");
            seed.activation(marking, false, true, "queue");
            seed.marker(marking, "CASE.DOOR", "M_DOOR", "false");
            seed.decision(marking, "Mark#u3", 1, false, "M_DOOR");
            seed.activation(sibling, false, true, "runner");
            seed.marker(sibling, "CASE.SIB", "M_SIB", "false");
            seed.decision(sibling, "Sib#u5", 1, false, "M_SIB");
            seed.write(at(runner, "SOLR_ZK#WRITE:.collections.c.state.json",
                    "Runner#run#1"), state, 1L, "", "[B");
            seed.read(at(client, "Processor#ro#u1", "Processor#ro#1"), state,
                    1L, "S_c1", null);
            seed.target(client, "Guard#u8#1", "false");
            seed.flush();
            List<JsonObject> schedule = new ArrayList<JsonObject>();
            // The queue turn's row first: its SEND, else a RECV of its own.
            schedule.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(1L,
                    kind, ContextShape.Stance.of(marking).render(),
                    "SOLR_ZK#REQUEST", 0, rooted ? "" : runner.id(),
                    "e-task")));
            // The Runner's turn takes the item in at its root.
            schedule.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(2L,
                    ScheduleEvent.Kind.RECV, ContextShape.Stance.of(runner)
                            .render(), "SOLR_ZK#REQUEST", 0, "", "e-task")));
            RowCodec.writeJsonl(SessionDir.of(iteration, "s-seed").schedule(),
                    schedule);
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Guard#u8"), scopeSite(StaticScopeMap.PROVENANCE_SITE, "",
                    "Processor#ro#u1", "Processor#ro",
                    "<P: boolean readOnly>", "<P: boolean readOnly>", ""));
            Path out = tree.newFolder("turn-" + at + "-out").toPath();
            Path results = results(out);
            Path wave = out.resolve("obligations-0000");
            plan(iteration, "solr-case/node1#epoch0/region/REGION.target#1",
                    null, results, wave, 0);
            assertEquals("case " + at, rooted,
                    named(obligations(wave), "Mark#u3") != null);
            // The Runner's own turn is no door of the item for the Runner,
            // and the queue turn's occurrence, a control producer, asks no
            // doors in turn.
            assertEquals("case " + at + ": the Runner's own turn", null,
                    named(obligations(wave), "Sib#u5"));
            // Each narrowing names what it cut (review M4).
            String gaps = RowCodec.readJsonl(wave.resolve(
                    ExploreMain.GAPS_FILE)).toString();
            assertTrue("case " + at + ": the own turn's cut is named",
                    gaps.contains("own turn hold no door of message e-task"));
        }
    }

    /**
     * A STORE WRITER'S ITEM SENDER IS A VALUE ({@code
     * ClosurePlanner#STORE_ITEM_PRODUCER}): the Overseer's state updater
     * wrote the state.json version the anchor read by applying the item the
     * task's Runner offered, so the version rests on the item's content (a
     * key it removed as much as a value it set:
     * solr-bugs-overseer-lock-leak's readOnly=""), and the doors of the
     * Runner's own item are asked -- the queue turn's markTaskAsRunning --
     * once: the item's submitter, a door of the Runner's item, is a control
     * producer whose own message is no question.  So is the writer of an
     * earlier version the read version rests on, though the read could
     * never have seen it (made under construction): PLAN's writers up to
     * the version read.
     */
    @Test
    public void aStoreWritersItemSenderIsAValue() throws Exception {
        LocationId state = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/collections/c/state.json");
        OccurrenceAddress client = occurrence("solr-case/node1",
                "REGION.target", CausalContext.of(Role.of("TEST"), "", 1),
                "Processor#add#1");
        OccurrenceAddress updater = occurrence("solr-case/node0",
                "REGION.update", CausalContext.of(
                        Role.of("OVERSEER_STATE_UPDATE"), "", 1),
                "Updater#run#1");
        CausalContext runnerTurn = CausalContext.of(Role.of("OVERSEER_TASK"),
                "", 1);
        OccurrenceAddress runner = occurrence("solr-case/node0",
                "REGION.task", runnerTurn, "Runner#offer#1");
        OccurrenceAddress sibling = occurrence("solr-case/node0",
                "REGION.sib", runnerTurn, "Runner#sib#1");
        OccurrenceAddress marking = occurrence("solr-case/node0",
                "REGION.mark", CausalContext.of(
                        Role.of("OVERSEER_TASK_QUEUE"), "", 1),
                "Queue#mark#1");
        OccurrenceAddress submitter = occurrence("solr-case/node0",
                "REGION.submit", CausalContext.of(Role.of("REQUEST"), "", 1),
                "Handler#submit#1");
        OccurrenceAddress front = occurrence("solr-case/node0",
                "REGION.front", CausalContext.of(Role.of("FRONT"), "", 1),
                "Front#take#1");
        // The earlier version's writer, its item's sender, and the queue
        // turn that took in that sender's own item.
        OccurrenceAddress setup = occurrence("solr-case/node0",
                "REGION.update", CausalContext.of(
                        Role.of("OVERSEER_STATE_UPDATE"), "", 2),
                "Updater#setup#1");
        OccurrenceAddress earlierRunner = occurrence("solr-case/node0",
                "REGION.task", CausalContext.of(Role.of("OVERSEER_TASK"), "",
                        2), "Runner#offer#2");
        OccurrenceAddress earlierMarking = occurrence("solr-case/node0",
                "REGION.mark", CausalContext.of(
                        Role.of("OVERSEER_TASK_QUEUE"), "", 2),
                "Queue#mark#2");
        Path iteration = tree.newFolder("item-sender").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(client, false);
        seed.activation(updater, false, true, "updater");
        seed.activation(setup, false, true, "updater");
        Object[][] doors = {{runner, "runner", "Run#u2"},
            {sibling, "runner", "Sib#u5"}, {marking, "queue", "Mark#u3"},
            {submitter, "request", "Sub#u4"}, {front, "front", "Front#u7"},
            {earlierRunner, "runner", "Run0#u9"},
            {earlierMarking, "queue", "Mark0#u10"}};
        for (Object[] door : doors) {
            OccurrenceAddress at = (OccurrenceAddress) door[0];
            String site = (String) door[2];
            seed.activation(at, false, true, (String) door[1]);
            seed.marker(at, "CASE." + site, "M_" + site.replace("#", "_"),
                    "false");
            seed.decision(at, site, 1, false, "M_" + site.replace("#", "_"));
        }
        seed.write(at(setup, "SOLR_ZK#WRITE:.collections.c.state.json",
                "<a.Setup: void <init>()>"), state, 1L, "", "[B");
        seed.write(at(updater, "SOLR_ZK#WRITE:.collections.c.state.json",
                "Updater#run#1"), state, 2L, "", "[B");
        seed.read(at(client, "Processor#ro#u1", "Processor#ro#1"), state, 2L,
                "S_c1", null);
        seed.target(client, "Guard#u8#1", "false");
        seed.flush();
        List<JsonObject> schedule = new ArrayList<JsonObject>();
        Object[][] events = {
            // the request's message, taken in at the front turn's root and
            // the submitter's
            {ScheduleEvent.Kind.RECV, front, "", "e-req"},
            {ScheduleEvent.Kind.RECV, submitter, "", "e-req"},
            // the task item: submitted, taken in by the queue turn and the
            // Runner's at their roots
            {ScheduleEvent.Kind.SEND, submitter, submitter.id(), "e-task"},
            {ScheduleEvent.Kind.RECV, marking, "", "e-task"},
            {ScheduleEvent.Kind.RECV, runner, "", "e-task"},
            // the state item the Runner offered, the updater's turn took in
            {ScheduleEvent.Kind.SEND, runner, runner.id(), "e-state"},
            {ScheduleEvent.Kind.RECV, updater, "", "e-state"},
            // the earlier version's: its writer applied the item the
            // earlier Runner offered, which ran the task the earlier queue
            // turn took in
            {ScheduleEvent.Kind.RECV, earlierMarking, "", "e-task0"},
            {ScheduleEvent.Kind.RECV, earlierRunner, "", "e-task0"},
            {ScheduleEvent.Kind.SEND, earlierRunner, earlierRunner.id(),
                    "e-state0"},
            {ScheduleEvent.Kind.RECV, setup, "", "e-state0"},
        };
        long seq = 1L;
        for (Object[] event : events) {
            schedule.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(seq++,
                    (ScheduleEvent.Kind) event[0], ContextShape.Stance.of(
                            (OccurrenceAddress) event[1]).render(),
                    "SOLR_ZK#REQUEST", 0, (String) event[2],
                    (String) event[3])));
        }
        RowCodec.writeJsonl(SessionDir.of(iteration, "s-seed").schedule(),
                schedule);
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"), scopeSite(StaticScopeMap.PROVENANCE_SITE, "",
                "Processor#ro#u1", "Processor#ro", "<P: boolean readOnly>",
                "<P: boolean readOnly>", ""));
        Path out = tree.newFolder("item-sender-out").toPath();
        Path results = results(out);
        Path wave = out.resolve("obligations-0000");
        plan(iteration, "solr-case/node1#epoch0/region/REGION.target#1", null,
                results, wave, 0);
        Object[][] rows = {
            {"Run#u2", true, "the item's sender, a value"},
            {"Mark#u3", true, "the queue turn, a door of the sender's item"},
            {"Sub#u4", true, "the item's submitter, a door of it"},
            {"Sib#u5", true,
                    "the sender's turn, a door of the state item it sent"},
            {"Front#u7", false,
                    "a door of a control producer's own message"},
            {"Run0#u9", true, "the earlier version's item sender"},
            {"Mark0#u10", true,
                    "a door of the earlier sender's own item, a value's"},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[2], row[1],
                    named(obligations(wave), (String) row[0]) != null);
        }
    }

    /**
     * A VALUE REASON OUTRANKS A DOOR'S ({@code ClosurePlanner.Demand
     * #absorb}): a control producer later reached as a store item's sender
     * is that sender, in either order, as PLAN states it; a member stays a
     * member; and a reason the rows connect is never replaced by a static
     * one, which wants the value all the same.
     */
    @Test
    public void aValueReasonOutranksADoorsReason() throws Exception {
        String[][] rows = {
            {ClosurePlanner.CONTROL_PRODUCER, ClosurePlanner.STORE_ITEM_PRODUCER,
                    ClosurePlanner.STORE_ITEM_PRODUCER, "true"},
            {ClosurePlanner.STORE_ITEM_PRODUCER, ClosurePlanner.CONTROL_PRODUCER,
                    ClosurePlanner.STORE_ITEM_PRODUCER, "true"},
            {ClosurePlanner.STORE_FETCH, ClosurePlanner.STORE_ITEM_PRODUCER,
                    ClosurePlanner.STORE_ITEM_PRODUCER, "true"},
            {ClosurePlanner.CLOSURE_MEMBER, ClosurePlanner.STORE_ITEM_PRODUCER,
                    ClosurePlanner.CLOSURE_MEMBER, "true"},
            {ClosurePlanner.CONTROL_PRODUCER,
                    ClosurePlanner.STATIC_CANDIDATE_WRITER,
                    ClosurePlanner.CONTROL_PRODUCER, "true"},
        };
        Class<?> shape = Class.forName(
                "edu.uva.liftlab.graphchecker.explore.ClosurePlanner$Demand");
        java.lang.reflect.Constructor<?> make = shape.getDeclaredConstructor(
                OccurrenceAddress.class, String.class, boolean.class);
        make.setAccessible(true);
        java.lang.reflect.Method absorb = shape.getDeclaredMethod("absorb",
                shape);
        absorb.setAccessible(true);
        java.lang.reflect.Field why = shape.getDeclaredField("why");
        why.setAccessible(true);
        java.lang.reflect.Field value = shape.getDeclaredField("value");
        value.setAccessible(true);
        OccurrenceAddress at = occurrence("solr-case/node0", "REGION.task",
                CausalContext.of(Role.of("OVERSEER_TASK"), "", 1),
                "Runner#offer#1");
        for (String[] row : rows) {
            Object held = make.newInstance(at, row[0], false);
            absorb.invoke(held, make.newInstance(at, row[1], false));
            assertEquals(row[0] + " then " + row[1], row[2], why.get(held));
            assertEquals(row[0] + " then " + row[1],
                    Boolean.valueOf(row[3]), value.get(held));
        }
    }

    /** A phi whose expression names its own read (ConcreteAnchor case). */
    private static final String NAMES_ITS_READ = "EXPR.00000000000000a7";

    /** {@code read == 7}, the read node at {@code event} of {@code at}. */
    private static JsonObject readTest(long event, LocationId at) {
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", Long.parseLong(at.owner()));
        location.addProperty("slot", Integer.parseInt(at.slot()));
        location.addProperty("locationKind", "INSTANCE_FIELD");
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 1L);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty("_java_type", "I");
        read.addProperty("readEventId", event);
        read.add("location", location);
        read.add("observedVersion", version);
        read.addProperty("writerSetComplete", true);
        read.addProperty("observedExact", true);
        JsonObject seven = new JsonObject();
        seven.addProperty("_type", "ConstExpr");
        seven.addProperty("_java_type", "I");
        seven.addProperty("_exp", "Y_I_7");
        JsonObject test = new JsonObject();
        test.addProperty("_type", "BinaryExpression");
        test.addProperty("_op", "==");
        test.add("_left", read);
        test.add("_right", seven);
        return test;
    }

    /**
     * The locations a term reads are every read node its expression holds,
     * each node walked once and to the end: a chain whose nodes name the one
     * below twice is 2^64 paths as a tree, and a read 100000 deep lay past
     * the walk's depth-64 cap.
     */
    @Test(timeout = 120_000L)
    public void aTermRestsOnAReadDeepInASharedChain() throws Exception {
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "MAP_STATE");
        location.addProperty("ownerSymRid", 474L);
        location.addProperty("slot", -3L);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty("_java_type", "I");
        read.add("location", location);
        read.addProperty("readEventId", 9L);
        JsonObject one = new JsonObject();
        one.addProperty("_type", "ConstExpr");
        one.addProperty("_java_type", "I");
        one.addProperty("_exp", "Y_I_1");
        for (int depth : new int[]{64, 100_000}) {
            JsonObject chain = read;
            for (int level = 0; level < depth; level++) {
                JsonObject sum = new JsonObject();
                sum.addProperty("_type", "BinaryExpression");
                sum.addProperty("_op", "+");
                sum.add("_left", chain);
                sum.add("_right", depth == 64 ? chain : one);
                chain = sum;
            }
            Path iteration = tree.newFolder("deep-" + depth).toPath();
            Session session = new Session(iteration, "s-deep");
            session.activation(TARGET, false);
            session.expression("EXPR.0000000000000001", chain);
            session.flush();
            assertEquals(depth + " levels", Collections.singleton(
                    SmtLowering.locationKey(location)),
                    Corpus.read(iteration, null).readLocations("s-deep",
                            "(not EXPR.0000000000000001)"));
        }
    }

    /** One session of a synthetic corpus, written in the contract's layout. */
    /**
     * THE PAIRING FLIP's candidates ({@link PairingFlip}): the anchor's task
     * offers each older decode of its node's view to its earliest read of
     * the view -- here one its node made under its causal context in role
     * work before it opened --, newest first, at most {@link
     * PairingFlip#PER_READ}, the rest a counted {@code pairing-bound} gap; a
     * task that is no anchor's and writes no store version offers none.
     * Solved, the world holds the read to the decode, and the schedule
     * prefix ends before the later decode recorded before the read.
     */
    @Test
    public void aViewReadIsOfferedEachOlderDecodeOfItsNode()
            throws Exception {
        for (boolean anchor : new boolean[] {true, false}) {
            Path iteration = tree.newFolder("pairing-" + anchor).toPath();
            LocationId view = LocationId.of(LocationKind.VIEW,
                    "SOLR_ZK@hdfs-case/dn0#epoch0", "/aliases.json");
            OccurrenceAddress role = OccurrenceAddress.of(TARGET.node(),
                    OccurrenceAddress.ROLE_REGION + "DATA_XCEIVER",
                    TARGET.context(), ExecutionIndex.empty());
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            Endpoint decoder = at(WRITER, "SOLR_ZK#VIEW:.aliases.json",
                    "decode#1");
            for (long version = 0L; version <= 10L; version++) {
                seed.write(decoder, view, version, "", "J");
            }
            seed.read(at(role, "SOLR_ZK#VIEWED:|aliases.json#VIEW",
                    "getAliases#1"), view, 10L, "V_p", "10");
            seed.read(at(TARGET, "Guard#u3#VIEW",
                    "o.a.h.h.s.d.DataXceiver#run#12"), view, 10L, "V_t",
                    "10");
            seed.decision(TARGET, "Guard#u8", 1, false, "(= M_A 1)");
            if (anchor) seed.target(TARGET, "Guard#u8", "(= M_A 1)");
            seed.flush();
            Corpus corpus = Corpus.read(iteration, null);
            Task task = Task.of("T", TARGET,
                    Collections.<OccurrenceAddress>emptyList(), "s-seed");
            List<GapRow> gaps = new ArrayList<GapRow>();
            List<ObligationFactory.Candidate> offered =
                    PairingFlip.candidates(corpus, task,
                            corpus.pathsOf(TARGET).get(0), gaps);
            if (!anchor) {
                assertTrue("no anchor's, no store write: " + offered,
                        offered.isEmpty());
                continue;
            }
            assertEquals(PairingFlip.PER_READ, offered.size());
            assertEquals(9L, offered.get(0).pairedVersion);
            assertEquals(10, offered.get(0).ordinal());
            assertEquals(2L, offered.get(PairingFlip.PER_READ - 1)
                    .pairedVersion);
            assertEquals(role, offered.get(0).pairedRead.endpoint()
                    .occurrence());
            assertTrue(offered.get(0).pairing()
                    && offered.get(0).flippedOutcome()
                    && Obligation.pairing(offered.get(0).siteId()));
            assertEquals(1, gaps.size());
            assertEquals("T pairing-bound=" + PairingFlip.PER_READ,
                    gaps.get(0).subject());
            // Solved with no query: the world's pairing, held by a STATE row
            // to the decode's version and a VIEW_HOLD; located back off its
            // published row.
            ObligationFactory.Candidate newest = offered.get(0);
            ObligationFactory.Outcome outcome = PairingFlip.solve(corpus,
                    newest, "given", Collections
                            .<String, ObligationDir.Answer>emptyMap());
            assertEquals(Verdict.SAT_MODEL_READY, outcome.result.verdict());
            assertEquals("VIEW@9", outcome.pairings.get(Confirmation.id(
                    newest.pairedRead.endpoint())));
            List<String> kinds = new ArrayList<String>();
            for (JsonObject edge : outcome.holding.edges) {
                kinds.add(edge.get("kind").getAsString());
            }
            assertEquals(Arrays.asList("STATE", "VIEW_HOLD"), kinds);
            // The schedule cut stops before the decode the hold reorders
            // (version 10, before the read), not before its occurrence.
            assertEquals(corpus.writeOf("s-seed", view, 10L).seq(),
                    outcome.holding.cutBefore);
            assertTrue(outcome.holding.reordered.isEmpty());
            ObligationFactory.Candidate located = PairingFlip.locate(corpus,
                    task, corpus.pathsOf(TARGET).get(0),
                    outcome.obligation);
            assertEquals(9L, located.pairedVersion);
            assertEquals(newest.siteId(), located.siteId());
        }
    }

    /**
     * A pairing flip never asks a version older than a decode the reader's
     * own work made before the read: the hold never holds that work's own
     * decodes, so its view is at least that one's ({@link PairingFlip}).
     */
    @Test
    public void aViewReadIsOfferedNoDecodeOlderThanItsOwnWorksLast()
            throws Exception {
        Path iteration = tree.newFolder("pairing-own").toPath();
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs-case/dn0#epoch0", "/aliases.json");
        OccurrenceAddress role = OccurrenceAddress.of(TARGET.node(),
                OccurrenceAddress.ROLE_REGION + "DATA_XCEIVER",
                TARGET.context(), ExecutionIndex.empty());
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        Endpoint decoder = at(WRITER, "SOLR_ZK#VIEW:.aliases.json",
                "decode#1");
        Endpoint own = at(role, "SOLR_ZK#VIEW:.aliases.json", "decode#2");
        for (long version = 0L; version <= 5L; version++) {
            seed.write(version == 2L ? own : decoder, view, version, "", "J");
        }
        seed.read(at(TARGET, "Guard#u3#VIEW",
                "o.a.h.h.s.d.DataXceiver#run#12"), view, 5L, "V_t", "5");
        seed.decision(TARGET, "Guard#u8", 1, false, "(= M_A 1)");
        seed.target(TARGET, "Guard#u8", "(= M_A 1)");
        seed.flush();
        Corpus corpus = Corpus.read(iteration, null);
        Task task = Task.of("T", TARGET,
                Collections.<OccurrenceAddress>emptyList(), "s-seed");
        List<Long> versions = new ArrayList<Long>();
        for (ObligationFactory.Candidate offered : PairingFlip.candidates(
                corpus, task, corpus.pathsOf(TARGET).get(0),
                new ArrayList<GapRow>())) {
            versions.add(offered.pairedVersion);
        }
        assertEquals(Arrays.asList(4L, 3L, 2L), versions);
    }

    /**
     * Decodes and reads the engine states at one VM event stand in the order
     * it stated them ({@link RowOrder}: seq, then tie; review re-check B3):
     * the decode of 2 tied before the read is an older decode it is offered,
     * and the decode of 3 tied before it is one the pairing's hold reorders,
     * so the schedule cut stops before it; the view's INITIAL (what the node
     * held when the window opened, seq 0) is offered too.  The decode of 4,
     * tied after the read, is none of them.
     */
    @Test
    public void tiedDecodesStandInTheOrderTheEngineStatedThem()
            throws Exception {
        Path iteration = tree.newFolder("pairing-tied").toPath();
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs-case/dn0#epoch0", "/aliases.json");
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        Endpoint decoder = at(WRITER, "SOLR_ZK#VIEW:.aliases.json",
                "decode#1");
        seed.writes.add(WriteRow.initial("s-seed", 0L, at(TARGET,
                Endpoint.initialSite("SOLR_ZK#VIEW:.aliases.json"),
                "first#1"), view, 0L, "", "J"));
        long[][] decodes = {{1L, 5L, 1L}, {2L, 8L, 1L}, {3L, 8L, 2L},
                {4L, 8L, 4L}};
        for (long[] decode : decodes) {
            seed.writes.add(WriteRow.of("s-seed", decode[1], decoder, view,
                    decode[0], "", "J").withTie((int) decode[2]));
        }
        seed.reads.add(ReadRow.of("s-seed", 8L, at(TARGET, "Guard#u3#VIEW",
                "o.a.h.h.s.d.DataXceiver#run#12"), view, 3L, "V_t", "J",
                "3").withTie(3));
        seed.decision(TARGET, "Guard#u8", 1, false, "(= M_A 1)");
        seed.target(TARGET, "Guard#u8", "(= M_A 1)");
        seed.flush();
        Corpus corpus = Corpus.read(iteration, null);
        Task task = Task.of("T", TARGET,
                Collections.<OccurrenceAddress>emptyList(), "s-seed");
        List<ObligationFactory.Candidate> offered = PairingFlip.candidates(
                corpus, task, corpus.pathsOf(TARGET).get(0),
                new ArrayList<GapRow>());
        List<Long> versions = new ArrayList<Long>();
        for (ObligationFactory.Candidate candidate : offered) {
            versions.add(candidate.pairedVersion);
        }
        assertEquals(Arrays.asList(2L, 1L, 0L), versions);
        ObligationFactory.Outcome outcome = PairingFlip.solve(corpus,
                offered.get(0), "given", Collections
                        .<String, ObligationDir.Answer>emptyMap());
        assertEquals(8L, outcome.holding.cutBefore);
    }

    /**
     * A view no publication hook publishes (no PUBLISHED_VIEW: Solr's
     * legacy clusterstate.json, a snapshot's metadata) offers no pairing
     * flip: no hold could defer it, and its read is named, never left to
     * give way at the bound.
     */
    @Test
    public void aViewNoHookPublishesOffersNoPairing() throws Exception {
        Path iteration = tree.newFolder("pairing-unhooked").toPath();
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@hdfs-case/dn0#epoch0", "/clusterstate.json");
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        Endpoint decoder = at(WRITER, "SOLR_ZK#VIEW:.clusterstate.json",
                "decode#1");
        for (long version = 0L; version <= 2L; version++) {
            seed.write(decoder, view, version, "", "J");
        }
        seed.read(at(TARGET, "Guard#u3#VIEW",
                "o.a.h.h.s.d.DataXceiver#run#12"), view, 2L, "V_t", "2");
        seed.decision(TARGET, "Guard#u8", 1, false, "(= M_A 1)");
        seed.target(TARGET, "Guard#u8", "(= M_A 1)");
        seed.flush();
        Corpus corpus = Corpus.read(iteration, null);
        Task task = Task.of("T", TARGET,
                Collections.<OccurrenceAddress>emptyList(), "s-seed");
        List<GapRow> gaps = new ArrayList<GapRow>();
        assertTrue(PairingFlip.candidates(corpus, task,
                corpus.pathsOf(TARGET).get(0), gaps).isEmpty());
        assertTrue(gaps.toString(), gaps.size() == 1 && gaps.get(0).detail()
                .contains("no publication hook publishes"));
    }

    /**
     * A role's view read is the occurrence's prefix when it stands before
     * the occurrence's first row by the one order ({@link RowOrder}), a tie
     * at one seq included (round SG3A tra: the seed's read at (538, 12), its
     * alias update's store write at (538, 24); by seq alone the seed offered
     * no pairing flip).  Tied after that row, it is none.
     */
    @Test
    public void aRolesReadTiedBeforeTheOccurrenceOpensIsItsPrefix()
            throws Exception {
        for (int readTie : new int[] {2, 4}) {
            Path iteration = tree.newFolder("pairing-prefix-" + readTie)
                    .toPath();
            LocationId view = LocationId.of(LocationKind.VIEW,
                    "SOLR_ZK@hdfs-case/dn0#epoch0", "/aliases.json");
            LocationId store = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                    "/aliases.json");
            OccurrenceAddress role = OccurrenceAddress.of(TARGET.node(),
                    OccurrenceAddress.ROLE_REGION + "SOLR_HTTP",
                    TARGET.context(), ExecutionIndex.empty());
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            Endpoint decoder = at(WRITER, "SOLR_ZK#VIEW:.aliases.json",
                    "decode#1");
            seed.writes.add(WriteRow.of("s-seed", 5L, decoder, view, 1L, "",
                    "J").withTie(1));
            seed.writes.add(WriteRow.of("s-seed", 8L, decoder, view, 2L, "",
                    "J").withTie(1));
            seed.reads.add(ReadRow.of("s-seed", 8L, at(role,
                    "SOLR_ZK#VIEWED:|aliases.json#VIEW", "getAliases#1"),
                    view, 2L, "V_p", "J", "2").withTie(readTie));
            // The occurrence opens with its store write, tied at 3.
            seed.writes.add(WriteRow.of("s-seed", 8L, at(TARGET,
                    "SOLR_ZK#STORE:/aliases.json", "setData#1"), store, 3L,
                    "", "[B").withTie(3));
            seed.flush();
            Corpus corpus = Corpus.read(iteration, null);
            Task task = Task.of("T", TARGET,
                    Collections.<OccurrenceAddress>emptyList(), "s-seed");
            List<Long> versions = new ArrayList<Long>();
            for (ObligationFactory.Candidate offered : PairingFlip.candidates(
                    corpus, task, corpus.pathsOf(TARGET).get(0),
                    new ArrayList<GapRow>())) {
                versions.add(offered.pairedVersion);
            }
            assertEquals("read tied " + readTie, readTie < 3
                    ? Collections.singletonList(1L)
                    : Collections.<Long>emptyList(), versions);
        }
    }

    /**
     * A corpus read again (a host's solver, after a landing) takes each
     * session the read before holds and the iteration still lists as it
     * is, unread: a landed session never changes.  A session that landed is
     * read; one that left is gone.
     */
    @Test
    public void aCorpusReadAgainKeepsTheSessionsItHolds() throws Exception {
        Path iteration = tree.newFolder("reread").toPath();
        for (String id : new String[] {"s-seed", "s-left"}) {
            Session session = new Session(iteration, id);
            session.activation(TARGET, false);
            session.flush();
        }
        Corpus before = Corpus.read(iteration, null);
        Session landed = new Session(iteration, "s-landed");
        landed.activation(TARGET, true);
        landed.flush();
        try (java.util.stream.Stream<Path> files = Files.walk(
                SessionDir.of(iteration, "s-left").dir())) {
            files.sorted(Collections.reverseOrder())
                    .forEach(path -> path.toFile().delete());
        }
        Corpus after = Corpus.read(iteration, null, before, null);
        assertTrue("kept, unread",
                before.session("s-seed") == after.session("s-seed"));
        assertNotNull("read", after.session("s-landed"));
        assertNull("gone", after.session("s-left"));
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

        /** A FORCE run's decision, forced off the arm its operands took. */
        private void forcedDecision(OccurrenceAddress occurrence, String site,
                                    int ordinal, boolean outcome,
                                    String term) {
            forced = true;
            decisions.add(DecisionRow.of(sessionId, ++seq, occurrence, site,
                    ordinal, outcome, term,
                    Collections.<String, Long>emptyMap()).forced(!outcome));
        }

        /** A FORCE run's target, standing at {@code from}: the forced path
         *  condition as its phi. */
        private void forcedTarget(OccurrenceAddress occurrence, String site,
                                  long from, String phi) {
            forced = true;
            targets.add(TargetRow.of(sessionId, from, occurrence, site, phi,
                    false, true).forced());
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
