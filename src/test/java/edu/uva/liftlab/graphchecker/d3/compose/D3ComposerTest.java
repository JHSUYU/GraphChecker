package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.Role;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.NodeId;
import edu.uva.liftlab.graphchecker.d3.contract.Frame;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;

import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * The composition rule, on a corpus small enough to read.
 *
 * <p>Every fixture here is two or three sessions of one wire interaction:
 * a producer that exports an expression over a declared marker, and a
 * consumer that reads it at the anchor.  That is the smallest shape in
 * which the rules the evidence settled can be told apart -- per-path
 * arrivals from a global pin, two producers on one port from one family,
 * an attested arm from an unattested one, and a witness with polarity from
 * a formula that was satisfiable all along.</p>
 */
public class D3ComposerTest {

    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    private static final OccurrenceAddress ANCHOR =
            occurrence("case/dn0#epoch0", "REGION.target", 1);
    private static final OccurrenceAddress PRODUCER =
            occurrence("case/nn0#epoch0", "REGION.nn", 1);
    private static final OccurrenceAddress UPSTREAM =
            occurrence("case/nn1#epoch0", "REGION.up", 1);
    private static final String ANCHOR_SITE = "BlockManager#get#8:READ";
    private static final String MARKER = "marker_m";
    private static final String MARKER_ROOT = "ROOT.MARKER";

    // ------------------------------------------------------------------
    // 1. Polarity: the recording is refuted, the flip reaches the failure.
    // ------------------------------------------------------------------

    @Test
    public void theHealthyRecordingIsRefutedAndTheFlipIsTheWitness()
            throws Exception {
        Path iteration = folder.newFolder("marker").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key", siteIndex(1), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key", siteIndex(1), 0);
        session(iteration, "s0", false, "false", producer, consumer,
                "vh", "false", null, true, false, "EXPR.v1.marker");
        session(iteration, "s1", true, "true", producer, consumer,
                "vh", "true", null, true, true, "EXPR.v1.marker");

        Composer.Composition composition = compose(iteration, 8);
        assertEquals("both sessions are admitted", 2,
                composition.paths().size());
        assertEquals("two valuations: recorded, and the marker flipped", 2,
                composition.valuations().size());

        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertEquals("unsat", decision.outcomes().get(0).answer().status());
        assertEquals("sat", decision.outcomes().get(1).answer().status());
        assertEquals(ClaimKind.MARKER_FLIPPED, decision.claim().kind());
        assertTrue("the recorded valuation refutes the recording",
                decision.claim().polarityDecides());
        assertEquals("the marker is what moved",
                Collections.singletonMap(MARKER_ROOT, "true"),
                decision.claim().movedRoots());
        assertEquals("the witness rests on the session that observed the "
                        + "fatal arm", "s1",
                decision.outcomes().get(1).selected().path().sessionId());
    }

    // ------------------------------------------------------------------
    // 2. Two producers on one port are two interactions, two families.
    // ------------------------------------------------------------------

    @Test
    public void twoProducersOnOnePortAreTwoFamilies() throws Exception {
        Path iteration = folder.newFolder("families").toPath();
        Endpoint first = Endpoint.of(PRODUCER, "PORT.key", siteIndex(1), 0);
        Endpoint second = Endpoint.of(PRODUCER, "PORT.key", siteIndex(2), 0);
        Session session = new Session(iteration, "s0", false);
        session.marker("false");
        session.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        session.export(first, "EXPR.v1.marker", 1L, "false");
        session.export(second, "EXPR.v1.marker", 2L, "false");
        session.attach(Endpoint.of(ANCHOR, "PORT.key", siteIndex(1), 0), "vh1",
                "false", first);
        session.attach(Endpoint.of(ANCHOR, "PORT.key", siteIndex(2), 0), "vh2",
                "false", second);
        session.target("(and vh1 vh2)", false, true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        assertEquals("one attach per producer endpoint is one family each",
                2, composition.families().size());
        assertEquals("and the disjunct reaches both", 2,
                composition.disjuncts().get(0).interactionIds().size());
    }

    // ------------------------------------------------------------------
    // 3. A witness may not move a root inside an unattested arm.
    // ------------------------------------------------------------------

    @Test
    public void aWitnessMayNotMoveARootInsideAnUnattestedArm()
            throws Exception {
        Path iteration = folder.newFolder("unattested").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key", siteIndex(1), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key", siteIndex(1), 0);
        // The producer ran concretely in both sessions: no decision of its
        // occurrence is recorded anywhere, so every arm is unattested.
        session(iteration, "s0", false, "false", producer, consumer,
                "vh", "false", null, false, false, "EXPR.v1.marker");
        session(iteration, "s1", true, "true", producer, consumer,
                "vh", "true", null, false, true, "EXPR.v1.marker");

        Composer.Composition composition = compose(iteration, 8);
        assertTrue("the marker is inside an unattested arm",
                composition.unattestedRoots().values().toString()
                        .contains(MARKER_ROOT));

        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertEquals("sat", decision.outcomes().get(1).answer().status());
        assertEquals("the move is satisfiable and is refused anyway",
                ClaimKind.NO_SUPPORTED_WITNESS, decision.claim().kind());
        assertTrue("and the refusal is named",
                named(decision.claim().gaps(), GapKind.UNATTESTED_ARM));
    }

    // ------------------------------------------------------------------
    // 4. A handoff whose delivery is itself a handoff is closed.
    // ------------------------------------------------------------------

    @Test
    public void aNestedHandoffIsClosedTransitively() throws Exception {
        Path iteration = folder.newFolder("nested").toPath();
        Endpoint upstream = Endpoint.of(UPSTREAM, "PORT.up", siteIndex(1), 0);
        Endpoint forwarded = Endpoint.of(PRODUCER, "PORT.up", siteIndex(1), 0);
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key", siteIndex(1), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key", siteIndex(1), 0);

        Session session = new Session(iteration, "s0", false);
        session.marker("false");
        session.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        // What the middle node exports is what it was itself handed.
        session.expression("EXPR.v1.forward", symbol("vh_up", "Z"));
        session.decision(UPSTREAM, "up#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        session.export(upstream, "EXPR.v1.marker", 1L, "false");
        session.attach(forwarded, "vh_up", "false", upstream);
        session.decision(PRODUCER, "nn#u1", "(or vh_up (not vh_up))");
        session.export(producer, "EXPR.v1.forward", 2L, "false");
        session.attach(consumer, "vh", "false", producer);
        session.target("vh", false, true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        assertEquals("the family of the family is in the formula too", 2,
                composition.families().size());
        assertTrue("and the chain reaches the upstream interaction",
                composition.body().contains("vh_up"));
        assertTrue("the upstream delivery carries the root",
                composition.body().contains(MARKER));
    }

    // ------------------------------------------------------------------
    // 5. Each path carries its own session's arrival.
    // ------------------------------------------------------------------

    @Test
    public void eachPathCarriesItsOwnSessionsArrival() throws Exception {
        Path iteration = folder.newFolder("arrivals").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.id", siteIndex(1), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.id", siteIndex(1), 0);
        for (String[] each : new String[][]{{"s0", "10", "false"},
                {"s1", "20", "true"}}) {
            Session session = new Session(iteration, each[0],
                    "true".equals(each[2]));
            session.marker("false");
            // No producer path is attested and no arm is published, so the
            // arrival is all this session states -- and the two sessions
            // recorded two different arrivals at the one attach.
            session.attach(consumer, "vh", "I", each[1], producer);
            session.target("true", false, true);
            session.write();
        }

        Composer.Composition composition = compose(iteration, 4);
        assertEquals(2, composition.disjuncts().size());
        Solver solver = solver();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            List<String> pinned = new ArrayList<String>(
                    composition.valuations().get(0).assertions());
            pinned.add("(assert " + disjunct.selector() + ")");
            assertEquals("each path is satisfiable as the execution that "
                            + "made it: " + disjunct.path().sessionId(),
                    "sat", solver.ask(composition.body(), pinned,
                            Collections.<String>emptyList(), false).status());
        }
    }

    // ------------------------------------------------------------------
    // 6. A declared occurrence nothing reached is a claim, not a crash.
    // ------------------------------------------------------------------

    @Test
    public void anUnreachedDeclarationIsAClaimAndNotACrash()
            throws Exception {
        Path iteration = folder.newFolder("missing").toPath();
        Session session = new Session(iteration, "s0", false);
        session.marker("false");
        // This session ran, and reached an occurrence that is not the one
        // the case declared.
        session.occurrence = PRODUCER;
        session.target("true", false, true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertEquals(ClaimKind.NO_SUPPORTED_WITNESS, decision.claim().kind());
        assertTrue("and it says the declaration was never reached",
                named(decision.claim().gaps(), GapKind.DECLARATION_MISSING));
        assertFalse("nothing was composed", composition.disjuncts().size() > 0);
    }

    // ------------------------------------------------------------------
    // Fixture.
    // ------------------------------------------------------------------

    private Composer.Composition compose(Path iteration, int maxValuations)
            throws IOException {
        return Composer.compose(CorpusIndex.of(iteration), ANCHOR,
                Collections.<String,
                        edu.uva.liftlab.graphchecker.d3.contract.RootDomain>
                        emptyMap(), maxValuations);
    }

    private Solver solver() {
        Path z3 = Paths.get("/usr/local/bin/z3");
        if (!Files.isExecutable(z3)) z3 = Paths.get("z3");
        Assume.assumeTrue("z3 is not on this machine",
                Files.isExecutable(z3) || !z3.isAbsolute());
        return new Solver(z3, 30000L);
    }

    private static boolean named(List<GapRow> gaps, GapKind kind) {
        for (GapRow gap : gaps) {
            if (gap.kind() == kind) return true;
        }
        return false;
    }

    private static JsonObject symbol(String name, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", name);
        node.addProperty("_java_type", javaType);
        return node;
    }

    /** One session of the fixture, written the way the runtime writes it. */
    private static final class Session {
        private final Path iteration;
        private final String id;
        private final boolean explored;
        private OccurrenceAddress occurrence = ANCHOR;
        /** The session's own monotonic event order. */
        private long seq;
        private final List<ActivationRow> activations =
                new ArrayList<ActivationRow>();
        private final List<DecisionRow> decisions =
                new ArrayList<DecisionRow>();
        private final List<ExportRow> exports = new ArrayList<ExportRow>();
        private final List<AttachRow> attaches = new ArrayList<AttachRow>();
        private final List<RootMintRow> roots =
                new ArrayList<RootMintRow>();
        private final List<TargetRow> targets = new ArrayList<TargetRow>();
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<String, JsonObject>();

        Session(Path iteration, String id, boolean explored) {
            this.iteration = iteration;
            this.id = id;
            this.explored = explored;
            activations.add(ActivationRow.of(id, ANCHOR,
                    explored ? "task-flip" : "task-seed", explored));
            this.seq = 0L;
        }

        void marker(String recorded) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, MARKER_ROOT, MARKER,
                    RootKind.MARKER, recorded, null, null, true));
        }

        void expression(String ref, JsonObject node) {
            expressions.put(ref, node);
        }

        void export(Endpoint endpoint, String ref, long handle,
                    String recorded) {
            exports.add(ExportRow.of(id, ++seq, endpoint, ref, "Z", handle,
                    recorded));
        }

        void attach(Endpoint endpoint, String symbol, String arrival,
                    Endpoint producer) {
            attach(endpoint, symbol, "Z", arrival, producer);
        }

        void attach(Endpoint endpoint, String symbol, String javaType,
                    String arrival, Endpoint producer) {
            attaches.add(AttachRow.of(id, ++seq, endpoint, symbol, javaType,
                    arrival, false, null, producer, "corr-" + symbol));
        }

        void decision(OccurrenceAddress at, String site, String term) {
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, true, term,
                    Collections.<String, Long>emptyMap()));
        }

        void target(String phi, boolean observedFatal, boolean reached) {
            targets.add(TargetRow.of(id, ++seq, occurrence, ANCHOR_SITE, phi,
                    observedFatal, reached));
        }

        void write() throws IOException {
            SessionDir dir = SessionDir.of(iteration, id).create();
            RowCodec.writeAll(dir.activations(), activations,
                    RowCodec::writeActivation);
            RowCodec.writeAll(dir.decisions(), decisions,
                    RowCodec::writeDecision);
            RowCodec.writeAll(dir.exports(), exports, RowCodec::writeExport);
            RowCodec.writeAll(dir.attaches(), attaches,
                    RowCodec::writeAttach);
            RowCodec.writeAll(dir.roots(), roots, RowCodec::writeRootMint);
            RowCodec.writeAll(dir.targets(), targets, RowCodec::writeTarget);
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
        }
    }

    /**
     * One session of the marker fixture: a producer exporting the marker,
     * a consumer reading it at the anchor.
     */
    private void session(Path iteration, String id, boolean explored,
                         String marker, Endpoint producer, Endpoint consumer,
                         String symbol, String arrival, String answered,
                         boolean attestProducer, boolean observedFatal,
                         String ref) throws IOException {
        Session session = new Session(iteration, id, explored);
        session.marker(marker);
        session.expression(ref, symbol(MARKER, "Z"));
        // The producer decides, then exports: a family arm is guarded by
        // the prefix its own session had taken by then.
        if (attestProducer) {
            session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
        }
        session.export(producer, ref, 1L, marker);
        session.attach(consumer, symbol, arrival, producer);
        // phi is published in the FATAL polarity by the runtime, healthy
        // sessions included; the composer never re-derives it.
        session.target(symbol, observedFatal, true);
        session.write();
        assertNotNull(answered == null ? "" : answered);
    }

    /**
     * The site index of the k-th event at one site, for a fixture.
     *
     * <p>Contract v2.0 replaced the site ordinal with the execution index of
     * the frames between the region and the event (IDENTITY-IMPL section A).
     * A fixture has no real stack, so one frame carrying k is what "the k-th
     * event of this site" means here: distinct per k, stable across runs.</p>
     */
    private static ExecutionIndex siteIndex(int k) {
        return ExecutionIndex.of(Collections.singletonList(
                Frame.of("Fixture#site#0", k)));
    }


    /**
     * One occurrence of a region on a node, as contract v2.0 addresses it.
     *
     * <p>The fixture states the causal context a real recording would carry
     * from its scope -- a daemon tick of the region's role, the k-th of the
     * window -- and one frame of execution index, which is what "the k-th
     * activation" meant before the index replaced the ordinal.</p>
     */
    private static OccurrenceAddress occurrence(String node, String region,
                                                int k) {
        return OccurrenceAddress.of(NodeId.parse(node), region,
                CausalContext.of(Role.BP_SERVICE_ACTOR, k),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("Fixture#" + region + "#0", 0))));
    }

}
