package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.Frame;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.NodeId;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
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

    /** The target region, started by the request the case is about. */
    private static final OccurrenceAddress ANCHOR = occurrence("case/dn0",
            "REGION.target",
            CausalContext.of("producer-endpoint", "case/client/read-block"),
            frame("DataXceiver#run#12", 0));
    private static final OccurrenceAddress PRODUCER = occurrence("case/nn0",
            "REGION.nn", CausalContext.of(Role.IPC_HANDLER, 1),
            frame("Server#call#40", 0));
    private static final OccurrenceAddress UPSTREAM = occurrence("case/nn1",
            "REGION.up", CausalContext.of(Role.KEY_MANAGER_TICK, 1),
            frame("KeyManager#tick#8", 0));
    private static final String ANCHOR_SITE = "BlockManager#get#8:READ";
    private static final String MARKER = "marker_m";
    private static final String MARKER_ROOT = "ROOT.MARKER";
    private static final String SERIAL = "serial_s";
    private static final String SERIAL_ROOT = "ROOT.SERIAL";

    // ------------------------------------------------------------------
    // 1. Polarity: the recording is refuted, the flip reaches the failure.
    // ------------------------------------------------------------------

    @Test
    public void theHealthyRecordingIsRefutedAndTheFlipIsTheWitness()
            throws Exception {
        Path iteration = folder.newFolder("marker").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
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
        // Two exports at ONE port: two site-local execution indexes, so two
        // endpoints, so two interactions.
        Endpoint first = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint second = Endpoint.of(PRODUCER, "PORT.key",
                at("export#2", 0), 0);
        Session session = new Session(iteration, "s0", false);
        session.marker("false");
        session.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        session.export(first, "EXPR.v1.marker", 1L, "false");
        session.export(second, "EXPR.v1.marker", 2L, "false");
        session.attach(Endpoint.of(ANCHOR, "PORT.key", at("attach#1", 0), 0),
                "vh1", "false", first);
        session.attach(Endpoint.of(ANCHOR, "PORT.key", at("attach#2", 0), 0),
                "vh2", "false", second);
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
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        // The producer ran CONCRETELY in both sessions -- its activation is
        // not instrumented -- so the recording can say what it delivered and
        // nothing about what it would have delivered.
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
        Endpoint upstream = Endpoint.of(UPSTREAM, "PORT.up",
                at("export#1", 0), 0);
        Endpoint forwarded = Endpoint.of(PRODUCER, "PORT.up",
                at("attach#1", 0), 0);
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);

        Session session = new Session(iteration, "s0", false);
        session.activation(PRODUCER);
        session.activation(UPSTREAM);
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
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.id",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.id",
                at("attach#1", 0), 0);
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
    // 7. A relative domain is relative to the reading it was declared on.
    // ------------------------------------------------------------------

    @Test
    public void aDeclaredWindowIsResolvedAgainstEachPathsOwnReading()
            throws Exception {
        Path iteration = folder.newFolder("window").toPath();
        // The NameNode's serial advances between replays, so "up to three
        // rotations ahead of what this run read" is three different windows.
        for (String[] each : new String[][]{{"s0", "119994", "false"},
                {"s1", "119997", "true"}}) {
            Session session = new Session(iteration, each[0],
                    "true".equals(each[2]));
            session.serial(each[1], "+0", "+3");
            session.target("true", false, true);
            session.write();
        }

        Composer.Composition composition = compose(iteration, 8);
        assertEquals(2, composition.disjuncts().size());
        assertFalse("a root two sessions read differently gets no "
                        + "corpus-wide window",
                composition.body().contains("root_domain__"));
        assertTrue("the seed's own window is on the seed's path",
                composition.body().contains("(>= " + SERIAL + " 119994)"));
        assertTrue("and the later session's own window is on its path",
                composition.body().contains("(>= " + SERIAL + " 119997)"));

        // The value the old corpus-wide window excluded: legal for the
        // session that read 119997, and for no other.
        Solver solver = solver();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            List<String> pinned = new ArrayList<String>();
            pinned.add("(assert " + disjunct.selector() + ")");
            pinned.add("(assert (= " + SERIAL + " 120000))");
            String status = solver.ask(composition.body(), pinned,
                    Collections.<String>emptyList(), false).status();
            assertEquals("three rotations past its own reading, on "
                            + disjunct.path().sessionId(),
                    "s1".equals(disjunct.path().sessionId())
                            ? "sat" : "unsat", status);
        }
    }

    // ------------------------------------------------------------------
    // 8. A mechanism the recording does not decide is not a finding.
    // ------------------------------------------------------------------

    @Test
    public void aWitnessWithoutPolarityIsNotAFinding() throws Exception {
        Path iteration = folder.newFolder("polarity").toPath();
        Session session = new Session(iteration, "s0", false);
        session.marker("false");
        // phi holds whatever the marker is: the run as it happened reaches
        // the arm too, so moving the marker explains no difference.
        session.target("(or " + MARKER + " (not " + MARKER + "))", false,
                true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertEquals("sat", decision.outcomes().get(0).answer().status());
        assertEquals("sat", decision.outcomes().get(1).answer().status());
        assertEquals("the flip is satisfiable and explains nothing",
                ClaimKind.NO_SUPPORTED_WITNESS, decision.claim().kind());
        assertTrue("and the alarm says why",
                named(decision.claim().gaps(),
                        GapKind.FORMULA_SAT_AT_RECORDED_VALUATION));
    }

    // ------------------------------------------------------------------
    // 9. What the recording does not state is named, never dropped.
    // ------------------------------------------------------------------

    @Test
    public void whatTheRecordingDoesNotStateIsNamed() throws Exception {
        Path iteration = folder.newFolder("named").toPath();
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        Endpoint other = Endpoint.of(ANCHOR, "PORT.ref",
                at("attach#1", 0), 0);
        // Two sessions, neither of which focused anything: two recordings.
        for (String each : new String[]{"s0", "s1"}) {
            Session session = new Session(iteration, each, false);
            session.marker("false");
            // An attach the wire delivered to and the recording cannot
            // pair, and one whose Java type names no scalar.
            session.attach(consumer, "vh", "I", "7", null);
            session.attach(other, "vh_ref", "Lorg/apache/Foo;", "7", null);
            session.target("true", false, true);
            session.write();
        }

        Composer.Composition composition = compose(iteration, 4);
        List<GapRow> gaps = composition.gaps();
        assertTrue("an unpaired attach is a named row",
                says(gaps, GapKind.UNSTATED_VALUE,
                        "names no producer endpoint"));
        assertTrue("a Java type this lowering cannot place is refused",
                says(gaps, GapKind.UNSTATED_VALUE, "names no scalar"));
        assertTrue("and two recordings are not one",
                says(gaps, GapKind.UNSTATED_VALUE, "focused nothing"));
        assertFalse("the unplaceable symbol is not in the formula",
                composition.body().contains("vh_ref"));
    }

    // ------------------------------------------------------------------
    // 10. A case declares a selector; the seed session resolves it.
    // ------------------------------------------------------------------

    @Test
    public void aCaseSelectorIsResolvedAgainstTheSeedSession()
            throws Exception {
        Path iteration = folder.newFolder("selector").toPath();
        // Three activations of one region on one node, two of them started
        // by the api the case names.
        OccurrenceAddress first = occurrence("case/dn0", "REGION.sel",
                CausalContext.of("p1", "case/client#epoch0/checksum"),
                frame("DataXceiver#run#12", 0));
        OccurrenceAddress second = occurrence("case/dn0", "REGION.sel",
                CausalContext.of("p2", "case/client#epoch0/read-block"),
                frame("DataXceiver#run#12", 1));
        OccurrenceAddress third = occurrence("case/dn0", "REGION.sel",
                CausalContext.of("p3", "case/client#epoch0/checksum"),
                frame("DataXceiver#run#12", 2));
        Session session = new Session(iteration, "s0", false);
        session.activation(first);
        session.activation(second);
        session.activation(third);
        session.marker("false");
        session.occurrence = first;
        session.target("true", false, true);
        session.write();
        CorpusIndex corpus = CorpusIndex.of(iteration);

        assertEquals("the k-th activation of the region, in seed order",
                second.id(), ComposeMain.anchorOf(
                        "case/dn0#epoch0/region/REGION.sel#2", corpus)
                        .id());
        assertEquals("and with an api, the k-th that api started",
                third.id(), ComposeMain.anchorOf(
                        "case/dn0#epoch0/region/REGION.sel@"
                                + "case/client#epoch0/checksum#2", corpus)
                        .id());
        assertEquals("a full id is taken as one, not re-resolved",
                third.id(),
                ComposeMain.anchorOf(third.render(), corpus).id());
        assertEquals("another node's declaration matches nothing here",
                "REGION.sel", ComposeMain.anchorOf(
                        "case/dn9#epoch0/region/REGION.sel#1", corpus)
                        .regionId());
        assertTrue("and an unresolved declaration is degraded, not thrown",
                ComposeMain.anchorOf(
                        "case/dn9#epoch0/region/REGION.sel#1", corpus)
                        .context().isLost());
    }

    // ------------------------------------------------------------------
    // 11. Which writer the read could have seen (R-I7.1).
    // ------------------------------------------------------------------

    @Test
    public void anHbConcurrentWriterIsAnAlternativeAndAnAncestorIsNot()
            throws Exception {
        Path iteration = folder.newFolder("state").toPath();
        // The reader's own request; a writer concurrent with it; and a
        // writer that STARTED it, which is therefore ordered before it.
        OccurrenceAddress reader = occurrence("case/dn0", "REGION.read",
                CausalContext.of(Endpoint.of(UPSTREAM, "PORT.rpc",
                        at("call#1", 0), 0).id(), "case/client/read"),
                frame("Reader#run#4", 0));
        OccurrenceAddress concurrent = occurrence("case/dn0",
                "REGION.heartbeat", CausalContext.of(Role.HEARTBEAT_TICK, 1),
                frame("Heartbeat#run#9", 0));
        // IDENTITY-V3 sec 5: the map is named by the endpoint that
        // ALLOCATED it, which is the same name in every replay.
        LocationId keys = LocationId.allocated(Endpoint.of(UPSTREAM,
                "KeyManager#<init>#1:NEW", at("alloc#1", 0), 0),
                LocationKind.MAP, "allKeys");
        // The same storage named by its class instead: one name for every
        // instance, so it names none of them.
        LocationId aliased = LocationId.of(LocationKind.MAP,
                "BlockTokenSecretManager", "allKeys");

        Session session = new Session(iteration, "s0", false);
        session.occurrence = reader;
        session.activation(reader);
        session.activation(concurrent);
        session.activation(UPSTREAM);
        session.marker("false");
        // The request that started the reader, as a row: without it the
        // causal chain stops at an endpoint nothing places, and an
        // unfollowable chain states no ordering at all.
        session.expression("EXPR.v1.rpc", symbol(MARKER, "Z"));
        session.export(Endpoint.of(UPSTREAM, "PORT.rpc", at("call#1", 0), 0),
                "EXPR.v1.rpc", 1L, "false");
        session.expression("EXPR.v1.first", symbol(MARKER, "Z"));
        session.expression("EXPR.v1.second", symbol(MARKER, "Z"));
        session.expression("EXPR.v1.ancestor", symbol(MARKER, "Z"));
        // The ancestor writes, then the concurrent tick writes, then the
        // reader reads -- and observes the ancestor's version.
        session.decision(UPSTREAM, "up#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        session.write(Endpoint.of(UPSTREAM, "KeyManager#put#3:WRITE",
                at("w#1", 0), 0), keys, 1L, "EXPR.v1.ancestor");
        session.decision(concurrent, "hb#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        session.write(Endpoint.of(concurrent, "Heartbeat#put#7:WRITE",
                at("w#1", 0), 0), keys, 2L, "EXPR.v1.second");
        session.read(Endpoint.of(reader, "Reader#get#5:READ",
                at("r#1", 0), 0), keys, 1L, "read_k", "false");
        // The same two writers and the same read, on storage whose rows
        // name only the CLASS.
        session.write(Endpoint.of(UPSTREAM, "KeyManager#put#4:WRITE",
                at("w#2", 0), 0), aliased, 3L, "EXPR.v1.ancestor");
        session.write(Endpoint.of(concurrent, "Heartbeat#put#8:WRITE",
                at("w#2", 0), 0), aliased, 4L, "EXPR.v1.second");
        session.read(Endpoint.of(reader, "Reader#get#6:READ",
                at("r#2", 0), 0), aliased, 3L, "read_a", "false");
        session.target("read_k", false, true);
        session.write();

        Composer.Composition composition = Composer.compose(
                CorpusIndex.of(iteration), reader,
                Collections.<String,
                        edu.uva.liftlab.graphchecker.d3.contract.RootDomain>
                        emptyMap(), 4);
        assertEquals("one disjunct", 1, composition.disjuncts().size());
        assertTrue("the concurrent writer is an alternative",
                composition.body().contains("state_family__"));
        assertTrue("and the composition says which slots it filled",
                composition.families().size() >= 2);
        // The ancestor started the reader's request, so it is ordered before
        // it and is never an interleaving the reader could have taken.
        assertFalse("an ancestor of the reader is not an alternative",
                new edu.uva.liftlab.graphchecker.d3.smt.Arms(
                        CorpusIndex.of(iteration))
                        .concurrent(reader, UPSTREAM, "s0"));
        assertTrue("a heartbeat tick beside it is",
                new edu.uva.liftlab.graphchecker.d3.smt.Arms(
                        CorpusIndex.of(iteration))
                        .concurrent(reader, concurrent, "s0"));
        // IDENTITY-V3 sec 5: alternatives need an owner that names the
        // storage.  The class-owned copy of the same state gets the
        // delivery its own run gave it, and says so.
        assertTrue("an allocation endpoint names the storage",
                edu.uva.liftlab.graphchecker.d3.smt.Arms.namedOwner(keys));
        assertFalse("a class on a heap location names every instance",
                edu.uva.liftlab.graphchecker.d3.smt.Arms.namedOwner(aliased));
        String aliasedKey = SmtLowering.locationKey(aliased);
        boolean named = false;
        for (GapRow gap : composition.gaps()) {
            named |= gap.kind() == GapKind.DECLARATION_MISSING
                    && gap.subject().equals(aliasedKey);
        }
        assertTrue("and the aliasing owner is named, not used", named);
        assertFalse("so no family chooses a writer for it",
                composition.body().contains("state_family__0__"
                        + JsonText.digest(aliasedKey, 12)));
    }

    // ------------------------------------------------------------------
    // 12. A witness that needs the other writer says so.
    // ------------------------------------------------------------------

    @Test
    public void aWitnessOnAnotherEligibleWriterIsStatePairingFlipped()
            throws Exception {
        Path iteration = folder.newFolder("pairing").toPath();
        OccurrenceAddress reader = occurrence("case/dn0", "REGION.read",
                CausalContext.of(Role.DATA_XCEIVER, 1),
                frame("Reader#run#4", 0));
        OccurrenceAddress first = occurrence("case/dn0", "REGION.first",
                CausalContext.of(Role.IPC_HANDLER, 1),
                frame("Handler#run#2", 0));
        OccurrenceAddress second = occurrence("case/dn0", "REGION.second",
                CausalContext.of(Role.HEARTBEAT_TICK, 1),
                frame("Heartbeat#run#9", 0));
        LocationId keys = LocationId.allocated(Endpoint.of(first,
                "KeyManager#<init>#1:NEW", at("alloc#1", 0), 0),
                LocationKind.MAP, "allKeys");

        for (String[] each : new String[][]{{"s0", "false", "false"},
                {"s1", "true", "true"}}) {
            Session session = new Session(iteration, each[0],
                    "true".equals(each[2]));
            session.occurrence = reader;
            session.activation(reader);
            session.activation(first);
            session.activation(second);
            session.marker(each[1]);
            // The writer the read observed holds a constant; the writer
            // beside it holds the marker itself.
            session.expression("EXPR.v1.observed", constant("false"));
            session.expression("EXPR.v1.other", symbol(MARKER, "Z"));
            session.decision(first, "first#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
            session.write(Endpoint.of(first, "Handler#put#3:WRITE",
                    at("w#1", 0), 0), keys, 1L, "EXPR.v1.observed");
            session.decision(second, "second#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
            session.write(Endpoint.of(second, "Heartbeat#put#7:WRITE",
                    at("w#1", 0), 0), keys, 2L, "EXPR.v1.other");
            session.read(Endpoint.of(reader, "Reader#get#5:READ",
                    at("r#1", 0), 0), keys, 1L, "read_k", "false");
            session.target("read_k", false, true);
            session.write();
        }

        Composer.Composition composition = Composer.compose(
                CorpusIndex.of(iteration), reader,
                Collections.<String,
                        edu.uva.liftlab.graphchecker.d3.contract.RootDomain>
                        emptyMap(), 4);
        assertTrue("the read has alternatives, so the family owns it",
                composition.body().contains("state_family__"));

        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertEquals("the run as it happened does not reach the arm",
                "unsat", decision.outcomes().get(0).answer().status());
        assertEquals("sat", decision.outcomes().get(1).answer().status());
        assertEquals("the witness needs the writer the read did not observe",
                ClaimKind.STATE_PAIRING_FLIPPED, decision.claim().kind());
        assertTrue("with the polarity the recording decides",
                decision.claim().polarityDecides());
    }

    // ------------------------------------------------------------------
    // 13. A published term is a predicate; the row says which arm.
    // ------------------------------------------------------------------

    @Test
    public void aDecisionContributesTheArmItsRunTook() throws Exception {
        Path iteration = folder.newFolder("polarity-arm").toPath();
        Session session = new Session(iteration, "s0", false);
        session.marker("false");
        // One site, taken; one site, not taken.  The runtime publishes the
        // PREDICATE both times and the outcome says which arm ran.
        session.decision(ANCHOR, "anchor#u1", true, MARKER);
        session.decision(ANCHOR, "anchor#u2", false, MARKER);
        session.target("true", false, true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        assertEquals(1, composition.disjuncts().size());
        assertTrue("the arm it took is the term",
                composition.body().contains(MARKER));
        assertTrue("the arm it did not take is the negation",
                composition.body().contains("(not " + MARKER + ")"));

        // And the one routine says the same of either row.
        List<DecisionRow> rows = CorpusIndex.of(iteration)
                .path("s0", ANCHOR).decisions();
        List<String> pi = edu.uva.liftlab.graphchecker.d3.smt.Arms
                .pathCondition(rows, Long.MAX_VALUE);
        assertEquals(MARKER, pi.get(0));
        assertEquals("(not " + MARKER + ")", pi.get(1));
    }

    // ------------------------------------------------------------------
    // 14. One thread is one order, and a thread's starter is before it.
    // ------------------------------------------------------------------

    @Test
    public void aThreadOrdersItsOwnActivationsAndWhatStartedIt()
            throws Exception {
        Path iteration = folder.newFolder("threads").toPath();
        OccurrenceAddress earlier = occurrence("case/dn0", "REGION.earlier",
                CausalContext.of(Role.BP_SERVICE_ACTOR, 1),
                frame("Actor#run#1", 0));
        OccurrenceAddress later = occurrence("case/dn0", "REGION.later",
                CausalContext.of(Role.BP_SERVICE_ACTOR, 2),
                frame("Actor#run#1", 1));
        OccurrenceAddress started = occurrence("case/dn0", "REGION.started",
                CausalContext.of(Role.EXECUTOR_TASK, 1),
                frame("Task#run#1", 0));
        LocationId keys = LocationId.of(LocationKind.MAP, "Manager", "keys");

        Session session = new Session(iteration, "s0", false);
        session.occurrence = earlier;
        // Two activations of one thread, and a third on a thread the first
        // of them started.
        session.activation(earlier, "thread#actor", null, false);
        session.activation(later, "thread#actor", null, false);
        Endpoint starter = Endpoint.of(earlier, "Thread#start#2:NEW",
                at("start#1", 0), 0);
        session.activation(started, "thread#task", starter, false);
        session.marker("false");
        session.expression("EXPR.v1.k", constant("false"));
        Endpoint first = Endpoint.of(earlier, "Actor#put#3:WRITE",
                at("w#1", 0), 0);
        Endpoint second = Endpoint.of(later, "Actor#put#4:WRITE",
                at("w#2", 0), 0);
        Endpoint third = Endpoint.of(started, "Task#put#5:WRITE",
                at("w#3", 0), 0);
        session.write(first, keys, 1L, "EXPR.v1.k");
        session.write(second, keys, 2L, "EXPR.v1.k");
        session.write(third, keys, 3L, "EXPR.v1.k");
        session.target("true", false, true);
        session.write();

        edu.uva.liftlab.graphchecker.d3.smt.Arms rule =
                new edu.uva.liftlab.graphchecker.d3.smt.Arms(
                        CorpusIndex.of(iteration));
        assertTrue("one thread is one order, whatever the occurrence",
                rule.ancestor(first, second, "s0"));
        assertFalse("and it runs one way",
                rule.ancestor(second, first, "s0"));
        assertFalse("so two activations of one thread never interleave",
                rule.concurrent(earlier, later, "s0"));
        assertFalse("what started a thread is before everything on it",
                rule.concurrent(earlier, started, "s0"));
        assertTrue("and the direction says which way",
                rule.ancestor(first, third, "s0"));
        // Attestation: instrumented and symbolic in this session -- the seed
        // -- with no decision anywhere in it.
        assertTrue("a symbolic straight-line region is attested",
                rule.attested("s0", later));
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

    /** Whether some gap of this kind says this. */
    private static boolean says(List<GapRow> gaps, GapKind kind,
                                String fragment) {
        for (GapRow gap : gaps) {
            if (gap.kind() == kind && gap.detail().contains(fragment)) {
                return true;
            }
        }
        return false;
    }

    /** One occurrence: component, region, why it ran, where in the code. */
    private static OccurrenceAddress occurrence(String node, String region,
                                                CausalContext context,
                                                Frame... frames) {
        return OccurrenceAddress.of(NodeId.of(node, 0), region, context,
                ExecutionIndex.of(Arrays.asList(frames)));
    }

    private static Frame frame(String callSite, int iteration) {
        return Frame.of(callSite, iteration);
    }

    /** One site-local execution index, the k-th event's stand-in. */
    private static ExecutionIndex at(String callSite, int iteration) {
        return ExecutionIndex.of(Collections.singletonList(
                Frame.of(callSite, iteration)));
    }

    /** One recorded constant, as the VM serializes it. */
    private static JsonObject constant(String value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_java_type", "Z");
        node.addProperty("_exp", "true".equals(value) ? "Y_Z_1" : "Y_Z_0");
        return node;
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
        private final List<WriteRow> writes = new ArrayList<WriteRow>();
        private final List<ReadRow> reads = new ArrayList<ReadRow>();
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<String, JsonObject>();

        Session(Path iteration, String id, boolean explored) {
            this.iteration = iteration;
            this.id = id;
            this.explored = explored;
            activation(ANCHOR);
            this.seq = 0L;
        }

        /**
         * One more activation, on a thread of its own.
         *
         * <p>Each occurrence gets its own thread unless a test says
         * otherwise: sharing one would order every pair of them, which is
         * true of a thread and not of this fixture.</p>
         */
        void activation(OccurrenceAddress at) {
            activation(at, "thread#" + at.regionId(), null, explored);
        }

        void activation(OccurrenceAddress at, String threadKey,
                        Endpoint startedBy, boolean focused) {
            activation(at, threadKey, startedBy, focused, true);
        }

        void activation(OccurrenceAddress at, String threadKey,
                        Endpoint startedBy, boolean focused,
                        boolean instrumented) {
            activations.add(ActivationRow.of(id, at,
                    explored ? "task-flip" : "task-seed", focused,
                    instrumented, threadKey, startedBy));
        }

        void marker(String recorded) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, MARKER_ROOT, MARKER,
                    RootKind.MARKER, recorded, null, null, true));
        }

        /** A declared counter, with the window the CASE states around it. */
        void serial(String recorded, String min, String max) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, SERIAL_ROOT,
                    SERIAL, RootKind.INTEGRAL, recorded, min, max, true));
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

        void write(Endpoint endpoint, LocationId location, long version,
                   String ref) {
            writes.add(WriteRow.of(id, ++seq, endpoint, location, version,
                    ref, "Z"));
        }

        void read(Endpoint endpoint, LocationId location, long version,
                  String symbol, String concrete) {
            reads.add(ReadRow.of(id, ++seq, endpoint, location, version,
                    symbol, "Z", concrete));
        }

        void decision(OccurrenceAddress at, String site, String term) {
            decision(at, site, true, term);
        }

        void decision(OccurrenceAddress at, String site, boolean outcome,
                      String term) {
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, outcome, term,
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
            RowCodec.writeAll(dir.writes(), writes, RowCodec::writeWrite);
            RowCodec.writeAll(dir.reads(), reads, RowCodec::writeRead);
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
        // A producer the replay did not instrument is one that ran
        // concretely: it states its delivery and attests nothing.
        session.activation(PRODUCER, "thread#" + PRODUCER.regionId(), null,
                explored, attestProducer);
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
}
