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
    /**
     * A declared region input, as the runtime publishes it: a READ
     * placeholder, so the row states its value and nothing mints it.
     */
    private static final String PLACEHOLDER =
            "M_I_field_REGION.target.in.count";
    private static final String NO_ROW = "M_I_field_REGION.target.in.absent";

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

        // The same composition, answered by a solver that ERRORS.  An
        // "(error ...)" is z3 saying it could not READ the query, so
        // nothing it printed is a verdict about this recording: the claim
        // is refused by name and blocks, instead of being read off the
        // answers as if an undecided valuation.
        ClaimPolicy.Decision errored = ClaimPolicy.decide(composition,
                new Solver(erroringSolver(), 30000L));
        assertEquals("an error is not a finding",
                ClaimKind.NO_SUPPORTED_WITNESS, errored.claim().kind());
        assertTrue("and it is named and blocking",
                errored.claim().blocked() && says(errored.claim().gaps(),
                        GapKind.DECLARATION_MISSING,
                        "z3 answered the composed query with an error"));
        assertFalse("nothing about the recording is decided by it",
                errored.claim().polarityDecides());
    }

    /** A solver that answers every question with an SMT-LIB read error. */
    private Path erroringSolver() throws IOException {
        Path script = folder.newFile("z3-error.sh").toPath();
        Files.write(script, Arrays.asList("#!/bin/sh",
                "cat > /dev/null",
                "echo '(error \"line 32 column 27: invalid bit-vector "
                        + "literal, expecting x or b\")'"));
        assertTrue("the fixture solver is executable",
                script.toFile().setExecutable(true));
        return script;
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
        // And the FILE says so as well.  A composition with no path
        // asserts nothing about the anchor, and a query that asserts
        // nothing is satisfiable -- so a reader running `z3` on the
        // artifact by hand read "sat" off a composition that had refused
        // to answer.  The blocker is asserted false, by name.
        String candidate = ComposeMain.candidate(composition, decision);
        assertTrue("the blocked candidate closes the question: " + candidate,
                candidate.contains("(assert false) ; fail closed: "
                        + GapKind.DECLARATION_MISSING.name() + ":"));
        assertTrue("with check-sat after it and nothing else",
                candidate.endsWith("(check-sat)\n"));
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
            // A read of ONE associative cell, joined to a write of the
            // WHOLE map at the version it observed.  The location names
            // its key by hash, so which entry the read returned is not
            // stated: that is refused by name, and not by passing a
            // container on to the operator over it, which named the
            // operator and not the projection.
            session.expression("EXPR.00000000000000b1",
                    symbol("M_L'java/util/HashMap'_4", "java/util/HashMap"));
            session.expression("EXPR.00000000000000b2", binary("==",
                    read("MAP_STATE", 4L, -3L, 1L, "I"), integer("I", 7L)));
            // And a reference-typed field read the VM valued NEITHER way:
            // no version to join to and no identity to pin to, so it is
            // refused by name -- naming the class and the offset -- and
            // never left free for the solver to define as it likes.
            session.expression("EXPR.00000000000000b3", binary("==",
                    fieldRead("org/apache/Store", 48L,
                            symbol("M_L'org/apache/Store'_4",
                                    "org/apache/Store"), null),
                    vmNull()));
            session.decision(ANCHOR, "anchor#u10", true,
                    "EXPR.00000000000000b3");
            // And a scalar leaf NO row of this session states: no root
            // mint, no clock reading, no attach and no read, so nothing
            // says what it means.  Cut by name -- declared free, the
            // solver would answer with a value no execution produced.
            session.expression("EXPR.00000000000000b4", binary("==",
                    symbol(NO_ROW, "I"), integer("I", 4L)));
            session.decision(ANCHOR, "anchor#u11", true,
                    "EXPR.00000000000000b4");
            session.write(Endpoint.of(ANCHOR, "Keys#put#9:WRITE",
                            at("put#1", 0), 0),
                    LocationId.of(LocationKind.MAP, "4", "-3"), 1L,
                    "EXPR.00000000000000b1");
            session.decision(ANCHOR, "anchor#u9", true,
                    "EXPR.00000000000000b2");
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
        assertTrue("a cell the location does not name is refused by name, "
                        + "naming the location, the version and both sorts",
                named(gaps, "ContainerElement:MAP/4#-3@1:MAP!=INT"));
        assertTrue("a scalar symbol no row of the session states is cut "
                        + "by name, and not declared free",
                named(gaps, "PROPAGATION_CUT:UndeclaredFreeSymbol:"
                        + NO_ROW));
        assertTrue("a reference projection the VM valued neither way is "
                        + "refused by name, naming the class and offset",
                named(gaps, "UNSTATED_FIELD_PROJECTION:"
                        + "org/apache/Store@48:L"));
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
        // Two leaves the same path is made of, published by reference.
        // The array a store wrote WHOLE at version 1, and a read of ONE
        // cell of it at that version: the read is of the element, so the
        // conjunct is the element -- not the array, which an operator over
        // it would refuse as a sort conflict naming the operator.
        session.expression("EXPR.00000000000000a1", symbol("A[I_7-1", "[I"));
        session.expression("EXPR.00000000000000c1", binary("==",
                read("ARRAY_ELEMENT", 7L, 2L, 1L, "I"), integer("I", 5L)));
        Endpoint store = Endpoint.of(ANCHOR, "Saver#store#3:WRITE",
                at("store#1", 0), 0);
        session.write(store, LocationId.of(LocationKind.ARRAY, "7", "2"),
                1L, "EXPR.00000000000000a1");
        session.decision(ANCHOR, "anchor#u3", true, "EXPR.00000000000000c1");
        // Two reference-typed field reads, each asked the question every
        // key case's predicate asks of one: is what it returned null?  A
        // reference read states what it returned exactly as a primitive
        // read does -- concreteOwner and concreteValue in the VM's own rid
        // spelling, or "N" for null -- so the first projection IS the
        // identity of object 9, the SAME name an ordinary identity leaf of
        // that rid gets (which is what an OWNER is lowered as, so one
        // read's reference can be equated with another read's owner), and
        // the second is nullRef and not an identity of its own.
        //
        // The first one's OWNER is a read this session's write log does not
        // cover.  The projection does not rest on it -- what the read
        // returned is stated on the node -- so the owner is not lowered and
        // its refusal is not this path's.  Lowering it anyway refused a
        // projection the recording states exactly, which is what took 12
        // Snapshot@32 projections and the whole 17960 anchor path with them.
        session.expression("EXPR.00000000000000d1", binary("==",
                fieldRead("org/apache/Store", 24L,
                        read("MAP_STATE", 4L, -3L, 9L, "L"),
                        symbol("M_L'org/apache/Held'_9",
                                "org/apache/Held")),
                vmNull()));
        session.expression("EXPR.00000000000000d2", binary("==",
                fieldRead("org/apache/Store", 32L,
                        symbol("M_L'org/apache/Store'_4",
                                "org/apache/Store"),
                        vmNull()),
                symbol("M_L'org/apache/Held'_9", "org/apache/Held")));
        session.decision(ANCHOR, "anchor#u4", true, "EXPR.00000000000000d1");
        session.decision(ANCHOR, "anchor#u5", true, "EXPR.00000000000000d2");
        // A declared region input, published as a READ placeholder: no
        // version to join to, the row's own value, and leaves of it in two
        // places.  Its symbol is a declared symbol of this session, so
        // every leaf naming it is this path's binding for it -- the pin.
        //
        // The JOINED read that names it comes FIRST in the session's rows,
        // so its write expression is lowered before the row that states
        // the value is reached: bound row by row as they were met, that
        // leaf was cut as a free symbol (18 PROPAGATION_CUT rows on the
        // 17960 anchor, reached through write v172's expression, beside a
        // declare-const of the same name in the same file).
        session.expression("EXPR.00000000000000e1", symbol(PLACEHOLDER, "I"));
        session.write(Endpoint.of(ANCHOR, "Manager#store#7:WRITE",
                        at("store#2", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "Manager", "count"), 2L,
                "EXPR.00000000000000e1");
        session.read(Endpoint.of(ANCHOR, "Manager#read#7:READ",
                        at("read#2", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "Manager", "count"), 2L,
                "INSTANCE/Manager#count@v2", "I", null);
        session.read(Endpoint.of(ANCHOR,
                        "<Manager: int count>#PLACEHOLDER#0:READ",
                        at("count#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "Manager", "held"),
                -1L, PLACEHOLDER, "I", "2");
        // And phi: a null test, which is what every key case's fatal
        // predicate is, and -- phi is published SMT TEXT over the
        // session's expression references -- a second leaf of the
        // placeholder beside it.  The VM spells null "N" on a symbolic
        // leaf.
        session.expression("EXPR.00000000000000f1", binary("!=",
                symbol("P_L'org/apache/Foo'_", "Lorg/apache/Foo;"),
                vmNull()));
        session.expression("EXPR.00000000000000f2", binary("!=",
                symbol(PLACEHOLDER, "I"), integer("I", 3L)));
        session.target("(and EXPR.00000000000000f1 EXPR.00000000000000f2)",
                false, true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        assertEquals(1, composition.disjuncts().size());
        assertTrue("the arm it took is the term",
                composition.body().contains(MARKER));
        assertTrue("the arm it did not take is the negation",
                composition.body().contains("(not " + MARKER + ")"));
        assertTrue("an element read is the element, at the element's sort",
                composition.body().contains("(valueInt (indexed_read "));
        assertTrue("and the cell it read is the slot the location names",
                composition.body().contains(" 2)) 5)"));
        assertTrue("a read whose value the ROW states is pinned to it: "
                        + fatalArm(composition),
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(= " + PLACEHOLDER + " 2)")));
        assertTrue("phi's own leaf of that symbol IS that symbol",
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(not (= " + PLACEHOLDER + " 3))")));
        assertTrue("and so is one reaching the formula through the write "
                        + "expression a JOINED read observed",
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(= INSTANCE/Manager#count@v2 "
                                + PLACEHOLDER + ")")));
        assertTrue("a reference read the VM valued is the identity of the "
                        + "object it names, under the SAME name an ordinary "
                        + "identity leaf of that rid gets -- and one it "
                        + "valued \"N\" is nullRef, not an identity of its "
                        + "own: " + fatalArm(composition),
                fatalArm(composition).matches(
                        ".*\\(= (identity__[0-9a-f]+) nullRef\\)"
                                + ".*\\(= nullRef \\1\\).*"));
        assertTrue("x != null compares against the null encoding, and not "
                        + "against an opaque identity of its own session: "
                        + fatalArm(composition),
                fatalArm(composition).matches(
                        ".*\\(not \\(= identity__[0-9a-f]+ "
                                + "nullRef\\)\\).*"));

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

    /** The one assertion that carries a path's own conjunction. */
    private static String fatalArm(Composer.Composition composition) {
        for (String line : composition.body().split("\n")) {
            if (line.contains("path_fatal__0")) return line;
        }
        return "";
    }

    /** Whether some gap names this subject. */
    private static boolean named(List<GapRow> gaps, String subject) {
        for (GapRow gap : gaps) {
            if (gap.subject().endsWith(subject)) return true;
        }
        return false;
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

    /** Java null, exactly as the VM serializes it on a symbolic leaf. */
    private static JsonObject vmNull() {
        return symbol("N", "");
    }

    /** One recorded binary relation. */
    private static JsonObject binary(String operator, JsonObject left,
                                     JsonObject right) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", operator);
        node.add("_left", left);
        node.add("_right", right);
        return node;
    }

    /** One read of one cell, naming the version it observed and nothing else. */
    private static JsonObject read(String kind, long owner, long slot,
                                   long version, String javaType) {
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", kind);
        location.addProperty("ownerSymRid", owner);
        location.addProperty("slot", slot);
        JsonObject observed = new JsonObject();
        observed.addProperty("fieldVersionId", version);
        observed.addProperty("versionKind", "WRITE");
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ReadFromExpression");
        node.addProperty("_java_type", javaType);
        node.addProperty("expressionAuthority", "VM_GUARDED_READ_FROM_V1");
        node.add("location", location);
        node.add("observedVersion", observed);
        return node;
    }

    /**
     * One reference-typed field read, as the VM serializes it.
     *
     * <p>The owner it read from, and -- when the VM stated them -- the
     * pair that says what the read returned: the owner's identity and the
     * identity of the object read, both in the rid spelling an identity
     * leaf carries.  {@code concreteValue} null here is the VM stating
     * neither, which is the projection no evidence values.</p>
     */
    private static JsonObject fieldRead(String ownerClass, long offset,
                                        JsonObject owner,
                                        JsonObject concreteValue) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "FieldAccessExpression");
        node.addProperty("_java_type", "L");
        node.addProperty("ownerClass", ownerClass);
        node.addProperty("fieldOffset", offset);
        node.add("owner", owner);
        if (concreteValue != null) {
            node.add("concreteOwner", owner);
            node.add("concreteValue", concreteValue);
        }
        return node;
    }

    /** One integer literal, as the VM serializes it. */
    private static JsonObject integer(String javaType, long value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_java_type", javaType);
        node.addProperty("_exp", "Y_" + javaType + "_" + value);
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
            read(endpoint, location, version, symbol, "Z", concrete);
        }

        void read(Endpoint endpoint, LocationId location, long version,
                  String symbol, String javaType, String concrete) {
            reads.add(ReadRow.of(id, ++seq, endpoint, location, version,
                    symbol, javaType, concrete));
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
