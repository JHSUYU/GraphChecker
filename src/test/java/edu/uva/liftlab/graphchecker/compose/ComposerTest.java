package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Arm;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;

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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
public class ComposerTest {

    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    /** The target region, started by the request the case is about. */
    private static final OccurrenceAddress ANCHOR = occurrence("case/dn0",
            "REGION.target",
            CausalContext.of("producer-endpoint", "case/client/read-block"),
            frame("DataXceiver#run#12", 0));
    private static final OccurrenceAddress PRODUCER = occurrence("case/nn0",
            "REGION.nn", CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
            frame("Server#call#40", 0));
    private static final OccurrenceAddress UPSTREAM = occurrence("case/nn1",
            "REGION.up", CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", 1),
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
    /**
     * The same, at a VERSION: the VM's mint primitive gives the field a
     * new version whose value IS this symbol, so a read of that version
     * has a read row and no write row at all.
     */
    private static final String MINTED =
            "M_I_field_REGION.target.in.counter";
    /**
     * The same, on a location a real write log entry covers: the version
     * a placeholder row states is the LAST REAL WRITE the mint was laid
     * over, so the row joins to that write's expression while the term's
     * ReadFrom names the version the mint carried.
     */
    private static final String MINTED_JOINED =
            "M_I_field_REGION.target.in.counter2";
    /**
     * One occurrence's SECOND declared port on one cell.
     *
     * <p>Two ports, two mints, two symbols -- and one location, which is
     * why the location cannot be what a reader is matched by.</p>
     */
    private static final String PLACEHOLDER_TWO =
            "M_I_field_REGION.target.in.count.port2";

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
                decision.outcomes().get(1).selected().path().sessionId);

        // The same composition, answered by a solver that ERRORS.  An
        // "(error ...)" is z3 saying it could not READ the query, so
        // nothing it printed is a verdict about this recording: the claim
        // is refused by name and blocks, instead of being read off the
        // answers as if an undecided valuation.
        ClaimPolicy.Decision errored = ClaimPolicy.decide(composition,
                new Z3(erroringSolver(), 30000L));
        assertEquals("an error is not a finding",
                ClaimKind.NO_SUPPORTED_WITNESS, errored.claim().kind());
        assertTrue("and it is named and blocking",
                errored.claim().blocked() && says(errored.claim().gaps(),
                        GapKind.DECLARATION_MISSING,
                        "z3 answered the composed query with an error"));
        assertFalse("nothing about the recording is decided by it",
                errored.claim().polarityDecides());

        // And the same composition answered `unknown`.  Undecided is not a
        // refutation and not a witness, and it used to reach the manifest
        // as a bare state=unknown with nothing to route: named, BLOCKING,
        // and carrying the fragment z3 named.
        ClaimPolicy.Decision undecided = ClaimPolicy.decide(composition,
                new Z3(undecidingSolver(), 30000L));
        assertEquals("an undecided valuation is not a finding",
                ClaimKind.NO_SUPPORTED_WITNESS, undecided.claim().kind());
        assertTrue("it blocks, and the row names the valuation",
                undecided.claim().blocked() && named(
                        undecided.claim().gaps(), "valuation 0:unknown"));
        assertTrue("and carries z3's own reason, so a reader knows which "
                        + "fragment it was: " + undecided.claim().gaps(),
                says(undecided.claim().gaps(),
                        GapKind.DECLARATION_MISSING,
                        "(incomplete quantifiers)"));
        assertFalse("and decides nothing about the recording",
                undecided.claim().polarityDecides());

        // 1b. The same claim where the marker reaches the target only
        // through CONTROL dependence -- 17960's shape.  The marker gates a
        // branch of ANOTHER occurrence, so no decision of the anchor names
        // it and the anchor's own phi is CONCRETE: false as the seed ran
        // (a counter that was written), true in the flip replay (the write
        // was skipped).  What connects the two is that each path carries
        // its own replay's valuation of the varied root.
        Path control = folder.newFolder("marker-control").toPath();
        for (String[] each : new String[][]{
                {"s0", "true", "2", "false"}, {"s1", "false", "0", "true"}}) {
            Session session = new Session(control, each[0],
                    "true".equals(each[3]));
            session.marker(each[1]);
            // The counter the anchor reads: concrete, and different in the
            // two replays because the marker skipped the write.
            session.read(Endpoint.of(ANCHOR,
                            "<Manager: int count>#PLACEHOLDER#0:READ",
                            at("count#1", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "Manager", "held"),
                    -1L, PLACEHOLDER, "I", each[2]);
            // phi as the runtime publishes it: the FATAL polarity, over
            // the value this replay read.  Concrete either way.
            session.expression("EXPR.0000000000000fc1", binary("!=",
                    integer("I", 2L), symbol(PLACEHOLDER, "I")));
            session.target("EXPR.0000000000000fc1", "true".equals(each[3]),
                    true);
            session.write();
        }

        Composer.Composition controlled = compose(control, 8);
        assertEquals("both replays reach the anchor", 2,
                controlled.paths().size());
        assertFalse("and no decision of the anchor names the marker",
                controlled.body().contains("anchor#"));
        assertEquals("a root the two replays minted differently is carried "
                        + "on each path, so it is declared and enumerated",
                2, controlled.valuations().size());
        assertEquals("ordinal 0 is the SEED's value", "true",
                controlled.valuations().get(0).assignment().get(MARKER_ROOT));
        assertTrue("each path carries its own replay's valuation",
                controlled.body().contains("(= " + MARKER + " true)")
                        && controlled.body().contains(
                        "(= " + MARKER + " false)"));

        ClaimPolicy.Decision flipped = ClaimPolicy.decide(controlled,
                solver());
        assertEquals("the run as it happened does not reach the fatal arm",
                "unsat", flipped.outcomes().get(0).answer().status());
        assertEquals("the other polarity does", "sat",
                flipped.outcomes().get(1).answer().status());
        assertEquals(ClaimKind.MARKER_FLIPPED, flipped.claim().kind());
        assertEquals(Collections.singletonMap(MARKER_ROOT, "false"),
                flipped.claim().movedRoots());
        assertTrue(flipped.claim().polarityDecides());

        // 1e. The three-session 17960 shape, as the first real corpus has
        // it: one seed (marker true) whose counter is written only by the
        // createSnapshot occurrence, and TWO exploration replays (marker
        // false) in which the deleteSnapshot occurrence writes it as well
        // -- each write ReadFrom{previous} +- 1, the anchor's placeholder
        // joining the last of them, and phi published AS TAKEN (the FATAL
        // arm, observedFatal true) because those replays reached the
        // failure.  Two anchor activations per session, so six paths.
        Path three = folder.newFolder("marker-three").toPath();
        OccurrenceAddress saver = occurrence("case/nn0", "REGION.saver",
                CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                frame("Saver#serializeSnapshotSection#8", 0));
        OccurrenceAddress creating = occurrence("case/nn0",
                "REGION.create", CausalContext.of(Role.CLIENT, "", 1),
                frame("Manager#createSnapshot#27", 0));
        OccurrenceAddress deleting = occurrence("case/nn0",
                "REGION.delete", CausalContext.of(Role.CLIENT, "", 2),
                frame("Manager#deleteSnapshot#31", 0));
        // The anchor region's other activation: same region, same context,
        // one execution-index frame apart (17960's saveFSImageInAllDirs#u36
        // @0 and @1, the two storage directories' FSImageSaver threads).
        OccurrenceAddress sibling = occurrence("case/nn0", "REGION.saver",
                CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                frame("Saver#serializeSnapshotSection#8", 1));
        // The counter, owned by its ALLOCATION and not by a session rid,
        // so nothing about alternatives is withheld for the owner's
        // spelling: what is asked here is the attestation rule.
        Endpoint allocation = Endpoint.of(creating,
                "AtomicInteger#<init>#1:NEW", at("alloc#1", 0), 0);
        LocationId counter = LocationId.allocated(allocation,
                LocationKind.INSTANCE, "value");
        String owner = counter.owner();
        for (String[] each : new String[][]{
                {"s0", "true", "77", "2", "false"},
                {"s1", "false", "141", "0", "true"},
                {"s2", "false", "141", "0", "true"}}) {
            boolean flip = "true".equals(each[4]);
            Session session = new Session(three, each[0], flip);
            session.occurrence = saver;
            session.activation(saver, "thread#saver", null, flip);
            session.activation(creating, "thread#create", null, false);
            session.marker(each[1]);
            // createSnapshot: 0 + 1, then that version + 1.
            session.expression("EXPR.000000000000c050", binary("+",
                    integer("I", 0L), integer("I", 1L)));
            session.expression("EXPR.000000000000c077", binary("+",
                    read("INSTANCE_FIELD", owner, "value", 50L, "I"),
                    integer("I", 1L)));
            session.write(Endpoint.of(creating, "Manager#create#27:WRITE",
                            at("w#50", 0), 0), counter, 50L,
                    "EXPR.000000000000c050");
            session.write(Endpoint.of(creating, "Manager#create#27:WRITE",
                            at("w#77", 0), 0), counter, 77L,
                    "EXPR.000000000000c077");
            if (flip) {
                // deleteSnapshot ran the un-ordered arm -- the branch this
                // case's marker gates -- and decremented twice.
                session.activation(deleting, "thread#delete", null, false);
                session.decision(deleting, "delete#u27", false, MARKER);
                session.expression("EXPR.000000000000c125", binary("-",
                        read("INSTANCE_FIELD", owner, "value", 77L, "I"),
                        integer("I", 1L)));
                session.expression("EXPR.000000000000c141", binary("-",
                        read("INSTANCE_FIELD", owner, "value", 125L, "I"),
                        integer("I", 1L)));
                session.write(Endpoint.of(deleting,
                                "Manager#delete#31:WRITE", at("w#125", 0), 0),
                        counter, 125L, "EXPR.000000000000c125");
                session.write(Endpoint.of(deleting,
                                "Manager#delete#31:WRITE", at("w#141", 0), 0),
                        counter, 141L, "EXPR.000000000000c141");
            }
            // The anchor's declared input, the way laneA4 found it: ONE
            // occurrence declaring ONE cell under TWO ports, so two
            // placeholder rows of the same location -- each with its own
            // MINT VERSION, and each read's ReadFrom naming its own.  The
            // (occurrence, location) bridge could not choose between them
            // and refused both, taking the flip paths with it; the mint
            // version is unique by construction, so each resolves to its
            // own symbol and both paths stand.
            String[] port = {PLACEHOLDER, PLACEHOLDER_TWO};
            for (int activation = 0; activation < 2; activation++) {
                // The SECOND row is published at the SIBLING activation of
                // the same region, which is where the runtime puts it: the
                // two FSImageSaver activations race on one AtomicInteger, so
                // the one that mints installs the symbol and the one that
                // closes first publishes the row -- under its own address.
                // The anchor's phi still reads the version that mint
                // created, and a mint's identity in a session is that
                // version, so the row states it wherever it was published.
                session.placeholder(Endpoint.of(
                                activation == 0 ? saver : sibling,
                                "INSTANCE_FIELD/counter#PLACEHOLDER#"
                                        + activation + ":READ",
                                at("count#" + activation, 0), 0),
                        counter, Long.parseLong(each[2]),
                        500L + activation, port[activation], "I", each[3]);
                // phi over the version the MINT created, not over the
                // symbol: the composer has to get there through the row.
                session.expression("EXPR.0000000000000fe" + activation,
                        binary("!=", integer("I", 2L),
                                read("INSTANCE_FIELD", owner, "value",
                                        500L + activation, "I")));
            }
            // One phi, naming BOTH ports' reads: a fatal arm that rests on
            // the counter however the occurrence declared it.
            session.target("(and EXPR.0000000000000fe0 "
                    + "EXPR.0000000000000fe1)", flip, true);
            session.target("(and EXPR.0000000000000fe0 "
                    + "EXPR.0000000000000fe1)", flip, true);
            session.write();
        }

        Composer.Composition all = Composer.compose(Corpus.read(three, null),
                saver, Collections.<String,
                        edu.uva.liftlab.graphchecker.contract.RootDomain>
                        emptyMap(), 8);
        assertEquals("one path per anchor activation per session", 6,
                all.paths().size());
        assertEquals("the marker is what the three replays varied", 2,
                all.valuations().size());
        assertEquals("ordinal 0 is the seed's value", "true",
                all.valuations().get(0).assignment().get(MARKER_ROOT));
        assertTrue("each replay's counter is the chain of the writes it "
                        + "made: " + fatalArm(all),
                fatalArm(all).contains("(java_int_wrap (+ (java_int_wrap "
                        + "(+ 0 1)) 1))"));
        assertTrue("and each port's ReadFrom resolves to ITS OWN mint, so "
                        + "one cell declared twice states two reads and "
                        + "not a contradiction: " + fatalArm(all),
                all.body().contains(SmtLowering.legalSymbols(
                        "(not (= 2 " + PLACEHOLDER + "))"))
                        && all.body().contains(SmtLowering.legalSymbols(
                        "(not (= 2 " + PLACEHOLDER_TWO + "))")));
        assertFalse("nothing is refused for two rows of one location",
                says(all.gaps(), GapKind.UNSTATED_VALUE,
                        "under different symbols"));
        assertFalse("and nothing is cut for a mint whose row this session "
                        + "published at ANOTHER occurrence of the region: "
                        + all.gaps(),
                named(all.gaps(), "PROPAGATION_CUT:UndeclaredFreeSymbol:"
                        + PLACEHOLDER_TWO)
                        || says(all.gaps(), GapKind.UNSTATED_VALUE,
                        "nothing binds it"));
        // The counter read's writer is delivered and registered -- one
        // arm per exploration replay, the deleteSnapshot occurrence whose
        // write the anchor's placeholder joined -- and it gets NO
        // ALTERNATIVE, which is not the owner's doing: this owner is an
        // allocation id.  In the seed the createSnapshot occurrence is the
        // only writer of the counter, and one arm says nothing the join
        // has not; in an exploration replay the createSnapshot occurrence
        // is instrumented but is NOT the focused region, so it is
        // unattested (Arms.attested) and an unattested writer is
        // delivered, never offered as an alternative (Arms.stateArms).
        // An alternative here would also let the RECORDED valuation reach
        // the fatal arm, which is the FORMULA_SAT_AT_RECORDED_VALUATION
        // alarm and not this claim.
        assertEquals("one registered arm per replay that delivered the "
                        + "counter: " + all.families(), 2,
                all.families().size());
        for (edu.uva.liftlab.graphchecker.contract.Family family
                : all.families()) {
            assertEquals("delivered, not chosen between", 1,
                    family.arms().size());
        }
        assertFalse("so no alternative family is composed over the read",
                all.body().contains("state_family__"));
        assertFalse("and nothing is withheld for the owner's spelling",
                says(all.gaps(), GapKind.DECLARATION_MISSING,
                        "neither an allocation endpoint id"));

        ClaimPolicy.Decision three3 = ClaimPolicy.decide(all, solver());
        assertEquals("the recording does not reach the fatal arm", "unsat",
                three3.outcomes().get(0).answer().status());
        assertEquals("the other polarity does", "sat",
                three3.outcomes().get(1).answer().status());
        assertEquals("claim gaps: " + three3.claim().gaps(),
                ClaimKind.MARKER_FLIPPED, three3.claim().kind());
        assertEquals(Collections.singletonMap(MARKER_ROOT, "false"),
                three3.claim().movedRoots());
        assertTrue(three3.claim().polarityDecides());
        assertTrue("and the witness is one of the replays that reached it",
                three3.outcomes().get(1).selected().path().sessionId
                        .startsWith("s"));

        // 1c. The negative: two replays that minted the marker the SAME
        // way vary nothing, so no path carries a valuation of it, nothing
        // declares it, and there is one question to ask.
        Path agreed = folder.newFolder("marker-agreed").toPath();
        for (String[] each : new String[][]{
                {"s0", "2", "false"}, {"s1", "0", "true"}}) {
            Session session = new Session(agreed, each[0],
                    "true".equals(each[2]));
            session.marker("true");
            session.read(Endpoint.of(ANCHOR,
                            "<Manager: int count>#PLACEHOLDER#0:READ",
                            at("count#1", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "Manager", "held"),
                    -1L, PLACEHOLDER, "I", each[1]);
            session.expression("EXPR.0000000000000fc1", binary("!=",
                    integer("I", 2L), symbol(PLACEHOLDER, "I")));
            session.target("EXPR.0000000000000fc1", "true".equals(each[2]),
                    true);
            session.write();
        }
        // 1d. And an ARM is guarded by the delivering replay's valuation
        // of every varied root, not only by the roots its own expression
        // names: the delivery happened under that replay's values, so it
        // is available under them and under no other valuation.  This
        // arm's expression names no root at all.
        Path guarded = folder.newFolder("marker-guarded").toPath();
        for (String[] each : new String[][]{{"s0", "true", "false"},
                {"s1", "false", "true"}}) {
            Session session = new Session(guarded, each[0],
                    "true".equals(each[2]));
            session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
                    null, "true".equals(each[2]), true);
            session.marker(each[1]);
            session.expression("EXPR.v1.plain", integer("I", 7L));
            session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
            session.export(Endpoint.of(PRODUCER, "PORT.key",
                    at("export#1", 0), 0), "EXPR.v1.plain", 1L, "7");
            session.attach(Endpoint.of(ANCHOR, "PORT.key",
                            at("attach#1", 0), 0), "vh", "I", "7",
                    Endpoint.of(PRODUCER, "PORT.key", at("export#1", 0), 0));
            session.target("true", false, true);
            session.write();
        }
        Composer.Composition armed = compose(guarded, 8);
        assertEquals(1, armed.families().size());
        assertEquals(2, armed.families().get(0).arms().size());
        for (Arm arm : armed.families().get(0).arms()) {
            assertTrue("an arm carries the delivering replay's valuation "
                            + "of the varied root its expression never "
                            + "names: " + arm.guardRoots(),
                    arm.guardRoots().contains(MARKER_ROOT));
        }
        assertTrue("both replays' values are in the two arms",
                armed.body().contains("(= " + MARKER + " true)")
                        && armed.body().contains(
                        "(= " + MARKER + " false)"));

        Composer.Composition same = compose(agreed, 8);
        assertEquals(2, same.paths().size());
        assertFalse("nothing varied, so no path states a valuation of it",
                same.body().contains("(= " + MARKER + " "));
        assertEquals("and there is one question", 1,
                same.valuations().size());
    }

    /** A solver that answers every question with an SMT-LIB read error. */
    /**
     * A solver that decides nothing, and says why.
     *
     * <p>z3 answers `unknown` on a formula in a fragment it is incomplete
     * for, and it will name the fragment when asked: 17960's moved
     * valuation came back "(incomplete quantifiers)" after 141 s, from the
     * two `lambda` definitions the container preamble wrote.</p>
     */
    private Path undecidingSolver() throws IOException {
        Path script = folder.newFile("z3-unknown.sh").toPath();
        Files.write(script, Arrays.asList("#!/bin/sh",
                "cat > /dev/null",
                "echo unknown",
                "echo '(:reason-unknown \"(incomplete quantifiers)\")'"));
        assertTrue("the fixture solver is executable",
                script.toFile().setExecutable(true));
        return script;
    }

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
        Z3 solver = solver();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            List<String> pinned = new ArrayList<String>(
                    composition.valuations().get(0).assertions());
            pinned.add("(assert " + disjunct.selector() + ")");
            assertEquals("each path is satisfiable as the execution that "
                            + "made it: " + disjunct.path().sessionId,
                    "sat", solver.ask(composition.query(pinned),
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
        Z3 solver = solver();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            List<String> pinned = new ArrayList<String>();
            pinned.add("(assert " + disjunct.selector() + ")");
            pinned.add("(assert (= " + SERIAL + " 120000))");
            String status = solver.ask(composition.query(pinned),
                    Collections.<String>emptyList(), false).status();
            assertEquals("three rotations past its own reading, on "
                            + disjunct.path().sessionId,
                    "s1".equals(disjunct.path().sessionId)
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
            // TWO placeholder rows stating ONE mint version under
            // DIFFERENT symbols.  A mint version is unique by
            // construction, so this is the recording contradicting itself
            // and what the read that version made returned has no answer:
            // taking either one would put one read's value on another
            // read, so the ReadFrom naming it is refused by name -- and so
            // is the reader whose own row states nothing.  Two rows at two
            // DIFFERENT mint versions are two reads, not a conflict, and
            // are not refused (the 17960 anchor's two ports).
            session.placeholder(Endpoint.of(ANCHOR, "Counter#a#1:READ",
                            at("two#1", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "9", "16"), 7L,
                    11L, "two_a", "I", "1");
            session.placeholder(Endpoint.of(ANCHOR, "Counter#b#1:READ",
                            at("two#2", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "9", "16"), 9L,
                    11L, "two_b", "I", "2");
            session.read(Endpoint.of(ANCHOR, "Counter#r#1:READ",
                            at("two#3", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "9", "16"), 11L,
                    "INSTANCE/9#16@v11", "I", null);
            session.expression("EXPR.00000000000000b5", binary("==",
                    read("INSTANCE_FIELD", 9L, 16L, 11L, "I"),
                    integer("I", 1L)));
            session.decision(ANCHOR, "anchor#u12", true,
                    "EXPR.00000000000000b5");
            // A write row citing an expression its OWN session's table
            // does not hold, and a read joined to it.  The chain the read
            // takes its value from is not in this corpus, which is an
            // inconsistency the corpus states: named, BLOCKING, and no
            // stack trace.  Composed over the sort an absent expression
            // refuses at, it also declared the read's symbol as a
            // reference -- and the same symbol is a scalar in the other
            // session, which is how the first three-session 17960 corpus
            // came out of the composer as IllegalStateException "declared
            // as REF and INT".
            session.write(Endpoint.of(ANCHOR, "Absent#put#1:WRITE",
                            at("absent#1", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "5", "8"), 3L,
                    "EXPR.00000000000000ff");
            session.read(Endpoint.of(ANCHOR, "Absent#get#1:READ",
                            at("absent#2", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "5", "8"), 3L,
                    "absent_join", "I", null);
            // And ONE solver name this corpus states at two sorts: the
            // same read symbol pinned to a scalar by one session's row and
            // to a reference by the other's.  One name has one sort, so
            // the second is refused by name -- the first declaration
            // stands, because a name already written into an assertion
            // cannot be re-sorted under it without making that assertion
            // ill-sorted and z3 answer (error …).
            session.read(Endpoint.of(ANCHOR, "TwoSorts#get#1:READ",
                            at("sorts#1", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "6", "8"), -1L,
                    "two_sorts", "s0".equals(each) ? "I" : "L",
                    "s0".equals(each) ? "3" : "M_L'org/apache/Held'_9");
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
        assertTrue("a declared root no admitted path's formula names is "
                        + "named too: which valuations were asked is what "
                        + "the claim's polarity gate is about",
                says(gaps, GapKind.DECLARATION_MISSING,
                        "no admitted path's formula names it"));
        assertTrue("a scalar symbol no row of the session states is cut "
                        + "by name, and not declared free",
                named(gaps, "PROPAGATION_CUT:UndeclaredFreeSymbol:"
                        + NO_ROW));
        assertTrue("a reference projection the VM valued neither way is "
                        + "refused by name, naming the class and offset",
                named(gaps, "UNSTATED_FIELD_PROJECTION:"
                        + "org/apache/Store@48:L"));
        assertTrue("two placeholder rows stating one mint version under "
                        + "different symbols state nothing about the read "
                        + "it made, and the ReadFrom is refused by name",
                named(gaps, "UNSTATED_VALUE:MintVersion:INSTANCE/9#16@11:"
                        + "[two_a, two_b]"));
        assertTrue("and so is the reader whose own row states no value",
                says(gaps, GapKind.UNSTATED_VALUE,
                        "two placeholder rows of this session state mint "
                                + "version 11 under different symbols: "
                                + "[two_a, two_b]"));
        assertTrue("a row citing an expression its session's table does "
                        + "not hold is BLOCKING, by the ref it names",
                blocking(gaps, "EXPR.00000000000000ff"));
        assertFalse("and the read that joined to it is not declared at the "
                        + "sort an absent expression refuses at",
                composition.body().contains("absent_join"));
        assertTrue("and it says which row cited it",
                says(gaps, GapKind.UNSTATED_VALUE,
                        "cites an expression its session's table does not "
                                + "hold"));
        assertTrue("one solver name the corpus states at two sorts is "
                        + "BLOCKING too, and not a stack trace",
                blocking(gaps, "two_sorts") && says(gaps,
                        GapKind.UNSTATED_VALUE, "one solver name at two "
                                + "sorts: INT and REF"));
        assertFalse("the unplaceable symbol is not in the formula",
                composition.body().contains("vh_ref"));
        // And nothing the query does not rest on is declared in it.  A
        // lowering answers many questions and this corpus refuses most of
        // them; every name a refused or dropped term left in the declaration
        // table used to be emitted anyway, which is how hdfs-17960's
        // candidate.smt2 came to declare unsupported__d8d8220dc6,
        // INSTANCE_FIELD/17#60@v209 and the selector of the path that was
        // cut, and to use none of the three.
        assertEquals("every declaration the query emits is a name some "
                        + "assertion of it mentions",
                Collections.<String>emptyList(),
                deadDeclarations(composition));
    }

    /**
     * Declarations the body emits that no assertion of the query mentions.
     *
     * <p>The query is the body plus the valuation it is asked with, so a pin
     * naming a declared root counts as a mention; the theory preamble is not
     * a declaration OF this recording and is not examined.</p>
     */
    private static List<String> deadDeclarations(
            Composer.Composition composition) {
        String[] lines = composition.body().split("\n");
        int composed = 0;
        for (int index = 0; index < lines.length; index++) {
            if (lines[index].startsWith("(define-fun java_long_wrap")) {
                composed = index + 1;
                break;
            }
        }
        StringBuilder asked = new StringBuilder();
        for (Composer.Valuation valuation : composition.valuations()) {
            for (String pin : valuation.assertions()) {
                asked.append(pin).append('\n');
            }
        }
        List<String> declared = new ArrayList<String>();
        for (int index = 0; index < lines.length; index++) {
            String name = index < composed ? "" : declaredName(lines[index]);
            if (name.isEmpty()) {
                asked.append(lines[index]).append('\n');
            } else {
                declared.add(name);
            }
        }
        String text = asked.toString();
        List<String> dead = new ArrayList<String>();
        for (String name : declared) {
            if (!text.contains(name)) dead.add(name);
        }
        return dead;
    }

    /** The name one declaration line declares, or {@code ""}. */
    private static String declaredName(String line) {
        for (String opening : new String[]{"(declare-const ",
                "(define-fun "}) {
            if (!line.startsWith(opening)) continue;
            String rest = line.substring(opening.length());
            int end = rest.indexOf(rest.startsWith("|") ? '|' : ' ');
            if (end <= 0) return "";
            return rest.startsWith("|") ? rest.substring(1, end)
                    : rest.substring(0, end);
        }
        return "";
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
        Corpus corpus = Corpus.read(iteration, null);

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
                "REGION.heartbeat", CausalContext.of(Role.of("HEARTBEAT_TICK"), "", 1),
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
                Corpus.read(iteration, null), reader,
                Collections.<String,
                        edu.uva.liftlab.graphchecker.contract.RootDomain>
                        emptyMap(), 4);
        assertEquals("one disjunct", 1, composition.disjuncts().size());
        assertTrue("the concurrent writer is an alternative",
                composition.body().contains("state_family__"));
        assertTrue("and the composition says which slots it filled",
                composition.families().size() >= 2);
        // The ancestor started the reader's request, so it is ordered before
        // it and is never an interleaving the reader could have taken.
        assertFalse("an ancestor of the reader is not an alternative",
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null))
                        .concurrent(reader, UPSTREAM, "s0"));
        assertTrue("a heartbeat tick beside it is",
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null))
                        .concurrent(reader, concurrent, "s0"));
        // IDENTITY-V3 sec 5: alternatives need an owner that names the
        // storage.  The class-owned copy of the same state gets the
        // delivery its own run gave it, and says so.
        assertTrue("an allocation endpoint names the storage",
                edu.uva.liftlab.graphchecker.smt.Arms.namedOwner(keys));
        assertFalse("a class on a heap location names every instance",
                edu.uva.liftlab.graphchecker.smt.Arms.namedOwner(aliased));
        String aliasedKey = SmtLowering.locationKey(aliased);
        boolean named = false;
        for (GapRow gap : composition.gaps()) {
            named |= gap.kind() == GapKind.DECLARATION_MISSING
                    && gap.subject().equals(aliasedKey);
        }
        assertTrue("and the aliasing owner is named, not used", named);
        assertFalse("so no family chooses a writer for it",
                composition.body().contains("state_family__0__"
                        + ArtifactIO.digest(aliasedKey, 12)));
    }

    // ------------------------------------------------------------------
    // 12. A witness that needs the other writer says so.
    // ------------------------------------------------------------------

    @Test
    public void aWitnessOnAnotherEligibleWriterIsStatePairingFlipped()
            throws Exception {
        Path iteration = folder.newFolder("pairing").toPath();
        OccurrenceAddress reader = occurrence("case/dn0", "REGION.read",
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 1),
                frame("Reader#run#4", 0));
        OccurrenceAddress first = occurrence("case/dn0", "REGION.first",
                CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                frame("Handler#run#2", 0));
        OccurrenceAddress second = occurrence("case/dn0", "REGION.second",
                CausalContext.of(Role.of("HEARTBEAT_TICK"), "", 1),
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
                Corpus.read(iteration, null), reader,
                Collections.<String,
                        edu.uva.liftlab.graphchecker.contract.RootDomain>
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
        // Two declared roots, and what each may be is its KIND: the marker
        // is free in {recorded, flipped} with no domain row of its own,
        // and the integral, which the case declares no window for, is
        // pinned to what the recording read.
        session.marker("false");
        session.serial("41", null, null);
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
        session.expression("EXPR.00000000000000c2", binary("==",
                symbol(SERIAL, "I"), integer("I", 41L)));
        session.decision(ANCHOR, "anchor#u6", true, "EXPR.00000000000000c2");
        // A list the recording states the size of, inserted into twice --
        // once at a literal index, once at a SYMBOLIC one.  The shift used
        // to be a lambda over every index, which is the fragment z3
        // answered "(incomplete quantifiers)" on for 141 s; the recording
        // says how many elements the list held, so it is written out as
        // that many stores at CONCRETE indices, and the index stays
        // symbolic.
        JsonObject empty = relation("INDEXED", "SNAPSHOT_BASE",
                relation("INDEXED", "STATE",
                        symbol("M_L'java/util/ArrayList'_3",
                                "java/util/ArrayList")));
        JsonObject one = relation("INDEXED", "INSERT", empty,
                integer("I", 0L), integer("I", 7L));
        // The second element is the declared ROOT, so the list's chain
        // carries a symbol of the RECORDING and not only lowering-minted
        // names: that is the shape a closure has to see through the name
        // the chain is shared under.
        JsonObject two = relation("INDEXED", "INSERT", one,
                integer("I", 1L), symbol(SERIAL, "I"));
        // READ, not SIZE: a size is answered arithmetically along the
        // chain, and it is the STATE the shift has to produce.
        session.expression("EXPR.00000000000000c3", binary("==",
                relation("INDEXED", "READ", "I", two, integer("I", 0L)),
                integer("I", 7L)));
        session.decision(ANCHOR, "anchor#u7", true,
                "EXPR.00000000000000c3");
        // And a read of the WHOLE list, joined to the write that made it:
        // a read of one cell is answered through the mutations without
        // materialising the state, and it is this one -- the list as a
        // value -- that needs every index of it written out.
        session.expression("EXPR.00000000000000c4", two);
        session.write(Endpoint.of(ANCHOR, "Saver#snapshots#5:WRITE",
                        at("list#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "8", "16"), 3L,
                "EXPR.00000000000000c4");
        session.read(Endpoint.of(ANCHOR, "Saver#snapshots#6:READ",
                        at("list#2", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "8", "16"), 3L,
                "INSTANCE/8#16@v3", "java/util/ArrayList", null);
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
        // The same placeholder AT A VERSION, which is what the VM's mint
        // primitive actually leaves behind: symbolizing a field replaces
        // its shadow, so the tracked-location log gets a new version whose
        // value is the minted symbol.  Nobody wrote it, so the row
        // contract publishes no write -- and a ReadFrom naming that
        // version is then valued by the placeholder row whose mintVersion
        // IS that version, bound by that row's own pin -- this one was
        // laid over no write at all, so it has no join of its own.  Taken
        // from the copy of the version's expression the node carries, the
        // binding would rest on no row at all.
        session.placeholder(Endpoint.of(ANCHOR,
                        "INSTANCE_FIELD/22#24#PLACEHOLDER#0:READ",
                        at("count#2", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "22", "24"),
                -1L, 174L, MINTED, "I", "2");
        // And the reader of that version, as the runtime publishes it: its
        // own row states no value, and the version's does.
        session.read(Endpoint.of(ANCHOR,
                        "INSTANCE_FIELD/22#24#READ_FROM#0:READ",
                        at("count#3", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "22", "24"),
                174L, "INSTANCE/22#24@v174", "I", null);
        // The same shape where the mint was laid over a REAL write: the
        // counter's RMW at v77 is in the write log, the placeholder row
        // states v77 as the version it was laid over -- its OWN join --
        // and v178 as the version the mint created, which is the one the
        // term's ReadFrom names.  The two are matched by that mint
        // version, so the row's symbol is the read's value, and the row's
        // own value comes from the JOIN to v77: the writer's chain, not
        // the pin to what it happened to read.
        session.expression("EXPR.00000000000000e2", binary("+",
                symbol(SERIAL, "I"), integer("I", 1L)));
        session.write(Endpoint.of(PRODUCER, "Manager#createSnapshot#27:WRITE",
                        at("rmw#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "2", "24"), 77L,
                "EXPR.00000000000000e2");
        session.placeholder(Endpoint.of(ANCHOR,
                        "INSTANCE_FIELD/2#24#PLACEHOLDER#0:READ",
                        at("count#4", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "2", "24"),
                77L, 178L, MINTED_JOINED, "I", "2");
        session.read(Endpoint.of(ANCHOR,
                        "<Manager: int getNumSnapshots()>#u2:READ",
                        at("count#5", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "2", "24"),
                178L, "INSTANCE/2#24@v178", "I", null);
        // Two reference-typed reads whose value the ROW states, the way a
        // reference read states one: the VM's rid spelling, and "N" for
        // null.  A row and a FieldAccess concreteValue mean the same thing
        // by the same spelling, so the identity here is the SAME name the
        // rid-9 leaf above gets, and the null one is nullRef -- not an
        // identity of its own, which would answer "is it null" with "it is
        // some other object".
        session.read(Endpoint.of(ANCHOR,
                        "INSTANCE_FIELD/Snapshot#32#FIELD#32:READ",
                        at("held#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "Snapshot", "32"),
                -1L, "INSTANCE/Snapshot#32@e-1", "L",
                "M_L'org/apache/Held'_9");
        session.read(Endpoint.of(ANCHOR,
                        "INSTANCE_FIELD/Snapshot#40#FIELD#40:READ",
                        at("held#2", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "Snapshot", "40"),
                -1L, "INSTANCE/Snapshot#40@e-1", "L", "N");
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
        // phi also reads the minted version, as a ReadFrom naming it: no
        // write of that location at that version exists anywhere in the
        // session.
        session.expression("EXPR.00000000000000f3", binary("!=",
                read("INSTANCE_FIELD", 22L, 24L, 174L, "I"),
                integer("I", 5L)));
        session.expression("EXPR.00000000000000f4", binary("!=",
                read("INSTANCE_FIELD", 2L, 24L, 178L, "I"),
                integer("I", 9L)));
        session.target("(and EXPR.00000000000000f1 EXPR.00000000000000f2 "
                        + "EXPR.00000000000000f3 EXPR.00000000000000f4)",
                false, true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        assertEquals(1, composition.disjuncts().size());
        assertTrue("the arm it took is the term",
                composition.body().contains(MARKER));
        assertTrue("the arm it did not take is the negation",
                composition.body().contains("(not " + MARKER + ")"));
        // The shift, quantifier-free: no indexed_insert application is
        // left, the elements are a store chain, and the index carries the
        // operation's own definedness -- List.add(i, v) requires
        // 0 <= i <= size and throws otherwise, so an out-of-range index is
        // an execution that threw and not a path that reached the anchor.
        assertFalse("no list mutation lowers to a quantified relation "
                        + "any more: " + composition.body(),
                composition.body().contains("(indexed_insert ")
                        || composition.body().contains("(indexed_remove "));
        assertTrue("each insertion carries the operation's own "
                        + "definedness, at the size the recording stated: "
                        + composition.body(),
                composition.body().contains("(and (<= 0 0) (<= 0 0))")
                        && composition.body().contains(
                        "(and (<= 0 1) (<= 1 1))"));
        assertTrue("and the element lands at the index, cell by cell, with "
                        + "no quantifier over the indices",
                composition.body().contains("(ite (= 0 1) "));
        assertTrue("an element read is the element, at the element's sort",
                composition.body().contains("(valueInt (indexed_read "));
        assertTrue("and the cell it read is the slot the location names",
                composition.body().contains(" 2)) 5)"));
        // What each root may be, by kind, with no root-domains row for
        // either: two valuations, the recorded one first.
        assertEquals("a declared marker is free in {recorded, flipped} "
                        + "by its kind, and needs no declared domain", 2,
                composition.valuations().size());
        assertEquals("ordinal 0 is the run as it happened", 0,
                composition.valuations().get(0).ordinal());
        assertTrue("so it moves nothing",
                composition.valuations().get(0).moved().isEmpty());
        assertEquals("at the value the recording read", "false",
                composition.valuations().get(0).assignment()
                        .get(MARKER_ROOT));
        assertEquals("and the other polarity is the one move asked",
                Collections.singletonMap(MARKER_ROOT, "true"),
                composition.valuations().get(1).moved());
        assertFalse("an integral the case declares no window for is not "
                        + "enumerated",
                composition.valuations().get(1).moved()
                        .containsKey(SERIAL_ROOT));
        assertTrue("it is pinned to what the recording read, by a named "
                        + "conjunct an unsat core can read",
                composition.body().contains("(= " + SERIAL + " 41)")
                        && composition.body().contains("root_domain__"));
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
        // A ReadFrom over a version only a READ row states: the mint the
        // VM performed at a declared region input, which no write log
        // entry covers.
        assertTrue("the row that states the minted version is pinned to "
                        + "the value it returned: " + fatalArm(composition),
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(= " + MINTED + " 2)")));
        assertTrue("and phi's ReadFrom over that version IS that row's "
                        + "symbol: " + fatalArm(composition),
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(not (= " + MINTED + " 5))")));
        assertTrue("so is the reader row of the same version, whose own "
                        + "row states no value",
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(= INSTANCE/22#24@v174 " + MINTED + ")")));
        // The mint laid over a real write: matched by occurrence and
        // location, and valued by the JOIN to the version its row states.
        assertTrue("a placeholder row whose version the write log DOES "
                        + "cover takes the writer's expression, not the "
                        + "value it read: " + fatalArm(composition),
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(= " + MINTED_JOINED + " (java_int_wrap (+ "
                                + SERIAL + " 1)))")));
        assertFalse("so it is not pinned to that value",
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(= " + MINTED_JOINED + " 2)")));
        assertTrue("and the term's ReadFrom over the version the MINT "
                        + "carried is that row's symbol, which no row and "
                        + "no write states by version: "
                        + fatalArm(composition),
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(not (= " + MINTED_JOINED + " 9))")));
        assertTrue("as is the reader row of the mint version",
                fatalArm(composition).contains(SmtLowering.legalSymbols(
                        "(= INSTANCE/2#24@v178 " + MINTED_JOINED + ")")));
        // A row whose stated value is a REFERENCE, through the one
        // lowering a FieldAccess concreteValue goes through.
        assertTrue("a row that states an identity pins its symbol to the "
                        + "SAME identity name the rid's own leaf gets: "
                        + fatalArm(composition),
                fatalArm(composition).matches(".*\\(= \\|INSTANCE/"
                        + "Snapshot#32@e-1\\| (identity__[0-9a-f]+)\\)"
                        + ".*|.*\\(= (identity__[0-9a-f]+) nullRef\\)"
                        + ".*\\(= \\|INSTANCE/Snapshot#32@e-1\\| "
                        + "\\1\\).*"));
        assertTrue("and one that states \"N\" pins it to nullRef, not to "
                        + "an identity of its own",
                fatalArm(composition).contains(
                        "(= |INSTANCE/Snapshot#40@e-1| nullRef)"));

        // And the one routine says the same of either row.
        Corpus corpus = Corpus.read(iteration, null);
        List<DecisionRow> rows = corpus.path("s0", ANCHOR).decisions;
        List<String> pi = edu.uva.liftlab.graphchecker.smt.Arms
                .pathCondition(rows, Long.MAX_VALUE);
        assertEquals(MARKER, pi.get(0));
        assertEquals("(not " + MARKER + ")", pi.get(1));

        // THE SYMBOLS OF A TERM ARE THE ONES REACHABLE FROM IT, not the ones
        // visible in it.  A container version is lowered once and NAMED, so
        // the list read above stands in the text as one container_dag__ name
        // that declares nothing, and the recording's own symbol -- the list
        // the STATE leaf names -- is inside the body behind it.  Asking for
        // the visible names instead is what left 11741's anchor demanding a
        // single container name that matches no read row and no attach row,
        // so its closure never left the target's own node.
        SmtLowering lowering = corpus.lowering("s0");
        String guard = lowering.statedTerm("EXPR.00000000000000c3", "test");
        assertTrue("the container version stands in the text as one name: "
                        + guard,
                guard.contains("container_dag__"));
        assertFalse("which is not a symbol of the recording",
                SmtLowering.symbols(guard, new LinkedHashSet<String>())
                        .contains(SERIAL));
        Set<String> reached = lowering.reachedSymbols(guard,
                new LinkedHashSet<String>());
        assertTrue("and the recorded symbol behind it is: " + reached,
                reached.contains(SERIAL));
        for (String name : reached) {
            assertFalse("a name this lowering minted is not one of the "
                            + "recording's: " + name,
                    lowering.minted(name));
        }
    }

    // ------------------------------------------------------------------
    // 14. One thread is one order, and a thread's starter is before it.
    // ------------------------------------------------------------------

    @Test
    public void aThreadOrdersItsOwnActivationsAndWhatStartedIt()
            throws Exception {
        Path iteration = folder.newFolder("threads").toPath();
        OccurrenceAddress earlier = occurrence("case/dn0", "REGION.earlier",
                CausalContext.of(Role.of("BP_SERVICE_ACTOR"), "", 1),
                frame("Actor#run#1", 0));
        OccurrenceAddress later = occurrence("case/dn0", "REGION.later",
                CausalContext.of(Role.of("BP_SERVICE_ACTOR"), "", 2),
                frame("Actor#run#1", 1));
        OccurrenceAddress started = occurrence("case/dn0", "REGION.started",
                CausalContext.of(Role.EXECUTOR_TASK, "", 1),
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
        long firstAt = session.write(first, keys, 1L, "EXPR.v1.k");
        long secondAt = session.write(second, keys, 2L, "EXPR.v1.k");
        long thirdAt = session.write(third, keys, 3L, "EXPR.v1.k");
        session.target("true", false, true);
        session.write();

        edu.uva.liftlab.graphchecker.smt.Arms rule =
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null));
        assertTrue("one thread is one order, whatever the occurrence",
                rule.ancestor(first, firstAt, second, secondAt, "s0"));
        assertFalse("and it runs one way",
                rule.ancestor(second, secondAt, first, firstAt, "s0"));
        assertFalse("so two activations of one thread never interleave",
                rule.concurrent(earlier, later, "s0"));
        assertFalse("what started a thread is before everything on it",
                rule.concurrent(earlier, started, "s0"));
        assertTrue("and the direction says which way",
                rule.ancestor(first, firstAt, third, thirdAt, "s0"));
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
        return Composer.compose(Corpus.read(iteration, null), ANCHOR,
                Collections.<String,
                        edu.uva.liftlab.graphchecker.contract.RootDomain>
                        emptyMap(), maxValuations);
    }

    private Z3 solver() {
        Path z3 = Paths.get("/usr/local/bin/z3");
        if (!Files.isExecutable(z3)) z3 = Paths.get("z3");
        Assume.assumeTrue("z3 is not on this machine",
                Files.isExecutable(z3) || !z3.isAbsolute());
        return new Z3(z3, 30000L);
    }

    /** The one assertion that carries a path's own conjunction. */
    private static String fatalArm(Composer.Composition composition) {
        for (String line : composition.body().split("\n")) {
            if (line.contains("path_fatal__0")) return line;
        }
        return "";
    }

    /** Whether some gap names this subject. */
    /** Whether a BLOCKING row of this subject was named. */
    private static boolean blocking(List<GapRow> gaps, String subject) {
        for (GapRow gap : gaps) {
            if (gap.blocking() && gap.subject().endsWith(subject)) {
                return true;
            }
        }
        return false;
    }

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
        return read(kind, Long.toString(owner), Long.toString(slot),
                version, javaType);
    }

    /**
     * The same, where the owner NAMES the storage across replays.
     *
     * <p>An allocation endpoint id, not a session rid: the spelling a
     * location needs before alternatives may be asked for it
     * (IDENTITY-V3 sec 5, {@code Arms.namedOwner}).</p>
     */
    private static JsonObject read(String kind, String owner, String slot,
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

    /**
     * One container relation, as the VM serializes it.
     *
     * <p>{@code CLEAR} with no receiver is the empty list the recording
     * states the size of; {@code INSERT} and {@code REMOVE} are the
     * mutations whose shift a lambda used to state.</p>
     */
    private static JsonObject relation(String shape, String operation,
                                       JsonObject receiver,
                                       JsonObject... arguments) {
        return relation(shape, operation, "java/util/ArrayList", receiver,
                arguments);
    }

    /** The same, where the relation answers a scalar rather than a list. */
    private static JsonObject relation(String shape, String operation,
                                       String javaType, JsonObject receiver,
                                       JsonObject... arguments) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ContainerRelation");
        node.addProperty("shape", shape);
        node.addProperty("operation", operation);
        node.addProperty("_java_type", javaType);
        if (receiver != null) node.add("receiver", receiver);
        com.google.gson.JsonArray list = new com.google.gson.JsonArray();
        for (JsonObject argument : arguments) list.add(argument);
        node.add("arguments", list);
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

        /** @return the session event this write was sequenced at. */
        long write(Endpoint endpoint, LocationId location, long version,
                   String ref) {
            writes.add(WriteRow.of(id, ++seq, endpoint, location, version,
                    ref, "Z"));
            return seq;
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

        /**
         * A PLACEHOLDER read, stating both of its versions.
         *
         * <p>{@code version} is the last real write the mint was laid over
         * -- this row's own join -- and {@code mint} is the version the
         * mint created, which is the one a reader's ReadFrom names.</p>
         */
        void placeholder(Endpoint endpoint, LocationId location,
                         long version, long mint, String symbol,
                         String javaType, String concrete) {
            reads.add(ReadRow.of(id, ++seq, endpoint, location, version,
                    symbol, javaType, concrete, mint));
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
