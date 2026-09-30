package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.VmRows;
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
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.explore.ExploreCodec;
import edu.uva.liftlab.graphchecker.explore.SlotTable;

import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
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
    private static final String CLOCK = "clock_now";
    private static final String CLOCK_ROOT = "ROOT.NOW";
    /**
     * A declared region input, as the runtime publishes it: a READ
     * placeholder, so the row states its value and nothing mints it.
     */
    private static final String PLACEHOLDER =
            "M_I_field_REGION.target.in.count";
    private static final String NO_ROW = "M_I_field_REGION.target.in.absent";
    private static final String NO_ROW_LONG =
            "M_J_field_REGION.target.in.absent";
    /** A call's result the VM minted a symbol for, which no row declares. */
    private static final String RETURNED = "M_J_return9";
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

        // And answered by a z3 that WARNS first, as its optimizer does under
        // quantifiers: the answer is the line after the warning.
        assertEquals("a warning is not the verdict", ClaimKind.MARKER_FLIPPED,
                ClaimPolicy.decide(composition, new Z3(warningSolver(),
                        30000L)).claim().kind());

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
        // The counter, owned the way the runtime writes an owner -- the
        // VM's rid of the object -- so nothing about alternatives is
        // withheld for the owner's spelling: what is asked here is the
        // attestation rule.
        LocationId counter = LocationId.of(LocationKind.INSTANCE, "31",
                "value");
        String owner = counter.owner();
        for (String[] each : new String[][]{
                {"s0", "true", "77", "2", "false"},
                {"s1", "false", "141", "0", "true"},
                {"s2", "false", "141", "0", "true"}}) {
            boolean flip = "true".equals(each[4]);
            Session session = new Session(three, each[0], flip);
            session.occurrence = saver;
            session.activation(saver, "thread#saver", flip);
            session.activation(creating, "thread#create", false);
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
                session.activation(deleting, "thread#delete", false);
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

        Composer.Composition all = compose(three, saver, 8, StaticScopeMap.empty());
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
                all.body().contains(SmtNames.legalSymbols(
                        "(not (= 2 " + PLACEHOLDER + "))"))
                        && all.body().contains(SmtNames.legalSymbols(
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
        // The counter read's writer is delivered and registered, one slot
        // per replay that delivered it -- the deleteSnapshot occurrence
        // whose write the anchor's placeholder joined.  In an exploration
        // replay the createSnapshot occurrence is instrumented but is NOT
        // the focused region, and ATTESTATION IS ABOUT THE ROWS AND NOT
        // ABOUT THE FOCUS: this session states its activation and its
        // decisions, so it is attested and it IS offered as an alternative
        // writer (Arms.attested, Arms.stateArms).  That is the point of
        // the rule -- the concurrent writer's prefix is a world the corpus
        // states -- and it does NOT let the recorded valuation reach the
        // fatal arm, which is what the asserts below measure: outcome 0 is
        // still unsat and the polarity still decides.
        assertEquals("one slot per replay that delivered the counter: "
                        + all.families(), 2, all.families().size());
        assertTrue("so an alternative writer IS composed over the read",
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
                    "true".equals(each[2]), true);
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
        // TWO arms: neither run was held to a flip, so each is a
        // delivery the other's path could have received (PIPELINE §8),
        // and each arm carries its own replay's valuation.
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

        // 1f. The same control shape where the flip replay's MINT states
        // no value.  It PLANTED the marker, so by rule it states no
        // recordedValue -- a counterfactual is not a recording -- and what
        // it ran under is stated by the obligation it ran under.  Read off
        // the mint alone (05f4bf265), that valuation was stated nowhere: no
        // path's formula named the marker, no valuation of it was asked,
        // and 17960's composition published MESSAGE_PAIRING_FLIPPED at the
        // recorded valuation over a corpus with no wire row in it.
        Path planted = folder.newFolder("marker-planted").toPath();
        for (String[] each : new String[][]{
                {"s0", "true", "2", "false"}, {"s1", "", "0", "true"}}) {
            controlSession(planted, each);
        }
        obligation(planted, "s1", Collections.singletonMap(
                MARKER_ROOT, "false"));
        Composer.Composition asked = compose(planted, 8);
        assertEquals("both replays reach the anchor", 2,
                asked.paths().size());
        assertEquals("the ask is what the flip replay ran the root at, so "
                        + "the root is varied, declared and enumerated", 2,
                asked.valuations().size());
        assertEquals("ordinal 0 is still the SEED's reading", "true",
                asked.valuations().get(0).assignment().get(MARKER_ROOT));
        assertTrue("each path carries its own replay's valuation: " + asked
                        .gaps(),
                asked.body().contains("(= " + MARKER + " true)")
                        && asked.body().contains(
                        "(= " + MARKER + " false)"));
        ClaimPolicy.Decision planted3 = ClaimPolicy.decide(asked, solver());
        assertEquals("the recording does not reach the fatal arm", "unsat",
                planted3.outcomes().get(0).answer().status());
        assertEquals(ClaimKind.MARKER_FLIPPED, planted3.claim().kind());
        assertEquals(Collections.singletonMap(MARKER_ROOT, "false"),
                planted3.claim().movedRoots());
        assertTrue(planted3.claim().polarityDecides());

        // And fail closed both ways.  Nothing states what the flip replay
        // ran the declared root at: the path is REFUSED by name, because a
        // disjunct free in a root the query enumerates is satisfiable at
        // every valuation of it and reads as one that decided something.
        Path unstated = folder.newFolder("marker-unstated").toPath();
        for (String[] each : new String[][]{
                {"s0", "true", "2", "false"}, {"s1", "", "0", "true"}}) {
            controlSession(unstated, each);
        }
        Composer.Composition silent = compose(unstated, 8);
        assertEquals("the flip path is not in the disjunction", 1,
                silent.paths().size());
        assertTrue("and the row names the root and the replay: "
                        + silent.gaps(),
                says(silent.gaps(), GapKind.UNSTATED_VALUE,
                        "states no value it ran it at"));
        assertTrue("it blocks", blocking(silent.gaps()));

        // Both state it and they disagree: one replay ran the root at one
        // value, so a corpus that names two is not one this path can
        // carry.  This is the shape the leak had -- the reused mint read
        // the plant back and published it as `recordedValue` -- and it is
        // named rather than resolved by preferring one of them silently.
        Path twice = folder.newFolder("marker-twice").toPath();
        for (String[] each : new String[][]{
                {"s0", "true", "2", "false"}, {"s1", "true", "0", "true"}}) {
            controlSession(twice, each);
        }
        obligation(twice, "s1", Collections.singletonMap(
                MARKER_ROOT, "false"));
        Composer.Composition contradicted = compose(twice, 8);
        assertEquals("the flip path is not in the disjunction", 1,
                contradicted.paths().size());
        assertTrue("and the row names both statements: "
                        + contradicted.gaps(),
                says(contradicted.gaps(), GapKind.UNSTATED_VALUE,
                        "stated twice and differently"));
        assertTrue("it blocks", blocking(contradicted.gaps()));
    }

    /** One session of the control-dependence marker fixture. */
    private void controlSession(Path iteration, String[] each)
            throws IOException {
        Session session = new Session(iteration, each[0],
                "true".equals(each[3]));
        session.marker(each[1]);
        session.read(Endpoint.of(ANCHOR,
                        "<Manager: int count>#PLACEHOLDER#0:READ",
                        at("count#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "Manager", "held"),
                -1L, PLACEHOLDER, "I", each[2]);
        session.expression("EXPR.0000000000000fc1", binary("!=",
                integer("I", 2L), symbol(PLACEHOLDER, "I")));
        session.target("EXPR.0000000000000fc1", "true".equals(each[3]),
                true);
        session.write();
    }

    /**
     * One obligation worker: the ask, the FOCUS ROW and the session its
     * replay wrote.
     *
     * <p>The layout the campaign publishes, because that is what the
     * corpus reads: {@code obligations-0000/<id>/obligation.jsonl} and the
     * {@code focused_task.jsonl} the replay was driven by, beside the
     * {@code obligation_result.jsonl} that names the session.  The WORLD a
     * session ran in is read off the focus row -- it is the only row that
     * states the whole of it -- so a fixture that wrote only the ask left
     * the replay's valuation stated nowhere.</p>
     */
    private static void obligation(Path iteration, String sessionId,
                                   Map<String, String> roots)
            throws IOException {
        obligation(iteration, sessionId, roots, "nn#u1",
                Collections.<String>emptyList());
    }

    /** The same, held to {@code site} and to the inherited flips. */
    private static void obligation(Path iteration, String sessionId,
                                   Map<String, String> roots, String site,
                                   List<String> inherited)
            throws IOException {
        Path worker = iteration.resolve("obligations-0000")
                .resolve("ob-" + sessionId);
        Files.createDirectories(worker);
        RowCodec.writeJsonl(worker.resolve(ObligationDir.OBLIGATION),
                Collections.singletonList(ExploreCodec.writeObligation(
                        Obligation.of("ob-" + sessionId, "task-flip",
                                "path-flip", "nn#u1", 1, true, roots,
                                Collections.<String, String>emptyMap(),
                                Collections.<String>emptyList()))));
        com.google.gson.JsonObject focus = new com.google.gson.JsonObject();
        focus.addProperty("schemaVersion", 1);
        focus.addProperty("kind", "FOCUSED_TASK");
        focus.addProperty("obligationId", "ob-" + sessionId);
        focus.addProperty("taskId", "task-flip");
        focus.addProperty("pathId", "path-flip");
        com.google.gson.JsonObject flip = new com.google.gson.JsonObject();
        flip.addProperty("siteId", site);
        flip.addProperty("ordinal", 1);
        flip.addProperty("outcome", true);
        focus.add("flip", flip);
        com.google.gson.JsonArray held = new com.google.gson.JsonArray();
        for (String each : inherited) {
            com.google.gson.JsonObject earlier =
                    new com.google.gson.JsonObject();
            earlier.addProperty("siteId", each);
            earlier.addProperty("ordinal", 1);
            earlier.addProperty("outcome", true);
            held.add(earlier);
        }
        com.google.gson.JsonObject assigned =
                new com.google.gson.JsonObject();
        for (Map.Entry<String, String> root : roots.entrySet()) {
            assigned.addProperty(root.getKey(), root.getValue());
        }
        focus.add("rootAssignments", assigned);
        focus.add("clockDeltas", new com.google.gson.JsonObject());
        focus.add("answers", new com.google.gson.JsonObject());
        focus.add("rootMints", new com.google.gson.JsonObject());
        focus.add("inheritedFlips", held);
        focus.add("unproducible", new com.google.gson.JsonArray());
        RowCodec.writeJsonl(worker.resolve(ObligationDir.FOCUSED_TASK),
                Collections.singletonList(focus));
        RowCodec.writeJsonl(worker.resolve(ObligationDir.RESULT),
                Collections.singletonList(RowCodec.writeObligationResult(
                        ObligationResult.of("ob-" + sessionId,
                                Verdict.ADMITTED, sessionId,
                                "the focused prefix reproduced"))));
    }

    /** Whether any of these rows blocks. */
    private static boolean blocking(List<GapRow> gaps) {
        for (GapRow gap : gaps) {
            if (gap.blocking()) return true;
        }
        return false;
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

    private Path warningSolver() throws IOException {
        Path script = folder.newFile("z3-warns.sh").toPath();
        Files.write(script, Arrays.asList("#!/bin/sh",
                "echo 'WARNING: optimization with quantified constraints is"
                        + " not supported'",
                "exec " + z3() + " \"$@\""));
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
        // The producer's own rows: an activation, instrumented, so its
        // decisions are recorded and its arms are attested (Arms.attested).
        // Without the activation row the corpus states a producer's
        // decisions and not that it ran, and a read no attested arm
        // delivers is refused rather than pinned to its arrival.
        session.activation(PRODUCER);
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

        // R4 item 3: AN ARM WHOSE DELIVERED EXPRESSION NAMES A ROOT ITS OWN
        // SESSION STATES NO MINT ROW FOR IS REFUSED, not emitted with an
        // empty guard.  Which quantities are roots is a fact about the
        // corpus, so the seed's mint row is what makes the marker a root;
        // a replay that carries the marker's SYMBOL out of an activation it
        // abandoned publishes no row of its own, and the arm it would
        // deliver is available under every valuation of a quantity nothing
        // of that session attributes.  hdfs-11741 campaign #4 composed
        // satisfiably at the recorded valuation on exactly that.
        Path unrowed = folder.newFolder("unrowed").toPath();
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        Session seed = new Session(unrowed, "s0", false);
        seed.activation(PRODUCER);
        seed.marker("false");
        seed.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        seed.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        seed.export(first, "EXPR.v1.marker", 1L, "false");
        seed.attach(consumer, "vh1", "false", first);
        seed.target("vh1", false, true);
        seed.write();

        Session abandoned = new Session(unrowed, "s1", true);
        abandoned.activation(PRODUCER);
        // The symbol, and no RootMintRow for the root it names.
        abandoned.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        abandoned.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        abandoned.export(first, "EXPR.v1.marker", 1L, "true");
        abandoned.attach(consumer, "vh1", "true", first);
        abandoned.target("vh1", true, true);
        abandoned.write();

        Composer.Composition refused = compose(unrowed, 4);
        assertTrue("the arm that session would deliver is refused by name: "
                        + refused.gaps(),
                says(refused.gaps(), GapKind.UNATTESTED_ARM,
                        "an arm delivered by session s1 names root "
                                + MARKER_ROOT + " and that session states "
                                + "no RootMintRow for it, so the arm is "
                                + "refused"));
        assertTrue("and the refusal names the slot",
                named(refused.gaps(), Interaction.of(InteractionKind.WIRE,
                        first, consumer).id()));
        int delivered = 0;
        for (Family family : refused.families()) {
            delivered += family.arms().size();
        }
        assertEquals("so that session contributes no arm and the slot's "
                        + "family carries the seed's alone: "
                        + refused.families(), 1, delivered);

        // ONLY AN ADMITTED REPLAY STATES A TOPOLOGY.  A session pairing
        // this epoch's consumer with ANOTHER producer is a replacement
        // either way -- the two pairings cannot both be this epoch's, so
        // its arms stay out of every family -- and only an ADMITTED
        // replay's replacement STOPS the composition.  FAIL CLOSED ON THE
        // ARMS, OPEN ON THE CLAIM: hdfs-11741 campaign #2 filed eight
        // BLOCKING rows for one replay whose mint had planted nothing, so
        // a replay that did not run the world it was asked for refused a
        // claim about the world that did run.
        Path unadmitted = folder.newFolder("replaced-unadmitted").toPath();
        Session held = new Session(unadmitted, "s0", false);
        held.activation(PRODUCER);
        held.marker("false");
        held.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        held.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        held.export(first, "EXPR.v1.marker", 1L, "false");
        held.attach(consumer, "vh1", "false", first);
        held.target("vh1", false, true);
        held.write();
        // The epoch's skeleton, where EXPLORE publishes it: the seed's
        // pairing, and the composition reads it from that file.
        SlotTable skeleton = SlotTable.read(unadmitted);
        skeleton.reconcile(Corpus.read(unadmitted, null),
                Collections.singleton(ANCHOR.id()), 0);
        skeleton.write(unadmitted);

        Session wrongWorld = new Session(unadmitted, "s1", true);
        wrongWorld.activation(PRODUCER);
        wrongWorld.marker("true");
        wrongWorld.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        wrongWorld.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        wrongWorld.export(second, "EXPR.v1.marker", 2L, "true");
        wrongWorld.attach(consumer, "vh1", "true", second);
        wrongWorld.target("vh1", true, true);
        wrongWorld.refused("the obligation assigns a root no mint of this "
                + "replay planted");
        wrongWorld.write();

        Composer.Composition stands = compose(unadmitted, 4);
        boolean diagnostic = false;
        for (GapRow gap : stands.gaps()) {
            if (gap.kind() != GapKind.TOPOLOGY_DIVERGENCE) continue;
            assertFalse("a replay that was not admitted stops nothing: "
                    + gap.detail(), gap.cls() == GapClass.BLOCKING);
            diagnostic |= gap.sessionId().equals("s1")
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.detail().endsWith("(this replay was not "
                            + "admitted, so it states no topology)");
        }
        assertTrue("the replacement is still filed, naming why it stops "
                + "nothing: " + stands.gaps(), diagnostic);
        int standing = 0;
        for (Family family : stands.families()) {
            standing += family.arms().size();
        }
        assertEquals("and its arms are out of every family all the same, "
                        + "so only the seed's arm stands: "
                        + stands.families(), 1, standing);
    }

    // ------------------------------------------------------------------
    // 3. A witness may not move a root inside an unattested arm.
    // ------------------------------------------------------------------

    @Test
    public void aWitnessMayNotMoveARootInsideAnUnattestedArm()
            throws Exception {
        Path iteration = folder.newFolder("unattested").toPath();
        LocationId cell = LocationId.of(LocationKind.INSTANCE, "5", "8");
        // A STATE arm, which is where this rule still bites: the OBSERVED
        // writer is stated whatever it is (it is what the run did), so an
        // unattested one reaches the formula and carries the marker.  On a
        // WIRE read the rule is now stronger and earlier -- a read no
        // attested arm delivers is refused by name and its path never
        // enters the disjunction at all (Composer.handoffRead) -- so the
        // witness this test is about cannot be built there.
        for (String[] each : new String[][]{{"s0", "false", "false"},
                {"s1", "true", "true"}}) {
            boolean flip = "true".equals(each[2]);
            Session session = new Session(iteration, each[0], flip);
            // The WRITER ran CONCRETELY -- its activation is not
            // instrumented -- so the recording can say what it wrote and
            // nothing about what it would have written.
            session.activation(PRODUCER, "thread#nn", flip, false);
            session.marker(each[1]);
            session.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
            session.write(Endpoint.of(PRODUCER, "Keys#put#1:WRITE",
                            at("put#1", 0), 0), cell, 1L,
                    "EXPR.v1.marker");
            session.read(Endpoint.of(ANCHOR, "Keys#get#1:READ",
                            at("get#1", 0), 0), cell, 1L, "vh", "Z", null);
            session.target("vh", flip, true);
            session.write();
        }

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

        // ONE RUN BEHIND EVERY OUT OF ONE OCCURRENCE (PIPELINE §8).  The
        // producer exports at TWO ports and the anchor attaches both; one
        // run delivered (true, false) there and the other (false, true).
        // With a selector per family a witness takes the first port from
        // one run and the second from the other and reads (true, true) --
        // an export no execution made, which is how 11741's four
        // block-key-id handoffs came back 182906, 182908, 182908, 182907
        // out of a NameNode whose export held 182905, 182906, 182907,
        // 182908.  One selector per (occurrence, run) is what forbids it,
        // and the fatal predicate here IS that mixture.
        Path positions = folder.newFolder("two-positions").toPath();
        Endpoint portA = Endpoint.of(PRODUCER, "PORT.a", at("export#1", 0), 0);
        Endpoint portB = Endpoint.of(PRODUCER, "PORT.b", at("export#2", 0), 0);
        Endpoint inA = Endpoint.of(ANCHOR, "PORT.a", at("attach#1", 0), 0);
        Endpoint inB = Endpoint.of(ANCHOR, "PORT.b", at("attach#2", 0), 0);
        for (String[] each : new String[][]{{"s0", "true", "false"},
                {"s1", "false", "true"}}) {
            Session run = new Session(positions, each[0],
                    !"s0".equals(each[0]));
            run.activation(PRODUCER);
            // ONE value in both runs, so the two are not told apart by a
            // root's guard: what separates them is the selector alone.
            run.marker("false");
            run.expression("EXPR.v1.a", constant(each[1]));
            run.expression("EXPR.v1.b", constant(each[2]));
            run.export(portA, "EXPR.v1.a", 1L, each[1]);
            run.export(portB, "EXPR.v1.b", 2L, each[2]);
            // ONE message, two leaves: the arrival carries one
            // correlation id on both of them, exactly as an RPC response
            // whose body a loop converted leaf by leaf does.
            run.attach(inA, "vh_a", "Z", each[1], portA, "rpc#1");
            run.attach(inB, "vh_b", "Z", each[2], portB, "rpc#1");
            run.target("(and vh_a vh_b)", false, true);
            run.write();
        }
        Composer.Composition mixed = compose(positions, 4);
        assertEquals("both runs are paths", 2, mixed.disjuncts().size());
        // The two leaves of one MESSAGE share ONE selector, so the eight
        // a per-leaf split declared are four: one per (path, run whose
        // world is compatible), each binding both leaves out of that one
        // run -- so a model may not answer the two leaves out of two
        // different runs.
        assertEquals("one selector per (path, compatible run): "
                        + mixed.armSelectors(), 4,
                mixed.armSelectors().size());
        assertEquals("and no witness reads an export no run made",
                "unsat", solver().ask(mixed.query(
                        mixed.valuations().get(0).assertions()),
                        null, false).status());

        // R3c: A RUN THAT DELIVERED FEWER OUTS IS NO OPTION.  The same two
        // ports, and now one run exported at the first only and the other
        // at the second only: every port has an attested delivery, and no
        // run of this corpus made both, so nothing could have produced what
        // this path attached and the path leaves the disjunction by name.
        Path partial = folder.newFolder("partial-export").toPath();
        for (String[] each : new String[][]{{"s0", "a"}, {"s1", "b"}}) {
            Session run = new Session(partial, each[0],
                    !"s0".equals(each[0]));
            run.activation(PRODUCER);
            run.marker("false");
            run.expression("EXPR.v1.a", constant("true"));
            run.expression("EXPR.v1.b", constant("true"));
            if ("a".equals(each[1])) {
                run.export(portA, "EXPR.v1.a", 1L, "true");
            } else {
                run.export(portB, "EXPR.v1.b", 2L, "true");
            }
            run.attach(inA, "vh_a", "Z", "true", portA, "rpc#1");
            run.attach(inB, "vh_b", "Z", "true", portB, "rpc#1");
            run.target("(and vh_a vh_b)", false, true);
            run.write();
        }
        Composer.Composition short_ = compose(partial, 4);
        assertTrue("a path no run of this corpus could have produced every "
                        + "delivery of is out of the disjunction: "
                        + short_.disjuncts(),
                short_.disjuncts().isEmpty());
        assertTrue("and the refusal names the message and the first leaf "
                        + "it cannot answer: " + short_.gaps(),
                says(short_.gaps(), GapKind.UNPRODUCIBLE_ANSWER,
                        "attested delivery at every leaf of this message"));
    }

    // ------------------------------------------------------------------
    // 4b. The run as it happened holds each path to its own pairing.
    // ------------------------------------------------------------------

    /**
     * hdfs-17967 path B's shape: a healthy run reaches the fatal arm at the
     * recorded valuation only on another run's delivery, and the marker is
     * the witness.
     *
     * <p>The anchor fails when the id it was delivered is not the id it
     * holds.  s0 (the seed) was delivered 10 and holds 10; s2 was delivered
     * 30 and holds 30; s1 flipped the marker, was delivered 20 and holds 10.
     * The family offers s0's attach every attested delivery, so s0 on s2's
     * reaches the fatal arm with the marker as recorded -- a pairing no run
     * had.  Held to the pairing each run had, the recorded valuation is
     * refuted, that refutation is the polarity, and the flipped marker is
     * the finding: no alarm, and no pairing claim in its place.</p>
     */
    @Test
    public void aHealthyRunOnAnotherRunsDeliveryDoesNotDecideTheRecording()
            throws Exception {
        Path iteration = folder.newFolder("own-pairing").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.id",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.id",
                at("attach#1", 0), 0);
        for (String[] each : new String[][]{{"s0", "false", "10", "10"},
                {"s1", "true", "20", "10"}, {"s2", "false", "30", "30"}}) {
            boolean fatal = !each[2].equals(each[3]);
            Session session = new Session(iteration, each[0],
                    !"s0".equals(each[0]));
            session.activation(PRODUCER);
            session.marker(each[1]);
            session.expression("EXPR.v1.id", integer("I",
                    Long.parseLong(each[2])));
            session.export(producer, "EXPR.v1.id", 1L, each[2]);
            session.attach(consumer, "vh", "I", each[2], producer);
            session.read(Endpoint.of(ANCHOR,
                            "<Manager: int count>#PLACEHOLDER#0:READ",
                            at("count#1", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "Manager", "held"),
                    -1L, PLACEHOLDER, "I", each[3]);
            session.expression("EXPR.0000000000000fc2", binary("!=",
                    symbol("vh", "I"), symbol(PLACEHOLDER, "I")));
            session.target("EXPR.0000000000000fc2", fatal, true);
            session.write();
        }

        Composer.Composition composition = compose(iteration, 8);
        assertEquals("the three runs reach the anchor", 3,
                composition.paths().size());
        assertEquals("every path is held to its own pairing", 3,
                composition.recordedPairings().size());

        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertFalse("a pairing no run had is not the run as it happened: "
                        + decision.claim().gaps(),
                says(decision.claim().gaps(),
                        GapKind.FORMULA_SAT_AT_RECORDED_VALUATION, ""));
        assertEquals(decision.claim().gaps().toString(),
                ClaimKind.MARKER_FLIPPED, decision.claim().kind());
        assertEquals(Collections.singletonMap(MARKER_ROOT, "true"),
                decision.claim().movedRoots());
        assertTrue("the refutation held to the recording is the polarity",
                decision.claim().polarityDecides());
    }

    // ------------------------------------------------------------------
    // 5. Each path carries its own session's arrival -- and a read no
    //    attested arm delivers is refused, never pinned to one.
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
            // The producer's rows are stated, so its arm is attested and
            // the read is bound to what it DELIVERED; the arrival is kept
            // beside the path, one per session, because it is the pairing
            // that run had and not a reason for it.
            session.activation(PRODUCER);
            session.marker("false");
            session.expression("EXPR.v1.id", integer("I",
                    Long.parseLong(each[1])));
            session.export(producer, "EXPR.v1.id", 1L, each[1]);
            session.attach(consumer, "vh", "I", each[1], producer);
            session.target("true", false, true);
            session.write();
        }

        Composer.Composition composition = compose(iteration, 4);
        assertEquals(2, composition.disjuncts().size());
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            String own = "s0".equals(disjunct.path().sessionId) ? "10" : "20";
            assertTrue("this path states the arrival ITS OWN session "
                            + "recorded: " + disjunct.path().sessionId + " "
                            + composition.observedArrivals(
                                    disjunct.path().pathId),
                    composition.observedArrivals(disjunct.path().pathId)
                            .toString().contains("vh " + own + ")"));
        }
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

        // AND THE OTHER HALF OF THE ONE RULE.  The same two sessions with
        // no rows for the producer at all: nothing attests what it
        // delivered, so the read is refused BY NAME and neither path
        // enters the disjunction.  Binding it to the literal each session
        // happened to receive is the pin this composer no longer makes --
        // an arrival is the value, and the question the path asks is
        // whether the producer could have delivered another one.
        Path unstated = folder.newFolder("arrivals-unstated").toPath();
        for (String[] each : new String[][]{{"s0", "10", "false"},
                {"s1", "20", "true"}}) {
            Session session = new Session(unstated, each[0],
                    "true".equals(each[2]));
            session.marker("false");
            session.attach(consumer, "vh", "I", each[1], producer);
            session.target("true", false, true);
            session.write();
        }
        Composer.Composition refused = compose(unstated, 4);
        assertTrue("no path rests on an arrival: " + refused.disjuncts(),
                refused.disjuncts().isEmpty());
        assertTrue("and the refusal is named: " + refused.gaps(),
                named(refused.gaps(), GapKind.UNATTESTED_ARM));

        // R1: ATTESTATION IS THE PRODUCER'S PROPERTY.  The same two paths,
        // where the SEED instrumented the producer and the focused replay
        // did not: what that occurrence would have delivered is stated by
        // the session that ran it symbolically, so BOTH paths bind the
        // attach to that session's export expression and neither falls back
        // to the arrival it happened to receive.  Asking whether the
        // CONSUMER's own session attests the producer asked about the wrong
        // run, and left every hdfs-11741 focused path on the literal.
        Path attested = folder.newFolder("attested").toPath();
        session(attested, "s0", false, "false", producer, consumer,
                "vh", "false", null, true, false, "EXPR.v1.marker");
        session(attested, "s1", true, "false", producer, consumer,
                "vh", "true", null, false, false, "EXPR.v1.marker");
        Composer.Composition across = compose(attested, 4);
        assertEquals("both sessions reached the anchor", 2,
                across.disjuncts().size());
        assertTrue("the arm the seed attests binds the consumer's variable",
                across.body().contains("(= vh " + MARKER + ")"));
        assertFalse("so the focused replay's own arrival is not the answer",
                across.body().contains("(= vh true)"));

        // A REFUSAL IS ITS FRAME'S.  The first corpus again, where s1's run
        // refused an attach at the anchor itself, which then computed on
        // the arrival as a constant, and s0's run refused one in an
        // occurrence no closure here reaches: s1's path is refused, by
        // name, and s0's is composed as before.
        Path framed = folder.newFolder("framed").toPath();
        for (String[] each : new String[][]{{"s0", "10", "false"},
                {"s1", "20", "true"}}) {
            Session session = new Session(framed, each[0],
                    "true".equals(each[2]));
            session.activation(PRODUCER);
            session.marker("false");
            session.expression("EXPR.v1.id", integer("I",
                    Long.parseLong(each[1])));
            session.export(producer, "EXPR.v1.id", 1L, each[1]);
            session.attach(consumer, "vh", "I", each[1], producer);
            session.target("true", false, true);
            session.refusedAttach("s1".equals(each[0]) ? ANCHOR : UPSTREAM);
            session.write();
        }
        Composer.Composition refusedFrame = compose(framed, 4);
        assertEquals("only s0's path: " + refusedFrame.gaps(), "s0",
                refusedFrame.disjuncts().get(0).path().sessionId);
        assertEquals(1, refusedFrame.disjuncts().size());
        assertTrue("s1's is refused for its anchor's refusal",
                says(refusedFrame.gaps(), GapKind.UNSTATED_VALUE,
                        "whose own run refused a value it computes on"));
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

        // R4b: A VERDICT IS THE SESSION'S OWN ROW.  A replay that refused
        // the obligation it ran collected no arm the seed lacks, so its
        // path is not a disjunct -- and where the WAVE's aggregate copy
        // states a different verdict than the session's own, the corpus
        // states one verdict twice and differently and the composition
        // refuses by name.  The campaign shell stamped ADMITTED onto the
        // aggregate after every replay that merely finished, so hdfs-11741
        // campaign #3 composed all eleven focused paths, six of whose own
        // sessions said NOT_ADMITTED.
        Path refused = folder.newFolder("verdicts").toPath();
        Session recording = new Session(refused, "s0", false);
        recording.marker("false");
        recording.target("true", false, true);
        recording.write();
        Session flip = new Session(refused, "s1", true);
        flip.marker("false");
        flip.refused("wrong decision at nn#u1: took true, the obligation "
                + "flips it to false");
        flip.target("true", false, true);
        flip.write();
        // The wave's own copy of that verdict, as the aggregate holds it.
        Path worker = refused.resolve("obligations-0000").resolve("OBL.s1");
        Files.createDirectories(worker);
        RowCodec.writeAll(worker.resolve(ObligationDir.RESULT),
                Collections.singletonList(ObligationResult.of("OBL.s1",
                        Verdict.ADMITTED, "s1", "the shell said so")),
                RowCodec::writeObligationResult);

        Composer.Composition verdicts = compose(refused, 4);
        assertEquals("only the recording is a path", 1,
                verdicts.disjuncts().size());
        assertEquals("s0", verdicts.disjuncts().get(0).path().sessionId);
        assertTrue("the refusal is named",
                named(verdicts.gaps(), GapKind.ADMISSION_GAP));
        boolean twice = false;
        for (GapRow gap : verdicts.gaps()) {
            twice |= gap.cls() == GapClass.BLOCKING
                    && gap.kind() == GapKind.UNSTATED_VALUE
                    && "OBL.s1".equals(gap.subject());
        }
        assertTrue("and so is the disagreement with the wave's own file",
                twice);
    }

    // ------------------------------------------------------------------
    // 7. A relative domain is relative to the reading it was declared on;
    //    a path states the roots IT minted, and a root its own terms never
    //    name is not something it is refused for.
    // ------------------------------------------------------------------

    @Test
    public void aPathIsNotRefusedForARootItsOwnTermsNeverName()
            throws Exception {
        Path iteration = folder.newFolder("unminted").toPath();
        twoReadings(iteration);

        Composer.Composition window = compose(iteration, 8);
        assertEquals(2, window.disjuncts().size());
        assertFalse("a root two sessions read differently gets no "
                        + "corpus-wide window",
                window.body().contains("root_domain__"));
        assertTrue("the seed's own window is on the seed's path",
                window.body().contains("(>= " + SERIAL + " 119994)"));
        assertTrue("and the later session's own window is on its path",
                window.body().contains("(>= " + SERIAL + " 119997)"));
        // The value the old corpus-wide window excluded: legal for the
        // session that read 119997, and for no other.
        Z3 solver = solver();
        for (Composer.Disjunct disjunct : window.disjuncts()) {
            List<String> pinned = new ArrayList<String>();
            pinned.add("(assert " + disjunct.selector() + ")");
            pinned.add("(assert (= " + SERIAL + " 120000))");
            String status = solver.ask(window.query(pinned),
                    Collections.<String>emptyList(), false).status();
            assertEquals("three rotations past its own reading, on "
                            + disjunct.path().sessionId,
                    "s1".equals(disjunct.path().sessionId)
                            ? "sat" : "unsat", status);
        }

        // s2 replayed an occurrence that never mints the counter: no row
        // of it states the root and no term of its path names the symbol.
        // hdfs-11741's three hook-minted BLOCK_KEY.EXPIRY_DATE roots are
        // exactly this shape -- twelve focused replays of nn0's
        // KEY_MANAGER_TICK mint them and neither the seed nor any other
        // replay does.
        Session quiet = new Session(iteration, "s2", true);
        quiet.target("true", false, true);
        quiet.write();

        Composer.Composition composition = compose(iteration, 8);
        assertEquals("the path that says nothing about the root is in the "
                        + "disjunction with the two that do: "
                        + composition.gaps(), 3,
                composition.disjuncts().size());
        assertFalse("and nothing about that root is BLOCKING",
                blocking(composition.gaps(), SERIAL_ROOT));
        assertTrue("each minting path still states its own reading",
                composition.body().contains("(>= " + SERIAL + " 119994)")
                        && composition.body().contains(
                                "(>= " + SERIAL + " 119997)"));

        // The same corpus, where s2's OWN phi names the counter.  Now the
        // path does rest on a quantity no row of its session states -- the
        // symbol would be free, or worse, answered by another execution's
        // reading -- and it is refused by the root's name.
        Path naming = folder.newFolder("unminted-named").toPath();
        twoReadings(naming);
        Session names = new Session(naming, "s2", true);
        names.target("(> " + SERIAL + " 0)", false, true);
        names.write();

        Composer.Composition refused = compose(naming, 8);
        assertEquals("the path whose own term names the root is out of the "
                        + "disjunction", 2, refused.disjuncts().size());
        assertTrue("and the refusal is BLOCKING and names the root",
                blocking(refused.gaps(), SERIAL_ROOT));
    }

    /**
     * s0 and s1 mint the declared counter at two readings, so the corpus
     * VARIES it and each path carries its own valuation of it: the
     * NameNode's serial advances between replays, so "up to three rotations
     * ahead of what this run read" is a different window on each.
     */
    private void twoReadings(Path iteration) throws IOException {
        for (String[] each : new String[][]{{"s0", "119994", "false"},
                {"s1", "119997", "true"}}) {
            Session session = new Session(iteration, each[0],
                    "true".equals(each[2]));
            session.serial(each[1], "+0", "+3");
            session.target("true", false, true);
            session.write();
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

        // R2: A CLOCK IS PART OF THE WITNESS.  phi holds only where the
        // clock sits past an instant this run did not read, and pinning the
        // cell to what it DID read refutes it -- so the clock is necessary,
        // the mechanism is CLOCK_SKEW, and the claim has to say WHERE the
        // cell had to sit.  No valuation pins a clock and none can report
        // one: the model is the only statement of it, and CLOCK_SKEW was
        // published with
        // movedRoots {} -- 11741 campaign #3's own claim -- about the one
        // finding whose whole content is that something moved.
        Path skew = folder.newFolder("clock-skew").toPath();
        Session skewed = new Session(skew, "s0", false);
        skewed.clock("700");
        // The predicate names the cell so the formula declares it, which is
        // what makes the cell a cell of this composition at all.
        skewed.decision(ANCHOR, "anchor#u1", "(or (> " + CLOCK + " 1000) "
                + "(not (> " + CLOCK + " 1000)))", CLOCK_ROOT, 700L);
        skewed.target("(> " + CLOCK + " 1000)", false, true);
        skewed.write();

        Composer.Composition clocked = compose(skew, 4);
        assertEquals("the cell is the name the formula names",
                Collections.singletonList(CLOCK), clocked.clockCells());
        ClaimPolicy.Decision skewing = ClaimPolicy.decide(clocked,
                solver());
        assertEquals("the arm is reachable with the clock free", "sat",
                skewing.outcomes().get(0).answer().status());
        assertEquals("no declared root moved, and the clock is necessary",
                ClaimKind.CLOCK_SKEW, skewing.claim().kind());
        String at = skewing.claim().movedRoots().get(CLOCK);
        assertNotNull("the witness states where the cell had to sit: "
                + skewing.claim().movedRoots(), at);
        assertTrue("past the instant its session read, which is what the "
                        + "skew IS: " + at,
                Long.parseLong(at.trim()) > 1000L);
        assertTrue("and with room: a confirming replay reads its clocks "
                        + "fresh, so an instant at the boundary would fall "
                        + "back on the recorded arm: " + at,
                Long.parseLong(at.trim())
                        > 1000L + edu.uva.liftlab.graphchecker.explore
                        .ClockMargin.margin(1_000_000L));

        // R3: AND A WINDOWED ROOT BESIDE THE CLOCK DOES NOT TAKE THE CLAIM
        // AWAY.  Same clock, plus one declared counter the case gave a
        // window: ordinal 0 is sat (a clock is free in every valuation),
        // and so is every moved ordinal, because moving the counter does
        // the clock witness no harm.  The moved-root loop asked
        // `polarityDecides` of that and filed the blocking
        // FORMULA_SAT_AT_RECORDED_VALUATION, so a clock-driven case with
        // any other declared root could never publish CLOCK_SKEW -- which
        // is the shape of hdfs-11741.  The clock pin is what decides a
        // clock-driven recorded valuation, and it is asked once.
        Path driven = folder.newFolder("clock-driven").toPath();
        Session both = new Session(driven, "s0", false);
        both.clock("700");
        both.serial("119994", "+0", "+3");
        both.decision(ANCHOR, "anchor#u1", "(or (> " + CLOCK + " 1000) "
                + "(not (> " + CLOCK + " 1000)))", CLOCK_ROOT, 700L);
        both.target("(and (> " + CLOCK + " 1000) (>= " + SERIAL
                + " 119994))", false, true);
        both.write();

        Composer.Composition mixed = compose(driven, 4);
        ClaimPolicy.Decision decided = ClaimPolicy.decide(mixed, solver());
        assertEquals("the arm is reachable at the recorded valuation, the "
                        + "clocks being free there as everywhere", "sat",
                decided.outcomes().get(0).answer().status());
        boolean movedIsSatToo = false;
        for (ClaimPolicy.Outcome outcome : decided.outcomes()) {
            if (outcome.valuation().ordinal() == 0) continue;
            movedIsSatToo |= outcome.answer().sat();
        }
        assertTrue("and so is a valuation that moved the counter, which is "
                + "what used to raise the alarm", movedIsSatToo);
        assertEquals("the clock pin decides it, so the mechanism is the "
                        + "clock and not the counter",
                ClaimKind.CLOCK_SKEW, decided.claim().kind());
        assertEquals("stated at the recorded valuation, where the clock is "
                        + "already free", 0,
                decided.claim().valuationOrdinal());
        assertTrue("with the polarity CLOCK_SKEW carries of its own",
                decided.claim().polarityDecides());
        assertNotNull("and the cell the model had to move: "
                        + decided.claim().movedRoots(),
                decided.claim().movedRoots().get(CLOCK));
        assertFalse("the moved-root loop files no alarm about a witness "
                        + "whose mechanism it never asked about",
                named(decided.claim().gaps(),
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
            // ANSWERED, because that is the only rule left that binds a
            // handoff read to a literal: the arrival fallback is deleted,
            // and an attach nothing attests is refused by name before a
            // sort is ever asked for.
            session.answered(other, "vh_ref", "Lorg/apache/Foo;", "7", null);
            // A read of ONE associative cell, joined to a write of the
            // WHOLE map (its state root) at the version it observed.  The
            // location names its key by hash, so which entry the read
            // returned is not stated: that is refused by name, and not by
            // passing a container on to the operator over it, which named
            // the operator and not the projection.
            session.expression("EXPR.00000000000000b1", relation(
                    "ASSOCIATIVE", "STATE", "java/util/HashMap",
                    symbol("M_L'java/util/HashMap'_4", "java/util/HashMap")));
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
            // A long no row states, compared as the JVM compares longs, and
            // a boolean read no row values, under ==.  Each is refused ONCE,
            // as the long and the boolean they are: at an int and a VALUE
            // cell, the operators over them were refused again (a malformed
            // lcmp, 57 VALUE!=BOOL sort conflicts on a SOLR-18406 path).
            session.expression("EXPR.00000000000000b6", binary(">=",
                    binary("--", symbol(NO_ROW_LONG, "J"),
                            integer("J", 4L)), integer("I", 0L)));
            session.expression("EXPR.00000000000000b7", binary("==",
                    read("INSTANCE_FIELD", 6L, 12L, 5L, "Z"),
                    integer("Z", 1L)));
            // And a call's result the VM minted and no row declares, whose
            // node states what it returned but not the call (a VM before
            // f14): what it was computed from is unknown, so it is refused.
            JsonObject returned = symbol(RETURNED, "J");
            returned.add("concreteValue", integer("J", 2L));
            session.expression("EXPR.00000000000000b8", binary("<",
                    binary("--", returned, integer("J", 3L)),
                    integer("I", 0L)));
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
            // phi rests on every term the decisions above compare and on
            // both reads, so each of their refusals is this path's (a term
            // sharing nothing with phi or a root is left out,
            // Independence).
            session.expression("EXPR.00000000000000fe", binary(">",
                    symbol("absent_join", "I"), integer("I", 0L)));
            session.expression("EXPR.00000000000000fd", binary("==",
                    symbol("two_sorts", "s0".equals(each) ? "I"
                            : "org/apache/Held"),
                    symbol("two_sorts", "s0".equals(each) ? "I"
                            : "org/apache/Held")));
            session.target("(and EXPR.00000000000000b2 "
                    + "EXPR.00000000000000b3 EXPR.00000000000000b4 "
                    + "EXPR.00000000000000b5 EXPR.00000000000000fe "
                    + "EXPR.00000000000000fd EXPR.00000000000000b6 "
                    + "EXPR.00000000000000b7 EXPR.00000000000000b8)", false,
                    true);
            session.write();
        }

        Composer.Composition composition = compose(iteration, 4);
        List<GapRow> gaps = composition.gaps();
        assertTrue("an unpaired attach is a named row",
                says(gaps, GapKind.UNSTATED_VALUE,
                        "names no producer endpoint"));
        assertTrue("a Java type this lowering cannot place is refused",
                says(gaps, GapKind.UNSTATED_VALUE, "names no scalar"));
        assertTrue("and two recordings are not one: the sessions STATE the "
                        + "role they ran as, and two SEEDs is no answer",
                says(gaps, GapKind.UNSTATED_VALUE, "state role SEED"));
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
        assertTrue("and the composition's row for that cut says why the "
                        + "lowering cut it, not a stock sentence",
                says(gaps, GapKind.UNSTATED_VALUE, "no root mint, clock "
                        + "reading, attach or read row of this corpus "
                        + "states this symbol"));
        assertTrue("a long no row states is cut, and a boolean read no row "
                        + "values is refused",
                named(gaps, "UndeclaredFreeSymbol:" + NO_ROW_LONG)
                        && named(gaps, "UNSTATED_VALUE:Read:"
                        + "INSTANCE/6#12@5"));
        for (GapRow gap : gaps) {
            assertFalse("each once, as what it is: no operator over it is "
                            + "refused again: " + gap.subject(),
                    gap.subject().contains("MalformedJvmLcmpOperands")
                            || gap.subject().contains("BinarySortConflict"));
        }
        assertTrue("a method-return symbol whose node states no call is "
                        + "refused by name, whatever value it states",
                named(gaps, "MethodReturnCallUnstated:" + RETURNED)
                        && !named(gaps, "MethodReturnPinned:" + RETURNED));
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
    // 11. Which writer the read could have seen (IDENTITY §4).
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
        // The map, named the way the runtime names an owner: the VM's rid
        // of the object whose state this is, which inside one session is
        // exactly one object.
        LocationId keys = LocationId.of(LocationKind.MAP, "21", "allKeys");
        // The same storage named by its class instead -- the other
        // spelling the runtime writes, for a declared-field read with no
        // VM location key: one name for every instance, so it names none
        // of them.
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
        // R1: what the ancestor STORED is what it was handed over the wire,
        // so the state join reaches a handoff variable the anchor has no
        // attach of its own for.  Bound by nothing it is a free constant in
        // the query -- hdfs-11741 #3 declared dn1's addKeys arrival twelve
        // times inside the allKeys dag and asserted nothing about it -- so
        // the path binds every handoff its own conjunction reaches, by the
        // same three rules the anchor's attaches take.
        session.expression("EXPR.v1.ancestor", symbol("vh_wire", "Z"));
        session.expression("EXPR.v1.wired", symbol(MARKER, "Z"));
        session.activation(PRODUCER);
        Endpoint wireProducer = Endpoint.of(PRODUCER, "PORT.wire",
                at("export#1", 0), 0);
        session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        session.export(wireProducer, "EXPR.v1.wired", 9L, "false");
        session.attach(Endpoint.of(UPSTREAM, "PORT.wire",
                at("attach#1", 0), 0), "vh_wire", "false", wireProducer);
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

        Composer.Composition composition = compose(iteration, reader, 4, StaticScopeMap.empty());
        assertEquals("one disjunct", 1, composition.disjuncts().size());
        assertTrue("the concurrent writer is an alternative",
                composition.body().contains("state_family__"));
        assertTrue("a handoff the state join reaches is bound, not free",
                composition.body().contains("(= vh_wire " + MARKER + ")"));
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
        // A read that joined its version at a location whose writer set was
        // not whole keeps the observed writer only.
        Endpoint readAt = Endpoint.of(reader, "Reader#get#5:READ",
                at("r#1", 0), 0);
        edu.uva.liftlab.graphchecker.smt.Arms arms =
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null));
        String keysKey = SmtLowering.locationKey(keys);
        assertEquals("a whole writer set offers the concurrent writer", 2,
                arms.stateArms(readAt, "s0", keysKey, 1L, true).size());
        assertEquals("a partial one only the writer the read observed", 1,
                arms.stateArms(readAt, "s0", keysKey, 1L, false).size());
        // PIPELINE §8: alternatives need an owner that names the
        // storage.  The class-owned copy of the same state gets the
        // delivery its own run gave it, and says so.
        assertTrue("the rid the runtime writes names the storage",
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

    @Test
    public void aGuardedReadInPhiIsTheSymbolItsStateFamilyMoves()
            throws Exception {
        // The VM's guarded read names no symbol; phi reads the stamp a tick
        // wrote and another tick is concurrent.  Observed at v2, the second
        // tick's write; at v3, a write no row states (its writer ran
        // outside every region), so the read's own pin is the run's arm.
        for (long observed : new long[]{2L, 3L}) {
            Path iteration = folder.newFolder("guarded-" + observed).toPath();
            OccurrenceAddress reader = occurrence("case/nn0", "REGION.commit",
                    CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                    frame("Namesystem#commit#12", 0));
            OccurrenceAddress first = occurrence("case/nn0", "REGION.tick",
                    CausalContext.of(Role.of("TICK_A"), "", 1),
                    frame("TickA#run#3", 0));
            OccurrenceAddress second = occurrence("case/nn0", "REGION.tock",
                    CausalContext.of(Role.of("TICK_B"), "", 1),
                    frame("TickB#run#3", 0));
            LocationId stamp = LocationId.of(LocationKind.INSTANCE, "10",
                    "value");
            String symbol = SmtLowering.locationKey(stamp) + "@v" + observed
                    + "@s0";
            Session session = new Session(iteration, "s0", false);
            session.occurrence = reader;
            session.activation(reader);
            session.activation(first);
            session.activation(second);
            session.marker("false");
            session.expression("EXPR.v1.one", integer("I", 1L));
            session.expression("EXPR.v1.two", integer("I", 2L));
            session.write(Endpoint.of(first, "TickA#set#4:WRITE",
                    at("w#1", 0), 0), stamp, 1L, "EXPR.v1.one");
            session.write(Endpoint.of(second, "TickB#set#4:WRITE",
                    at("w#2", 0), 0), stamp, 2L, "EXPR.v1.two");
            session.read(Endpoint.of(reader, "Block#getStamp#29:READ",
                            at("r#1", 0), 0), stamp, observed, symbol, "I",
                    Long.toString(observed));
            session.expression("EXPR.00000000000000f1", binary("!=",
                    integer("I", observed),
                    read("INSTANCE_FIELD", stamp.owner(), "value", observed,
                            "I")));
            session.target("EXPR.00000000000000f1", false, true);
            session.write();

            Composer.Composition composition = compose(iteration, reader, 4, StaticScopeMap.empty());
            String body = composition.body();
            assertTrue("the other tick is an alternative at v" + observed,
                    body.contains("state_family__"));
            assertTrue("and phi reads the symbol it moves, not the value "
                            + "the run's writer stored: " + body,
                    body.contains(SmtNames.legalSymbols("(not (= "
                            + observed + " " + symbol + "))")));
            assertEquals("a write no row states is the run's own arm",
                    observed == 3L, body.contains("observed_arm__"));
        }
    }

    @Test
    public void aFieldThroughAMovedOwnerIsTheFieldOfTheObjectItIs()
            throws Exception {
        // SOLR-18406's latestCommit: two writers each build a commit, store
        // it and a flag as one block; phi reads the generation THROUGH the
        // reference.  The run read commit 11 (generation 5) and the healthy
        // flag.  Moved to the other writer, phi reads commit 12's
        // generation, never 11's: 3 is no witness, 7 is one, whether a write
        // before the store states it or, never written, a read of it.  A
        // cell with no one value while 12 was stored -- written twice, or
        // only after the store -- answers nothing: that pairing is refused
        // by name.
        String commit = "org/apache/Commit";
        LocationId latest = LocationId.of(LocationKind.INSTANCE, "8", "48");
        LocationId flag = LocationId.of(LocationKind.INSTANCE, "8", "56");
        LocationId own = LocationId.of(LocationKind.INSTANCE, "11", "24");
        LocationId other = LocationId.of(LocationKind.INSTANCE, "12", "24");
        for (Object[] each : new Object[][]{
                {3L, "written", ClaimKind.NO_SUPPORTED_WITNESS},
                {7L, "written", ClaimKind.STATE_PAIRING_FLIPPED},
                {7L, "read", ClaimKind.STATE_PAIRING_FLIPPED},
                {7L, "twice", ClaimKind.NO_SUPPORTED_WITNESS},
                {7L, "late", ClaimKind.NO_SUPPORTED_WITNESS}}) {
            long generation = (Long) each[0];
            String row = generation + " " + each[1];
            Path iteration = folder.newFolder("moved-owner-" + generation
                    + "-" + each[1]).toPath();
            OccurrenceAddress reader = occurrence("case/leader",
                    "REGION.fetch", CausalContext.of(Role.of("DATA_XCEIVER"),
                            "", 1), frame("Stream#write#4", 0));
            OccurrenceAddress mine = occurrence("case/leader",
                    "REGION.commit", CausalContext.of(Role.of("IPC_HANDLER"),
                            "", 1), frame("Policy#onCommit#2", 0));
            OccurrenceAddress theirs = occurrence("case/leader",
                    "REGION.init", CausalContext.of(Role.of("HEARTBEAT_TICK"),
                            "", 1), frame("Policy#onInit#9", 0));
            Session session = new Session(iteration, "s0", false);
            session.occurrence = reader;
            session.activation(reader);
            session.activation(mine);
            session.activation(theirs);
            session.expression("EXPR.v1.theirs",
                    symbol("M_L'" + commit + "'_12", commit));
            session.expression("EXPR.v1.mine",
                    symbol("M_L'" + commit + "'_11", commit));
            session.expression("EXPR.v1.five", integer("I", 5L));
            session.expression("EXPR.v1.true", constant("true"));
            session.expression("EXPR.v1.false", constant("false"));
            session.expression("EXPR.v1.generation",
                    integer("I", generation));
            // The other writer first: it builds commit 12, then stores it.
            long version = 0L;
            for (int index = 0; index < ("twice".equals(each[1]) ? 2
                    : "written".equals(each[1]) ? 1 : 0); index++) {
                session.write(Endpoint.of(theirs, "Commit#init#3:WRITE",
                        at("generation#" + index, 0), 0), other, ++version,
                        "EXPR.v1.generation");
            }
            if ("read".equals(each[1])) {
                session.read(Endpoint.of(theirs, "Commit#get#2:READ",
                        at("generation#0", 0), 0), other, 99L,
                        SmtLowering.locationKey(other) + "@v99@s0", "I",
                        Long.toString(generation));
            }
            session.write(Endpoint.of(theirs, "Policy#update#4:WRITE",
                    at("latest#1", 0), 0), latest, ++version,
                    "EXPR.v1.theirs");
            session.write(Endpoint.of(theirs, "Policy#update#5:WRITE",
                    at("flag#1", 0), 0), flag, ++version, "EXPR.v1.true");
            if ("late".equals(each[1])) {
                session.write(Endpoint.of(theirs, "Commit#set#6:WRITE",
                        at("generation#0", 0), 0), other, ++version,
                        "EXPR.v1.generation");
            }
            // Then the writer whose versions the reader observed.
            long constructed = ++version;
            session.write(Endpoint.of(mine, "Commit#init#3:WRITE",
                    at("generation#9", 0), 0), own, constructed,
                    "EXPR.v1.five");
            long stored = ++version;
            session.write(Endpoint.of(mine, "Policy#update#4:WRITE",
                    at("latest#2", 0), 0), latest, stored, "EXPR.v1.mine");
            long flagged = ++version;
            session.write(Endpoint.of(mine, "Policy#update#5:WRITE",
                    at("flag#2", 0), 0), flag, flagged, "EXPR.v1.false");
            session.read(Endpoint.of(reader, "Stream#latest#6:READ",
                    at("read#1", 0), 0), latest, stored,
                    SmtLowering.locationKey(latest) + "@v" + stored + "@s0",
                    "L", null);
            session.read(Endpoint.of(reader, "Stream#flag#7:READ",
                    at("read#2", 0), 0), flag, flagged,
                    SmtLowering.locationKey(flag) + "@v" + flagged + "@s0",
                    "Z", null);
            // The VM's pair: concreteValue is the run's cell, 11#24.
            JsonObject owner = read("INSTANCE_FIELD", 8L, 48L, stored, "L");
            session.expression("EXPR.00000000000000f1", binary(">",
                    fieldRead(commit, 24L, "I", owner, read("INSTANCE_FIELD",
                            11L, 24L, constructed, "I")),
                    integer("I", 4L)));
            session.expression("EXPR.00000000000000f2", read("INSTANCE_FIELD",
                    8L, 56L, flagged, "Z"));
            session.target("(and EXPR.00000000000000f1 EXPR.00000000000000f2)",
                    false, true);
            session.write();

            Composer.Composition composition = compose(iteration, reader, 4, StaticScopeMap.empty());
            assertTrue(row + ": the other writer is an alternative",
                    composition.body().contains("state_family__"));
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            assertEquals(row, each[2], decision.claim().kind());
            boolean named = false;
            for (GapRow gap : composition.gaps()) {
                named |= gap.subject().equals("CANDIDATE_UNANSWERED:"
                        + SmtLowering.locationKey(other) + "@s0");
            }
            assertEquals(row + ": a cell with no one value is named",
                    each[2] == ClaimKind.NO_SUPPORTED_WITNESS
                            && generation == 7L, named);
        }
    }

    /**
     * SOLR-18406's shape (R3-REFCONT §4.3).  Each commit builds a fresh
     * map, puts every commit whose deleted flag is false, and swaps it into
     * {@code knownCommits}; a reader asks it for generation 5 and throws on
     * an absent one.  Generation 5 is deleted when the clock passed its
     * reservation ({@code nanoTime < reserves.getOrDefault(5, 0L)} failed,
     * the deadline a reserver's clock plus its duration).  The seed's newer
     * map holds 5; in the flipped replay the clock ran past the deadline,
     * the flag was set, the put was skipped, and the reader threw.  The query is asked of the map the reference
     * holds under each of its writers (one answer per candidate identity),
     * the newer map rests on the decisions that built it (the construction
     * guard names the flag), and the claim is CLOCK_SKEW with the clock
     * moved and polarity deciding.
     */
    @Test
    public void aQueryThroughAReplacedReferenceIsAskedOfTheMapItHolds()
            throws Exception {
        Path iteration = folder.newFolder("replaced-map").toPath();
        OccurrenceAddress reader = occurrence("solr/leader", "REGION.fetch",
                CausalContext.of(Role.of("REPLICATION"), "", 1),
                frame("ReplicationHandler#fetch#3", 0));
        OccurrenceAddress older = occurrence("solr/leader", "REGION.commit",
                CausalContext.of(Role.of("COMMIT"), "", 1),
                frame("Policy#onCommit#2", 0));
        OccurrenceAddress newer = occurrence("solr/leader", "REGION.commit",
                CausalContext.of(Role.of("COMMIT"), "", 2),
                frame("Policy#onCommit#2", 0));
        OccurrenceAddress reserver = occurrence("solr/leader",
                "REGION.reserve", CausalContext.of(Role.of("RESERVE"), "", 1),
                frame("Wrapper#setReserveDuration#4", 0));
        for (String each : new String[]{"s0", "w1"}) {
            replacedMap(iteration, each, "w1".equals(each), reader, older,
                    newer, reserver);
        }
        Path map = iteration.resolve(StaticScopeMap.FILE);
        String put = "{\"kind\":\"STATIC_SCOPE_SITE\",\"role\":"
                + "\"WRITE_SITE\",\"regionId\":\"REGION.commit\","
                + "\"vmSite\":\"" + UPDATE + "\",\"cell\":\"" + KNOWN
                + "\",\"carrier\":\"" + KNOWN + "\",";
        Files.write(map, Arrays.asList(put + "\"siteId\":\"" + UPDATE_SITE
                        + "56\",\"guards\":[]}",
                put + "\"siteId\":\"" + UPDATE_SITE + "54\","
                        + "\"declaredCallee\":\"<java.util.Map: "
                        + "java.lang.Object put(java.lang.Object,"
                        + "java.lang.Object)>\",\"publishedFrom\":\"$r18\","
                        + "\"guards\":[\"" + UPDATE_SITE + "49\"],"
                        + "\"guardOutcomes\":[false]}"),
                StandardCharsets.UTF_8);

        Composer.Composition composition = compose(iteration, reader, 4,
                StaticScopeMap.read(map));
        String flipped = "";
        for (String line : composition.body().split("\n")) {
            if (line.contains("path_fatal__1")) flipped = line;
        }
        assertTrue("both writers of the reference are its family: "
                        + composition.gaps(),
                composition.body().contains("state_family__"));
        assertTrue("the query is asked of the map each writer stored: "
                        + flipped, flipped.contains("(ite (= kc@w1 "));
        assertTrue("the newer map rests on the flag that left 5 out: "
                + flipped, flipped.contains("deleted5@w1"));
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertEquals(decision.claim().gaps().toString(), ClaimKind.CLOCK_SKEW,
                decision.claim().kind());
        assertTrue(decision.claim().polarityDecides());
        assertTrue("the reservation clock is what moved: "
                        + decision.claim().movedRoots(),
                decision.claim().movedRoots().containsKey(NANO));
        // Without the static fact, nothing ties the newer map to the flag.
        assertFalse(compose(iteration, reader, 4, StaticScopeMap.empty())
                .body().contains("deleted5@w1"));
    }

    /**
     * A read is movable only in the path that made it so: lowered again in a
     * later path (a message arm in its session), a query through it is the
     * run's own answer, and it mints no nested selector no arm of that path
     * could bind.
     */
    @Test
    public void aReadIsMovableOnlyInThePathThatMovedIt() throws Exception {
        Path iteration = folder.newFolder("movable-per-path").toPath();
        OccurrenceAddress reader = occurrence("solr/leader", "REGION.fetch",
                CausalContext.of(Role.of("REPLICATION"), "", 1),
                frame("ReplicationHandler#fetch#3", 0));
        replacedMap(iteration, "s0", false, reader, occurrence("solr/leader",
                "REGION.commit", CausalContext.of(Role.of("COMMIT"), "", 1),
                frame("Policy#onCommit#2", 0)), occurrence("solr/leader",
                "REGION.commit", CausalContext.of(Role.of("COMMIT"), "", 2),
                frame("Policy#onCommit#2", 0)), occurrence("solr/leader",
                "REGION.reserve", CausalContext.of(Role.of("RESERVE"), "", 1),
                frame("Wrapper#setReserveDuration#4", 0)));
        Corpus corpus = Corpus.read(iteration, null);
        SmtLowering lowering = new SmtLowering(corpus.declaredSymbols());
        // path, whether this path moved the read
        Object[][] paths = {{"the path that joined it", true},
                {"a later path", false}};
        for (Object[] path : paths) {
            lowering.path();
            lowering.begin("s0", corpus.join("s0"),
                    corpus.expressions("s0"));
            if ((Boolean) path[1]) lowering.movable("kc@s0");
            String asked = lowering.term("EXPR.00000000000000d1", "test")
                    .text + " " + lowering.end();
            assertEquals((String) path[0] + ": " + asked, path[1],
                    asked.contains("nest__"));
            assertEquals((String) path[0], path[1],
                    !lowering.nestedSelectors().isEmpty());
        }
    }

    /**
     * A String a map answers is null where its cell is the null cell (a key
     * never put, a value stored null), so {@code get(k) != null} is a
     * condition over the state, never refused for an unknown nullness.
     */
    @Test
    public void aStringAMapAnswersIsNullWhereItsCellIs() {
        Map<String, VmTermLowering.Sort> declared =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        declared.put("s", VmTermLowering.Sort.STRING);
        declared.put("k", VmTermLowering.Sort.INT);
        SmtLowering lowering = new SmtLowering(declared);
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        JsonObject put = relation("ASSOCIATIVE", "PUT", "java/util/Map",
                relation("ASSOCIATIVE", "SNAPSHOT_BASE", "java/util/HashMap",
                        null), integer("I", 5L),
                vmLeaf("SymbolExpression", "s", "Ljava/lang/String;"));
        JsonObject asked = relation("ASSOCIATIVE", "READ",
                "Ljava/lang/String;", put,
                vmLeaf("SymbolExpression", "k", "I"));
        String text = lowering.dispatch(binary("!=", asked, vmNull()),
                VmTermLowering.Sort.BOOL, "test").text;
        lowering.end();
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        assertTrue(text, text.contains(ContainerStateModel.NULL_CELL));
    }

    /**
     * A reference compared with an object the VM named is an identity
     * test whichever side the object is on.
     */
    @Test
    public void aNamedObjectBesideAReferenceIsItsIdentityOnEitherSide() {
        Map<String, VmTermLowering.Sort> declared =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        declared.put("r", VmTermLowering.Sort.REF);
        SmtLowering lowering = new SmtLowering(declared);
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        JsonObject reference = symbol("r", "Ljava/lang/Object;");
        JsonObject named = symbol("M_L'java/util/HashMap'_3",
                "java/util/HashMap");
        String left = lowering.dispatch(binary("==", reference, named),
                VmTermLowering.Sort.BOOL, "test").text;
        String right = lowering.dispatch(binary("==", named, reference),
                VmTermLowering.Sort.BOOL, "test").text;
        lowering.end();
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        assertTrue(left, left.startsWith("(= r identity__"));
        assertEquals(left, right.replaceFirst("^\\(= (\\S+) r\\)$",
                "(= r $1)"));
    }

    /**
     * What another writer of the reference may have handed the reader, by
     * variant: a map mutated after its store by a writer concurrent with the
     * reader is each state the reader could have seen, chosen by nested
     * selectors; stored again after that mutation, the later store lets the
     * reader see only the later state; the run's own map, mutated and stored
     * again, is seen through that re-store from its referent on, not as the
     * run read it; a store whose map state the VM refused is no case, named;
     * a reader that mutated the map through the reference, or a store of a
     * wrapper over the map (a query through it names no owner), holds it to
     * the run's own pairing, named.  Each writer's arm states the states it
     * may deliver and the read the query answered, which CONFIRM holds;
     * where only the other map's later state reaches the fatal, the claim's
     * witness takes that store and names that state, and that state rests
     * on the decision its writer mutated the map under.
     */
    @Test
    public void aReplacedReferencesOtherMapIsEachStateTheReaderCouldSee()
            throws Exception {
        String map = "java/util/HashMap";
        LocationId known = LocationId.of(LocationKind.INSTANCE, "8", "16");
        LocationId other = LocationId.of(LocationKind.MAP, "20", "-3");
        LocationId own = LocationId.of(LocationKind.MAP, "30", "-3");
        Object[][] variants = {
                // variant, states on the first writer's arm, on the third's
                {"mutated", 2, 0}, {"restored", 2, 1}, {"own-restored", 1, 1},
                {"claimed", 2, 0}, {"guarded", 2, 0}, {"refused", 0, 0},
                {"put", 0, 0}, {"wrapper", 0, 0}};
        for (Object[] row : variants) {
            String variant = (String) row[0];
            // The run's own map holds 5 too: only the other map's later
            // state reaches the fatal; guarded, its writer removed 5 under
            // a clock comparison.
            boolean guarded = "guarded".equals(variant);
            boolean claimed = "claimed".equals(variant) || guarded;
            boolean mutated = "mutated".equals(variant)
                    || "restored".equals(variant) || claimed;
            boolean asked = mutated || "own-restored".equals(variant);
            Path iteration = folder.newFolder("other-map-" + variant)
                    .toPath();
            OccurrenceAddress reader = occurrence("solr/leader",
                    "REGION.fetch", CausalContext.of(Role.of("REPLICATION"),
                            "", 1), frame("ReplicationHandler#fetch#3", 0));
            OccurrenceAddress[] writers = new OccurrenceAddress[3];
            Session session = new Session(iteration, "s0", false);
            session.occurrence = reader;
            session.activation(reader);
            for (int index = 0; index < writers.length; index++) {
                writers[index] = occurrence("solr/leader", "REGION.commit",
                        CausalContext.of(Role.of("COMMIT"), "", index + 1),
                        frame("Policy#onCommit#2", 0));
                session.activation(writers[index], "commit#" + index, false);
            }
            JsonObject base = relation("ASSOCIATIVE", "SNAPSHOT_BASE", map,
                    null);
            JsonObject five = putCommit(base, 5L);
            JsonObject six = putCommit(claimed ? five : base, 6L);
            JsonObject[] states = {base, five, base, six};
            LocationId[] held = {other, other, own, own};
            for (int index = 0; index < states.length; index++) {
                session.expression("EXPR.000000000000001" + index,
                        states[index]);
                session.write(Endpoint.of(writers[index / 2], "Map#put#"
                        + index + ":WRITE", at("m#" + index, 0), 0),
                        held[index], index + 1L, "EXPR.000000000000001"
                                + index);
            }
            session.expression("EXPR.0000000000000020",
                    symbol("M_L'" + map + "'_20", map));
            session.expression("EXPR.0000000000000030",
                    symbol("M_L'" + map + "'_30", map));
            String wrapper = "java/util/Collections$UnmodifiableMap";
            session.expression("EXPR.0000000000000070",
                    symbol("M_L'" + wrapper + "'_25", wrapper));
            session.writes.add(WriteRow.of("s0", ++session.seq,
                    Endpoint.of(writers[0], UPDATE + "#56:WRITE",
                            at("kc#1", 0), 0), known, 5L,
                    "wrapper".equals(variant) ? "EXPR.0000000000000070"
                            : "EXPR.0000000000000020", "L",
                    "refused".equals(variant)
                            ? null : WriteRow.Referent.of(other, 2L),
                    "refused".equals(variant) ? "RESIZING" : null));
            session.writes.add(WriteRow.of("s0", ++session.seq,
                    Endpoint.of(writers[1], UPDATE + "#56:WRITE",
                            at("kc#2", 0), 0), known, 6L,
                    "EXPR.0000000000000030", "L", WriteRow.Referent.of(own,
                            4L), null));
            JsonObject owner = read("INSTANCE_FIELD", 8L, 16L, 6L,
                    "Ljava/util/Map;");
            JsonObject query = six;
            long version = 4L;
            if ("put".equals(variant)) {
                query = putCommit(six, 9L);
                query.add("owner", owner);
                session.expression("EXPR.0000000000000040", query);
                session.write(Endpoint.of(reader, "Map#put#9:WRITE",
                        at("m#9", 0), 0), own, version = 7L,
                        "EXPR.0000000000000040");
            }
            session.read(Endpoint.of(reader, "Wrapper#getAndSave#3:READ",
                    at("kc#3", 0), 0), known, 6L, "kc", "Ljava/util/Map;",
                    null);
            JsonObject get = relation("ASSOCIATIVE", "READ", "L", query,
                    integer("J", 5L));
            get.add("owner", owner);
            JsonObject answered = read("MAP_STATE", 30L, -3L, version, "L");
            answered.getAsJsonObject("observedVersion").add("expression",
                    get);
            Endpoint asking = Endpoint.of(reader, "Wrapper#getAndSave#9:READ",
                    at("q#1", 0), 0);
            session.read(asking, own, version, "q", "L", null);
            // After the read, on a thread of its own: 5 leaves the other
            // map, or joins the run's own.
            boolean ownMoved = "own-restored".equals(variant);
            if (guarded) {
                session.roots.add(RootMintRow.of("s0", ++session.seq,
                        writers[2], "ROOT.CLEAN", "M_J_clean",
                        RootKind.CLOCK, "1000", null, null, true, 1L));
                session.expression("EXPR.0000000000000090", binary("<",
                        symbol("M_J_clean", "J"), integer("J", 2_000L)));
                session.decision(writers[2], "Cleaner#clean#u3", true,
                        "EXPR.0000000000000090");
            }
            if (mutated || ownMoved) {
                session.expression("EXPR.0000000000000050", ownMoved
                        ? putCommit(six, 5L) : relation("ASSOCIATIVE",
                        "REMOVE", map, five, integer("J", 5L)));
                session.write(Endpoint.of(writers[2], "Map#remove#1:WRITE",
                        at("m#10", 0), 0), ownMoved ? own : other, 10L,
                        "EXPR.0000000000000050");
            }
            if ("restored".equals(variant) || ownMoved) {
                session.writes.add(WriteRow.of("s0", ++session.seq,
                        Endpoint.of(writers[2], UPDATE + "#56:WRITE",
                                at("kc#4", 0), 0), known, 11L, ownMoved
                                ? "EXPR.0000000000000030"
                                : "EXPR.0000000000000020", "L",
                        WriteRow.Referent.of(ownMoved ? own : other, 10L),
                        null));
            }
            session.expression("EXPR.0000000000000060", binary("==",
                    answered, vmNull()));
            session.target("EXPR.0000000000000060", !claimed, true);
            session.write();

            Composer.Composition composition = compose(iteration, reader, 4,
                    StaticScopeMap.empty());
            if (claimed) {
                ClaimPolicy.Decision decision = ClaimPolicy.decide(
                        composition, solver());
                assertEquals(decision.claim().gaps().toString(),
                        ClaimKind.STATE_PAIRING_FLIPPED,
                        decision.claim().kind());
                List<String> seen = new ArrayList<String>();
                for (ComposedFamilies.ArmChoice arm : decision.outcomes()
                        .get(decision.claim().valuationOrdinal())
                        .selectedArms().values()) {
                    for (SmtLowering.StateChoice state : arm.states()) {
                        seen.add(state.state.endpoint().site() + "@"
                                + state.state.version() + " for "
                                + endpoints(state.readers));
                    }
                }
                assertEquals("the witness's query saw the mutated map",
                        Collections.singletonList("Map#remove#1:WRITE@10 for "
                                + Collections.singletonList(asking)), seen);
            }
            String path = fatalArm(composition);
            assertEquals(variant + ": " + path, asked,
                    path.contains("nest__"));
            // The refused map is no case, and a pinned owner is the run's.
            assertEquals(variant + ": " + path, asked,
                    path.contains("(ite (= kc "));
            assertEquals(variant + ": " + composition.gaps(),
                    "refused".equals(variant), named(composition.gaps(),
                            "@s0") && says(composition.gaps(),
                            GapKind.UNSTATED_VALUE, "(RESIZING)"));
            // A family of the reference binds its read to each writer's map.
            assertEquals(variant, asked || "refused".equals(variant),
                    composition.body().contains("(= kc identity__"));
            assertEquals(variant, "put".equals(variant),
                    named(composition.gaps(),
                            "OWNER_PINNED_BY_MUTATION:INSTANCE/8#16@s0"));
            assertEquals(variant, "wrapper".equals(variant),
                    named(composition.gaps(),
                            "OWNER_PINNED_BY_WRAPPER:INSTANCE/8#16@s0"));
            // Through the first store the reader sees the map as stored or
            // as mutated after; through a store after the mutation, only
            // the latter; each state held to the read the query answered.
            for (int index : new int[]{0, 2}) {
                String digest = ArtifactIO.digest(writers[index].id()
                        + "|s0", 12);
                String arm = "";
                for (String line : composition.body().split("\n")) {
                    if (line.contains("writer_family__")
                            && line.contains(digest)) {
                        arm = line;
                    }
                }
                int expected = (Integer) row[index == 0 ? 1 : 2];
                Set<String> nested = new LinkedHashSet<String>();
                java.util.regex.Matcher named = java.util.regex.Pattern
                        .compile("nest__[0-9a-f]+").matcher(arm);
                while (named.find()) nested.add(named.group());
                assertEquals(variant + ": " + arm, expected, nested.size());
                ComposedFamilies.ArmChoice choice =
                        composition.arm("writer_arm__0__" + digest);
                List<String> chosen = new ArrayList<String>();
                for (SmtLowering.StateChoice state : choice == null
                        ? Collections.<SmtLowering.StateChoice>emptyList()
                        : choice.states()) {
                    assertEquals(variant, Collections.singletonList(asking),
                            endpoints(state.readers));
                    chosen.add(state.selector);
                }
                assertEquals(variant, expected, chosen.size());
            }
            String selector = composition.disjuncts().get(0).selector();
            if (guarded) {
                // The later state holds only where its writer's comparison
                // does: with the clock past it, no arm reaches the fatal.
                for (String clock : new String[]{"1500", "2500"}) {
                    assertEquals(variant + " at " + clock,
                            "1500".equals(clock), solver().ask(
                                    composition.query(Arrays.asList(
                                            "(assert " + selector + ")",
                                            "(assert (= M_J_clean " + clock
                                                    + "))")),
                                    Collections.<String>emptyList(), false)
                                    .sat());
                }
            }
            if (!ownMoved) continue;
            // Through the re-store the run's own map holds 5: no fatal
            // there; through the store the read saw, it is the run's.
            for (int index : new int[]{1, 2}) {
                String arm = "writer_arm__0__" + ArtifactIO.digest(
                        writers[index].id() + "|s0", 12);
                assertEquals(variant + " through writer " + index,
                        index == 1, solver().ask(composition.query(
                                Arrays.asList("(assert " + selector + ")",
                                        "(assert " + arm + ")")),
                                Collections.<String>emptyList(), false)
                                .sat());
            }
        }
    }

    private static List<Endpoint> endpoints(List<ReadRow> reads) {
        List<Endpoint> found = new ArrayList<Endpoint>();
        for (ReadRow read : reads) found.add(read.endpoint());
        return found;
    }

    private static final String UPDATE = "org.apache.solr.core"
            + ".IndexDeletionPolicyWrapper#updateKnownCommitPoints"
            + "(Ljava/util/List;)V";
    private static final String UPDATE_SITE = "<org.apache.solr.core"
            + ".IndexDeletionPolicyWrapper: void updateKnownCommitPoints"
            + "(java.util.List)>#u";
    private static final String KNOWN = "<org.apache.solr.core"
            + ".IndexDeletionPolicyWrapper: java.util.Map knownCommits>";
    private static final String NANO = "M_J_nano_reserve";
    private static final String RESERVED = "M_J_nano_reserved";

    /**
     * One run of the replaced-map fixture: the older commit's map of 4 and
     * 5, the newer commit's map of 6 and, unless the reservation of 5 ran
     * out, 5; the reader's query of 5 through {@code knownCommits}.
     */
    private void replacedMap(Path iteration, String id, boolean expired,
                             OccurrenceAddress reader,
                             OccurrenceAddress older,
                             OccurrenceAddress newer,
                             OccurrenceAddress reserver) throws IOException {
        String map = "java/util/concurrent/ConcurrentHashMap";
        LocationId known = LocationId.of(LocationKind.INSTANCE, "8", "16");
        LocationId olderMap = LocationId.of(LocationKind.MAP, "20", "-3");
        LocationId newerMap = LocationId.of(LocationKind.MAP, "30", "-3");
        LocationId flag = LocationId.of(LocationKind.INSTANCE, "45", "36");
        Session session = new Session(iteration, id, expired);
        session.occurrence = reader;
        for (OccurrenceAddress at : Arrays.asList(reader, older, newer,
                reserver)) {
            session.activation(at);
        }
        long seed = 1_000_000_000_000L;
        // The reservation of 5: the reserver's clock plus 6000.
        LocationId reserves = LocationId.of(LocationKind.MAP, "50", "-3");
        session.roots.add(RootMintRow.of(id, ++session.seq, reserver,
                "ROOT.RESERVED", RESERVED, RootKind.CLOCK,
                Long.toString(seed - 1_000L), null, null, true, 1L));
        JsonObject deadline = binary("+", symbol(RESERVED, "J"),
                integer("J", 6_000L));
        deadline.addProperty("_java_type", "J");
        JsonObject reserved = relation("ASSOCIATIVE", "PUT", "java/util/Map",
                relation("ASSOCIATIVE", "SNAPSHOT_BASE",
                        "java/util/concurrent/ConcurrentHashMap", null),
                integer("J", 5L), deadline);
        session.expression("EXPR.00000000000000e1", reserved);
        session.write(Endpoint.of(reserver, "Map#merge#1:WRITE",
                at("reserve#1", 0), 0), reserves, 70L,
                "EXPR.00000000000000e1");
        session.roots.add(RootMintRow.of(id, ++session.seq, newer,
                "ROOT.RESERVE", NANO, RootKind.CLOCK, Long.toString(
                        expired ? seed + 10_000L : seed), null, null, true,
                1L));
        // The older commit's map, then its store.
        JsonObject base = relation("ASSOCIATIVE", "SNAPSHOT_BASE", map, null);
        JsonObject four = putCommit(base, 4L);
        JsonObject five = putCommit(four, 5L);
        session.expression("EXPR.00000000000000a1", base);
        session.expression("EXPR.00000000000000a2", four);
        session.expression("EXPR.00000000000000a3", five);
        session.expression("EXPR.00000000000000a4",
                symbol("M_L'" + map + "'_20", map));
        long version = 0L;
        for (String ref : new String[]{"a1", "a2", "a3"}) {
            session.write(Endpoint.of(older, "Map#put#" + ref + ":WRITE",
                    at("m20#" + ref, 0), 0), olderMap, ++version,
                    "EXPR.00000000000000" + ref);
        }
        session.writes.add(WriteRow.of(id, ++session.seq, Endpoint.of(older,
                UPDATE + "#56:WRITE", at("kc#1", 0), 0), known, ++version,
                "EXPR.00000000000000a4", "L", WriteRow.Referent.of(olderMap,
                        3L), null));
        // The newer commit: the reservation of 5, the flag it set, the
        // loop over 5 and 6, its map, its store.
        JsonObject reservation = read("MAP_STATE", 50L, -3L, 70L, "J");
        reservation.getAsJsonObject("observedVersion").add("expression",
                relation("ASSOCIATIVE", "READ_OR_DEFAULT", "J", reserved,
                        integer("J", 5L), integer("J", 0L)));
        session.read(Endpoint.of(newer, "IndexCommitWrapper#delete#2:READ",
                at("reserve#2", 0), 0), reserves, 70L, "reserve@" + id,
                "J", Long.toString(seed + 5_000L));
        session.expression("EXPR.00000000000000b1", binary("<",
                symbol(NANO, "J"), reservation));
        session.decisions.add(DecisionRow.of(id, ++session.seq, newer,
                "IndexCommitWrapper#delete#u5", 1, !expired,
                "EXPR.00000000000000b1",
                Collections.singletonMap(NANO, seed)));
        long deleted = 90L;
        if (expired) {
            session.expression("EXPR.00000000000000b2", constant("true"));
            deleted = ++version;
            session.write(Endpoint.of(newer, "CommitPoint#delete#3:WRITE",
                    at("deleted#1", 0), 0), flag, deleted,
                    "EXPR.00000000000000b2");
        }
        session.read(Endpoint.of(newer, UPDATE + "#40:READ",
                at("deleted#2", 0), 0), flag, deleted, "deleted5@" + id,
                "Z", expired ? "1" : "0");
        session.expression("EXPR.00000000000000b3", binary("==",
                read("INSTANCE_FIELD", 45L, 36L, deleted, "Z"),
                integer("Z", 0L)));
        session.decision(newer, UPDATE_SITE + "49", !expired,
                "EXPR.00000000000000b3");
        JsonObject kept = expired ? base : putCommit(base, 5L);
        JsonObject six = putCommit(kept, 6L);
        session.expression("EXPR.00000000000000c1", base);
        session.expression("EXPR.00000000000000c2", kept);
        session.expression("EXPR.00000000000000c3", six);
        session.expression("EXPR.00000000000000c4",
                symbol("M_L'" + map + "'_30", map));
        long built = 0L;
        for (String ref : expired ? new String[]{"c1", "c3"}
                : new String[]{"c1", "c2", "c3"}) {
            built = ++version;
            session.write(Endpoint.of(newer, "Map#put#" + ref + ":WRITE",
                    at("m30#" + ref, 0), 0), newerMap, built,
                    "EXPR.00000000000000" + ref);
        }
        long stored = ++version;
        session.writes.add(WriteRow.of(id, ++session.seq, Endpoint.of(newer,
                UPDATE + "#56:WRITE", at("kc#2", 0), 0), known, stored,
                "EXPR.00000000000000c4", "L", WriteRow.Referent.of(newerMap,
                        built), null));
        // The reader: the reference, then the query through it.
        session.read(Endpoint.of(reader, "Wrapper#getAndSave#3:READ",
                at("kc#3", 0), 0), known, stored, "kc@" + id,
                "Ljava/util/Map;", "M_L'" + map + "'_30");
        JsonObject query = relation("ASSOCIATIVE", "READ", "L", six,
                integer("J", 5L));
        query.add("owner", read("INSTANCE_FIELD", 8L, 16L, stored,
                "Ljava/util/Map;"));
        JsonObject answered = read("MAP_STATE", 30L, -3L, built, "L");
        answered.getAsJsonObject("observedVersion").add("expression", query);
        session.read(Endpoint.of(reader, "Wrapper#getAndSave#9:READ",
                at("q#1", 0), 0), newerMap, built, "q@" + id, "L", null);
        session.expression("EXPR.00000000000000d1", binary("==", answered,
                vmNull()));
        session.target("EXPR.00000000000000d1", expired, true);
        session.write();
    }

    /** One {@code put(Long.valueOf(generation), commit)} on a map state. */
    private static JsonObject putCommit(JsonObject state, long generation) {
        return relation("ASSOCIATIVE", "PUT", "java/util/Map", state,
                integer("J", generation), symbol(
                        "M_L'org/apache/solr/core/IndexCommitWrapper'_"
                                + (100L + generation),
                        "org/apache/solr/core/IndexCommitWrapper"));
    }

    @Test
    public void anRpcHandlersChainGoesOnThroughTheSenderItsActivationPlaces()
            throws Exception {
        Path iteration = folder.newFolder("sender").toPath();
        // A plain RPC declares no port, so no export or attach row places
        // the client's send; the handler's own activation does.
        OccurrenceAddress client = occurrence("case/client", "REGION.append",
                CausalContext.of(Role.of("TEST_MAIN"), "", 1),
                frame("Test#append#3", 0));
        Endpoint sent = Endpoint.of(client, "PORT.ipc", at("send#1", 0), 0);
        OccurrenceAddress placed = occurrence("case/nn0", "REGION.complete",
                CausalContext.of(sent.id(), "case/client/ipc"),
                frame("Server#call#40", 0));
        OccurrenceAddress unplaced = occurrence("case/nn0", "REGION.addBlock",
                CausalContext.of(Endpoint.of(client, "PORT.ipc",
                        at("send#2", 0), 0).id(), "case/client/ipc"),
                frame("Server#call#41", 0));
        OccurrenceAddress tick = occurrence("case/nn0", "REGION.monitor",
                CausalContext.of(Role.of("LEASE_MONITOR"), "", 1),
                frame("Monitor#run#9", 0));
        Session session = new Session(iteration, "s0", false);
        session.activation(placed, sent);
        session.activation(unplaced);
        session.activation(tick);
        session.write();

        edu.uva.liftlab.graphchecker.smt.Arms arms =
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null));
        assertTrue("a handler whose sender is placed reaches its root",
                arms.concurrent(placed, tick, "s0"));
        assertFalse("one whose sender nothing places states no order",
                arms.concurrent(unplaced, tick, "s0"));
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
        LocationId keys = LocationId.of(LocationKind.MAP, "21", "allKeys");

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

        Composer.Composition composition = compose(iteration, reader, 4, StaticScopeMap.empty());
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
        // A findingKind names a mechanism, and the claim may name one only
        // where the EVIDENCE for it is in this composition: the state slot
        // this witness replaces is there to be pinned, and there is no wire
        // slot at all -- no attach, no arrival.  A branch whose `otherwise`
        // was MESSAGE_PAIRING_FLIPPED published exactly that mechanism over
        // a composition with families=0 and no wire row, which is
        // verification #6's wrong claim; the rule is now one routine
        // (ClaimPolicy#mechanism) with no such parameter.
        String witness = decision.outcomes().get(1).selected()
                .path().pathId;
        assertFalse("the replaced state slot is this kind's evidence",
                composition.observedReads(witness).isEmpty());
        assertTrue("and a wire pairing is a mechanism this composition "
                        + "could not name: there is no arrival to replace",
                composition.observedArrivals(witness).isEmpty());
    }

    /**
     * The recorded arm is the pairing the run took, or there is none and the
     * claim is blocked by name.  (a) The observed writer wrote again after
     * the read: its arm is the write read, not the later one.  (b) Two reads
     * of one location saw two writes, and one arm binds both.  (c) The one
     * writer read has no arm: its block, stretched to its write of another
     * location, rests on a decision nothing states.  (p) A second read saw a
     * version no row wrote: the pins' arm, holding each read to its own
     * join or pin, is the run, whichever read came first.
     */
    @Test
    public void theRecordedArmIsTheWriteReadOrABlockingGap()
            throws Exception {
        OccurrenceAddress reader = occurrence("case/dn0", "REGION.read",
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 1),
                frame("Reader#run#4", 0));
        OccurrenceAddress first = occurrence("case/dn0", "REGION.first",
                CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                frame("Handler#run#2", 0));
        OccurrenceAddress second = occurrence("case/dn0", "REGION.second",
                CausalContext.of(Role.of("HEARTBEAT_TICK"), "", 1),
                frame("Heartbeat#run#9", 0));
        OccurrenceAddress third = occurrence("case/dn0", "REGION.third",
                CausalContext.of(Role.of("LEASE_MONITOR"), "", 1),
                frame("Monitor#run#5", 0));
        LocationId keys = LocationId.of(LocationKind.MAP, "21", "allKeys");
        LocationId stamp = LocationId.of(LocationKind.INSTANCE, "10",
                "value");
        String taut = "(or " + MARKER + " (not " + MARKER + "))";
        for (String shape : new String[]{"a", "b", "c", "p"}) {
            Path iteration = folder.newFolder("recorded-" + shape).toPath();
            for (String[] each : new String[][]{{"s0", "false", "false"},
                    {"s1", "true", "true"}}) {
                Session session = new Session(iteration, each[0],
                        "true".equals(each[2]));
                session.occurrence = reader;
                session.activation(reader);
                session.activation(first);
                session.activation(second);
                session.activation(third);
                session.marker(each[1]);
                session.expression("EXPR.v1.observed", constant("false"));
                session.expression("EXPR.v1.other", symbol(MARKER, "Z"));
                session.expression("EXPR.v1.later", constant("true"));
                session.decision(first, "first#u1", taut);
                session.write(Endpoint.of(first, "Handler#put#3:WRITE",
                        at("w#1", 0), 0), keys, 1L, "EXPR.v1.observed");
                session.decision(second, "second#u1", taut);
                session.write(Endpoint.of(second, "Heartbeat#put#7:WRITE",
                        at("w#1", 0), 0), keys, 2L, "EXPR.v1.other");
                if ("a".equals(shape)) {
                    session.write(Endpoint.of(first, "Handler#put#8:WRITE",
                            at("w#2", 0), 0), keys, 3L, "EXPR.v1.later");
                }
                if ("c".equals(shape)) {
                    session.decision(first, "first#u2", "(and " + MARKER
                            + " ghost)");
                    session.write(Endpoint.of(first, "Handler#set#9:WRITE",
                            at("w#3", 0), 0), stamp, 5L, "EXPR.v1.later");
                    session.write(Endpoint.of(second, "Heartbeat#set#8:WRITE",
                            at("w#2", 0), 0), stamp, 4L, "EXPR.v1.other");
                    session.decision(third, "third#u1", taut);
                    session.write(Endpoint.of(third, "Monitor#put#6:WRITE",
                            at("w#1", 0), 0), keys, 3L, "EXPR.v1.observed");
                    session.read(Endpoint.of(reader, "Reader#stamp#6:READ",
                            at("r#2", 0), 0), stamp, 4L, "read_s", each[1]);
                }
                session.read(Endpoint.of(reader, "Reader#get#5:READ",
                        at("r#1", 0), 0), keys, 1L, "read_k", "false");
                if ("b".equals(shape) || "p".equals(shape)) {
                    // The other writer's version, or one no row wrote (a
                    // boolean returned is spelled 0 or 1).
                    long seen = "b".equals(shape) ? 2L : 9L;
                    session.read(Endpoint.of(reader, "Reader#get#7:READ",
                            at("r#3", 0), 0), keys, seen, "read_j", "0");
                }
                session.target("read_k", false, true);
                session.write();
            }
            Composer.Composition composition = compose(iteration, reader, 4, StaticScopeMap.empty());
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            assertEquals(shape + ": both runs are paths", 2,
                    composition.disjuncts().size());
            boolean stated = "a".equals(shape) || "p".equals(shape);
            assertEquals(shape + ": a recorded pairing iff one arm is it",
                    stated, !composition.recordedPairings().isEmpty());
            assertEquals(shape + ": the pins' arm iff a read saw no write",
                    "p".equals(shape),
                    composition.body().contains("observed_arm__"));
            boolean named = false;
            for (GapRow gap : decision.claim().gaps()) {
                named |= gap.kind() == GapKind.UNSTATED_VALUE
                        && gap.blocking()
                        && gap.subject().equals(SmtLowering.locationKey(keys));
            }
            assertEquals(shape + ": else the location is named", !stated,
                    named);
            assertEquals(shape + ": and the claim is blocked " + decision
                    .claim().gaps(), !stated, decision.claim().blocked());
            if (stated) {
                assertEquals(shape + ": the run as it happened is healthy",
                        "unsat", decision.outcomes().get(0).answer()
                                .status());
                assertEquals(shape, ClaimKind.STATE_PAIRING_FLIPPED,
                        decision.claim().kind());
            }
        }
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
        // A clock the anchor's own predicate reads, with the instant this
        // run read it.  The decision keys its reading by the clock's ROOT
        // ID and the formula names the SYMBOL the session minted: asked
        // whether the lowering declared the root id, the answer was no for
        // every cell of every corpus, so the composition had no clock cell
        // at all and CLOCK_SKEW could not be asked about in 52+ manifests.
        session.clock("700");
        session.decision(ANCHOR, "anchor#u9", "(> " + CLOCK + " 300)",
                CLOCK_ROOT, 700L);
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
        // Then written in place and shrunk: a WRITE keeps the size it was
        // written at, and the removal after it shifts that many cells
        // (Lucene's deleteCommits compaction was unstated-size without it).
        JsonObject three = relation("INDEXED", "REMOVE", relation("INDEXED",
                "WRITE", two, integer("I", 1L), integer("I", 9L)),
                integer("I", 1L));
        // READ, not SIZE: a size is answered arithmetically along the
        // chain, and it is the STATE the shift has to produce.
        session.expression("EXPR.00000000000000c3", binary("==",
                relation("INDEXED", "READ", "I", three, integer("I", 0L)),
                integer("I", 7L)));
        session.decision(ANCHOR, "anchor#u7", true,
                "EXPR.00000000000000c3");
        // And a read of the WHOLE list, joined to the write that made it:
        // a read of one cell is answered through the mutations without
        // materialising the state, and it is this one -- the list as a
        // value -- that needs every index of it written out.
        session.expression("EXPR.00000000000000c4", three);
        session.write(Endpoint.of(ANCHOR, "Saver#snapshots#5:WRITE",
                        at("list#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "8", "16"), 3L,
                "EXPR.00000000000000c4");
        session.read(Endpoint.of(ANCHOR, "Saver#snapshots#6:READ",
                        at("list#2", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "8", "16"), 3L,
                "INSTANCE/8#16@v3", "java/util/ArrayList", null);
        // A read no term names whose join REQUIRES something: one cell of
        // that list, at a position another field held (a stream's pos, its
        // row stating 0).  The position in range and the cell a boxed int
        // are what the join required, and they go with the join: neither
        // the position nor its read is in the query (hdfs-17899-bug3 r4
        // left 480 such requires on free positions in the path).
        session.expression("EXPR.00000000000000c5", relation("INDEXED",
                "READ", "I", three, read("INSTANCE_FIELD", 8L, 32L, 6L,
                        "I")));
        session.write(Endpoint.of(ANCHOR, "Saver#cell#7:WRITE",
                        at("cell#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "8", "40"), 7L,
                "EXPR.00000000000000c5");
        session.read(Endpoint.of(ANCHOR, "Saver#cell#8:READ",
                        at("cell#2", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "8", "40"), 7L,
                "INSTANCE/8#40@v7", "I", null);
        session.read(Endpoint.of(ANCHOR, "Saver#pos#9:READ",
                        at("pos#1", 0), 0),
                LocationId.of(LocationKind.INSTANCE, "8", "32"), 6L,
                "INSTANCE/8#32@v6", "I", "0");
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
        // A map with three keys in it, and the three positions of the view
        // over it: the shape 11741's NameNode exports its block keys at
        // (`allKeys.values().toArray(...)`, one element per position).  Put
        // in an order that is NOT the ascending one, because what a
        // traversal hands back is the map's business and "ascending ints"
        // is not a fact any recording of a HashMap states.
        JsonObject held = relation("ASSOCIATIVE", "SNAPSHOT_BASE",
                "java/util/HashMap", relation("ASSOCIATIVE", "STATE",
                        "java/util/HashMap",
                        symbol("M_L'java/util/HashMap'_88",
                                "java/util/HashMap")));
        for (long key : new long[]{30L, 10L, 20L}) {
            held = relation("ASSOCIATIVE", "PUT", "java/util/HashMap",
                    held, integer("I", key), integer("I", key));
        }
        for (int index = 0; index < 3; index++) {
            session.expression("EXPR.0000000000000e4" + index,
                    viewKey(held, index));
        }
        // And one read of it at a literal key.
        session.expression("EXPR.0000000000000e50", relation("ASSOCIATIVE",
                "READ", "I", held, integer("I", 10L)));
        // And phi reads the array cell the decision above compares: every
        // read of one location is one variable, so that decision is what
        // phi rests on (a decision sharing nothing with phi or a root is
        // left out, Independence).
        session.expression("EXPR.00000000000000f5", binary("!=",
                read("ARRAY_ELEMENT", 7L, 2L, 1L, "I"), integer("I", 6L)));
        // And the reference the two projections above ask about: phi rests
        // on them through it, and not through the null both compare
        // against, which every null check spells alike (Independence).
        session.expression("EXPR.00000000000000f6", binary("!=",
                fieldRead("org/apache/Store", 24L,
                        read("MAP_STATE", 4L, -3L, 9L, "L"),
                        symbol("M_L'org/apache/Held'_9", "org/apache/Held")),
                vmNull()));
        session.target("(and EXPR.00000000000000f1 EXPR.00000000000000f2 "
                        + "EXPR.00000000000000f3 EXPR.00000000000000f4 "
                        + "EXPR.00000000000000f5 EXPR.00000000000000f6)",
                false, true);
        session.write();

        Composer.Composition composition = compose(iteration, 4);
        assertEquals(1, composition.disjuncts().size());
        assertTrue("the arm it took is the term",
                composition.body().contains(MARKER));
        assertTrue("the arm it did not take is the negation",
                composition.body().contains("(not " + MARKER + ")"));
        // The shift, quantifier-free: the elements are a store chain, and
        // the index carries the operation's own definedness -- List.add(i,
        // v) requires 0 <= i <= size and throws otherwise, so an
        // out-of-range index is an execution that threw and not a path
        // that reached the anchor.  The rule is now structural rather than
        // a property of this query: the quantified whole-state relations
        // are not APPLIED and are no longer DECLARED either, so no query
        // can name them and none carries the (exists ...) that made
        // 17960's moved valuation come back "(incomplete quantifiers)".
        assertFalse("no list mutation lowers to a quantified relation, and "
                        + "the preamble declares none: " + composition.body(),
                composition.body().contains("indexed_insert")
                        || composition.body().contains("indexed_remove")
                        || composition.body().contains("indexed_contains"));
        assertTrue("each insertion, the write and the removal carry the "
                        + "operation's own definedness, at the size the "
                        + "recording stated and a write in place kept: "
                        + composition.body(),
                composition.body().contains("(and (<= 0 0) (<= 0 0))")
                        && composition.body().contains(
                        "(and (<= 0 1) (<= 1 1))")
                        && composition.body().contains(
                        "(i 1)) (and (<= 0 i) (< i (indexed_size s))))")
                        && composition.body().contains(
                        "(and (<= 0 1) (< 1 2))"));
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
        assertFalse("and a CLOCK is not a root a valuation moves at all: "
                        + "its domain is the composer's",
                composition.valuations().get(1).moved()
                        .containsKey(CLOCK_ROOT));
        // The CELL of a clock is the name the FORMULA names -- the symbol
        // the session minted -- and not the root id the decision keyed its
        // reading by.  Keyed by the root id, no cell was ever declared, so
        // #clocksNeeded answered "no clocks" without a solver run and
        // CLOCK_SKEW was unreachable.
        assertEquals("one clock cell, named as the formula names it",
                Collections.singletonList(CLOCK), composition.clockCells());
        assertEquals("at the instant this session read", Long.valueOf(700L),
                composition.clockReadings().get(CLOCK));
        assertTrue("floored at the instant the recording read: a clock "
                        + "turned back is no run of anything",
                composition.body().contains("(>= " + CLOCK + " 700)"));
        assertTrue("it is pinned to what the recording read, by a named "
                        + "conjunct an unsat core can read",
                composition.body().contains("(= " + SERIAL + " 41)")
                        && composition.body().contains("root_domain__"));
        assertTrue("a read whose value the ROW states is pinned to it: "
                        + fatalArm(composition),
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(= " + PLACEHOLDER + " 2)")));
        assertTrue("phi's own leaf of that symbol IS that symbol",
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(not (= " + PLACEHOLDER + " 3))")));
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
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(= " + MINTED + " 2)")));
        assertTrue("and phi's ReadFrom over that version IS that row's "
                        + "symbol: " + fatalArm(composition),
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(not (= " + MINTED + " 5))")));
        // The mint laid over a real write: matched by occurrence and
        // location, and valued by the JOIN to the version its row states.
        assertTrue("a placeholder row whose version the write log DOES "
                        + "cover takes the writer's expression, not the "
                        + "value it read: " + fatalArm(composition),
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(= " + MINTED_JOINED + " (java_int_wrap (+ "
                                + SERIAL + " 1)))")));
        assertFalse("so it is not pinned to that value",
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(= " + MINTED_JOINED + " 2)")));
        assertTrue("and the term's ReadFrom over the version the MINT "
                        + "carried is that row's symbol, which no row and "
                        + "no write states by version: "
                        + fatalArm(composition),
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(not (= " + MINTED_JOINED + " 9))")));
        // A ROW'S OWN SYMBOL IS STATED WHERE THE QUESTION ASKS ABOUT IT,
        // and the rows below are the ones it does not.  A read symbol is
        // the runtime's handle for a row; a published expression names a
        // VERSION, which the join resolves to the WRITE's expression, so a
        // reader row's own symbol is reachable from a term only where some
        // row's expression spells it.  These are spelled nowhere: the
        // equation binds a variable no other conjunct, no family arm and
        // no side condition mentions, which is satisfiable for every value
        // of everything it names and therefore constrains nothing -- while
        // its right-hand side drags its whole theory into the query.  The
        // conjunction states what the question reaches
        // ({@code Composer#statedJoins}), each join with what it required
        // (the list cell's position and tag above).
        //
        // MEASURED on hdfs-11741 campaign #4: 119 such joins over 7 paths,
        // among them the anchor's OWN allKeys read as an AssocState
        // (`(= |MAP_STATE/321#-3@v1337| (assoc_put ...))`) -- a second,
        // parallel encoding of the container the fatal predicate reads as
        // the ite DAG.  With the arrivals pinned to literals it was cheap;
        // with them bound by their families it cost z3 the entire 1800 s
        // budget on `assoc_put`/`assoc_remove` (array-and-lambda), all four
        // valuations UNDECIDED.  Dropping the unreached joins and nothing
        // else: every valuation decided, 6.8 s.  It cannot move a verdict
        // -- a fresh variable's defining equation is satisfiable under
        // every model of the rest, so the two formulas are equisatisfiable
        // and agree on every other variable.
        for (String unasked : new String[]{
                "INSTANCE/Manager#count@v2", "INSTANCE/22#24@v174",
                "INSTANCE/2#24@v178", "INSTANCE/Snapshot#32@e-1",
                "INSTANCE/Snapshot#40@e-1", "INSTANCE/8#40@v7",
                "INSTANCE/8#32@v6"}) {
            assertFalse("a row symbol no term of this path names is not "
                            + "written into the query: " + unasked,
                    composition.body().contains(
                            SmtNames.legalSymbols(unasked)));
        }
        // What it does NOT drop: the rows the question DOES reach keep
        // every binding asserted above -- the placeholder's pin, the mint
        // laid over a write taking the writer's chain, and a reference the
        // VM valued "N" answering nullRef rather than an identity of its
        // own (asserted over identity__ names, which phi's own leaves
        // reach).
        assertTrue("the rows the conjunction asks about are all stated: "
                        + fatalArm(composition),
                fatalArm(composition).contains(SmtNames.legalSymbols(
                        "(= " + PLACEHOLDER + " 2)"))
                        && fatalArm(composition).contains(
                        SmtNames.legalSymbols("(= " + MINTED + " 2)"))
                        && fatalArm(composition).contains(
                        SmtNames.legalSymbols("(= " + MINTED_JOINED
                                + " (java_int_wrap (+ " + SERIAL + " 1)))")));

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
                SmtNames.symbols(guard, new LinkedHashSet<String>())
                        .contains(SERIAL));
        Set<String> reached = lowering.reachedSymbols(guard,
                new LinkedHashSet<String>(), new LinkedHashSet<String>());
        assertTrue("and the recorded symbol behind it is: " + reached,
                reached.contains(SERIAL));
        for (String name : reached) {
            assertFalse("a name this lowering minted is not one of the "
                            + "recording's: " + name,
                    lowering.minted(name));
        }

        // AN INDEXED VIEW OF A MAP IS A BIJECTION between its positions and
        // the keys the map holds.  Three keys put into an empty base, and
        // the three positions of the view over it, asked with real z3: no
        // two positions may name one key, no key the map holds may sit at
        // no position, and the order is the map's own and not an order this
        // lowering invented.  Stated position by position -- "this position
        // names SOME present key" -- a formula answers every position with
        // one key and leaves another at none, which is how hdfs-11741's
        // composed query delivered 182906, 182908, 182908, 182907 out of an
        // export that held 182905, 182906, 182907, 182908.
        // A READ AT A LITERAL KEY IS ANSWERED BY ITS OWN PUT: the puts at
        // other literal keys cannot touch it and are not lowered.  A map
        // rebuilt from a store's bytes (Solr's cluster state, one per
        // notification) was millions of named container states otherwise.
        String lookup = lowering.statedTerm("EXPR.0000000000000e50",
                "lookup");
        assertFalse("the read is lowered", lookup.isEmpty());
        for (SmtLowering.Declaration declaration : lowering.reachedBy(
                Collections.singletonList(lookup))) {
            assertFalse("the read reaches no put of the map: "
                            + declaration.render(),
                    declaration.render().contains("assoc_put"));
        }

        String[] position = new String[3];
        for (int index = 0; index < position.length; index++) {
            position[index] = lowering.statedTerm(
                    "EXPR.0000000000000e4" + index, "view");
            assertFalse("the view's position " + index + " is lowered",
                    position[index].isEmpty());
        }
        assertEquals("the view hands the keys back in the map's own order, "
                        + "and a permutation that is not the ascending one "
                        + "is satisfiable", "sat",
                viewAnswer(lowering, "(and (= " + position[0] + " 30) (= "
                        + position[1] + " 10) (= " + position[2]
                        + " 20))"));
        assertEquals("two positions never name one key", "unsat",
                viewAnswer(lowering, "(= " + position[0] + " "
                        + position[1] + ")"));
        assertEquals("and no key the map holds sits at no position",
                "unsat",
                viewAnswer(lowering, "(and (not (= " + position[0]
                        + " 10)) (not (= " + position[1] + " 10)) (not (= "
                        + position[2] + " 10)))"));

        // And a view whose state the recording does not bound -- an opaque
        // map this execution never built here -- has no positions to write
        // those facts out at, so it is refused BY NAME rather than left
        // with positions the solver may answer as it likes.
        lowering.begin("s0", SmtLowering.NO_JOIN, null);
        lowering.dispatch(viewKey(relation("ASSOCIATIVE", "STATE",
                "java/util/HashMap", symbol("M_L'java/util/HashMap'_89",
                        "java/util/HashMap")), 0), null, "view-unbounded");
        List<String> unbounded = new ArrayList<String>(
                lowering.openRefusals());
        lowering.end();
        assertTrue("a view of a map the recording does not bound is "
                        + "refused by name: " + unbounded,
                unbounded.contains(ContainerSmtCodec
                        .ASSOC_VIEW_SIZE_UNSTATED + ":STATE"));
    }

    /** One element of the key view of a map, at one position. */
    private static JsonObject viewKey(JsonObject map, long position) {
        return relation("ASSOCIATIVE", "KEY", "I",
                relation("ASSOCIATIVE", "NEXT", "L",
                        relation("ASSOCIATIVE", "ITERATOR", "L", map),
                        integer("I", position)));
    }

    /** What z3 answers this lowering's facts asked with one more question. */
    private String viewAnswer(SmtLowering lowering, String question) {
        String asked = SmtNames.legalSymbols(question);
        return solver().ask(lowering.body(Collections.singletonList(asked))
                + "(assert " + asked + ")\n", null, false).status();
    }

    // ------------------------------------------------------------------
    // 14. One thread is one order, and nothing else orders an activation.
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
        // Two activations of one thread, and a third on a thread of its
        // own that no message and no thread key places.
        session.activation(earlier, "thread#actor", false);
        session.activation(later, "thread#actor", false);
        session.activation(started, "thread#task", false);
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
        // A third occurrence on a thread of its own: the message chain does
        // not reach it and no recording states a thread-creation edge
        // (contract.ActivationRow), so nothing orders it and the rows say
        // CONCURRENT.  The thread-start edge used to be read off
        // ActivationRow.startedBy, which every producer passed as null --
        // so this was already the answer for every real corpus, stated by
        // a walk that could not fire.
        assertTrue("an occurrence nothing places is concurrent with all",
                rule.concurrent(earlier, started, "s0"));
        assertFalse("and no ordering is invented for it either way",
                rule.ancestor(first, firstAt, third, thirdAt, "s0")
                        || rule.ancestor(third, thirdAt, first, firstAt,
                        "s0"));
        // Attestation: instrumented and symbolic in this session -- the seed
        // -- with no decision anywhere in it.
        assertTrue("a symbolic straight-line region is attested",
                rule.attested("s0", later));
    }

    // ------------------------------------------------------------------
    // 15. A version rests on the earlier versions of its own location.
    // ------------------------------------------------------------------

    /**
     * 11741's shape: the anchor reads the version the PUT loop produced,
     * and what the map LACKS at that version is what an earlier occurrence
     * removed from it, under a comparison against the clock it read.  No
     * row of the session joins the two -- the put loop published no read of
     * the map, and the version it wrote names nothing under it -- so a
     * closure that stops at the writer the read named declared no cell of
     * the removing occurrence's clock and stated "the map lacks the key" as
     * a bare fact of the recording.
     */
    @Test
    public void anEarlierVersionOfTheSameLocationIsReachedWithIt()
            throws Exception {
        LocationId keys = LocationId.of(LocationKind.MAP, "474", "-3");
        Composer.Composition chained = versionChain(
                folder.newFolder("version-chain").toPath(), keys);
        assertEquals("the path is admitted", 1, chained.paths().size());
        assertEquals("the removing occurrence's clock is a cell of the "
                        + "composition", Collections.singletonList(CLOCK),
                chained.clockCells());
        assertTrue("and its decision is a conjunct of the path, before the "
                        + "write the sweep reached it at: "
                        + fatalArm(chained),
                fatalArm(chained).contains(SmtNames.legalSymbols(
                        "(> " + CLOCK + " 300)")));

        // The same corpus with that earlier write on ANOTHER location: the
        // rule is about one object's own history, so a version of some
        // other cell is no reason the value this path read is what it is.
        Composer.Composition alone = versionChain(
                folder.newFolder("version-chain-elsewhere").toPath(),
                LocationId.of(LocationKind.MAP, "999", "-3"));
        assertEquals("the path is admitted either way", 1,
                alone.paths().size());
        assertTrue("no clock cell reaches a composition whose closure stops "
                        + "at the writer the read named",
                alone.clockCells().isEmpty());
        assertFalse("and no decision of that occurrence is in the path: "
                        + fatalArm(alone),
                fatalArm(alone).contains(SmtNames.legalSymbols(
                        "(> " + CLOCK + " 300)")));

        // R3b: AN ARM IS CLOSED LIKE A PATH.  The same corpus once more,
        // with the put loop EXPORTING what it read and the anchor
        // attaching it: the delivery rests on the map at the version the
        // loop read, that version rests on the removal an earlier
        // occurrence made under a comparison against the clock it read,
        // and none of that is a fact about the CONSUMER's path -- it is
        // what the producer had in hand.  Stated as a bare (pi, e) pair an
        // arm said WHAT was delivered and not why, and no conjunct of any
        // composed query named that clock.
        Path delivered = folder.newFolder("arm-closure").toPath();
        LocationId swept = LocationId.of(LocationKind.INSTANCE, "474", "8");
        Session run = new Session(delivered, "s0", false);
        run.activation(UPSTREAM);
        run.activation(PRODUCER);
        run.marker("false");
        run.clock("700");
        // A: the expiry decision, and then what the sweep it guards wrote.
        run.decision(UPSTREAM, "up#u15", "(> " + CLOCK + " 300)",
                CLOCK_ROOT, 700L);
        run.expression("EXPR.arm.a", constant("true"));
        run.write(Endpoint.of(UPSTREAM, "Manager#remove#22:WRITE",
                at("w#a", 0), 0), swept, 6L, "EXPR.arm.a");
        // B: the occurrence the anchor reads from.  It READ what A wrote
        // and exported it; the export names the read and nothing about the
        // occurrence behind it.
        run.expression("EXPR.arm.b",
                read("INSTANCE_FIELD", 474L, 8L, 6L, "Z"));
        run.read(Endpoint.of(PRODUCER, "Manager#addKeys#70:READ",
                        at("r#b", 0), 0), swept, 6L, "INSTANCE/474#8@v6",
                "Z", null);
        Endpoint port = Endpoint.of(PRODUCER, "PORT.keys",
                at("export#1", 0), 0);
        run.export(port, "EXPR.arm.b", 1L, "true");
        run.attach(Endpoint.of(ANCHOR, "PORT.keys", at("attach#1", 0), 0),
                "vh_keys", "true", port);
        run.target("vh_keys", false, true);
        run.write();

        Composer.Composition armed = compose(delivered, 2);
        assertEquals("the path is admitted: " + armed.gaps(), 1,
                armed.disjuncts().size());
        assertEquals("and the removing occurrence's clock is a cell of the "
                        + "composition", Collections.singletonList(CLOCK),
                armed.clockCells());
        String clocked = "";
        for (String line : armed.body().split("\n")) {
            if (line.contains("message_arm__")
                    && line.contains(SmtNames.legalSymbols(
                            "(> " + CLOCK + " 300)"))) {
                clocked = line;
            }
        }
        assertFalse("and its decision stands UNDER THE SELECTOR OF THE "
                        + "MESSAGE that carried the delivery, because it is "
                        + "a reason that delivery is what it is and not a "
                        + "fact of the consumer's path: " + armed.body(),
                clocked.isEmpty());
    }

    /**
     * One session: A removes a key under a clock and writes v5 of
     * {@code removed}, B writes v9 of the map, the anchor reads v9.
     */
    private Composer.Composition versionChain(Path iteration,
                                              LocationId removed)
            throws IOException {
        LocationId keys = LocationId.of(LocationKind.MAP, "474", "-3");
        Session session = new Session(iteration, "s0", false);
        session.activation(UPSTREAM);
        session.activation(PRODUCER);
        session.marker("false");
        session.clock("700");
        // A: the expiry decision, over the clock this occurrence read, and
        // then the removal it made -- the decision BEFORE the write, so it
        // is in the prefix the sweep reaches A at.
        session.decision(UPSTREAM, "up#u15", "(> " + CLOCK + " 300)",
                CLOCK_ROOT, 700L);
        session.expression("EXPR.chain.a", removal());
        session.write(Endpoint.of(UPSTREAM, "Manager#remove#22:WRITE",
                at("w#a", 0), 0), removed, 5L, "EXPR.chain.a");
        // B: the put loop, which states its own chain from a snapshot base
        // and names neither A's write nor the version under it.
        session.expression("EXPR.chain.b", relation("ASSOCIATIVE", "PUT",
                "java/util/HashMap", snapshot(), integer("I", 9L),
                integer("I", 7L)));
        session.write(Endpoint.of(PRODUCER, "Manager#addKeys#71:WRITE",
                at("w#b", 0), 0), keys, 9L, "EXPR.chain.b");
        // The anchor's read of the map, at the version B produced.
        session.read(Endpoint.of(ANCHOR, "Manager#retrieve#18:READ",
                        at("r#1", 0), 0), keys, 9L, "MAP/474#-3@v9",
                "java/util/HashMap", null);
        session.target(MARKER, false, true);
        session.write();
        return compose(iteration, 2);
    }

    /** The map as the recording states it before anything was put in. */
    private static JsonObject snapshot() {
        return relation("ASSOCIATIVE", "SNAPSHOT_BASE", "java/util/HashMap",
                relation("ASSOCIATIVE", "STATE", "java/util/HashMap",
                        symbol("M_L'java/util/HashMap'_474",
                                "java/util/HashMap")));
    }

    /** One removal from it, naming no event and no version under it. */
    private static JsonObject removal() {
        return relation("ASSOCIATIVE", "REMOVE", "java/util/HashMap",
                snapshot(), integer("I", 5L));
    }

    // ------------------------------------------------------------------
    // 16. A declared root binds a read by its DOMAIN, not by a value.
    // ------------------------------------------------------------------

    /**
     * The location the DataNode's clock cell is minted at, and the two
     * rows the runtime publishes for it.
     *
     * <p>Taken from hdfs-11741 campaign #6: {@code INSTANCE/216#24}, mint
     * version 1125, javaType {@code J}, and a reader of that very version
     * on the next seq.  The placeholder row states the SYMBOL and no
     * {@code concreteValue} at all -- deliberately, because a value there
     * is a pin and {@code ClaimPolicy#clocksNeeded} re-asks under that
     * same pin, so CLOCK_SKEW could never reach unsat.</p>
     */
    private static final LocationId CLOCK_CELL =
            LocationId.of(LocationKind.INSTANCE, "216", "24");
    private static final long CLOCK_MINT = 1125L;
    private static final String CLOCK_READ = "INSTANCE_FIELD/216#24@v1125";
    /** The instant the recording's own DataNode read. */
    private static final long INSTANT = 1789997450091L;
    /** A mint of the same shape whose symbol is NO root of the session. */
    private static final LocationId COUNTER_CELL =
            LocationId.of(LocationKind.INSTANCE, "22", "24");
    private static final String COUNTER_READ = "INSTANCE_FIELD/22#24@v174";

    @Test
    public void aDeclaredClockRootBindsTheReadOfTheVersionItMinted()
            throws Exception {
        Path iteration = folder.newFolder("clock-placeholder").toPath();
        clockMint(iteration, false);

        Composer.Composition bound = compose(iteration, 4);
        // The path is NOT refused.  Before this rule every one of
        // campaign #6's 116 anchor paths died here, on this one row.
        assertEquals("the path that reads the minted clock version is in "
                        + "the disjunction: " + bound.gaps(), 1,
                bound.disjuncts().size());
        assertFalse("and nothing about the clock symbol is refused: "
                        + bound.gaps(), named(bound.gaps(), CLOCK));

        // The READ is joined to the ROOT'S symbol -- one name, so the
        // domain this composition states lands on the cell the decision
        // compares.
        assertTrue("the read of the minted version is joined to the root's "
                        + "own symbol: " + bound.body(),
                bound.body().contains(SmtNames.legalSymbols(
                        "(= " + CLOCK_READ + " " + CLOCK + ")")));
        assertTrue("which the query declares: " + bound.body(),
                bound.body().contains(SmtNames.legalSymbols(
                        "(declare-const " + CLOCK + " Int)")));

        // And its FREEDOM is stated once, as a domain: floor at the
        // instant the run read, ceiling a window above it.  Never as a
        // pin to that instant -- a query that pins it cannot conclude a
        // skew was needed.
        assertEquals("the cell reaches the composition",
                Collections.singletonList(CLOCK), bound.clockCells());
        assertTrue("the clock is bounded by its domain: " + bound.body(),
                bound.body().contains(SmtNames.legalSymbols(
                        JavaPrimitiveSmtSemantics.clockDomain(CLOCK,
                                Long.toString(INSTANT),
                                JavaPrimitiveSmtSemantics.clockSkewCeiling(
                                        Long.toString(INSTANT),
                                        1_000_000L)))));
        assertFalse("and NOT pinned to the instant it read: " + bound.body(),
                bound.body().contains(SmtNames.legalSymbols(
                        "(= " + CLOCK + " " + INSTANT + ")")));

        // THE NEGATIVE, and it is the whole rule: what binds the read is
        // that a ROOT of this session mints the symbol.  The same corpus
        // with a second mint of the same shape, whose symbol no root
        // states and whose row states no value, is refused exactly as
        // before -- nothing here widens to "any unstated symbol".
        Path unrooted = folder.newFolder("unrooted-placeholder").toPath();
        clockMint(unrooted, true);

        Composer.Composition refused = compose(unrooted, 4);
        assertTrue("a placeholder naming no root of its session and stating "
                        + "no value is still refused, in the unchanged "
                        + "words: " + refused.gaps(),
                says(refused.gaps(), GapKind.UNSTATED_VALUE,
                        "the read row that states this version's symbol "
                                + "states no value for it, and no root of "
                                + "this session mints it, so nothing binds "
                                + "it"));
        assertTrue("by the name of the symbol nothing binds",
                named(refused.gaps(), MINTED));
        assertFalse("and never by the clock's, which its root binds",
                named(refused.gaps(), CLOCK));
        assertTrue("so the path is out of the disjunction",
                refused.disjuncts().isEmpty());
    }

    /**
     * One session that mints a declared CLOCK at a version and reads it.
     *
     * <p>{@code alsoUnrooted} adds a second mint of the same shape whose
     * symbol is no root of the session: the control for the rule.</p>
     */
    private void clockMint(Path iteration, boolean alsoUnrooted)
            throws IOException {
        Session session = new Session(iteration, "s0", false);
        session.clock(Long.toString(INSTANT));
        // The mint row: the version it created, its symbol, and NO value.
        session.placeholder(Endpoint.of(ANCHOR,
                        "INSTANCE_FIELD/216#24#PLACEHOLDER#0:READ",
                        at("now#1", 0), 0),
                CLOCK_CELL, CLOCK_MINT, CLOCK_MINT, CLOCK, "J", null);
        // And the reader of that version: no write of the location at it.
        // Its row states the instant it returned, as every scalar read does,
        // and that value must not pin a root's version: the mint binds it.
        session.read(Endpoint.of(ANCHOR,
                        "INSTANCE_FIELD/216#24#READ_FROM#0:READ",
                        at("now#2", 0), 0),
                CLOCK_CELL, CLOCK_MINT, CLOCK_READ, "J",
                Long.toString(INSTANT));
        if (alsoUnrooted) {
            session.placeholder(Endpoint.of(ANCHOR,
                            "INSTANCE_FIELD/22#24#PLACEHOLDER#0:READ",
                            at("count#1", 0), 0),
                    COUNTER_CELL, 174L, 174L, MINTED, "I", null);
            session.read(Endpoint.of(ANCHOR,
                            "INSTANCE_FIELD/22#24#READ_FROM#0:READ",
                            at("count#2", 0), 0),
                    COUNTER_CELL, 174L, COUNTER_READ, "I", null);
        }
        // The expiry comparison the case turns on, as the runtime
        // publishes it: an expression whose leaf is a ReadFrom of the
        // version the mint created, and the reading of the root the
        // decision took -- which is what puts the cell in
        // `Composer.clocks`.
        session.expression("EXPR.00000000000000c1", binary(">",
                read("INSTANCE_FIELD", 216L, 24L, CLOCK_MINT, "J"),
                integer("J", 300L)));
        session.decision(ANCHOR, "removeExpiredKeys#u7",
                "EXPR.00000000000000c1", CLOCK_ROOT, INSTANT);
        // And one more over a LEAF naming what the read row returned: a
        // read symbol is a declared symbol of its session, so a leaf may
        // name it, and a join no term asks about is dropped -- this is
        // what makes the binding visible in the query.
        session.expression("EXPR.00000000000000c2", binary(">",
                symbol(CLOCK_READ, "J"), integer("J", 0L)));
        session.decision(ANCHOR, "removeExpiredKeys#u9",
                "EXPR.00000000000000c2");
        if (alsoUnrooted) {
            // phi rests on the unrooted read, so its refusal is the path's.
            session.expression("EXPR.00000000000000c3", binary(">",
                    symbol(COUNTER_READ, "I"), integer("I", 0L)));
            session.target("EXPR.00000000000000c3", false, true);
        } else {
            session.target("true", false, true);
        }
        session.write();
    }

    /**
     * A node that reads the wall clock and a monotonic one orders each on
     * its own: the second wall reading is no earlier than the first, and
     * neither is ordered against the monotonic one (hdfs-11741 v78: wall
     * 1.79e12 "before" monotonic 4.5e9 made all 165 paths false).
     */
    @Test
    public void aNodeReadingTwoClocksOrdersEachClockOnItsOwn()
            throws Exception {
        Path iteration = folder.newFolder("two-clocks").toPath();
        Session session = new Session(iteration, "s0", false);
        String[][] cells = {{"CLOCK.wall.1", "M_J_wall_1", "1790500000000"},
                {"CLOCK.mono", "M_J_mono", "4549240012"},
                {"CLOCK.wall.2", "M_J_wall_2", "1790500000900"}};
        StringBuilder phi = new StringBuilder("(and");
        for (String[] cell : cells) {
            session.roots.add(RootMintRow.of("s0", ++session.seq, ANCHOR,
                    cell[0], cell[1], RootKind.CLOCK, cell[2], null, null,
                    true, 1_000_000L));
            phi.append(" (> ").append(cell[1]).append(" 0)");
        }
        session.target(phi.append(")").toString(), false, true);
        session.write();

        String body = compose(iteration, 4).body();
        assertTrue("one clock's readings keep their order: " + body,
                body.contains("(<= M_J_wall_1 M_J_wall_2)"));
        assertFalse("and no clock is ordered against another",
                body.contains("(<= M_J_wall_1 M_J_mono)")
                        || body.contains("(<= M_J_mono M_J_wall_2)"));
    }

    // ------------------------------------------------------------------
    // 17. A name a term BINDS is not a name nothing declares.
    // ------------------------------------------------------------------

    /**
     * The associative size model, as {@code ContainerSmtCodec} writes it
     * for a map a key was removed from.
     */
    private static String sizeModel(String previous, String body) {
        return "(let ((previous_size " + previous + ")) (ite (> "
                + previous + " 0) " + body + " (- previous_size 1)))";
    }

    @Test
    public void aLetBoundNameIsNotFree() throws Exception {
        // The real shape: one binder, and its name used three times.
        String model = sizeModel(SERIAL, "previous_size");
        assertEquals("the size model binds exactly previous_size",
                Collections.singletonList("previous_size"),
                new ArrayList<String>(SmtNames.letBound(model)));
        // Nesting, in the order the binders appear.
        assertEquals("a nested let binds both, outermost first",
                Arrays.asList("outer", "inner"),
                new ArrayList<String>(SmtNames.letBound(
                        "(let ((outer (+ " + SERIAL + " 1))) (let "
                                + "((inner (- outer 2))) (+ outer "
                                + "inner)))")));
        // A term with no let binds nothing -- so nothing it names is
        // withheld from the caller's complaint.
        assertTrue("a term with no let binds nothing",
                SmtNames.letBound("(> (+ previous_size 1) 0)").isEmpty());

        // And the caller.  A path whose decision carries the size model
        // is admitted: previous_size is the term's own binder, not a
        // symbol the recording failed to declare.  Campaign #6 refused
        // every anchor path here, 41440 times, with "this term names
        // symbols nothing declares: [previous_size, previous_size,
        // previous_size]".
        Path iteration = folder.newFolder("let-bound").toPath();
        letCorpus(iteration, "previous_size");
        Composer.Composition bound = compose(iteration, 4);
        assertEquals("the path carrying the size model is in the "
                        + "disjunction: " + bound.gaps(), 1,
                bound.disjuncts().size());
        assertFalse("and previous_size is named by no refusal: "
                        + bound.gaps(),
                says(bound.gaps(), GapKind.UNSTATED_VALUE, "previous_size"));

        // The same term with ONE name the let does not bind: still
        // refused, and by that name alone.  Declining to report anything
        // at all once a let is seen would have lost this.
        Path free = folder.newFolder("let-and-free").toPath();
        letCorpus(free, "no_row_states_this");
        Composer.Composition refused = compose(free, 4);
        assertTrue("a name the let did NOT bind is still reported: "
                        + refused.gaps(),
                says(refused.gaps(), GapKind.UNSTATED_VALUE,
                        "this term names symbols nothing declares: "
                                + "[no_row_states_this]"));
        assertTrue("so the path is out of the disjunction",
                refused.disjuncts().isEmpty());
    }

    /**
     * Nor is a theory operator the lowering writes: every stage reads a name
     * outside {@link SmtNames#BUILTIN} as undeclared, and COMPOSE refuses
     * the path by it (solr-adhoc q13-22 dropped 36 conjuncts on str.substr
     * and str.indexof).  The Java String methods and a container emptied
     * and read are lowered here as a recording states them; the primitive
     * operators are spelled by their one writer.
     */
    @Test
    public void everyOperatorTheLoweringWritesIsBuiltin() {
        Map<String, VmTermLowering.Sort> declared =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        declared.put("s", VmTermLowering.Sort.STRING);
        declared.put("n", VmTermLowering.Sort.INT);
        declared.put("c", VmTermLowering.Sort.INT);
        SmtLowering lowering = new SmtLowering(declared);
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        JsonObject s = vmLeaf("SymbolExpression", "s", "java/lang/String");
        JsonObject n = vmLeaf("SymbolExpression", "n", "I");
        JsonObject c = vmLeaf("SymbolExpression", "c", "C");
        JsonObject emptied = relation("INDEXED", "SNAPSHOT_BASE",
                relation("INDEXED", "STATE", symbol(
                        "M_L'java/util/ArrayList'_3", "java/util/ArrayList")));
        // putAll(m) into an empty map, then a get of what m put.
        JsonObject empty = relation("ASSOCIATIVE", "SNAPSHOT_BASE", null);
        JsonObject all = relation("ASSOCIATIVE", "PUT_ALL", empty,
                relation("ASSOCIATIVE", "PUT", empty, integer("J", 5L), n));
        List<String> texts = new ArrayList<String>();
        for (JsonObject expression : Arrays.asList(
                vmString("substring", s, n), vmString("charAt", s, n),
                vmString("indexOf", s, c), vmString("lastIndexOf", s, s),
                vmString("toString", c),
                binary("==", relation("INDEXED", "READ", "I",
                        relation("INDEXED", "INSERT", emptied,
                                integer("I", 0L), n), integer("I", 0L)),
                        n),
                binary("==", relation("ASSOCIATIVE", "READ", "I", all,
                        integer("J", 5L)), n))) {
            VmTermLowering.Term term =
                    lowering.dispatch(expression, null, "test");
            texts.add(term.text);
            texts.add(term.precondition);
        }
        texts.addAll(lowering.end());
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        for (SmtLowering.Declaration declaration : lowering.reachedBy(texts)) {
            texts.add(declaration.body);
        }
        texts.addAll(Arrays.asList(
                JavaPrimitiveSmtSemantics.floatingComparison("<=", "x", "y"),
                JavaPrimitiveSmtSemantics.floatingArithmetic("/", "x", "y"),
                JavaPrimitiveSmtSemantics.floatingNegate("x"),
                JavaPrimitiveSmtSemantics.floatingCompareResult("x", "y",
                        true),
                JavaPrimitiveSmtSemantics.primitiveCast("x", "D", "J"),
                JavaPrimitiveSmtSemantics.primitiveCast("x", "I", "F"),
                JavaPrimitiveSmtSemantics.bitwise("&", "x", "y",
                        JavaPrimitiveSmtSemantics.IntegralWidth.JAVA_INT),
                JavaPrimitiveSmtSemantics.shift(">>>", "x", "y",
                        JavaPrimitiveSmtSemantics.IntegralWidth.JAVA_LONG),
                JavaPrimitiveSmtSemantics.complement("x",
                        JavaPrimitiveSmtSemantics.IntegralWidth.JAVA_INT)));
        for (String text : texts) {
            Set<String> free = SmtNames.symbols(text,
                    new LinkedHashSet<String>());
            free.removeAll(SmtNames.letBound(text));
            free.removeAll(SmtNames.preambleNames());
            free.removeAll(Arrays.asList("x", "y"));
            free.removeIf(lowering::defined);
            assertTrue(free + " in " + text, free.isEmpty());
        }
    }

    /** One session whose decision carries the size model over {@code body}. */
    private void letCorpus(Path iteration, String body) throws IOException {
        Session session = new Session(iteration, "s0", false);
        session.serial("5", "+0", "+3");
        session.decision(ANCHOR, "removeExpiredKeys#u7",
                "(= " + SERIAL + " " + sizeModel(SERIAL, body) + ")");
        session.target("true", false, true);
        session.write();
    }

    // ------------------------------------------------------------------
    // 16. A message's arms are the runs whose world is compatible with
    //     the path's (PIPELINE §8).
    // ------------------------------------------------------------------

    @Test
    public void aMessageBindsToEveryCompatibleWorld() throws Exception {
        Path iteration = folder.newFolder("worlds").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.id",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.id",
                at("attach#1", 0), 0);
        // Four runs, all attesting their own delivery: the seed (no
        // flip), one held to flip A, one to flip B, and one to B that
        // inherited A.
        for (String[] each : new String[][]{{"s0", "10"}, {"s1", "20"},
                {"s2", "30"}, {"s3", "40"}}) {
            Session session = new Session(iteration, each[0],
                    !"s0".equals(each[0]));
            session.activation(PRODUCER);
            session.marker("false");
            session.expression("EXPR.v1.id", integer("I",
                    Long.parseLong(each[1])));
            session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
            session.export(producer, "EXPR.v1.id", 1L, each[1]);
            session.attach(consumer, "vh", "I", each[1], producer);
            session.target("true", false, true);
            session.write();
        }
        Map<String, String> none = Collections.emptyMap();
        obligation(iteration, "s1", none, "a#u1",
                Collections.<String>emptyList());
        obligation(iteration, "s2", none, "b#u1",
                Collections.<String>emptyList());
        obligation(iteration, "s3", none, "b#u1",
                Collections.singletonList("a#u1"));

        Composer.Composition composition = compose(iteration, 4);
        assertEquals(4, composition.disjuncts().size());
        Map<String, String> ofPath = new LinkedHashMap<String, String>();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            ofPath.put(ordinal(disjunct.selector()),
                    disjunct.path().sessionId);
        }
        Map<String, Set<String>> armsOf =
                new LinkedHashMap<String, Set<String>>();
        for (String selector : composition.armSelectors()) {
            String path = ofPath.get(ordinal(selector));
            if (!armsOf.containsKey(path)) {
                armsOf.put(path, new LinkedHashSet<String>());
            }
            armsOf.get(path).add(composition.arm(selector).sessionId());
        }
        // One flip set contains the other: the seed's empty world is
        // compatible with every run and every run with it; A and B are
        // incomparable; {A, B} contains both.
        assertEquals("the seed's path takes any run's delivery",
                new LinkedHashSet<String>(Arrays.asList("s0", "s1", "s2",
                        "s3")), armsOf.get("s0"));
        assertEquals("a path under A never takes a delivery made under B "
                        + "alone", new LinkedHashSet<String>(
                        Arrays.asList("s0", "s1", "s3")), armsOf.get("s1"));
        assertEquals(new LinkedHashSet<String>(
                Arrays.asList("s0", "s2", "s3")), armsOf.get("s2"));
        assertEquals("and the path under both takes every delivery",
                new LinkedHashSet<String>(Arrays.asList("s0", "s1", "s2",
                        "s3")), armsOf.get("s3"));
        for (Family family : composition.families()) {
            assertEquals("the manifest states the arms the last path "
                    + "built: " + family, 4, family.arms().size());
        }
    }

    /**
     * ONE MESSAGE, TWO LEAVES, under one correlation id -- the shape an
     * array payload has: every position is its own handoff leaf -- binds to
     * a run attested at every leaf, and to no other.
     *
     * <p>A run that instrumented the head's occurrence and ran the TAIL's
     * concretely states at the tail what was delivered and not why -- R3c'
     * does not admit it, and the path it owns is answered by the run that
     * says why.  A run that exported a SHORTER response -- one leaf,
     * attested -- is no option either: R3c' is unchanged by this ruling, a
     * run that never sent the second leaf is no option for a message that
     * has one.</p>
     */
    @Test
    public void aRunThatRanALeafConcretelyIsNoOptionForTheMessage()
            throws Exception {
        // Each row a corpus: {run, value it delivered, how it ran the
        // message}.  s0 attests both leaves in every one.
        String[][][] corpora = {
                {{"s0", "10", "both"}, {"s1", "20", "concrete"}},
                {{"s0", "10", "both"}, {"s1", "30", "shorter"},
                        {"s2", "20", "concrete"}}};
        for (int row = 0; row < corpora.length; row++) {
            Path iteration = folder.newFolder("leaves-" + row).toPath();
            boolean shorter = false;
            for (String[] run : corpora[row]) {
                leafRun(iteration, run[0], run[1], run[2]);
                shorter |= "shorter".equals(run[2]);
            }
            Composer.Composition composition = compose(iteration, 4);
            assertEquals("row " + row + ": every run's path is in the "
                            + "disjunction", corpora[row].length,
                    composition.disjuncts().size());
            for (String selector : composition.armSelectors()) {
                ComposedFamilies.ArmChoice choice = composition.arm(selector);
                // A shorter run's own one-leaf arrival is a message of its
                // own, and that run is eligible to have sent it.
                if (shorter && choice.attachEndpointIds().size() < 2) continue;
                assertEquals("row " + row + ": s0 is the only run attested "
                        + "at every leaf: " + selector, "s0",
                        choice.sessionId());
            }
        }
    }

    /**
     * One run of the two-leaf message: {@code both} leaves attested, the
     * tail's occurrence run {@code concrete}ly, or a {@code shorter}
     * response carrying the head alone.
     */
    private void leafRun(Path iteration, String sessionId, String value,
                         String shape) throws IOException {
        Endpoint head = Endpoint.of(PRODUCER, "PORT.keys",
                at("export#1", 0), 0);
        Endpoint tail = Endpoint.of(UPSTREAM, "PORT.keys",
                at("export#2", 0), 0);
        Endpoint first = Endpoint.of(ANCHOR, "PORT.keys",
                at("attach#1", 0), 0);
        Endpoint second = Endpoint.of(ANCHOR, "PORT.keys",
                at("attach#2", 0), 0);
        boolean both = "both".equals(shape);
        boolean shorter = "shorter".equals(shape);
        Session session = new Session(iteration, sessionId,
                !"s0".equals(sessionId));
        session.activation(PRODUCER);
        if (both) {
            session.activation(UPSTREAM);
        } else if (!shorter) {
            session.activation(UPSTREAM, "thread#" + UPSTREAM.regionId(),
                    true, false);
        }
        session.marker("false");
        session.expression("EXPR.v1.id", integer("I",
                Long.parseLong(value)));
        session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                + MARKER + "))");
        if (both) {
            session.decision(UPSTREAM, "up#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
        }
        session.export(head, "EXPR.v1.id", 1L, value);
        if (!shorter) session.export(tail, "EXPR.v1.id", 2L, value);
        session.attach(first, "vh1", "I", value, head, "corr-m");
        if (!shorter) {
            session.attach(second, "vh2", "I", value, tail, "corr-m");
        }
        session.target("true", false, true);
        session.write();
    }

    /**
     * A PATH'S FAMILIES ARE ALL OR NOTHING.  s1 received message m, which
     * s0 and s2 could also have sent, and message n, which only s3 states
     * why it sent -- in a world (flip b) no path under s1's (flip a) takes a
     * delivery from.  So s1's path is refused at n, after m's family was
     * closed, and s2's path is composed at the ordinal s1 left free: m's
     * family is named there again, once, and nothing of s1's stays
     * (hdfs-17899-bug1 r1: 18 names defined twice, and z3 answered the query
     * with an error).
     */
    @Test
    public void aPathRefusedAtItsFamiliesLeavesNothingInTheQuery()
            throws Exception {
        Path iteration = folder.newFolder("refused-families").toPath();
        Endpoint sent = Endpoint.of(PRODUCER, "PORT.m", at("export#1", 0), 0);
        Endpoint other = Endpoint.of(UPSTREAM, "PORT.n", at("export#2", 0), 0);
        for (String id : new String[] {"s0", "s1", "s2", "s3"}) {
            Session session = new Session(iteration, id, !"s0".equals(id));
            session.activation(PRODUCER);
            session.marker("false");
            session.expression("EXPR.v1.id", integer("I", 10L));
            session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
            session.export(sent, "EXPR.v1.id", 1L, "10");
            session.attach(Endpoint.of(ANCHOR, "PORT.m", at("attach#1", 0),
                    0), "vh1", "I", "10", sent, "corr-m");
            if ("s1".equals(id) || "s3".equals(id)) {
                // s1 ran n's sender concretely; s3 states why it sent.
                boolean why = "s3".equals(id);
                session.activation(UPSTREAM, "thread#" + UPSTREAM.regionId(),
                        true, why);
                if (why) {
                    session.decision(UPSTREAM, "up#u1", "(or " + MARKER
                            + " (not " + MARKER + "))");
                }
                session.export(other, "EXPR.v1.id", 2L, "10");
                session.attach(Endpoint.of(ANCHOR, "PORT.n",
                        at("attach#2", 0), 0), "vh2", "I", "10", other,
                        "corr-n");
            }
            if (!"s3".equals(id)) session.target("true", false, true);
            session.write();
        }
        Map<String, String> none = Collections.emptyMap();
        obligation(iteration, "s1", none, "a#u1",
                Collections.<String>emptyList());
        obligation(iteration, "s3", none, "b#u1",
                Collections.<String>emptyList());

        Composer.Composition composition = compose(iteration, 4);
        Set<String> ordinals = new LinkedHashSet<String>();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            assertFalse("s1 is refused at n", "s1".equals(
                    disjunct.path().sessionId));
            ordinals.add(ordinal(disjunct.selector()));
        }
        assertEquals("s0 and s2 are paths", 2, ordinals.size());
        assertTrue("s1 is refused where no run of a compatible world sent n",
                says(composition.gaps(), GapKind.UNPRODUCIBLE_ANSWER,
                        "compatible with this path's"));
        for (String selector : composition.armSelectors()) {
            assertTrue("every arm is a disjunct's: " + selector,
                    ordinals.contains(ordinal(selector)));
        }
        Set<String> named = new LinkedHashSet<String>();
        for (String line : composition.body().split("\n")) {
            int at = line.indexOf(":named ");
            if (at < 0) continue;
            assertTrue("named once: " + line, named.add(
                    line.substring(at).split("[ )]")[1]));
        }
        assertTrue("z3 answers the query: " + named, solver().ask(
                composition.query(composition.valuations().get(0)
                        .assertions()), null, false).decided());
    }

    /**
     * One reference, one rule: lowered alone (the flip solver's and the
     * closure planner's entry) it states where it is defined, as it does
     * when a published term names it.  A node two expressions share is one
     * construct, lowered once: refused, it is one fresh name, and each
     * expression lowered alone is refused for it, its text still naming it.
     */
    @Test
    public void aLoweredReferenceStatesWhereItIsDefined() throws Exception {
        Path iteration = folder.newFolder("defined").toPath();
        Session seed = new Session(iteration, "s0", false);
        seed.activation(PRODUCER);
        seed.expression("EXPR.v1.quotient", binary("/",
                symbol("dividend", "I"), symbol("divisor", "I")));
        JsonObject unmodeled = new JsonObject();
        unmodeled.addProperty("_type", "UnmodeledExpression");
        unmodeled.addProperty("_java_type", "I");
        seed.expression("EXPR.00000000000001e1", binary("<", unmodeled,
                symbol("dividend", "I")));
        seed.expression("EXPR.00000000000001e2", binary(">", unmodeled,
                symbol("divisor", "I")));
        // A read joins the write it observed only where the VM saw every
        // writer of the location.
        seed.expression("EXPR.00000000000001e3", integer("I", 41L));
        seed.write(Endpoint.of(ANCHOR, "Saver#store#3:WRITE",
                at("store#1", 0), 0), LocationId.of(LocationKind.INSTANCE,
                "7", "3"), 5L, "EXPR.00000000000001e3");
        JsonObject whole = read("INSTANCE", 7L, 3L, 5L, "I");
        JsonObject partial = read("INSTANCE", 7L, 3L, 5L, "I");
        partial.addProperty(VmRows.WRITER_SET_COMPLETE, false);
        // Unless the VM verified the read itself: it loaded the word the
        // version stored.
        JsonObject exact = read("INSTANCE", 7L, 3L, 5L, "I");
        exact.addProperty(VmRows.WRITER_SET_COMPLETE, false);
        exact.addProperty(VmRows.OBSERVED_EXACT, true);
        seed.expression("EXPR.00000000000001e4", whole);
        seed.expression("EXPR.00000000000001e5", partial);
        seed.expression("EXPR.00000000000001e6", exact);
        seed.write();
        SmtLowering lowering = Corpus.read(iteration, null).lowering("s0");
        SmtLowering.Lowered quotient = lowering.lower("EXPR.v1.quotient");
        assertTrue("the quotient lowers: " + quotient, quotient.ok());
        List<String> facts =
                lowering.facts(Collections.singletonList(quotient.text()));
        assertTrue("and the JVM divided, so the divisor was not zero: "
                + facts, facts.contains("(not (= divisor 0))"));
        Set<String> free = new LinkedHashSet<String>();
        for (String reference : Arrays.asList("EXPR.00000000000001e1",
                "EXPR.00000000000001e2")) {
            SmtLowering.Lowered lowered = lowering.lower(reference);
            assertFalse(reference + " is refused", lowered.ok());
            for (String name : SmtNames.names(lowered.text())) {
                if (name.startsWith("unsupported__")) free.add(name);
            }
        }
        assertEquals("one construct, one name: " + free, 1, free.size());
        assertEquals("a read of a location every writer of which the VM saw"
                + " is the value written", "41",
                lowering.lower("EXPR.00000000000001e4").text());
        assertFalse("one whose writer set is incomplete is not joined to the"
                + " version it names", lowering.lower("EXPR.00000000000001e5")
                .text().contains("41"));
        assertEquals("an exact one is, whatever the writer set", "41",
                lowering.lower("EXPR.00000000000001e6").text());
    }

    /** The ordinal one selector was made under. */
    private static String ordinal(String selector) {
        String[] parts = selector.split("__");
        return parts.length < 2 ? "" : parts[1];
    }

    // ------------------------------------------------------------------
    // Fixture.
    // ------------------------------------------------------------------

    /**
     * Constraint independence: a condition sharing no variable with phi or
     * a root is left out, so one the composer cannot state -- a substring
     * of a block file's name, read from a tracked location -- does not
     * refuse the path (f4 visible-gs, sender-gs); the same condition over
     * the location phi reads still does.  Java null is no variable: every
     * null check spells it alike, and sharing it kept 80 of the 145
     * conditions and reads of a SOLR-18406 path.  What a family binds is
     * kept as phi is: a condition over an anchor handoff phi never names
     * still refuses (C1 review M2).
     */
    @Test
    public void aConditionPhiDoesNotRestOnDoesNotRefuseThePath()
            throws Exception {
        for (String shares : new String[]{"nothing", "location", "null",
                "handoff"}) {
            boolean shared = "location".equals(shares)
                    || "handoff".equals(shares);
            boolean nulls = "null".equals(shares);
            Path iteration = folder.newFolder("independence-" + shares)
                    .toPath();
            Session session = new Session(iteration, "s0", false);
            session.serial("3", "0", "8");
            session.expression("EXPR.00000000000000a3", integer("I", 1001L));
            session.write(Endpoint.of(ANCHOR, "Replica#set#1:WRITE",
                            at("stamp#1", 0), 0),
                    LocationId.of(LocationKind.INSTANCE, "58", "40"), 158L,
                    "EXPR.00000000000000a3");
            session.expression("EXPR.00000000000000a1", binary("<",
                    read("INSTANCE_FIELD", 58L, 40L, 158L, "I"),
                    symbol(SERIAL, "I")));
            JsonObject name = new JsonObject();
            name.addProperty("_type", "OpStrExpression");
            name.addProperty("_name", "substring");
            name.addProperty("_is_not", false);
            JsonArray parameters = new JsonArray();
            parameters.add("location".equals(shares)
                    ? read("INSTANCE_FIELD", 58L, 40L, 158L, "I")
                    : read("INSTANCE_FIELD", 59L, 32L, 157L,
                    "Ljava/lang/String;"));
            parameters.add(integer("I", 4L));
            name.add("_param_list", parameters);
            JsonObject named = binary("==", name, name);
            session.expression("EXPR.00000000000000a2", nulls
                    ? binary("&&", named, binary("!=", symbol(
                            "M_L'org/apache/Bar'_2", "org/apache/Bar"),
                    vmNull())) : "handoff".equals(shares)
                    ? binary("&&", named, binary("!=", symbol("vH_heard",
                    "I"), integer("I", 0L))) : named);
            if ("handoff".equals(shares)) {
                session.answered(Endpoint.of(ANCHOR, "Port#recv#1:ATTACH",
                        at("recv#1", 0), 0), "vH_heard", "I", "5", null);
            }
            session.decision(ANCHOR, "file#u3", true,
                    "EXPR.00000000000000a2");
            session.expression("EXPR.00000000000000a4", binary("!=",
                    symbol("M_L'org/apache/Foo'_1", "org/apache/Foo"),
                    vmNull()));
            session.target(nulls ? "(and EXPR.00000000000000a1 "
                    + "EXPR.00000000000000a4)" : "EXPR.00000000000000a1",
                    false, true);
            session.write();

            Composer.Composition composition = compose(iteration, 4);
            assertEquals(shared ? "a condition phi or a family rests on "
                            + "still refuses: " + shares
                            : "a condition phi does not rest on is left out: "
                            + shares,
                    shared ? 0 : 1, composition.disjuncts().size());
        }
    }

    /**
     * THE ONE BINDING RULE ({@code SmtLowering#bind}), at the row and at the
     * node alike: JOIN, MINT, PIN, REFUSE, a refused join giving way only
     * where nothing it rests on can move.  One case per row:
     * <ul>
     *   <li>pin: the write refuses over nothing that moves, and the row
     *       states its value: the pin binds the read, and what the dropped
     *       join raised (its recorded reading, its cut) went with it;</li>
     *   <li>unstated: the same with no value stated: the path is refused,
     *       the join's refusal beside the read's;</li>
     *   <li>H1: the write is a call no lowering models over R, a declared
     *       root (the review's {@code parseInt(valueOf(R))} is R now,
     *       {@link #aMethodReturnIsItsCall}): pinned, phi {@code x != R}
     *       would move R past a constant, so no pin stands and there is no
     *       path to move it in;</li>
     *   <li>H2a: the node's own projection lowers where the write refused:
     *       phi reads the projection, never the pinned constant;</li>
     *   <li>H2b: the write joins and a STATE family may re-pair the read,
     *       while the node's projection refuses: phi gets no literal the
     *       family cannot move, so the path is refused.</li>
     * </ul>
     */
    @Test
    public void theOneBindingRule() throws Exception {
        for (String name : new String[]{"pin", "unstated", "H1", "H2a",
                "H2b"}) {
            Path iteration = folder.newFolder("bind-" + name).toPath();
            OccurrenceAddress reader = occurrence("case/nn0", "REGION.commit",
                    CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                    frame("Namesystem#commit#12", 0));
            OccurrenceAddress first = occurrence("case/nn0", "REGION.tick",
                    CausalContext.of(Role.of("TICK_A"), "", 1),
                    frame("TickA#run#3", 0));
            LocationId stamp = LocationId.of(LocationKind.INSTANCE, "10",
                    "value");
            String key = SmtLowering.locationKey(stamp);
            String symbol = key + "@v2@s0";
            Session session = new Session(iteration, "s0", false);
            session.occurrence = reader;
            session.activation(reader);
            session.activation(first);
            session.serial("3", "0", "8");
            // Refused over nothing that moves (an undeclared leaf here, a
            // call no lowering models in EXPLORE's too), with what the run
            // read of it: a side condition of the join.
            JsonObject unmodeled = new JsonObject();
            unmodeled.addProperty("_type", "MethodExpression");
            unmodeled.addProperty("_name", "org/apache/Foo bar");
            unmodeled.add("_param_list", new JsonArray());
            unmodeled.add("_res_exp", integer("I", 7L));
            JsonObject refused = binary("+", symbol(NO_ROW, "I"), unmodeled);
            refused.add(VmRows.RECORDED_READING, integer("I", 4242L));
            JsonObject parsed = new JsonObject();
            parsed.addProperty("_type", "MethodExpression");
            parsed.addProperty("_name", "org/apache/Foo parse");
            JsonArray arguments = new JsonArray();
            arguments.add(vmString("toString", symbol(SERIAL, "I")));
            parsed.add("_param_list", arguments);
            parsed.add("_res_exp", symbol("M_I_return7", "I"));
            session.expression("EXPR.00000000000000b1", "H1".equals(name)
                    ? parsed : "H2b".equals(name) ? integer("I", 2L)
                    : refused);
            session.write(Endpoint.of(first, "TickA#set#4:WRITE",
                    at("w#1", 0), 0), stamp, 2L, "EXPR.00000000000000b1");
            if ("H2b".equals(name)) {
                // A concurrent writer: the read's STATE family re-pairs it.
                OccurrenceAddress second = occurrence("case/nn0",
                        "REGION.tock", CausalContext.of(Role.of("TICK_B"),
                                "", 1), frame("TickB#run#3", 0));
                session.activation(second);
                session.expression("EXPR.00000000000000b2",
                        integer("I", 1L));
                session.write(Endpoint.of(second, "TickB#set#4:WRITE",
                        at("w#2", 0), 0), stamp, 1L, "EXPR.00000000000000b2");
            }
            session.read(Endpoint.of(reader, "Block#getStamp#29:READ",
                            at("r#1", 0), 0), stamp, 2L, symbol, "I",
                    "unstated".equals(name) ? null : "H1".equals(name) ? "3"
                            : "H2b".equals(name) ? "2" : "1001");
            JsonObject node = read("INSTANCE_FIELD", stamp.owner(), "value",
                    2L, "I");
            if ("H2a".equals(name) || "H2b".equals(name)) {
                // The node's own projection of the version it observed.
                node.getAsJsonObject("observedVersion").add("expression",
                        "H2a".equals(name) ? integer("I", 1001L)
                                : binary("-", symbol(NO_ROW, "I"),
                                integer("I", 1L)));
            }
            if (!"unstated".equals(name) && !"H1".equals(name)) {
                // What it returned: a literal no family moves.
                node.add("concreteValue", integer("I",
                        "H2b".equals(name) ? 2L : 1001L));
            }
            session.expression("EXPR.00000000000000b3", binary(
                    "H1".equals(name) ? "!=" : "<", node,
                    symbol(SERIAL, "I")));
            session.target("EXPR.00000000000000b3", false, true);
            session.write();

            Composer.Composition composition = compose(iteration, reader, 4, StaticScopeMap.empty());
            List<GapRow> gaps = composition.gaps();
            String arm = fatalArm(composition);
            switch (name) {
                case "pin":
                    assertEquals(name + ": the pin binds the read", 1,
                            composition.disjuncts().size());
                    assertTrue(name + ": phi reads the pinned symbol: " + arm,
                            arm.contains(SmtNames.legalSymbols("(< " + symbol
                                    + " " + SERIAL + ")"))
                                    && arm.contains(SmtNames.legalSymbols(
                                    "(= " + symbol + " 1001)")));
                    assertFalse(name + ": the dropped join's recorded "
                                    + "reading binds nothing (M3)",
                            composition.body().contains("4242"));
                    assertFalse(name + ": and its cut is no gap (L3)",
                            named(gaps, "UndeclaredFreeSymbol:" + NO_ROW));
                    // EXPLORE: the node's value stands in for the join, no
                    // flip is built over it, and the closure still reaches
                    // what the join lowered (M1).
                    SmtLowering.Lowered explored = Corpus.read(iteration,
                            null).lowering("s0").lower(
                            "EXPR.00000000000000b3");
                    assertFalse(name + ": no flip over the pin: " + explored,
                            explored.ok());
                    assertTrue(name + ": the join is still reached: "
                                    + explored.reach(),
                            explored.reach().size() == 2
                                    && explored.reach().get(0).contains(
                                    "1001") && explored.reach().get(1)
                                    .contains(NO_ROW));
                    break;
                case "unstated":
                    assertEquals(name + ": nothing binds the read", 0,
                            composition.disjuncts().size());
                    assertTrue(name + ": the write's refusal is the path's, "
                                    + "beside the read's own",
                            says(gaps, GapKind.UNSTATED_VALUE,
                                    "did not lower")
                                    && named(gaps, "PROPAGATION_CUT:"
                                    + "UndeclaredFreeSymbol:" + NO_ROW));
                    break;
                case "H1":
                    assertEquals(name + ": no pin stands for a value a "
                                    + "root computed", 0,
                            composition.disjuncts().size());
                    assertTrue(name + ": and the refusal says why",
                            says(gaps, GapKind.UNSTATED_VALUE, "can move"));
                    assertEquals(name + ": so no witness moves the root",
                            ClaimKind.NO_SUPPORTED_WITNESS,
                            ClaimPolicy.decide(composition, solver())
                                    .claim().kind());
                    break;
                case "H2a":
                    assertEquals(name + ": the projection binds the node",
                            1, composition.disjuncts().size());
                    assertTrue(name + ": phi reads the projection that "
                                    + "lowered, not the pin: " + arm,
                            arm.contains(SmtNames.legalSymbols("(< 1001 "
                                    + SERIAL + ")"))
                                    && !arm.contains(SmtNames.legalSymbols(
                                    symbol)));
                    break;
                default:
                    assertEquals(name + ": a read a family re-pairs is no "
                                    + "literal", 0,
                            composition.disjuncts().size());
                    assertTrue(name + ": refused by name",
                            named(gaps, "JoinOverMovingValue:" + key
                                    + "@2"));
            }
        }
    }

    /**
     * A method-return symbol (the VM's result of a call it does not model)
     * is its CALL, which the node states (VM f14).  One case per row:
     * <ul>
     *   <li>parse: {@code Long.parseLong} of a String is its decimal
     *       reading, a relation and no pin;</li>
     *   <li>round-trip: {@code parseInt(toString(R))}, R a declared root, is
     *       R itself (a WIRE-CODEC §6.2 identity: no String theory), so phi
     *       {@code x != R} holds under no valuation: no moved-root witness
     *       (the pin C1 made gave one);</li>
     *   <li>pinned: a callee the lowering does not know, over nothing that
     *       moves, is pinned by a NAMED assertion an unsat core shows;</li>
     *   <li>moving: the same over R refuses: a pin would carry a moved R
     *       through the call as a constant;</li>
     *   <li>no-call: a node stating no call (a VM before f14) refuses.</li>
     * </ul>
     */
    @Test
    public void aMethodReturnIsItsCall() throws Exception {
        for (String name : new String[]{"parse", "round-trip", "pinned",
                "moving", "no-call"}) {
            Path iteration = folder.newFolder("return-" + name).toPath();
            Session session = new Session(iteration, "s0", false);
            session.serial("3", "0", "8");
            boolean integer = "round-trip".equals(name);
            JsonObject returned = symbol(integer ? "M_I_return4" : RETURNED,
                    integer ? "I" : "J");
            returned.add("concreteValue", integer ? integer("I", 3L)
                    : integer("J", 2L));
            if (!"no-call".equals(name)) {
                JsonObject call = new JsonObject();
                call.addProperty("holder", "parse".equals(name)
                        ? "java/lang/Long" : integer ? "java/lang/Integer"
                        : "org/apache/solr/Params");
                call.addProperty("name", "parse".equals(name) ? "parseLong"
                        : integer ? "parseInt" : "getLong");
                JsonArray arguments = new JsonArray();
                arguments.add("parse".equals(name) || "pinned".equals(name)
                        ? vmLeaf("ConStringSymbolExp", "Y_L'String'_2",
                        "java/lang/String")
                        : "moving".equals(name) ? symbol(SERIAL, "I")
                        : vmString("toString", symbol(SERIAL, "I")));
                call.add("arguments", arguments);
                returned.add("call", call);
            }
            session.expression("EXPR.00000000000000c1", integer
                    ? binary("!=", returned, symbol(SERIAL, "I"))
                    : binary("<", binary("--", returned,
                    integer("J", 3L)), integer("I", 0L)));
            session.target("EXPR.00000000000000c1", false, true);
            session.write();

            Composer.Composition composition = compose(iteration, 4);
            List<GapRow> gaps = composition.gaps();
            String body = composition.body();
            boolean composed = !"moving".equals(name)
                    && !"no-call".equals(name);
            assertEquals(name + ": composed", composed ? 1 : 0,
                    composition.disjuncts().size());
            if ("parse".equals(name) || integer) {
                assertEquals(name + ": the call is its relation, and a parse "
                                + "of a rendering the value rendered: " + body,
                        !integer, body.contains("str.to_int"));
                assertFalse(name + ": no pin",
                        named(gaps, "MethodReturnPinned:" + RETURNED));
            }
            if (integer) {
                ClaimPolicy.Decision decision = ClaimPolicy.decide(
                        composition, solver());
                for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
                    assertTrue(name + ": phi holds under no valuation: "
                                    + outcome,
                            outcome.answer().unsat());
                }
                assertEquals(name + ": so no witness moves the root past "
                                + "it", ClaimKind.NO_SUPPORTED_WITNESS,
                        decision.claim().kind());
            }
            if ("pinned".equals(name)) {
                assertTrue(name + ": pinned by a named assertion: " + body,
                        body.contains(":named pinned_returned__")
                                && named(gaps, "MethodReturnPinned:"
                                + RETURNED));
            }
            if ("moving".equals(name)) {
                assertTrue(name + ": refused by name",
                        named(gaps, "MethodReturnOverMovingArgument:"
                                + RETURNED));
            }
            if ("no-call".equals(name)) {
                assertTrue(name + ": refused by name",
                        named(gaps, "MethodReturnCallUnstated:"
                                + RETURNED));
            }
        }
    }

    /**
     * A map removal under a SYMBOLIC guard is decided, and renumbers the
     * view only when it fires.  An array-valued ite over a lambda branch is
     * "incomplete (theory array)" for z3 4.14: hdfs-11741 v79's witness
     * paths (the balancer's removeExpiredKeys over a clock, then puts) were
     * undecided until the guard went inside the lambdas.
     */
    @Test
    public void aGuardedRemovalIsDecided() {
        Z3 solver = solver();
        String empty = "(mkAssocState 0 ((as const (Array Value Bool)) false)"
                + " ((as const (Array Value Value)) (VRef nullRef))"
                + " ((as const (Array Int Value)) (VRef nullRef))"
                + " ((as const (Array Value Int)) (- 1)))";
        String query = String.join("\n", VmTermLowering.preamble())
                + "\n(declare-const x Int)"
                + "\n(define-fun s () AssocState (assoc_remove_if"
                + " (assoc_put (assoc_put " + empty
                + " (VInt 1) (VInt 10)) (VInt 2) (VInt 20))"
                + " (VInt 1) (< x 5)))"
                + "\n(define-fun grown () AssocState"
                + " (assoc_put s (VInt 3) (VInt 30)))\n";
        // What the state shows, and the guard side that contradicts it.
        String[][] cases = {
            {"(= (assoc_key_at grown 0) (VInt 2))", "(>= x 5)"},
            {"(= (assoc_size grown) 3)", "(< x 5)"},
        };
        for (String[] shown : cases) {
            Z3.Answer holds = solver.ask(query + "(assert " + shown[0] + ")",
                    Collections.<String>emptyList(), false);
            assertTrue("decided with the guard free: " + shown[0] + " "
                    + holds.status(), holds.decided() && holds.sat());
            Z3.Answer refuted = solver.ask(query + "(assert " + shown[0]
                    + ")\n(assert " + shown[1] + ")",
                    Collections.<String>emptyList(), false);
            assertTrue("and only on its own side: " + shown[1] + " "
                    + refuted.status(), refuted.decided() && !refuted.sat());
        }
    }

    /**
     * The Strings a file name carries lower as Java computes them: a path's
     * parent is its prefix up to the last separator (File.getParent) and is
     * undefined -- Java throws -- without one; a long names itself in decimal
     * (blk_<id>_<gs>.meta).  finalize-gs a8 lost every path to these.
     */
    @Test
    public void aPathsParentAndALongsNameLowerAsJavaComputesThem() {
        Z3 solver = solver();
        Map<String, VmTermLowering.Sort> declared =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        declared.put("s", VmTermLowering.Sort.STRING);
        declared.put("n", VmTermLowering.Sort.INT);
        JsonObject path = vmLeaf("SymbolExpression", "s", "java/lang/String");
        SmtLowering lowering = new SmtLowering(declared);
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        VmTermLowering.Term parent = lowering.dispatch(vmString("substring",
                path, vmLeaf("ConstExpr", "C_I_0", "I"), vmString(
                        "lastIndexOf", path, vmLeaf("ConstExpr", "C_I_47",
                                "I"))), VmTermLowering.Sort.STRING, "test");
        VmTermLowering.Term name = lowering.dispatch(vmString("toString",
                vmLeaf("SymbolExpression", "n", "J")), VmTermLowering.Sort.STRING, "test");
        List<String> conditions = lowering.end();
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        List<String> texts = new ArrayList<String>(conditions);
        texts.addAll(Arrays.asList(parent.text, parent.precondition,
                name.text));
        StringBuilder query = new StringBuilder(
                String.join("\n", lowering.preambleLines()));
        for (SmtLowering.Declaration declaration : lowering.reachedBy(texts)) {
            query.append('\n').append(declaration.render());
        }
        for (String fact : lowering.facts(texts)) {
            query.append("\n(assert ").append(fact).append(')');
        }
        for (String condition : conditions) {
            query.append("\n(assert ").append(condition).append(')');
        }
        query.append("\n(define-fun parent () String ").append(parent.text)
                .append(")\n(define-fun name () String ").append(name.text)
                .append(")\n(assert ").append(parent.precondition).append(')');
        String[][] cases = {
            {"(and (= s \"a/b/c\") (= parent \"a/b\"))", "sat"},
            {"(and (= s \"a/b/c\") (= parent \"a\"))", "unsat"},
            {"(= s \"abc\")", "unsat"},
            {"(and (= n (- 12)) (= name \"-12\"))", "sat"},
            {"(and (= n (- 12)) (= name \"12\"))", "unsat"},
        };
        for (String[] asked : cases) {
            Z3.Answer answer = solver.ask(query + "\n(assert " + asked[0]
                    + ")", Collections.<String>emptyList(), false);
            assertTrue(asked[0] + " " + answer.status(), answer.decided()
                    && answer.sat() == "sat".equals(asked[1]));
        }
    }

    /**
     * A recorded expression is walked once per node and to its end: a map
     * whose every put names the map below twice is 2^64 paths as a tree, and
     * one put 100000 deep passed the depth caps (512 for a term's symbols
     * and for the container subterms a query declares) or overflowed a
     * recursion.  The lowering itself recurses, on the engine's stack
     * (java.sh -Xss512m), so it runs on one here; the walks do not.
     */
    @Test(timeout = 300_000L)
    public void aDeepSharedChainIsWalkedToItsEnd() throws Exception {
        String deepest = "M_I_deepest";
        Map<String, VmTermLowering.Sort> declared =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        declared.put(deepest, VmTermLowering.Sort.INT);
        declared.put("M_I_key", VmTermLowering.Sort.INT);
        for (int depth : new int[]{64, 100_000}) {
            boolean doubled = depth == 64;
            JsonObject key = symbol("M_I_key", "I");
            JsonObject map = relation("ASSOCIATIVE", "PUT",
                    "java/util/HashMap", snapshot(), integer("I", 0L),
                    symbol(deepest, "I"));
            for (int level = 1; level < depth; level++) {
                map = relation("ASSOCIATIVE", "PUT", "java/util/HashMap", map,
                        integer("I", level), doubled ? relation("ASSOCIATIVE",
                                "READ", "I", map, key)
                                : integer("I", level));
            }
            JsonObject read = relation("ASSOCIATIVE", "READ", "I", map, key);
            Set<String> symbols = new LinkedHashSet<String>();
            edu.uva.liftlab.graphchecker.smt.Arms.symbolsIn(read, symbols);
            assertTrue(depth + ": " + symbols, symbols.contains(deepest));
            assertFalse(depth + ": walked whole, no marker",
                    VmRows.truncated(read));

            SmtLowering lowering = new SmtLowering(declared);
            lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
            String[] text = new String[1];
            Thread engine = new Thread(null, () -> text[0] = lowering.dispatch(
                    read, VmTermLowering.Sort.INT, "deep").text,
                    "engine-stack", 512L << 20);
            engine.start();
            engine.join();
            lowering.end();
            assertTrue(depth + ": the map is one named subterm per put",
                    text[0].contains("container_dag__"));
            assertTrue(depth + ": the query reaches the deepest put's symbol",
                    lowering.reachedSymbols(text[0],
                            new LinkedHashSet<String>(), null)
                            .contains(deepest));
            List<String> names = new ArrayList<String>();
            for (SmtLowering.Declaration declaration : lowering.reachedBy(
                    Collections.singletonList(text[0]))) {
                names.add(declaration.name);
            }
            assertTrue(depth + ": and declares it", names.contains(deepest));
            assertTrue(depth + ": after every put above it",
                    names.size() > depth);
        }
    }

    private static JsonObject vmLeaf(String type, String exp,
                                     String javaType) {
        JsonObject leaf = new JsonObject();
        leaf.addProperty("_type", type);
        leaf.addProperty("_exp", exp);
        leaf.addProperty("_java_type", javaType);
        return leaf;
    }

    private static JsonObject vmString(String name, JsonObject... params) {
        JsonObject operation = new JsonObject();
        operation.addProperty("_type", "OpStrExpression");
        operation.addProperty("_name", name);
        operation.addProperty("_is_not", false);
        JsonArray list = new JsonArray();
        for (JsonObject param : params) list.add(param);
        operation.add("_param_list", list);
        return operation;
    }

    private Composer.Composition compose(Path iteration, int maxValuations)
            throws IOException {
        return compose(iteration, ANCHOR, maxValuations,
                StaticScopeMap.empty());
    }

    /** One anchor's composition under the epoch's static facts. */
    private static Composer.Composition compose(Path iteration,
                                                OccurrenceAddress anchor,
                                                int maxValuations,
                                                StaticScopeMap scope)
            throws IOException {
        return Composer.compose(Corpus.read(iteration, null), anchor,
                Collections.<String,
                        edu.uva.liftlab.graphchecker.contract.RootDomain>
                        emptyMap(), maxValuations, scope);
    }

    private Z3 solver() {
        Path z3 = z3();
        Assume.assumeTrue("z3 is not on this machine",
                Files.isExecutable(z3) || !z3.isAbsolute());
        return new Z3(z3, 30000L);
    }

    private static Path z3() {
        Path z3 = Paths.get("/usr/local/bin/z3");
        return Files.isExecutable(z3) ? z3 : Paths.get("z3");
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
     * (PIPELINE §8, {@code Arms.namedOwner}).</p>
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
        return fieldRead(ownerClass, offset, "L", owner, concreteValue);
    }

    /** The same, of a field of this Java type. */
    private static JsonObject fieldRead(String ownerClass, long offset,
                                        String javaType, JsonObject owner,
                                        JsonObject concreteValue) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "FieldAccessExpression");
        node.addProperty("_java_type", javaType);
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
        private final List<GapRow> gaps = new ArrayList<GapRow>();
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<String, JsonObject>();

        Session(Path iteration, String id, boolean explored) {
            this.iteration = iteration;
            this.id = id;
            this.explored = explored;
            this.settled = ObligationResult.of("OBL." + id,
                    Verdict.ADMITTED, id, "the fixture's replay took the "
                            + "arm the obligation asked for");
            activation(ANCHOR);
            this.seq = 0L;
        }

        /** What this replay states it settled; ignored for a SEED. */
        private ObligationResult settled;

        /** The same session, whose replay refused its own obligation. */
        void refused(String detail) {
            settled = ObligationResult.of("OBL." + id,
                    Verdict.NOT_ADMITTED, id, detail);
        }

        /**
         * One more activation, on a thread of its own.
         *
         * <p>Each occurrence gets its own thread unless a test says
         * otherwise: sharing one would order every pair of them, which is
         * true of a thread and not of this fixture.</p>
         */
        void activation(OccurrenceAddress at) {
            activation(at, "thread#" + at.regionId(), explored);
        }

        void activation(OccurrenceAddress at, String threadKey,
                        boolean focused) {
            activation(at, threadKey, focused, true);
        }

        void activation(OccurrenceAddress at, String threadKey,
                        boolean focused, boolean instrumented) {
            activations.add(ActivationRow.of(id, at,
                    explored ? "task-flip" : "task-seed", focused,
                    instrumented, threadKey));
        }

        /** One more activation, placing the sender its anchor names. */
        void activation(OccurrenceAddress at, Endpoint anchorProducer) {
            activations.add(ActivationRow.of(id, at,
                    explored ? "task-flip" : "task-seed", explored, true,
                    "thread#" + at.regionId(), anchorProducer));
        }

        void marker(String recorded) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, MARKER_ROOT, MARKER,
                    RootKind.MARKER, recorded, null, null, true, 0L));
        }

        /**
         * A declared CLOCK: the instant it read; the domain is the
         * composer's ({@code Composer.clocks}).
         *
         * <p>A clock cell is not a root a valuation moves, and what names
         * it in a composed query is the SYMBOL the session minted, which
         * is what a decision's reading has to be joined to.</p>
         */
        void clock(String recorded) {
            roots.add(RootMintRow.of(id, ++seq, ANCHOR, CLOCK_ROOT, CLOCK,
                    RootKind.CLOCK, recorded, null, null, true, 1_000_000L));
        }

        /** One decision, and the clock cells its predicate read. */
        void decision(OccurrenceAddress at, String site, String term,
                      String clockRoot, long reading) {
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, true, term,
                    Collections.singletonMap(clockRoot, reading)));
        }

        /** A declared counter, with the window the CASE states around it. */
        void serial(String recorded, String min, String max) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, SERIAL_ROOT,
                    SERIAL, RootKind.INTEGRAL, recorded, min, max, true, 0L));
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
            attach(endpoint, symbol, javaType, arrival, producer,
                    "corr-" + symbol);
        }

        /**
         * The same, on a NAMED message: one correlation id over several
         * leaves is one arrival, which is the unit a family's selector
         * stands for.
         */
        void attach(Endpoint endpoint, String symbol, String javaType,
                    String arrival, Endpoint producer, String correlation) {
            attaches.add(AttachRow.of(id, ++seq, endpoint, symbol, javaType,
                    arrival, false, null, producer, correlation,
                    producer == null ? "" : "HANDLE"));
        }

        /**
         * An attach an OBLIGATION answered: the mint was planted.
         *
         * <p>The one place a handoff read is still bound to a literal, and
         * the literal is the wave's assignment and not the arrival: what
         * the replay was told to receive is a fact about the question that
         * was asked, so the sort the row states has to place it
         * ({@code Composer.bind}).</p>
         */
        void answered(Endpoint endpoint, String symbol, String javaType,
                      String value, Endpoint producer) {
            attaches.add(AttachRow.of(id, ++seq, endpoint, symbol, javaType,
                    value, true, value, producer, "corr-" + symbol,
                    producer == null ? "" : "HANDLE"));
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

        /** The row a VM-refused attach inside {@code at} files. */
        void refusedAttach(OccurrenceAddress at) {
            gaps.add(GapRow.of(id, GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    at.render(), "the VM refused the attach of handle 7 at "
                            + "PORT.id (HANDOFF_FOREIGN_HANDLE)"));
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
            RowCodec.writeAll(dir.gaps(), gaps, RowCodec::writeGap);
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
            // The fixture STATES the role, as a campaign's own session
            // manifest does: an exploration replay is FOCUSED under the
            // obligation it ran, the recording is SEED.
            RowCodec.writeManifest(dir.manifest(), SessionManifest.of(id,
                    explored ? SessionManifest.Role.FOCUSED
                            : SessionManifest.Role.SEED,
                    explored ? Collections.singletonList("OBL." + id)
                            : Collections.<String>emptyList()));
            // And the VERDICT, which the replay owns: a focused session
            // that states none settled nothing, and the composition asks
            // the session's own row rather than the wave's copy of it.
            RowCodec.writeAll(dir.obligations(), explored
                            ? Collections.singletonList(settled)
                            : Collections.<ObligationResult>emptyList(),
                    RowCodec::writeObligationResult);
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
        session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
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
