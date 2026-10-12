package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.contract.Clock;
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
import edu.uva.liftlab.graphchecker.contract.RootCategory;
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
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
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
    /** A configuration flag's root and the symbol its mint names. */
    private static final String CONFIG_ROOT = "CONFIG:k.flag";
    private static final String CONFIG = "config_k";
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
        obligation(iteration, sessionId, roots, site, inherited,
                Collections.<String, String>emptyMap());
    }

    /** The same, its world planting {@code pairings} (reader -> writer). */
    private static void obligation(Path iteration, String sessionId,
                                   Map<String, String> roots, String site,
                                   List<String> inherited,
                                   Map<String, String> pairings)
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
        com.google.gson.JsonObject paired = new com.google.gson.JsonObject();
        for (Map.Entry<String, String> pairing : pairings.entrySet()) {
            paired.addProperty(pairing.getKey(), pairing.getValue());
        }
        focus.add("pairings", paired);
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

    /**
     * A model CONFIRM refuted ({@code refuted_claims.jsonl}: a false
     * positive) is excluded from every later composition of the iteration,
     * its arms matched by their digests at whatever path ordinal the claim
     * spelled them ({@code Refutations#atPath}): the claim over it is another
     * model, or none, and an UNSAT names it as what it rests on.  One whose
     * path the corpus no longer composes states nothing.
     */
    @Test
    public void anExcludedModelIsNoModelOfTheNextComposition()
            throws Exception {
        // the path the model names, the arms' path ordinal moved
        Object[][] table = {
                {"elsewhere", false},
                {"claimed", false},
                {"claimed", true},
        };
        for (Object[] row : table) {
            Path iteration = folder.newFolder("excluded-" + row[0] + "-"
                    + row[1]).toPath();
            Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                    at("export#1", 0), 0);
            Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                    at("attach#1", 0), 0);
            session(iteration, "s0", false, "false", producer, consumer,
                    "vh", "false", null, true, false, "EXPR.v1.marker");
            session(iteration, "s1", true, "true", producer, consumer,
                    "vh", "true", null, true, true, "EXPR.v1.marker");
            ClaimPolicy.Decision first = ClaimPolicy.decide(
                    compose(iteration, 8), solver());
            assertEquals(ClaimKind.MARKER_FLIPPED, first.claim().kind());
            ClaimPolicy.Outcome claimed = first.outcomes().get(
                    first.claim().valuationOrdinal());
            boolean excluded = "claimed".equals(row[0]);
            JsonObject model = new JsonObject();
            model.addProperty("pathId", excluded
                    ? claimed.selected().path().pathId : "elsewhere");
            JsonArray arms = new JsonArray();
            for (String arm : claimed.selectedArms().keySet()) {
                arms.add((Boolean) row[1]
                        ? Refutations.atPath(arm, "41") : arm);
            }
            assertTrue("the claim chose arms", arms.size() > 0);
            model.add("arms", arms);
            JsonObject assignment = new JsonObject();
            for (Map.Entry<String, String> root
                    : claimed.valuation().assignment().entrySet()) {
                assignment.addProperty(root.getKey(), root.getValue());
            }
            model.add("assignment", assignment);
            JsonObject excludedRow = new JsonObject();
            excludedRow.add("model", model);
            excludedRow.addProperty("reason",
                    "the run published no target row");
            RowCodec.writeJsonl(iteration.resolve(Refutations.FILE),
                    Collections.singletonList(excludedRow));
            String detail = Arrays.toString(row);
            Composer.Composition next = compose(iteration, 8);
            String name = "refuted_claim__0";
            assertEquals(detail, excluded, next.body().contains(name));
            assertEquals(detail, excluded, named(next.gaps(),
                    GapKind.CLAIM_REFUTED));
            ClaimPolicy.Decision again = ClaimPolicy.decide(next, solver());
            assertEquals(detail, excluded ? ClaimKind.NO_SUPPORTED_WITNESS
                    : ClaimKind.MARKER_FLIPPED, again.claim().kind());
            // An excluded model is no part of the run itself: a path it
            // excludes does not contradict its own run, and the UNSAT names
            // what it rests on.
            assertFalse(detail + ": " + again.claim().gaps(),
                    named(again.claim().gaps(),
                            GapKind.PATH_SELF_CONTRADICTORY));
            if (!excluded) continue;
            JsonObject claim = ComposeMain.campaignClaim(next, again);
            assertEquals(detail + ": " + claim, "UNSAT_CLOSED",
                    claim.get("claim").getAsString());
            assertEquals(detail, name, claim.getAsJsonArray(
                    "restsOnRefutations").get(0).getAsJsonObject()
                    .get("name").getAsString());
        }
    }

    /**
     * A VERDICT IS JUDGED ON THE PATHS IT RESTS ON (PIPELINE §8, the claim;
     * compose.Cone, cone.py): a SAT on the path it claims -- another path
     * whose fatal condition rests on a value no attested producer made is
     * stated (unboundOffWitness) and gates nothing -- an UNSAT on every path:
     * one such path leaves no verdict, its open link named (openChain) with
     * the producer GROW would plan.
     */
    @Test
    public void aClaimIsJudgedOnThePathsItRestsOn() throws Exception {
        Path iteration = folder.newFolder("judged-on-its-paths").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        String vh = "M_Z_field_HOFF.key";
        session(iteration, "s0", false, "false", producer, consumer, vh,
                "false", null, true, false, "EXPR.v1.marker");
        session(iteration, "s1", true, "true", producer, consumer, vh,
                "true", null, true, true, "EXPR.v1.marker");
        // A replay paired with another export of the producer, which no
        // session attests (it ran concretely): its arrival is held.
        Endpoint unattested = Endpoint.of(PRODUCER, "PORT.key",
                at("export#2", 0), 0);
        session(iteration, "s2", true, "false", unattested, consumer, vh,
                "false", null, false, false, "EXPR.v1.marker");
        Composer.Composition composition = compose(iteration, 8);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        JsonObject sat = ComposeMain.campaignClaim(composition, decision);
        assertEquals(sat.toString(), "SAT_CANDIDATE",
                sat.get("claim").getAsString());
        assertFalse("the witness's own chain is closed: " + sat,
                sat.has("openChain"));
        JsonArray off = sat.getAsJsonArray("unboundOffWitness");
        assertEquals("s2's open link is stated: " + sat, 1, off.size());
        assertEquals(vh, off.get(0).getAsJsonObject().get("symbol")
                .getAsString());

        // The witness's model refuted: the formula is unsat, and rests on
        // s2's path too, whose fatal condition names the held arrival.
        ClaimPolicy.Outcome claimed = decision.outcomes().get(
                decision.claim().valuationOrdinal());
        JsonObject model = new JsonObject();
        model.addProperty("pathId", claimed.selected().path().pathId);
        JsonArray arms = new JsonArray();
        for (String arm : claimed.selectedArms().keySet()) arms.add(arm);
        model.add("arms", arms);
        JsonObject assignment = new JsonObject();
        for (Map.Entry<String, String> root
                : claimed.valuation().assignment().entrySet()) {
            assignment.addProperty(root.getKey(), root.getValue());
        }
        model.add("assignment", assignment);
        JsonObject refuted = new JsonObject();
        refuted.add("model", model);
        refuted.addProperty("reason", "the replay took the healthy arm");
        RowCodec.writeJsonl(iteration.resolve("refuted_claims.jsonl"),
                Collections.singletonList(refuted));
        Composer.Composition next = compose(iteration, 8);
        ClaimPolicy.Decision again = ClaimPolicy.decide(next, solver());
        assertEquals(ClaimKind.NO_SUPPORTED_WITNESS, again.claim().kind());
        JsonObject unsat = ComposeMain.campaignClaim(next, again);
        assertEquals(unsat.toString(), "RUN_DEFECT",
                unsat.get("claim").getAsString());
        JsonObject link = unsat.getAsJsonArray("openChain").get(0)
                .getAsJsonObject();
        assertEquals(vh, link.get("symbol").getAsString());
        assertEquals("the producer GROW would plan", PRODUCER.render(),
                link.get("producer").getAsString());
    }

    /**
     * WITHIN A RANK, ITS OWN RUN FIRST: of the moved-root witnesses, one
     * whose selected session already ran the model -- observed the fatal on
     * the selected path, took only its own pairings, ran the moved root at
     * the model's value (explore.Moved#ranBy, the test CONFIRM's
     * realizedBy confirms it by) -- is claimed before an earlier
     * valuation's that only the composition joins (hdfs-adhoc-10 SL1: a
     * fault first in the root order claimed through a re-paired arm, the
     * SYNC fault its own session had run thirteen valuations behind).  With
     * no such witness, the valuations' order stands.
     */
    @Test
    public void aWitnessItsOwnSessionRanIsClaimedFirst() throws Exception {
        String other = "marker_o";
        String otherRoot = "ROOT.OTHER";
        // its own session observed the fatal? -> the root the claim moves
        Object[][] table = {{true, MARKER_ROOT}, {false, otherRoot}};
        for (Object[] row : table) {
            boolean observed = (Boolean) row[0];
            Path iteration = folder.newFolder("own-run-" + observed)
                    .toPath();
            for (boolean explored : new boolean[]{false, true}) {
                Session session = new Session(iteration,
                        explored ? "s1" : "s0", explored);
                // The other fault first: the first single move.
                session.roots.add(RootMintRow.of(session.id, ++session.seq,
                        PRODUCER, otherRoot, other, RootKind.MARKER,
                        RootCategory.FAULT, "false", null, null, true, null,
                        0L));
                session.marker(explored ? "true" : "false");
                // The recording's path reaches the fatal with the other
                // fault; the explored one's, which ran the marker, with it.
                session.target(explored ? MARKER : other,
                        explored && observed, true);
                session.write();
            }
            obligation(iteration, "s1",
                    Collections.singletonMap(MARKER_ROOT, "true"));
            Composer.Composition composition = compose(iteration, 8);
            String detail = Arrays.toString(row) + ": "
                    + composition.valuations();
            assertEquals(detail, Collections.singleton(otherRoot),
                    composition.valuations().get(1).moved().keySet());
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            assertEquals(detail + " " + decision.claim().gaps(),
                    ClaimKind.MARKER_FLIPPED, decision.claim().kind());
            assertEquals(detail, Collections.singleton(row[1]),
                    decision.claim().movedRoots().keySet());
        }
    }

    /**
     * A refuted claim excludes its clocks' REGION, not their instants: the
     * jump it made, by any amount the same way, with every other cell
     * running on.  An instant alone excluded one point, and the next model
     * sat a tick beside it.
     */
    @Test
    public void aRefutedClockClaimExcludesItsJumpNotItsInstant()
            throws Exception {
        Path iteration = folder.newFolder("refuted-clock").toPath();
        Session skewed = new Session(iteration, "s0", false);
        skewed.clock("700");
        skewed.decision(ANCHOR, "anchor#u1", "(or (> " + CLOCK + " 1000) "
                + "(not (> " + CLOCK + " 1000)))", CLOCK_ROOT, 700L);
        skewed.target("(> " + CLOCK + " 1000)", false, true);
        skewed.write();
        ClaimPolicy.Decision first = ClaimPolicy.decide(
                compose(iteration, 4), solver());
        assertEquals(ClaimKind.CLOCK_SKEW, first.claim().kind());
        ClaimPolicy.Outcome claimed = first.outcomes().get(
                first.claim().valuationOrdinal());
        JsonObject model = new JsonObject();
        model.addProperty("pathId", claimed.selected().path().pathId);
        JsonArray arms = new JsonArray();
        for (String arm : claimed.selectedArms().keySet()) arms.add(arm);
        model.add("arms", arms);
        JsonObject moved = new JsonObject();
        for (Map.Entry<String, String> cell
                : first.claim().movedRoots().entrySet()) {
            moved.addProperty(cell.getKey(), cell.getValue());
        }
        model.add("moved", moved);
        JsonObject row = new JsonObject();
        row.add("model", model);
        row.addProperty("reason", "the run took the healthy arm");
        RowCodec.writeJsonl(iteration.resolve("refuted_claims.jsonl"),
                Collections.singletonList(row));
        Composer.Composition next = compose(iteration, 4);
        assertTrue(next.body(), next.body().contains("refuted_claim__0"));
        ClaimPolicy.Decision again = ClaimPolicy.decide(next, solver());
        assertEquals("every later instant is the jump CONFIRM refuted",
                "unsat", again.formula().status());
        assertEquals(ClaimKind.NO_SUPPORTED_WITNESS, again.claim().kind());
        // That UNSAT rests on the refutation: the formula's core names it
        // (asked for whenever a refutation is asserted), restsOnRefutations.
        List<JsonObject> rests = next.restsOn(again.formula().core());
        assertEquals(again.formula().core().toString(), 1, rests.size());
        assertEquals("refuted_claim__0", rests.get(0).get("name")
                .getAsString());
        assertEquals(claimed.selected().path().pathId, rests.get(0)
                .get("pathId").getAsString());
    }

    // ------------------------------------------------------------------
    // 2. Two producers on one port are two interactions, two families.
    // ------------------------------------------------------------------

    /**
     * A guard that read a decoded store version rests on it (IDENTITY §7.2):
     * the path's restsOn names the STORE location of each store read of its
     * closure before the cutoff, which no term names, so CONFIRM holds the
     * read to the version the session read; a store read past the cutoff
     * rests nothing.
     */
    @Test
    public void aStoreVersionAGuardReadIsWhatThePathRestsOn()
            throws Exception {
        Path iteration = folder.newFolder("store-rests").toPath();
        LocationId state = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/collections/t/state.json");
        LocationId aliases = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/aliases.json");
        Session session = new Session(iteration, "s0", false);
        session.activation(PRODUCER);
        session.marker("true");
        session.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        session.write(Endpoint.of(PRODUCER,
                "SOLR_ZK#WRITE:.collections.t.state.json", at("w#1", 0), 0),
                state, 3L, "");
        session.read(Endpoint.of(ANCHOR, "Router#route#4:READ",
                at("r#1", 0), 0), state, 3L, "S_state3", "[B", null);
        session.decision(ANCHOR, "Router#route#u5", MARKER);
        session.target(MARKER, false, true);
        session.read(Endpoint.of(ANCHOR, "Router#after#9:READ",
                at("r#2", 0), 0), aliases, 1L, "S_aliases1", "[B", null);
        session.write();

        Set<String> rests = compose(iteration, 2).disjuncts().get(0)
                .restsOn();
        assertTrue(rests.toString(),
                rests.contains(SmtLowering.locationKey(state)));
        assertFalse(rests.toString(),
                rests.contains(SmtLowering.locationKey(aliases)));
    }

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
        skeleton.write(Files.createDirectories(
                unadmitted.resolve("obligations-0000")));

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
        // WIRE read the rule is stronger and earlier -- a read no attested
        // arm delivers is held at the value it received (Composer#arrival),
        // so nothing inside its producer reaches the formula -- and the
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
        assertEquals("the move is satisfiable and names no mechanism: the "
                        + "formula's claim alone, CONFIRM's to judge",
                ClaimKind.FORMULA_SAT, decision.claim().kind());
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

        // ONE ARRIVAL RULE AT EVERY DEPTH (PIPELINE §8).  The same chain,
        // and the upstream node ran concretely: no session attests the
        // producer of what the middle node was handed.  The arm is not
        // refused for it (hdfs-11741 PS1-PS3: the SASL sender's arms read
        // the expiry dates of a refresh no session instrumented, and their
        // refusal took the key id's binding with them): the handed value is
        // HELD inside the arm at what its row received, named with the arm.
        Path concrete = folder.newFolder("nested-concrete").toPath();
        Session ran = new Session(concrete, "s0", false);
        ran.activation(PRODUCER);
        ran.activation(UPSTREAM, "thread#up", false, false);
        ran.marker("false");
        ran.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
        ran.expression("EXPR.v1.forward", symbol("vh_up", "Z"));
        ran.export(upstream, "EXPR.v1.marker", 1L, "false");
        ran.attach(forwarded, "vh_up", "false", upstream);
        ran.decision(PRODUCER, "nn#u1", "(or vh_up (not vh_up))");
        ran.export(producer, "EXPR.v1.forward", 2L, "false");
        ran.attach(consumer, "vh", "false", producer);
        ran.target("vh", false, true);
        ran.write();
        Composer.Composition held = compose(concrete, 4);
        assertEquals("the path stands: " + held.gaps(), 1,
                held.disjuncts().size());
        assertEquals("on the anchor's family alone", 1,
                held.families().size());
        String hold = "(= vh_up false)";
        String inArm = "";
        for (String line : held.body().split("\n")) {
            assertFalse("the hold is no part of the path's own fatal",
                    line.contains(":named path_fatal__")
                            && line.contains(hold));
            int arm = line.indexOf("(=> message_arm__");
            if (line.contains(":named message_family__") && arm >= 0
                    && line.indexOf(hold, arm) > arm) {
                inArm = line.substring(arm + 4, line.indexOf(' ', arm + 4));
            }
        }
        assertTrue("the handed value is held inside the arm's case: "
                + held.body(), inArm.startsWith("message_arm__"));
        boolean named = false;
        for (Composer.Concrete row : held.concrete()) {
            named |= "HELD".equals(row.kind) && "vh_up".equals(row.subject)
                    && inArm.equals(row.arm);
        }
        assertTrue("and named HELD with that arm: " + held.concrete(),
                named);

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

    /**
     * A session with two target rows at the anchor is two paths, of one
     * path id.  The seed's are asked one at a time
     * (ClaimPolicy#seedDisjunctUnsat): asserted together, two selectors
     * contradict the partition and read "unsat" whatever the roots, and
     * named by their path they name one label twice, which z3 refuses.
     * (A phi of {@code false} is no path at all, invariant 9: the unsat
     * paths state a fatal condition no world satisfies.)
     */
    @Test
    public void theSeedsPathsAreAskedEachAlone() throws Exception {
        Z3 solver = solver();
        String never = "EXPR.0000000000000aa1";
        for (Object[] row : new Object[][]{
                {"true", false},    // each path is sat: not unsat
                {never, true}}) {   // each path is unsat
            Path iteration = folder.newFolder("seed-" + row[0]).toPath();
            Session seed = new Session(iteration, "s0", false);
            seed.expression(never, binary("==", integer("I", 1L),
                    integer("I", 2L)));
            seed.target((String) row[0], true, true);
            seed.target((String) row[0], true, true);
            seed.write();
            Composer.Composition composition = compose(iteration, 4);
            assertEquals("two target rows, two paths", 2,
                    composition.disjuncts().size());
            try (Disjunction asks = new Disjunction(composition, solver)) {
                assertEquals("phi " + row[0], row[1],
                        ClaimPolicy.seedDisjunctUnsat(composition, asks));
            }
            assertTrue("z3 read every question: " + solver.errors(),
                    solver.errors().isEmpty());
        }
    }

    /**
     * Every path unsat with every root free is a contradiction the
     * composition built only when it is unsat without its fatal arm too, or
     * observed the fatal arm: refuted by phi alone, no root turns it to the
     * fatal arm, which is the claim's answer and no gap (b20h
     * BlockTokenSecretManager-511).  {the decision before the anchor, or
     * null; phi; observed fatal; BLOCKING PATH_SELF_CONTRADICTORY}.
     */
    @Test
    public void aPathRefutedByItsFatalArmAloneContradictsNothing()
            throws Exception {
        String never = "(and " + MARKER + " (not " + MARKER + "))";
        Object[][] rows = {
                {null, never, false, false},
                {never, MARKER, false, true},
                {null, never, true, true},
        };
        for (Object[] row : rows) {
            Path iteration = folder.newFolder().toPath();
            Session seed = new Session(iteration, "s0", false);
            seed.marker("false");
            if (row[0] != null) seed.decision(ANCHOR, "a#u1", (String) row[0]);
            seed.target((String) row[1], (Boolean) row[2], true);
            seed.write();
            ClaimPolicy.Decision decision = ClaimPolicy.decide(
                    compose(iteration, 4), solver());
            boolean blocked = false;
            for (GapRow gap : decision.claim().gaps()) {
                blocked |= gap.kind() == GapKind.PATH_SELF_CONTRADICTORY
                        && gap.cls() == GapClass.BLOCKING;
            }
            assertEquals(Arrays.toString(row), row[3], blocked);
            assertEquals(Arrays.toString(row), ClaimKind.NO_SUPPORTED_WITNESS,
                    decision.claim().kind());
        }
    }

    /**
     * A FORCED path (PIPELINE §7.10): the recording took the healthy arm of
     * a concrete guard, so its path is no world; the forced session, its
     * guard forced, stands at that guard with the whole way to the throw as
     * phi.  Composed beside it over the same root names, the forced
     * disjunct is the witness -- the marker flipped AND the counter past 5,
     * nested behind it.
     */
    @Test
    public void aForcedPathStatesTheWholeWayToTheThrow() throws Exception {
        Path iteration = folder.newFolder("forced").toPath();
        Session seed = new Session(iteration, "s0", false);
        seed.marker("false");
        seed.serial("0", "0", "10");
        seed.target("false", false, true);
        seed.write();
        Session forced = new Session(iteration, "s-forced", false);
        forced.marker("false");
        forced.serial("0", "0", "10");
        forced.forcedDecision(ANCHOR, "a#u1", MARKER);
        forced.forcedTarget(3L, "(and " + MARKER + " (> " + SERIAL + " 5))");
        forced.write();
        // Pairs of moves are enumerated after the single ones.
        Composer.Composition composition = compose(iteration, 64);
        assertEquals("the seed's path and the forced one", 2,
                composition.paths().size());
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertEquals(ClaimKind.MARKER_FLIPPED, decision.claim().kind());
        assertEquals("true", decision.claim().movedRoots().get(MARKER_ROOT));
        assertTrue("and the counter nested behind it moved with it",
                Integer.parseInt(decision.claim().movedRoots()
                        .get(SERIAL_ROOT)) > 5);
    }

    /**
     * A DISJUNCTION is asked whole while that decides, else path by path,
     * and the answer is the first sat path in order.  A path refuted under
     * some assertions is not asked again under more of them; a refutation
     * asked without a core answers no question that wants one, unless it
     * was asked under no assertion at all (the self-check), where no pin can
     * be in its core.  The fixture z3 answers the whole query
     * {@code unknown}, path 0 unsat and path 1 sat, and logs each time it
     * is asked path 0.  {what refuted path 0 first (null: nothing), the
     * assertions then asked, whether a core is wanted, path 0 asked again}.
     */
    @Test
    public void aRefutedPathIsNotAskedAgain() throws Exception {
        Path iteration = folder.newFolder("refuted").toPath();
        Session seed = new Session(iteration, "s0", false);
        seed.target("true", true, true);
        seed.target("true", true, true);
        seed.write();
        Composer.Composition composition = compose(iteration, 4);
        String first = composition.disjuncts().get(0).selector();
        String second = composition.disjuncts().get(1).selector();
        Path log = folder.newFile("asked.log").toPath();
        Path script = folder.newFile("z3-paths.sh").toPath();
        Files.write(script, Arrays.asList("#!/bin/bash",
                "input=$(cat)",
                "case $input in",
                "  *'(assert " + first + ")'*) echo 0 >> " + log
                        + "; echo unsat; echo '()' ;;",
                "  *'(assert " + second + ")'*) echo sat; echo '((x 1))' ;;",
                "  *) echo unknown ;;",
                "esac"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        List<String> none = Collections.emptyList();
        List<String> pinned = Collections.singletonList("(assert true)");
        List<String> more = Arrays.asList("(assert true)",
                "(assert (= 1 1))");
        Object[][] rows = {
                {null, none, false, true},
                {pinned, more, false, false},
                {pinned, more, true, true},
                {"self-check", more, true, false},
                {more, pinned, false, true},
        };
        for (Object[] row : rows) {
            try (Disjunction asks = new Disjunction(composition,
                    new Z3(script, 30000L))) {
                if ("self-check".equals(row[0])) {
                    asks.selfCheck();
                } else if (row[0] != null) {
                    @SuppressWarnings("unchecked")
                    List<String> refuting = (List<String>) row[0];
                    asks.ask(refuting, composition.selectors(), none, false);
                }
                long before = asked(log);
                @SuppressWarnings("unchecked")
                List<String> assertions = (List<String>) row[1];
                Z3.Answer answer = asks.ask(assertions,
                        composition.selectors(), none, (Boolean) row[2]);
                assertEquals(Arrays.toString(row), "sat", answer.status());
                assertEquals(Arrays.toString(row), row[3],
                        asked(log) > before);
            }
        }
    }

    private static long asked(Path log) throws IOException {
        return Files.readAllLines(log).size();
    }

    /**
     * Two recorded keys are one key when they print one text: compared node
     * by node ({@code ContainerSmtCodec#sameText}) exactly where their texts
     * are equal -- a number's spelling, a string against a number, member
     * order, null -- and a shared subterm is not walked twice.
     */
    @Test
    public void twoKeysAreOneKeyWhenTheyPrintOneText() {
        String[][] pairs = {
                {"1", "1"}, {"1", "1.0"}, {"\"1\"", "1"}, {"true", "\"true\""},
                {"null", "null"}, {"[1,2]", "[1,2]"}, {"[1,2]", "[2,1]"},
                {"{\"a\":1,\"b\":[null]}", "{\"a\":1,\"b\":[null]}"},
                {"{\"a\":1,\"b\":2}", "{\"b\":2,\"a\":1}"},
                {"{\"a\":{\"x\":9007199254740993}}",
                        "{\"a\":{\"x\":9007199254740992}}"},
        };
        for (String[] pair : pairs) {
            com.google.gson.JsonElement left =
                    com.google.gson.JsonParser.parseString(pair[0]);
            com.google.gson.JsonElement right =
                    com.google.gson.JsonParser.parseString(pair[1]);
            assertEquals(Arrays.toString(pair),
                    left.toString().equals(right.toString()),
                    ContainerSmtCodec.sameText(left, right,
                            new java.util.IdentityHashMap<com.google.gson
                                    .JsonElement, Set<com.google.gson
                                    .JsonElement>>()));
        }
        // A chain whose every node names the one below twice is 2^depth
        // nodes spelled; compared, each pair once.
        JsonObject one = new JsonObject();
        JsonObject other = new JsonObject();
        one.addProperty("leaf", 7L);
        other.addProperty("leaf", 7L);
        for (int depth = 0; depth < 64; depth++) {
            JsonObject up = new JsonObject();
            JsonObject across = new JsonObject();
            up.add("l", one);
            up.add("r", one);
            across.add("l", other);
            across.add("r", other);
            one = up;
            other = across;
        }
        assertTrue(ContainerSmtCodec.sameText(one, other,
                new java.util.IdentityHashMap<com.google.gson.JsonElement,
                        Set<com.google.gson.JsonElement>>()));
    }

    /**
     * An arrival nothing binds and nothing pins is FREE, named -- never a
     * dropped path: its producer attested by an export of it that does not
     * lower (attested), or no producer and a received value the lowering
     * places nowhere (unplaceable).
     */
    @Test
    public void anArrivalNothingBindsIsFreeAndNamedNeverADroppedPath()
            throws Exception {
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.id",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.id",
                at("attach#1", 0), 0);
        for (String variant : new String[]{"attested", "unplaceable"}) {
            Path iteration = folder.newFolder("free-" + variant).toPath();
            Session session = new Session(iteration, "s0", false);
            session.marker("false");
            if ("attested".equals(variant)) {
                session.activation(PRODUCER);
                session.export(producer, "EXPR.v1.gone", 1L, "10");
                session.attach(consumer, "vh", "I", "10", producer);
            } else {
                session.attach(consumer, "vh", "I", "ten", null);
            }
            session.target("(> vh 5)", false, true);
            session.write();
            Composer.Composition composition = compose(iteration, 4);
            assertEquals(variant + ": the path stands: " + composition.gaps(),
                    1, composition.disjuncts().size());
            assertTrue(variant, composition.refusedPaths().isEmpty());
            List<String> free = new ArrayList<String>();
            for (Composer.Concrete row : composition.concrete()) {
                if ("vh".equals(row.subject)) free.add(row.kind);
            }
            assertEquals(variant + ": " + concrete(composition),
                    Collections.singletonList("FREE"), free);
        }
    }

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
            // One path's question holds its own guarded commands and none
            // of the other path's (Composition#pathQuery).
            String alone = text(composition.pathQuery(disjunct.selector(),
                    composition.valuations().get(0).assertions()));
            for (Composer.Disjunct other : composition.disjuncts()) {
                assertEquals("guarded by " + other.selector(),
                        other == disjunct, alone.contains(
                                "(=> " + other.selector() + " "));
            }
            assertEquals("each path is satisfiable as the execution that "
                            + "made it: " + disjunct.path().sessionId,
                    "sat", solver.ask(alone,
                            Collections.<String>emptyList(), false).status());
        }

        // AND THE OTHER HALF OF THE ONE RULE.  The same two sessions with
        // no rows for the producer at all: no row states the producer, so
        // each path holds its arrival at what its own row states it
        // received, named HELD (producer unstated) beside the verdict --
        // never free by default, never a silent pin.
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
        Composer.Composition freed = compose(unstated, 4);
        assertEquals("each path composes: " + freed.gaps(),
                2, freed.disjuncts().size());
        assertTrue("each arrival held at its own value: " + freed.body(),
                freed.body().contains("(= vh 10)")
                        && freed.body().contains("(= vh 20)"));
        List<String> held = new ArrayList<String>();
        for (Composer.Concrete row : freed.concrete()) {
            held.add(row.kind + " " + row.subject + "=" + row.value + " "
                    + row.reason);
        }
        String why = SmtLowering.Unbound.PRODUCER_UNSTATED + ": no export "
                + "row of this corpus attests its producer " + producer.id();
        assertEquals("and named, per path", Arrays.asList(
                "HELD vh=10 " + why, "HELD vh=20 " + why), held);

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
        // refused an attach (VM handle 7) at the anchor itself, which then
        // computed on the arrival as a constant, and s0's run refused one in
        // an occurrence no closure here reaches: both paths compose, and
        // s1's frame is named by THE ONE RULE.  Its producer is the export
        // of handle 7: FREE where that export rests on a root (moving), or
        // reads a version a write of the root made (guarded: the NameNode's
        // currentKey.keyId, stored from the serial), held where it rests on
        // nothing that moves (constant), held as its producer unstated where
        // no export states the handle (unstated).
        // The refused arrival's producer: another port of the producer.
        Endpoint refusedFrom = Endpoint.of(PRODUCER, "PORT.refused",
                at("export#2", 0), 0);
        LocationId keyId = LocationId.of(LocationKind.INSTANCE, "77", "24");
        for (String variant : new String[]{"moving", "guarded", "constant",
                "unstated"}) {
            Path framed = folder.newFolder("framed-" + variant).toPath();
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
                if ("moving".equals(variant)) {
                    session.root(PRODUCER, "ROOT.ID", "M_I_id",
                            RootKind.INTEGRAL, each[1]);
                    session.expression("EXPR.0000000000000a07",
                            symbol("M_I_id", "I"));
                    session.export(refusedFrom, "EXPR.0000000000000a07",
                            7L, each[1]);
                } else if ("guarded".equals(variant)) {
                    session.root(PRODUCER, "ROOT.ID", "M_I_id",
                            RootKind.INTEGRAL, each[1]);
                    session.expression("EXPR.0000000000000a08",
                            symbol("M_I_id", "I"));
                    session.write(Endpoint.of(PRODUCER, "Key#set#2:WRITE",
                            at("w#1", 0), 0), keyId, 3L,
                            "EXPR.0000000000000a08");
                    session.expression("EXPR.0000000000000a09",
                            read("INSTANCE_FIELD", 77L, 24L, 3L, "I"));
                    session.export(refusedFrom, "EXPR.0000000000000a09",
                            7L, each[1]);
                } else if ("constant".equals(variant)) {
                    session.export(refusedFrom, "EXPR.v1.id", 7L, each[1]);
                }
                session.target("true", false, true);
                session.refusedAttach("s1".equals(each[0]) ? ANCHOR
                        : UPSTREAM);
                session.write();
            }
            Composer.Composition frame = compose(framed, 4);
            assertEquals(variant + ", both paths: " + frame.gaps(), 2,
                    frame.disjuncts().size());
            List<String> frames = new ArrayList<String>();
            for (Composer.Concrete row : frame.concrete()) {
                if (!row.subject.equals(ANCHOR.id())) continue;
                frames.add(row.kind + " " + row.movesWith + " "
                        + row.pathId.isEmpty() + " " + row.reason.startsWith(
                        SmtLowering.Unbound.PRODUCER_UNSTATED));
            }
            assertEquals(variant + ": s1's anchor rested on a frame: "
                    + concrete(frame), Collections.singletonList(
                    "moving".equals(variant) || "guarded".equals(variant)
                            ? "FREE [M_I_id] false false"
                            : "constant".equals(variant)
                            ? "HELD [] false false"
                            : "HELD [] false true"), frames);
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
        String candidate = text(ComposeMain.candidate(composition, decision));
        assertTrue("the blocked candidate closes the question: " + candidate,
                candidate.contains("(assert false) ; fail closed: "
                        + GapKind.DECLARATION_MISSING.name() + ":"));
        assertTrue("with check-sat after it and nothing else",
                candidate.endsWith("(check-sat)\n"));

        // RAN, AND LEFT THE WAY TO THE THROW.  A session whose target row
        // stands at the declared occurrence and never reached the anchor
        // took the healthy arm at a guard on the way: its path is a
        // disjunct whose fatal arm is the constant false, so the claim
        // closes UNSAT with no gap, the way it left named in concrete[],
        // and the formula states the decisions it took up to that guard,
        // each a proposition at the arm it took (its term, over nothing
        // that moves, in concrete[]), never a bare constant.
        Path ran = folder.newFolder("ran-unreached").toPath();
        Session unreached = new Session(ran, "s0", false);
        unreached.marker("false");
        unreached.decision(ANCHOR, "way#u3", false, "(< 3 2)");
        // A decision the VM recorded concretely, stating no term.
        unreached.decision(ANCHOR, "way#u4", true, "");
        unreached.target("", false, false);
        // An unreached target row's seq marks no point of the path (the
        // runtime states 0): a decision after it is the path's too.
        unreached.decision(ANCHOR, "way#u5", true, "(> 2 1)");
        unreached.write();
        Composer.Composition left = compose(ran, 4);
        ClaimPolicy.Decision healthy = ClaimPolicy.decide(left, solver());
        assertEquals("the run's path is a disjunct: " + left.gaps(), 1,
                left.disjuncts().size());
        assertEquals(ClaimKind.NO_SUPPORTED_WITNESS, healthy.claim().kind());
        assertFalse("no gap withholds it: " + healthy.claim().gaps(),
                healthy.claim().blocked());
        List<String> kinds = new ArrayList<String>();
        for (Composer.Concrete row : left.concrete()) {
            kinds.add(row.kind + " " + row.subject + " " + row.value);
        }
        assertEquals("the way it left is named, and each decision with its "
                        + "term", Arrays.asList("WAY " + ANCHOR.render() + " ",
                        "DECISION way#u3#1 false (< 3 2)",
                        "DECISION way#u4#2 true",
                        "DECISION way#u5#3 true (> 2 1)"), kinds);
        assertTrue("and the decisions it took are stated, each a "
                        + "proposition at its arm: " + left.body(),
                left.body().matches("(?s).*\\(and \\(and \\(not "
                        + "decided__0__\\w+\\) decided__0__\\w+ "
                        + "decided__0__\\w+\\) false\\).*"));

        // LEFT AT A SYMBOLIC GUARD.  The same path, left at a guard on the
        // way to the throw whose term names the marker: its fatal arm is
        // that guard's other arm, so the formula is satisfiable where the
        // marker turns it -- a witness CONFIRM judges -- and the WAY entry
        // names what the guard rests on; at a concrete guard, the constant.
        for (boolean symbolic : new boolean[]{true, false}) {
            Path way = folder.newFolder("way-" + symbolic).toPath();
            Session at = new Session(way, "s0", false);
            at.marker("false");
            at.decision(ANCHOR, "way#u3", false, symbolic ? MARKER
                    : "(< 3 2)");
            at.target("", false, false);
            at.write();
            Path map = way.resolve(StaticScopeMap.FILE);
            JsonObject site = new JsonObject();
            site.addProperty("schemaVersion", 1);
            site.addProperty("kind", StaticScopeMap.SITE_KIND);
            site.addProperty("role", StaticScopeMap.TARGET_SITE);
            site.addProperty("regionId", ANCHOR.regionId());
            site.addProperty("siteId", "Throw#u30");
            JsonArray guards = new JsonArray();
            guards.add("way#u3");
            guards.add(ANCHOR_SITE);
            site.add("guards", guards);
            Files.write(map, Collections.singletonList(site.toString()),
                    java.nio.charset.StandardCharsets.UTF_8);
            Composer.Composition atWay = compose(way, ANCHOR, 4,
                    StaticScopeMap.read(map));
            ClaimPolicy.Decision decided = ClaimPolicy.decide(atWay,
                    solver());
            if (symbolic) {
                assertEquals("the marker turns the guard: "
                                + decided.claim().gaps(),
                        ClaimKind.MARKER_FLIPPED, decided.claim().kind());
            } else {
                assertEquals("the constant: " + decided.claim().gaps(),
                        "unsat", decided.formula().status());
            }
            List<String> ways = new ArrayList<String>();
            for (Composer.Concrete row : atWay.concrete()) {
                if ("WAY".equals(row.kind)) {
                    ways.add(row.subject + " " + row.movesWith);
                }
            }
            assertEquals(Collections.singletonList("way#u3#1 "
                    + (symbolic ? Collections.singletonList(MARKER)
                    : Collections.emptyList())), ways);
        }

        // KEPT THE WAY, THEN STOPPED.  The guard's forcing-table arm toward
        // the throw is false (the anchor's own TARGET_SITE row's `force`).
        // A path whose last way decision took that arm, or a passable
        // branch's (either arm leads on), never LEFT the way there: the
        // scan goes back past it to the last decision that did leave, and
        // where none did, no guard is named and its fatal is the constant
        // false (solr-adhoc-19 SG2b: create's u9, taken toward the throw
        // before a loop bound cut the occurrence, was composed as the
        // CONFLICT throw).  Where a loop bound cut the occurrence, the
        // composition names the bound (`loop-body-bound`, counted in the
        // case's `bounded`).  A decider (a row with `via`) counts only in a
        // call of its helper from its via (DecisionRow#via).
        String keep = "{\"siteId\":\"way#u3\",\"arm\":false}";
        String bound = "MAX_LOOP_BODY_ITERATIONS_REACHED at L#loop:u44 after"
                + " 8 loop body iterations";
        String inWay = "MAX_LOOP_BODY_ITERATIONS_REACHED at way#loop:u2"
                + " after 8 loop body iterations";
        String leaveAt4 = "{\"siteId\":\"way#u4\",\"arm\":true}";
        String decider = "{\"siteId\":\"H#u1\",\"arm\":true,"
                + "\"via\":\"<V: void v()>\"}";
        Object[][] kept = {
                // {why, the table rows, the decisions (site, arm, via, its
                //  term when not the marker), the cut (null: none), the WAY
                //  subject, the claim's kind, a bounded row, blocked}
                {"took the arm toward the throw, then a loop bound cut it",
                        keep, new String[][] {{"way#u3", "false", ""}}, bound,
                        ANCHOR.render(), ClaimKind.NO_SUPPORTED_WITNESS, true,
                        false},
                {"a passable branch: neither arm leaves the way",
                        "{\"siteId\":\"way#u3\",\"arm\":true,"
                                + "\"passable\":true}",
                        new String[][] {{"way#u3", "false", ""}}, null,
                        ANCHOR.render(), ClaimKind.NO_SUPPORTED_WITNESS, false,
                        false},
                {"took the arm off the way: it left there",
                        "{\"siteId\":\"way#u3\",\"arm\":true}",
                        new String[][] {{"way#u3", "false", ""}}, null,
                        "way#u3#1", ClaimKind.MARKER_FLIPPED, false, false},
                {"left at u3, later kept the way at u4, then returned: it "
                        + "left at u3", "{\"siteId\":\"way#u3\",\"arm\":true},"
                        + leaveAt4, new String[][] {{"way#u3", "false", ""},
                        {"way#u4", "true", ""}}, null, "way#u3#1",
                        ClaimKind.MARKER_FLIPPED, false, false},
                {"a decider off its arm in a call from elsewhere is no "
                        + "decision of the way", "{\"siteId\":\"way#u3\","
                        + "\"arm\":true}," + decider,
                        new String[][] {{"way#u3", "false", ""},
                        {"H#u1", "false", "<W: void w()>"}}, null,
                        "way#u3#1", ClaimKind.MARKER_FLIPPED, false, false},
                {"the same decider in a call from its via left the way",
                        "{\"siteId\":\"way#u3\",\"arm\":true}," + decider,
                        new String[][] {{"way#u3", "false", "", "(< 3 2)"},
                        {"H#u1", "false", "<V: void v()>"}}, null,
                        "H#u1#2", ClaimKind.MARKER_FLIPPED, false, false},
                {"left at u3, then a bound cut a loop elsewhere: named "
                        + "all the same (a later turn of a caller's loop may "
                        + "come back)", "{\"siteId\":\"way#u3\","
                        + "\"arm\":true}", new String[][] {{"way#u3", "false",
                        ""}}, bound, "way#u3#1", ClaimKind.MARKER_FLIPPED,
                        true, false},
                {"a decider whose decision states no caller (a corpus "
                        + "before rows stated it) is taken as the way's",
                        "{\"siteId\":\"way#u3\",\"arm\":true}," + decider,
                        new String[][] {{"way#u3", "false", "", "(< 3 2)"},
                        {"H#u1", "false", ""}}, null, "H#u1#2",
                        ClaimKind.MARKER_FLIPPED, false, false},
                {"left at u3 inside a loop (decided again) a bound cut: "
                        + "named", "{\"siteId\":\"way#u3\",\"arm\":true}",
                        new String[][] {{"way#u3", "false", "", "(< 3 2)"},
                        {"way#u3", "false", ""}}, bound, "way#u3#2",
                        ClaimKind.MARKER_FLIPPED, true, false},
                {"left at u3 in the cut loop's own method: named",
                        "{\"siteId\":\"way#u3\",\"arm\":true}",
                        new String[][] {{"way#u3", "false", ""}}, inWay,
                        "way#u3#1", ClaimKind.MARKER_FLIPPED, true, false},
                {"the loop accounting failed: an engine defect, never a "
                        + "bound", keep, new String[][] {{"way#u3", "false",
                        ""}}, "INSTRUMENTATION_POLICY_MISMATCH at L#loop:u44"
                        + " after 8 loop body iterations", ANCHOR.render(),
                        ClaimKind.NO_SUPPORTED_WITNESS, false, true}};
        for (Object[] row : kept) {
            Path way = folder.newFolder().toPath();
            Session at = new Session(way, "s0", false);
            at.marker("false");
            for (String[] made : (String[][]) row[2]) {
                at.decision(ANCHOR, made[0], Boolean.parseBoolean(made[1]),
                        made.length > 3 ? made[3] : MARKER, made[2]);
            }
            // As the runtime labels it: the target branch's site and its
            // occurrence ordinal (RowPublication#target).
            at.anchorLabel = "way#u9#1";
            at.target("", false, false);
            if (row[3] != null) {
                at.cut(ANCHOR, "this activation's local path was cut: "
                        + row[3]);
            }
            at.write();
            Path map = way.resolve(StaticScopeMap.FILE);
            String site = "{\"schemaVersion\":1,\"kind\":\""
                    + StaticScopeMap.SITE_KIND + "\",\"role\":\""
                    + StaticScopeMap.TARGET_SITE + "\",\"regionId\":\""
                    + ANCHOR.regionId() + "\",\"siteId\":\"Throw#u30\","
                    + "\"guards\":[\"way#u3\",\"way#u4\",\"way#u9\"],"
                    + "\"guardOutcomes\":[false,true,true],"
                    + "\"guardDeciders\":{\"way#u4\":[{\"siteId\":\"H#u1\","
                    + "\"outcome\":true,\"verdict\":true}]},"
                    + "\"chain\":[{\"siteId\":\"H#u1\",\"outcome\":true}],"
                    + "\"force\":[" + row[1] + "]}";
            Files.write(map, Collections.singletonList(site),
                    java.nio.charset.StandardCharsets.UTF_8);
            Composer.Composition composed = compose(way, ANCHOR, 4,
                    StaticScopeMap.read(map));
            ClaimPolicy.Decision decided = ClaimPolicy.decide(composed,
                    solver());
            List<String> ways = new ArrayList<String>();
            for (Composer.Concrete concrete : composed.concrete()) {
                if ("WAY".equals(concrete.kind)) ways.add(concrete.subject);
            }
            assertEquals((String) row[0], Collections.singletonList(row[4]),
                    ways);
            assertEquals((String) row[0], row[5], decided.claim().kind());
            assertEquals((String) row[0], bounded(composed), row[6]);
            assertEquals((String) row[0], row[7], decided.claim().blocked());
        }

        // A SESSION BESIDE ONE THAT REACHED THE ANCHOR, cut on the way, is no
        // disjunct, yet its cut still bounds the search: named all the same.
        Path beside = folder.newFolder("beside").toPath();
        Session reaching = new Session(beside, "s0", false);
        reaching.marker("false");
        reaching.target(MARKER, false, true);
        reaching.write();
        Session stopped = new Session(beside, "s1", true);
        stopped.decision(ANCHOR, "way#u3", false, MARKER);
        stopped.target("", false, false);
        stopped.cut(ANCHOR, "this activation's local path was cut: " + bound);
        stopped.write();
        Path besideMap = beside.resolve(StaticScopeMap.FILE);
        Files.write(besideMap, Collections.singletonList("{\"schemaVersion\":1,"
                + "\"kind\":\"" + StaticScopeMap.SITE_KIND + "\",\"role\":\""
                + StaticScopeMap.TARGET_SITE + "\",\"regionId\":\""
                + ANCHOR.regionId() + "\",\"siteId\":\"Throw#u30\","
                + "\"guards\":[\"way#u3\",\"" + ANCHOR_SITE + "\"],"
                + "\"guardOutcomes\":[false,true],\"force\":[" + keep
                + "]}"), java.nio.charset.StandardCharsets.UTF_8);
        Composer.Composition besideComposed = compose(beside, ANCHOR, 4,
                StaticScopeMap.read(besideMap));
        assertEquals("only the reaching path is a disjunct", 1,
                besideComposed.disjuncts().size());
        assertTrue("the cut of the one beside it is named: "
                + besideComposed.gaps(), bounded(besideComposed));

        // A REPLAY ITS OWN ROWS DO NOT ADMIT reached the anchor and threw
        // there: no disjunct, and it drops no path -- the admitted session
        // that left the way stays a disjunct (solr-adhoc-19 F2V4: such a
        // replay made COMPOSE drop 63 unreached paths).
        Path refusedReach = folder.newFolder("refused-reach").toPath();
        Session leftWay = new Session(refusedReach, "s0", false);
        leftWay.marker("false");
        leftWay.decision(ANCHOR, "way#u3", true, MARKER);
        leftWay.target("", false, false);
        leftWay.write();
        Session threw = new Session(refusedReach, "s1", true);
        threw.refused("the flip site was never reached in this replay");
        threw.target(MARKER, true, true);
        threw.write();
        Path refusedMap = refusedReach.resolve(StaticScopeMap.FILE);
        Files.write(refusedMap, Collections.singletonList(
                Files.readAllLines(besideMap).get(0)),
                java.nio.charset.StandardCharsets.UTF_8);
        Composer.Composition refusedComposed = compose(refusedReach, ANCHOR,
                4, StaticScopeMap.read(refusedMap));
        assertEquals("the admitted path that left the way is the disjunct: "
                + refusedComposed.gaps(), 1,
                refusedComposed.disjuncts().size());
        boolean named = false;
        for (GapRow gap : refusedComposed.gaps()) {
            named |= gap.subject().equals("s1") && gap.detail().contains(
                    "reached the anchor and threw the target in a replay"
                            + " its own rows do not admit");
        }
        assertTrue("the refused reach is named: " + refusedComposed.gaps(),
                named);

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
     * A replay that read the counter and minted no root holds literals that
     * may be computed from its reading, through state no row tracks: its
     * arms and its path hold at the reading alone, varied or not.
     * Unguarded, such an arm was admitted under a moved counter, and COMPOSE
     * claimed a fatal no run reproduces (hdfs-17967-pathA F2b: the seed's
     * path took 185a3b77's key-id arm, 119528 as a literal, with the serial
     * moved to 119529; CONFIRM refuted it under every jar).  A replay that
     * never read the counter, or a counter some replay found DERIVED (its
     * source carried another input's expression, a clock's say), stays
     * free.  {variant, arms, guarded, the reading replay's path pinned}
     */
    @Test
    public void aRootReadConcretelyHoldsItsReplaysPathAndArmsAtTheReading()
            throws Exception {
        Object[][] table = {
                {"read", 2, 1, true},
                {"never read", 1, 0, false},
                {"read, derived", 1, 0, false}};
        for (Object[] row : table) {
            String variant = (String) row[0];
            Path iteration = folder.newFolder(variant.replaceAll("\\W+", "-"))
                    .toPath();
            for (String id : new String[]{"s0", "s1", "s2"}) {
                Session session = new Session(iteration, id,
                        !"s0".equals(id));
                session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
                        !"s0".equals(id), true);
                if (!"s2".equals(id)) {
                    session.serial("119994", "119994", "119997");
                } else if (!variant.equals("never read")) {
                    session.serialReadConcretely("119994");
                }
                if (variant.equals("read, derived") && "s1".equals(id)) {
                    session.derived.add(SERIAL_ROOT);
                }
                session.expression("EXPR.key", integer("I", 7L));
                session.export(Endpoint.of(PRODUCER, "PORT.key",
                        at("export#1", 0), 0), "EXPR.key", "I", 1L, "7");
                session.attach(Endpoint.of(ANCHOR, "PORT.key",
                                at("attach#1", 0), 0), "vh", "I", "7",
                        Endpoint.of(PRODUCER, "PORT.key", at("export#1", 0),
                                0));
                session.target("true", false, true);
                session.write();
            }
            Composer.Composition composition = compose(iteration, 8);
            assertEquals(variant, 3, composition.disjuncts().size());
            // Unguarded, the three deliveries are one arm (one body); the
            // reading replay's is its own, guarded by the counter.
            List<Arm> arms = composition.families().get(0).arms();
            int guarded = 0;
            for (Arm arm : arms) {
                if (arm.guardRoots().contains(SERIAL_ROOT)) guarded++;
            }
            assertEquals(variant + ": " + arms, row[1], arms.size());
            assertEquals(variant, row[2], guarded);
            if (!composition.body().contains(SERIAL)) continue;
            Z3 solver = solver();
            for (Composer.Disjunct disjunct : composition.disjuncts()) {
                if (!disjunct.path().sessionId.equals("s2")) continue;
                List<String> pinned = new ArrayList<String>();
                pinned.add("(assert " + disjunct.selector() + ")");
                pinned.add("(assert (= " + SERIAL + " 119995))");
                assertEquals(variant + ": its path off the reading",
                        (Boolean) row[3] ? "unsat" : "sat",
                        solver.ask(composition.query(pinned),
                                Collections.<String>emptyList(), false)
                                .status());
            }
        }
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
            session.serial(each[1], each[1],
                    String.valueOf(Long.parseLong(each[1]) + 3L));
            session.target("true", false, true);
            session.write();
        }
    }

    /**
     * An integral's moves are its domain's end anchors (each bound and its
     * two inward neighbours: where its outermost comparisons flip) first,
     * then outward from the value it ran at, each nearest first, within its
     * domain: a far threshold is reached under the cap, and a recording
     * outside the domain moves to the nearest bound first.  {recorded, min,
     * max, the values moved to, in order, under a cap of four valuations}.
     */
    @Test
    public void anIntegralMovesToItsDomainsEndsThenOutward()
            throws Exception {
        String[][] rows = {
                {"500", "0", "1000", "2 998 1"},
                {"0", "0", "1000", "1 2 998"},
                {"3", "3", "1001", "4 5 999"},
                {"7", "5", "8", "6 8 5"},
                {"20", "5", "8", "8 7 6"},
        };
        for (String[] row : rows) {
            Path iteration = folder.newFolder("outward-" + row[0] + "-"
                    + row[1]).toPath();
            Session session = new Session(iteration, "s0", false);
            session.serial(row[0], row[1], row[2]);
            // The fatal rests on the counter, so the valuations move it.
            session.expression("EXPR.0000000000000e01", binary(">",
                    symbol(SERIAL, "I"), integer("I", 2_000L)));
            session.target("EXPR.0000000000000e01", false, true);
            session.write();
            List<String> moved = new ArrayList<String>();
            for (Composer.Valuation valuation
                    : compose(iteration, 4).valuations()) {
                if (!valuation.moved().isEmpty()) {
                    moved.add(valuation.moved().get(SERIAL_ROOT));
                }
            }
            assertEquals(Arrays.toString(row),
                    Arrays.asList(row[3].split(" ")), moved);
        }
    }

    /**
     * A WITNESS MOVING CONFIGURATION ONLY RANKS LAST, AND ONE WHOSE WORLD
     * NO CLUSTER COULD HOLD IS NO CLAIM.  {what reaches the fatal arm, the
     * configuration's reads its plant leaves (the scope map's CONFIG_KEY
     * row), the claim's kind, its moves, whether it states configuration
     * only, whether a gap names the partial world, whether that is a
     * defect}: the fault and the configuration each alone, the
     * configuration declared first; the configuration alone, whole; the
     * same, a read of its key left -- satisfiable only in a world no replay
     * can plant, a defect (RUN_DEFECT) until that read is planted.
     */
    @Test
    public void aConfigurationWitnessRanksLastAndAPartialOneIsNoClaim()
            throws Exception {
        Object[][] rows = {
            {"(or (not " + MARKER + ") (not " + CONFIG + "))", "",
                ClaimKind.MARKER_FLIPPED, MARKER_ROOT, false, false, false},
            {"(not " + CONFIG + ")", "", ClaimKind.MARKER_FLIPPED,
                CONFIG_ROOT, true, false, false},
            {"(not " + CONFIG + ")", "<t.A: void a()>#u3",
                ClaimKind.NO_SUPPORTED_WITNESS, "", false, true, true}};
        int variant = 0;
        for (Object[] row : rows) {
            Path iteration = folder.newFolder("config-rank-" + variant++)
                    .toPath();
            Session session = new Session(iteration, "s0", false);
            session.configuration("true");
            session.marker("true");
            session.target((String) row[0], false, true);
            session.write();
            Path map = iteration.resolve(StaticScopeMap.FILE);
            Files.write(map, Collections.singletonList(
                    StaticScopeMap.configKeyRow(CONFIG_ROOT, "<t.A: int f>",
                            ((String) row[1]).isEmpty()
                                    ? Collections.<String>emptyList()
                                    : Collections.singletonList(
                                    (String) row[1])).toString()),
                    java.nio.charset.StandardCharsets.UTF_8);
            Composer.Composition composition = compose(iteration, ANCHOR, 8,
                    StaticScopeMap.read(map));
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            String moved = String.join(",",
                    decision.claim().movedRoots().keySet());
            boolean named = false;
            for (GapRow gap : decision.claim().gaps()) {
                named |= gap.kind() == GapKind.UNPRODUCIBLE_ANSWER
                        && CONFIG_ROOT.equals(gap.subject());
            }
            assertEquals((String) row[0] + " " + row[1],
                    row[2] + " " + row[3] + " " + row[4] + " " + row[5]
                            + " " + row[6],
                    decision.claim().kind() + " " + moved + " "
                            + composition.configurationOnly(
                            decision.claim().movedRoots().keySet())
                            + " " + named + " " + decision.claim().blocked());
        }
    }

    /**
     * A NODE'S CLOCK IS ONE ORDER, THE RECORDING'S.  Its cells are listed in
     * the recording's seq order whatever order the corpus holds them in (the
     * claim pins them back in it, and a replay runs a plant on in it); a
     * link the recording's own readings run against gives way by that much;
     * a cell the seed never read is placed at the seed's reading of a cell
     * its session also read, plus the time its host read between the two;
     * one no session can place refuses the paths that name it, by name, and
     * every other path composes.
     */
    @Test
    public void aNodesClockIsOneOrderOnTheRecordingsTimeline()
            throws Exception {
        Path iteration = folder.newFolder("clock-order").toPath();
        Session seed = new Session(iteration, "s0", false);
        seed.roots.add(clockCell("s0", 30L, "ROOT.LATE", "clk_late", "990"));
        seed.roots.add(clockCell("s0", 10L, "ROOT.EARLY", "clk_early",
                "1000"));
        seed.decision(ANCHOR, "anchor#u1", "(> (+ clk_late clk_early) 0)",
                "ROOT.LATE", 990L);
        seed.target("true", false, true);
        seed.write();
        Session grown = new Session(iteration, "s1", true);
        grown.roots.add(clockCell("s1", 10L, "ROOT.EARLY", "clk_early",
                "5000"));
        grown.roots.add(clockCell("s1", 20L, "ROOT.GROWN", "clk_grown",
                "5004"));
        grown.decision(ANCHOR, "anchor#u1", "(> (+ clk_grown clk_early) 0)",
                "ROOT.GROWN", 5004L);
        grown.target("true", false, true);
        grown.write();

        Composer.Composition composition = compose(iteration, 4);
        assertEquals("the recording's seq order, not the corpus's",
                Arrays.asList("clk_early", "clk_grown", "clk_late"),
                composition.clockCells());
        assertEquals("the grown cell: the seed's 1000 plus the 4 its "
                        + "session read after clk_early", Long.valueOf(1004L),
                composition.clockReadings().get("clk_grown"));
        assertEquals("clk_grown", composition.clockBefore().get("clk_late"));
        assertTrue(composition.body(), composition.body().contains(
                "(<= clk_early clk_grown)"));
        assertTrue("the recording read clk_late 14 before clk_grown, so the "
                        + "order gives way by 14: " + composition.body(),
                composition.body().contains("(<= (- clk_grown clk_late) 14)"));
        assertFalse(composition.gaps().toString(),
                blocking(composition.gaps()));

        Session lone = new Session(iteration, "s2", true);
        lone.roots.add(clockCell("s2", 40L, "ROOT.LONE", "clk_lone", "7000"));
        lone.decision(ANCHOR, "anchor#u1", "(> clk_lone 0)", "ROOT.LONE",
                7000L);
        lone.target("true", false, true);
        lone.write();
        Composer.Composition unplaced = compose(iteration, 4);
        assertEquals("a cell no session can place on the recording's "
                        + "timeline refuses the path that names it, by "
                        + "name, and no other: " + unplaced.refusedPaths(),
                "1 s2 DECLARATION_MISSING ROOT.LONE",
                unplaced.refusedPaths().size() + " "
                        + unplaced.refusedPaths().get(0).get("sessionId")
                        .getAsString() + " " + unplaced.refusedPaths()
                        .get(0).get("reason").getAsString().split(":")[0]);
        assertEquals(2, unplaced.disjuncts().size());
        assertFalse("nothing withholds the claim: " + unplaced.gaps(),
                blocking(unplaced.gaps()));
        assertFalse(unplaced.clockCells().contains("clk_lone"));
    }

    /**
     * EVERY SESSION ON THE RECORDING'S TIMELINE (hdfs-11741 L1): a replay
     * ran ten minutes after the recording, so the key it made at startup,
     * outside every clock root, expires at a constant on its own clock; its
     * plant jumped the one clock cell a second.  Compared with that cell,
     * the constant is the same instant on the recording's timeline, and the
     * replay's own world -- the cell at the recording's reading plus its
     * skew -- is a world of its path.  {session, recorded clock, skew, key
     * expiry, the expiry its path compares on the recording's timeline}.
     */
    @Test
    public void aReplaysInstantsAreOnTheRecordingsTimeline() throws Exception {
        Path iteration = folder.newFolder("timeline").toPath();
        long[][] rows = {
                {0L, 1_000_000L, 0L, 1_000_500L, 1_000_500L},
                {1L, 1_601_000L, 1_000L, 1_600_500L, 1_000_500L}};
        for (long[] row : rows) {
            String id = "s" + row[0];
            Session session = new Session(iteration, id, row[0] == 1L);
            session.roots.add(RootMintRow.of(id, 1L, ANCHOR, "ROOT.NOW",
                    "clk_now", RootKind.CLOCK, RootCategory.CLOCK,
                    Long.toString(row[1]), null,
                    null, true, Clock.of(1_000_000L, Clock.WALL), row[2]));
            session.expression("EXPR.00000000000003e1", binary("<",
                    integer("J", row[3]), symbol("clk_now", "J")));
            session.target("EXPR.00000000000003e1", row[0] == 1L, true);
            session.write();
        }
        Composer.Composition composition = compose(iteration, 4);
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            long[] row = rows[disjunct.path().sessionId.equals("s1") ? 1 : 0];
            String own = "(assert (= clk_now " + (1_000_000L + row[2]) + "))";
            assertEquals(disjunct.path().sessionId + " in its own world",
                    row[0] == 1L ? "sat" : "unsat", solver().ask(
                            composition.pathQuery(disjunct.selector(),
                                    Collections.singletonList(own)),
                            null, false).status());
        }
        assertTrue(composition.body(), composition.body().contains(
                "(< " + rows[1][4] + " clk_now)"));
        assertFalse(composition.body(), composition.body().contains(
                Long.toString(rows[1][3])));
    }

    private static RootMintRow clockCell(String session, long seq,
                                         String rootId, String symbol,
                                         String reading) {
        return RootMintRow.of(session, seq, ANCHOR, rootId, symbol,
                RootKind.CLOCK, RootCategory.CLOCK, reading, null, null, true, Clock.of(1_000_000L, Clock.WALL), 0L);
    }

    // ------------------------------------------------------------------
    // 8. A mechanism the recording does not decide is not a finding.
    // ------------------------------------------------------------------

    /**
     * THE FORMULA DECIDES.  Three markers must all flip to reach the fatal
     * arm: no single or pair move does, and the formula itself, every root
     * free, is satisfiable -- so the claim is FORMULA_SAT at the formula's
     * own model (all three moved), never a refutation over the moves the
     * enumeration tried; the exported file is that formula with no
     * valuation pinned, and the same corpus with a fourth, unflippable
     * conjunct is unsat, closed by the formula's own answer.
     */
    @Test
    public void theComposedFormulaDecidesNotTheEnumeration()
            throws Exception {
        for (boolean reachable : new boolean[]{true, false}) {
            Path iteration = folder.newFolder("formula-" + reachable)
                    .toPath();
            Session session = new Session(iteration, "s0", false);
            for (String marker : new String[]{"M_ONE", "M_TWO", "M_THREE"}) {
                session.root(PRODUCER, "ROOT." + marker, marker,
                        RootKind.MARKER, "false");
            }
            session.target(reachable ? "(and M_ONE M_TWO M_THREE)"
                    : "(and M_ONE M_TWO M_THREE (not M_ONE))", false, true);
            session.write();
            Composer.Composition composition = compose(iteration, 8);
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
                if (outcome.valuation().moved().size() < 3) {
                    assertTrue(reachable + ": no single or pair move "
                            + outcome, outcome.answer().unsat());
                }
            }
            String candidate = text(ComposeMain.candidate(composition,
                    decision));
            assertFalse("the file pins no valuation: " + candidate,
                    candidate.contains(":named valuation__"));
            assertEquals(reachable ? "sat" : "unsat",
                    solver().ask(candidate.replace("(check-sat)\n", ""),
                            Collections.<String>emptyList(), false)
                            .status());
            assertEquals(reachable ? "sat" : "unsat",
                    decision.formula().status());
            assertEquals(reachable ? ClaimKind.FORMULA_SAT
                    : ClaimKind.NO_SUPPORTED_WITNESS, decision.claim().kind());
            if (reachable) {
                assertEquals("all three moved", 3,
                        decision.claim().movedRoots().size());
            }
            assertFalse(decision.claim().blocked());
        }
    }

    /**
     * The run as recorded is no counterfactual (owner 2026-10-04: a claim
     * moving no root is never a finding).  A seed replay that observed the
     * fatal at the declared occurrence -- hdfs-adhoc-32 in HG4, published
     * SAT at valuation 0 with nothing moved -- leaves no claim: BLOCKING
     * SEED_OBSERVED_FATAL, and no witness is named although the formula is
     * sat, so the campaign has no verdict (RUN_DEFECT).
     */
    @Test
    public void aSeedThatObservedTheFatalIsNoClaim() throws Exception {
        Path iteration = folder.newFolder("seed-fatal").toPath();
        Session seed = new Session(iteration, "s0", false);
        seed.marker("false");
        seed.target("true", true, true);
        seed.write();
        Composer.Composition composition = compose(iteration, 4);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        assertTrue("named: " + decision.claim().gaps(),
                named(decision.claim().gaps(), GapKind.SEED_OBSERVED_FATAL));
        assertTrue(decision.claim().blocked());
        assertEquals("no witness is named on it",
                ClaimKind.NO_SUPPORTED_WITNESS, decision.claim().kind());
        assertEquals("the formula's answer is still stated", "sat",
                decision.formula().status());
    }

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
        assertEquals("the flip is satisfiable and explains nothing: the "
                        + "formula's claim alone, CONFIRM's to judge",
                ClaimKind.FORMULA_SAT, decision.claim().kind());
        assertEquals("at the flip: the run as recorded is no witness while "
                        + "another moves something", 1,
                decision.claim().valuationOrdinal());
        assertTrue("and the alarm says why",
                named(decision.claim().gaps(),
                        GapKind.FORMULA_SAT_AT_RECORDED_VALUATION));
        assertFalse("which withholds no verdict", decision.claim().blocked());

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

        // R2b: THE CLOCK RUNS ON FROM ITS JUMP.  A later reading of the same
        // clock is no earlier than the cell before it, so the model moves it
        // too; it runs on from the jump as a replay runs it, and the claim
        // names the jump alone (SOLR-18406's cleanReserves clock, moved with
        // delete()'s and outside the witness path's cone).
        Path runs = folder.newFolder("clock-runs-on").toPath();
        Session twice = new Session(runs, "s0", false);
        twice.clock("700");
        twice.roots.add(RootMintRow.of("s0", ++twice.seq, ANCHOR, "ROOT.THEN",
                "clock_then", RootKind.CLOCK, RootCategory.CLOCK, "705", null, null, true,
                Clock.of(1_000_000L, Clock.WALL), 0L));
        twice.decision(ANCHOR, "anchor#u1", "(or (> " + CLOCK + " 1000) "
                + "(not (> " + CLOCK + " 1000)))", CLOCK_ROOT, 700L);
        twice.decision(ANCHOR, "anchor#u2", "(or (> clock_then 0) "
                + "(not (> clock_then 0)))", "ROOT.THEN", 705L);
        twice.target("(> " + CLOCK + " 1000)", false, true);
        twice.write();
        ClaimPolicy.Decision ranOn = ClaimPolicy.decide(compose(runs, 4),
                solver());
        assertEquals(ClaimKind.CLOCK_SKEW, ranOn.claim().kind());
        assertEquals("the jump alone: the later reading runs on from it",
                Collections.singleton(CLOCK),
                ranOn.claim().movedRoots().keySet());

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
        both.serial("119994", "119994", "119997");
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

    /**
     * A CONCRETE FATAL CONDITION states phi as the constant of the arm it
     * took (SOLR-18413 r9: {@code targetColl == null} on a reference the
     * lookup returned concretely).  {@code true} rests the fatal on the path
     * condition that reached the anchor -- here the clock compare before
     * it; on the seed, which then observed the fatal, that is no claim at
     * all (SEED_OBSERVED_FATAL: the run as recorded is no counterfactual);
     * {@code false} is the constant
     * healthy decision, a disjunct no valuation satisfies (the claim closes
     * negative, no gap); a row stating none is no path, as the composer
     * never invents phi.  {phi, observedFatal, disjuncts}.
     */
    @Test
    public void aConcreteFatalConditionRestsOnThePathThatReachedIt()
            throws Exception {
        Object[][] rows = {{"true", true, 1}, {"false", false, 1},
                {"", true, 0}};
        for (Object[] row : rows) {
            Path iteration = folder.newFolder("concrete-" + row[0] + "-"
                    + row[1]).toPath();
            Session session = new Session(iteration, "s0", false);
            session.clock("700");
            session.decision(ANCHOR, "anchor#u1", "(> " + CLOCK + " 1000)",
                    CLOCK_ROOT, 700L);
            session.target((String) row[0], (Boolean) row[1], true);
            session.write();

            Composer.Composition composition = compose(iteration, 4);
            assertEquals("phi \"" + row[0] + "\": " + composition.gaps(),
                    row[2], composition.disjuncts().size());
            if (composition.disjuncts().isEmpty()) {
                assertTrue("refused by name: " + composition.gaps(),
                        named(composition.gaps(), "phi of "
                                + ANCHOR.render()));
                continue;
            }
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            if ("false".equals(row[0])) {
                assertEquals(ClaimKind.NO_SUPPORTED_WITNESS,
                        decision.claim().kind());
                assertFalse("a constant decision is no gap: "
                        + decision.claim().gaps(), decision.claim().blocked());
                for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
                    assertTrue(outcome.answer().unsat());
                }
                continue;
            }
            assertTrue("the fatal rests on the compare before the anchor: "
                            + fatalArm(composition),
                    fatalArm(composition).contains("(> " + CLOCK + " 1000)"));
            assertTrue("and the seed that observed it is no claim: "
                            + decision.claim().gaps(),
                    decision.claim().blocked() && named(decision.claim()
                            .gaps(), GapKind.SEED_OBSERVED_FATAL));
        }
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
            // pair, and one an obligation ANSWERED: no producer attests
            // either, so each is held at the value its run received (the
            // answer, for the answered one), a pin and no refusal.
            session.attach(consumer, "vh", "I", "7", null);
            session.answered(other, "vh_ref", "I", "7", "8", null);
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
        assertFalse("an answered attach no family binds is pinned to its "
                        + "answer, no refusal",
                named(gaps, GapKind.UNATTESTED_ARM));
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

    /**
     * AN ANSWERED HANDOFF IS BOUND BY ITS FAMILY, NEVER BY ITS ANSWER: the
     * answer is what an obligation's replay planted at the consumer, and a
     * path rests only on what a run compatible with it delivered.
     * <ul>
     *   <li>delivered: the flip replay's producer delivered the answer, and
     *       the marker witness stands;</li>
     *   <li>undelivered (hdfs-17967-pathC rb1): the serial moved, the
     *       producer, whose export the VM valued as a constant, delivered
     *       the moved serial, and the consumer was answered with the
     *       recorded one.  Pinned to the answer, the solver moved the
     *       serial past a key id no run delivers with it;</li>
     *   <li>foreign: a path names a handoff variable its session minted no
     *       attach for, so no family of that run binds it: refused by
     *       name.</li>
     * </ul>
     */
    @Test
    public void anAnsweredHandoffIsBoundByItsFamily() throws Exception {
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        Path delivered = folder.newFolder("answered-delivered").toPath();
        session(delivered, "s0", false, "false", producer, consumer,
                "vh", "false", null, true, false, "EXPR.v1.marker");
        session(delivered, "s1", true, "true", producer, consumer,
                "vh", "true", "true", true, true, "EXPR.v1.marker");
        ClaimPolicy.Decision witness = ClaimPolicy.decide(
                compose(delivered, 8), solver());
        assertEquals("delivered", ClaimKind.MARKER_FLIPPED,
                witness.claim().kind());
        assertEquals(Collections.singletonMap(MARKER_ROOT, "true"),
                witness.claim().movedRoots());

        for (String shape : new String[]{"undelivered", "foreign"}) {
            Path iteration = folder.newFolder("answered-" + shape).toPath();
            // {session, serial it ran at}: the flip replay moved it.
            for (String[] each : new String[][]{{"s0", "5"}, {"s1", "6"}}) {
                boolean flip = "s1".equals(each[0]);
                Session session = new Session(iteration, each[0], flip);
                session.activation(PRODUCER, "thread#"
                        + PRODUCER.regionId(), flip, true);
                session.serial(each[1], "5", "8");
                session.expression("EXPR.0000000000000d01", integer("I",
                        Long.parseLong(each[1])));
                session.export(producer, "EXPR.0000000000000d01", "I", 1L,
                        each[1]);
                if (!flip) {
                    session.attach(consumer, "vh", "I", each[1], producer);
                } else if ("undelivered".equals(shape)) {
                    session.answered(consumer, "vh", "I", each[1], "5",
                            producer);
                }
                // The fatal: the key id the handoff named is not current.
                session.expression("EXPR.0000000000000d02", binary("!=",
                        symbol("vh", "I"), symbol(SERIAL, "I")));
                session.target("EXPR.0000000000000d02", flip, true);
                session.write();
            }
            Composer.Composition composition = compose(iteration, 8);
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
                assertFalse(shape + ": no valuation reaches the fatal with "
                                + "the key id a run delivered: " + outcome,
                        outcome.answer().sat());
            }
            assertEquals(shape, ClaimKind.NO_SUPPORTED_WITNESS,
                    decision.claim().kind());
            assertEquals(shape + ": the answered path stays a disjunct, "
                            + "its read bound by the family",
                    "undelivered".equals(shape) ? 2 : 1,
                    composition.disjuncts().size());
            assertEquals(shape + ": a handoff variable no attach of the "
                            + "path's session minted is refused by name",
                    "foreign".equals(shape), says(composition.gaps(),
                            GapKind.UNSTATED_VALUE, "no attach row of its "
                                    + "session minted"));
        }
    }

    /**
     * A HANDOFF AN ARM'S CLOSURE READS IS BOUND LIKE ONE ITS DELIVERY NAMES
     * (hdfs-11741 r8: the balancer's block-key expiry): the producer decided
     * over a value it was handed before it sent the marker, and the flip
     * replay's producer was answered 5 where upstream sent 2.  Free inside
     * the arm, the solver took 5 and moved the marker; bound by its nested
     * family, no run sent a value that decides that way.
     */
    @Test
    public void aHandoffAnArmsClosureReadsIsBoundByItsFamily()
            throws Exception {
        Path iteration = folder.newFolder("arm-handoff").toPath();
        Endpoint upstream = Endpoint.of(UPSTREAM, "PORT.count",
                at("export#0", 0), 0);
        Endpoint handed = Endpoint.of(PRODUCER, "PORT.count",
                at("attach#0", 0), 0);
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        for (String each : new String[]{"s0", "s1"}) {
            boolean flip = "s1".equals(each);
            Session session = new Session(iteration, each, flip);
            session.activation(UPSTREAM, "thread#" + UPSTREAM.regionId(),
                    flip, true);
            session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
                    flip, true);
            session.marker(String.valueOf(flip));
            session.expression("EXPR.0000000000000e01", integer("I", 2L));
            session.export(upstream, "EXPR.0000000000000e01", "I", 1L, "2");
            if (flip) {
                session.answered(handed, "vu", "I", "2", "5", upstream);
            } else {
                session.attach(handed, "vu", "I", "2", upstream);
            }
            session.expression("EXPR.0000000000000e02", binary("&&",
                    symbol(MARKER, "Z"), binary(">", symbol("vu", "I"),
                            integer("I", 3L))));
            session.decision(PRODUCER, "nn#u1", flip,
                    "EXPR.0000000000000e02");
            session.expression("EXPR.0000000000000e03", symbol(MARKER, "Z"));
            session.export(producer, "EXPR.0000000000000e03", 2L,
                    String.valueOf(flip));
            session.attach(consumer, "vh", String.valueOf(flip), producer);
            session.target("vh", flip, true);
            session.write();
        }
        ClaimPolicy.Decision decision = ClaimPolicy.decide(
                compose(iteration, 8), solver());
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            assertFalse("no run handed the producer a value past 3: "
                    + outcome, outcome.answer().sat());
        }
        assertEquals(ClaimKind.NO_SUPPORTED_WITNESS, decision.claim().kind());
    }

    /**
     * AN ARM NOT CHOSEN IMPOSES NOTHING (hdfs-11741 m1): s1's delivery rests
     * on what upstream handed it in s1's world, the marker set, and that
     * nested family holds under s1's arm alone.  Under the path selector it
     * held on the seed's path too, whose anchor decided on the marker unset,
     * and no world of that path was left.  {path's session, assertion,
     * answer}; "nested" is the nested family's arm on the seed's path.
     */
    @Test
    public void aNestedFamilyHoldsOnlyUnderTheArmThatNeedsIt()
            throws Exception {
        Path iteration = folder.newFolder("nested-under-arm").toPath();
        Endpoint upstream = Endpoint.of(UPSTREAM, "PORT.count",
                at("export#0", 0), 0);
        Endpoint handed = Endpoint.of(PRODUCER, "PORT.count",
                at("attach#0", 0), 0);
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        for (String each : new String[]{"s0", "s1"}) {
            boolean flip = "s1".equals(each);
            Session session = new Session(iteration, each, flip);
            session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
                    flip, true);
            session.marker(String.valueOf(flip));
            if (flip) {
                session.activation(UPSTREAM, "thread#"
                        + UPSTREAM.regionId(), true, true);
                session.expression("EXPR.0000000000000f01",
                        integer("I", 2L));
                session.export(upstream, "EXPR.0000000000000f01", "I", 1L,
                        "2");
                session.attach(handed, "vu", "I", "2", upstream);
                session.expression("EXPR.0000000000000f02", binary(">",
                        symbol("vu", "I"), integer("I", 1L)));
                session.decision(PRODUCER, "nn#u1", true,
                        "EXPR.0000000000000f02");
            }
            session.expression("EXPR.0000000000000f03", constant("true"));
            session.export(producer, "EXPR.0000000000000f03", 2L, "true");
            session.attach(consumer, "vh", "true", producer);
            session.expression("EXPR.0000000000000f04", symbol(MARKER, "Z"));
            session.decision(ANCHOR, "dn#u1", flip, "EXPR.0000000000000f04");
            session.target("vh", true, true);
            session.write();
        }
        Composer.Composition composition = compose(iteration, 8);
        Map<String, String> selectorOf = new LinkedHashMap<String, String>();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            selectorOf.put(disjunct.path().sessionId, disjunct.selector());
        }
        String nested = null;
        for (String arm : composition.armSelectors()) {
            if (ordinal(arm).equals(ordinal(selectorOf.get("s0")))
                    && composition.arm(arm).attachEndpointIds()
                    .contains(handed.id())) {
                nested = arm;
            }
        }
        assertNotNull("s1's arm on the seed's path has its nested family: "
                + composition.armSelectors(), nested);
        String[][] rows = {
                {"s0", null, "sat"},
                {"s0", "(not (= vu 2))", "sat"},
                {"s0", nested, "unsat"},
                {"s1", null, "sat"},
                {"s1", "(not (= vu 2))", "unsat"}};
        for (String[] row : rows) {
            String answer = solver().ask(composition.pathQuery(
                    selectorOf.get(row[0]), row[1] == null
                            ? Collections.<String>emptyList()
                            : Collections.singletonList("(assert "
                            + row[1] + ")")), null, false).status();
            assertEquals(Arrays.toString(row), row[2], answer);
        }
        // Each path's own run is its own session's delivery of the message
        // it received, which Disjunction asks under first.
        for (Map.Entry<String, String> path : selectorOf.entrySet()) {
            List<String> own = composition.ownRun(path.getValue());
            assertEquals(path.getKey() + ": " + own, 1, own.size());
            String arm = own.get(0).replace("(assert ", "")
                    .replace(")", "");
            assertEquals(path.getKey(), path.getKey(),
                    composition.arm(arm).sessionId());
        }
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
        // by name.  So does a cell copied through the very owner asking for
        // it ({@code new Block(b)} where b may be the copy: a40h2
        // FsDatasetImpl-1092), which once recursed until the heap was full.
        // A target a helper decision decided stands at that decision, before
        // the reads the guard then made (`f == null ? -1 : f.count`): they
        // are still phi's, so the owner still moves -- 3 is still no
        // witness, the run's cell kept under the other writer's flag.
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
                {7L, "late", ClaimKind.NO_SUPPORTED_WITNESS},
                {7L, "copied", ClaimKind.NO_SUPPORTED_WITNESS},
                {3L, "decided", ClaimKind.NO_SUPPORTED_WITNESS},
                {7L, "decided", ClaimKind.STATE_PAIRING_FLIPPED}}) {
            long generation = (Long) each[0];
            String row = generation + " " + each[1];
            boolean decided = "decided".equals(each[1]);
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
                    : "written".equals(each[1]) || "copied".equals(each[1])
                    || decided ? 1 : 0); index++) {
                session.write(Endpoint.of(theirs, "Commit#init#3:WRITE",
                        at("generation#" + index, 0), 0), other, ++version,
                        "copied".equals(each[1]) ? "EXPR.v1.copied"
                                : "EXPR.v1.generation");
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
            long latestRead = session.read(Endpoint.of(reader,
                    "Stream#latest#6:READ", at("read#1", 0), 0), latest,
                    stored, SmtLowering.locationKey(latest) + "@v" + stored
                            + "@s0", "L", null);
            session.read(Endpoint.of(reader, "Stream#flag#7:READ",
                    at("read#2", 0), 0), flag, flagged,
                    SmtLowering.locationKey(flag) + "@v" + flagged + "@s0",
                    "Z", null);
            // The VM's pair: concreteValue is the run's cell, 11#24.
            JsonObject owner = read("INSTANCE_FIELD", 8L, 48L, stored, "L");
            owner.addProperty("readEventId", latestRead);
            JsonObject generationThroughOwner = fieldRead(commit, 24L, "I",
                    owner, read("INSTANCE_FIELD", 11L, 24L, constructed, "I"));
            session.expression("EXPR.v1.copied", generationThroughOwner);
            session.expression("EXPR.00000000000000f1", binary(">",
                    generationThroughOwner, integer("I", 4L)));
            session.expression("EXPR.00000000000000f2", read("INSTANCE_FIELD",
                    8L, 56L, flagged, "Z"));
            if (decided) {
                session.targetAt(latestRead - 1,
                        "(and EXPR.00000000000000f1 EXPR.00000000000000f2)",
                        false, true);
            } else {
                session.target(
                        "(and EXPR.00000000000000f1 EXPR.00000000000000f2)",
                        false, true);
            }
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
                        + SmtLowering.locationKey(other) + "@s0")
                        && gap.detail().contains("LoweringCycle")
                        == "copied".equals(each[1]);
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
            if ((Boolean) path[1]) lowering.movable(corpus.read("s0", "kc@s0"));
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
     * What the lowering states of a value it hands the container codec stays
     * stated: a String keeps its nullness (hdfs-adhoc-19: the blockPoolId a
     * FinalizeCommand taken from the command list holds, recorded as a
     * String, reached String.equals as of unknown nullness and was
     * refused), and an object a cell stores, a list included, is its
     * reference (hdfs-adhoc-33: bpStorageDirMap.put(bpid, dirs) with a list
     * the VM placed unnamed was cut, CannotBox, and so was every read of
     * that version).
     */
    @Test
    public void aValueKeepsWhatItsLoweringStatesAcrossTheCodec() {
        JsonObject commands = relation("INDEXED", "READ", "L",
                relation("INDEXED", "SNAPSHOT_BASE", "java/util/ArrayList",
                        null), integer("I", 0L));
        JsonObject blockPool = fieldRead(
                "org/apache/hadoop/hdfs/server/protocol/FinalizeCommand", 32L,
                commands, vmLeaf("ConStringSymbolExp", "Y_L'String'_BP-1",
                        "java/lang/String"));
        Object[][] rows = {
            {"a recorded String a field read hands String.equals",
                    vmString("equals", symbol("s", "Ljava/lang/String;"),
                            blockPool)},
            {"a list the VM placed unnamed, stored in a map",
                    stored(symbol("P_L'java/util/ArrayList'_",
                            "java/util/ArrayList"))},
            {"a list the VM named, stored in a map",
                    stored(symbol("M_L'java/util/ArrayList'_7",
                            "java/util/ArrayList"))},
        };
        for (Object[] row : rows) {
            Map<String, VmTermLowering.Sort> declared =
                    new LinkedHashMap<String, VmTermLowering.Sort>();
            declared.put("s", VmTermLowering.Sort.STRING);
            SmtLowering lowering = new SmtLowering(declared);
            lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
            lowering.dispatch((JsonObject) row[1], VmTermLowering.Sort.BOOL,
                    "test");
            List<String> refused = lowering.openRefusals();
            lowering.end();
            assertTrue(row[0] + ": " + refused, refused.isEmpty());
        }
    }

    /** Whether key 5 of a map that stores {@code value} there is null. */
    private static JsonObject stored(JsonObject value) {
        JsonObject put = relation("ASSOCIATIVE", "PUT", "java/util/Map",
                relation("ASSOCIATIVE", "SNAPSHOT_BASE", "java/util/HashMap",
                        null), integer("I", 5L), value);
        return binary("==", relation("ASSOCIATIVE", "READ",
                "java/util/ArrayList", put, integer("I", 5L)), vmNull());
    }

    /**
     * What a read recorded, as a flip query holds it: a literal, else the
     * object's identity, non-null and the one COMPOSE names it by
     * (hdfs-adhoc-07 HF3: jn0's {@code BestEffortLongFile.ch} was no value
     * and refused four flips); nothing for what is neither.
     */
    @Test
    public void aRecordedValueIsItsLiteralElseItsObjectsIdentity() {
        SmtLowering lowering = new SmtLowering(
                new LinkedHashMap<String, VmTermLowering.Sort>());
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        String channel = lowering.recordedValue(
                "M_L'sun/nio/ch/FileChannelImpl'_860", "Ref");
        assertTrue(channel, channel.startsWith("identity__"));
        assertEquals(channel, lowering.recordedValue(
                "M_L'sun/nio/ch/FileChannelImpl'_860", "Ref"));
        assertTrue(lowering.facts(Collections.singletonList(channel))
                .contains("(not (= " + channel + " nullRef))"));
        assertEquals("nullRef", lowering.recordedValue(
                VmExpressionIr.SYMBOLIC_NULL, "Ref"));
        assertEquals("7", lowering.recordedValue("7", "Int"));
        assertEquals("", lowering.recordedValue("some_symbol", "Ref"));
        lowering.end();
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
     * An object the VM placed unnamed ({@code P_L'class'_}) is non-null, as
     * a named one is: a lookup that returned it is no null in any model.
     */
    @Test
    public void aPlacedObjectIsNonNull() {
        SmtLowering lowering = new SmtLowering(
                new LinkedHashMap<String, VmTermLowering.Sort>());
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        String test = lowering.dispatch(binary("==",
                symbol("P_L'org/apache/zookeeper/server/DataNode'_",
                        "org/apache/zookeeper/server/DataNode"), vmNull()),
                VmTermLowering.Sort.BOOL, "test").text;
        lowering.end();
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        List<String> facts = lowering.facts(Collections.singletonList(test));
        assertTrue(test + " " + facts, facts.size() == 1
                && facts.get(0).matches("\\(not \\(= identity__\\w+ nullRef\\)\\)")
                && test.contains(facts.get(0).substring(8, 8 + 20)));
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
            owner.addProperty("readEventId", session.read(Endpoint.of(reader,
                    "Wrapper#getAndSave#3:READ", at("kc#3", 0), 0), known,
                    6L, "kc", "Ljava/util/Map;", null));
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
                        RootKind.CLOCK, RootCategory.CLOCK, "1000", null, null, true, Clock.of(1L, Clock.MONOTONIC), 0L));
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
                "ROOT.RESERVED", RESERVED, RootKind.CLOCK, RootCategory.CLOCK,
                Long.toString(seed - 1_000L), null, null, true, Clock.of(1L, Clock.MONOTONIC), 0L));
        // As the VM publishes it: an arithmetic node states no Java type,
        // and the deadline is a Long cell by its width alone.
        JsonObject deadline = binary("+", symbol(RESERVED, "J"),
                integer("J", 6_000L));
        JsonObject reserved = relation("ASSOCIATIVE", "PUT", "java/util/Map",
                relation("ASSOCIATIVE", "SNAPSHOT_BASE",
                        "java/util/concurrent/ConcurrentHashMap", null),
                integer("J", 5L), deadline);
        session.expression("EXPR.00000000000000e1", reserved);
        session.write(Endpoint.of(reserver, "Map#merge#1:WRITE",
                at("reserve#1", 0), 0), reserves, 70L,
                "EXPR.00000000000000e1");
        session.roots.add(RootMintRow.of(id, ++session.seq, newer,
                "ROOT.RESERVE", NANO, RootKind.CLOCK, RootCategory.CLOCK, Long.toString(
                        expired ? seed + 10_000L : seed), null, null, true,
                Clock.of(1L, Clock.MONOTONIC), 0L));
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
        long reference = session.read(Endpoint.of(reader,
                "Wrapper#getAndSave#3:READ", at("kc#3", 0), 0), known,
                stored, "kc@" + id, "Ljava/util/Map;", "M_L'" + map + "'_30");
        JsonObject query = relation("ASSOCIATIVE", "READ", "L", six,
                integer("J", 5L));
        JsonObject owner = read("INSTANCE_FIELD", 8L, 16L, stored,
                "Ljava/util/Map;");
        owner.addProperty("readEventId", reference);
        query.add("owner", owner);
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
     * Writers_W(l)'s writer at version 0, the location's INITIAL: a read
     * that observed a later write may have run before every write it
     * followed.  Each of those an HB-concurrent occurrence's, the INITIAL is
     * an arm, and a map lookup at the anchor asked of the state before the
     * put reaches the fatal the run's state did not (hdfs a40 V4h-2: the
     * block pool looked up before the DataNode registered it).  A write
     * made under construction -- in a constructor, or in a method one
     * called on the writer's own thread -- or one the reader's own thread
     * made before it, no read precedes; nor one past a version a read saw
     * that no row states.  A thread a constructor started is not under it.
     */
    @Test
    public void theInitialIsTheWriterAtVersionZero() throws Exception {
        String map = "java/util/concurrent/ConcurrentHashMap";
        LocationId pools = LocationId.of(LocationKind.MAP, "21", "-3");
        for (String variant : new String[]{"concurrent", "constructor",
                "constructor-caller", "started-in-constructor", "own-thread",
                "unrowed-between"}) {
            boolean moves = "concurrent".equals(variant)
                    || "started-in-constructor".equals(variant);
            long observed = "unrowed-between".equals(variant) ? 3L : 2L;
            Path iteration = folder.newFolder("initial-" + variant).toPath();
            OccurrenceAddress reader = occurrence("case/dn0", "REGION.get",
                    CausalContext.of(Role.of("CLIENT"), "", 1),
                    frame("Test#get#4", 0));
            OccurrenceAddress writer = occurrence("case/dn0",
                    "REGION.register", CausalContext.of(
                            Role.of("BP_SERVICE_ACTOR"), "", 1),
                    frame("Actor#register#2", 0));
            Session session = new Session(iteration, "s0", false);
            session.occurrence = reader;
            session.activation(reader);
            session.activation(writer, "own-thread".equals(variant)
                    ? "thread#" + reader.regionId()
                    : "thread#" + writer.regionId(), false);
            JsonObject base = relation("ASSOCIATIVE", "SNAPSHOT_BASE", map,
                    null);
            JsonObject put = putCommit(base, 5L);
            session.expression("EXPR.0000000000000010", base);
            session.expression("EXPR.0000000000000011", put);
            session.writes.add(WriteRow.initial("s0", ++session.seq,
                    Endpoint.of(writer, "Pools#add#3:INITIAL", at("w#0", 0),
                            0), pools, 1L, "EXPR.0000000000000010", "L"));
            List<Frame> chain = new ArrayList<Frame>();
            if ("constructor-caller".equals(variant)) {
                chain.add(Frame.of("<Pools: void <init>()>", 0));
            } else if ("started-in-constructor".equals(variant)) {
                chain.add(Frame.of("<Pools: void <init>()>", 0));
                chain.add(Frame.of("<Pools$1: void run()>", 0));
            }
            chain.add(Frame.of("w#1", 0));
            session.write(Endpoint.of(writer, "constructor".equals(variant)
                            ? "Pools#<init>()V#3:WRITE" : "Pools#add#3:WRITE",
                    ExecutionIndex.of(chain), 0), pools, observed,
                    "EXPR.0000000000000011");
            if ("unrowed-between".equals(variant)) {
                session.read(Endpoint.of(writer, "Pools#size#7:READ",
                        at("w#2", 0), 0), pools, 2L, "MAP_STATE/21#-3@v2@s0",
                        "L", null);
            }
            JsonObject answered = read("MAP_STATE", 21L, -3L, observed, "L");
            answered.getAsJsonObject("observedVersion").add("expression",
                    relation("ASSOCIATIVE", "READ", "L", put,
                            integer("J", 5L)));
            Endpoint asking = Endpoint.of(reader, "Pools#get#5:READ",
                    at("r#1", 0), 0);
            answered.addProperty("readEventId", session.read(asking, pools,
                    observed, "MAP_STATE/21#-3@v" + observed + "@s0", "L",
                    null));
            session.expression("EXPR.0000000000000060", binary("==",
                    answered, vmNull()));
            session.target("EXPR.0000000000000060", false, true);
            session.write();

            edu.uva.liftlab.graphchecker.smt.Arms arms =
                    new edu.uva.liftlab.graphchecker.smt.Arms(
                            Corpus.read(iteration, null));
            assertEquals(variant, moves ? 2 : 1, arms.stateArms(asking, "s0",
                    SmtLowering.locationKey(pools), observed, true).size());
            Composer.Composition composition = compose(iteration, reader, 4,
                    StaticScopeMap.empty());
            assertEquals(variant + ": " + composition.body(), moves,
                    composition.body().contains("state_family__"));
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            assertEquals(variant + ": " + decision.claim().gaps(), moves,
                    decision.claim().kind() == ClaimKind.STATE_PAIRING_FLIPPED);
        }
    }

    /**
     * ONE re-pairing rule: a read the selected session's world planted a
     * pairing on is re-paired as the anchor's reads are, away from the
     * anchor (hdfs-bugs-slowdisk-zero: the detector turn's read of the
     * exclusion bound, paired to its INITIAL ahead of the reconfiguration).
     * Its family offers the plant (1) and the reconfiguration's write (0);
     * the turn's guard {@code bound > 0} binds to it; the turn's store is
     * what the anchor's read pairs with; the fatal is SAT under the plant
     * and UNSAT under the recording's arm, so the recording decides it: a
     * STATE_PAIRING_FLIPPED whose re-paired arm is the INITIAL.  The same
     * session in a world that planted nothing names no mechanism.  Where
     * the turn also read a version no row wrote, its observed arm holds the
     * reads to what the plant gave them: no recording's pairing either, so a
     * witness resting on it is a STATE_PAIRING_FLIPPED too.
     */
    @Test
    public void aWorldPlantedPairingIsRePairedAsTheAnchorsReadsAre()
            throws Exception {
        LocationId bound = LocationId.of(LocationKind.INSTANCE, "1", "48");
        LocationId list = LocationId.of(LocationKind.INSTANCE, "1", "88");
        OccurrenceAddress writer = occurrence("case/dn0", "REGION.write",
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 1),
                frame("Volumes#choose#4", 0));
        OccurrenceAddress turn = occurrence("case/dn0", "REGION.turn",
                CausalContext.of(Role.of("WAKE"), "", 1),
                frame("Detector#run#2", 0));
        OccurrenceAddress reconf = occurrence("case/dn0", "REGION.reconf",
                CausalContext.of(Role.of("CLIENT"), "", 1),
                frame("Test#reconf#7", 0));
        Endpoint guard = Endpoint.of(turn, "Detector#bound#3:READ",
                at("g#1", 0), 0);
        Endpoint asking = Endpoint.of(writer, "Volumes#excluded#5:READ",
                at("r#1", 0), 0);
        Endpoint unrowed = Endpoint.of(turn, "Detector#bound#4:READ",
                at("g#2", 0), 0);
        // planted?, the reconfiguration writes under construction?, the turn
        // also reads a version no row wrote?, the claim: a planted read is
        // admitted by the anchor's test, so a write no read could have
        // preceded leaves it the run's; where no pairing is the mechanism,
        // the satisfiable formula is its own claim (FORMULA_SAT)
        Object[][] table = {
                {true, false, false, ClaimKind.STATE_PAIRING_FLIPPED},
                {false, false, false, ClaimKind.FORMULA_SAT},
                {true, true, false, ClaimKind.FORMULA_SAT},
                {true, false, true, ClaimKind.STATE_PAIRING_FLIPPED},
        };
        for (Object[] row : table) {
            boolean planted = (Boolean) row[0];
            boolean constructing = (Boolean) row[1];
            boolean second = (Boolean) row[2];
            Path iteration = folder.newFolder("planted-" + planted + "-"
                    + constructing + "-" + second).toPath();
            for (boolean explored : new boolean[]{false, true}) {
                String id = explored ? "s1" : "s0";
                Session session = new Session(iteration, id, explored);
                session.occurrence = writer;
                session.activation(writer);
                session.activation(turn);
                session.activation(reconf);
                session.expression("EXPR.0000000000000001", integer("I", 1));
                session.expression("EXPR.0000000000000000", integer("I", 0));
                session.expression("EXPR.0000000000000007", integer("I", 7));
                session.writes.add(WriteRow.initial(id, ++session.seq,
                        Endpoint.of(turn, "Detector#bound#3:INITIAL",
                                at("g#0", 0), 0), bound, 1L,
                        "EXPR.0000000000000001", "I"));
                session.writes.add(WriteRow.initial(id, ++session.seq,
                        Endpoint.of(writer, "Volumes#excluded#5:INITIAL",
                                at("r#0", 0), 0), list, 3L,
                        "EXPR.0000000000000000", "I"));
                Endpoint set = Endpoint.of(reconf, "Metrics#set#5:WRITE",
                        ExecutionIndex.of(constructing ? Arrays.asList(
                                Frame.of("<Metrics: void <init>()>", 0),
                                Frame.of("w#1", 0))
                                : Collections.singletonList(
                                Frame.of("w#1", 0))), 0);
                // The recording: the reconfiguration's 0 before the turn
                // read it.  The world: the turn first, held to the INITIAL.
                if (!explored) session.write(set, bound, 2L,
                        "EXPR.0000000000000000");
                long seen = explored ? 1L : 2L;
                JsonObject read = read("INSTANCE_FIELD", 1L, 48L, seen, "I");
                read.getAsJsonObject("observedVersion").add("expression",
                        integer("I", explored ? 1L : 0L));
                read.addProperty("readEventId", session.read(guard, bound,
                        seen, "INSTANCE_FIELD/1#48@v" + seen + "@" + id, "I",
                        explored ? "1" : "0"));
                JsonObject guarded = binary(">", read, integer("I", 0L));
                if (second) {
                    JsonObject other = read("INSTANCE_FIELD", 1L, 48L, 9L,
                            "I");
                    other.addProperty("readEventId", session.read(unrowed,
                            bound, 9L, "INSTANCE_FIELD/1#48@v9@" + id, "I",
                            "5"));
                    guarded = binary("&&", guarded, binary(">", other,
                            integer("I", 0L)));
                }
                session.expression("EXPR.0000000000000010", guarded);
                session.decision(turn, "Detector#u63", explored,
                        "EXPR.0000000000000010");
                long listed = 3L;
                if (explored) {
                    session.write(set, bound, 2L, "EXPR.0000000000000000");
                    session.write(Endpoint.of(turn, "Detector#run#9:WRITE",
                                    at("w#2", 0), 0), list, 4L,
                            "EXPR.0000000000000007");
                    listed = 4L;
                }
                JsonObject excluded = read("INSTANCE_FIELD", 1L, 88L, listed,
                        "I");
                excluded.getAsJsonObject("observedVersion").add("expression",
                        integer("I", explored ? 7L : 0L));
                excluded.addProperty("readEventId", session.read(asking, list,
                        listed, "INSTANCE_FIELD/1#88@v" + listed + "@" + id,
                        "I", explored ? "7" : "0"));
                session.expression("EXPR.0000000000000060",
                        binary("==", excluded, integer("I", 7L)));
                session.target("EXPR.0000000000000060", explored, true);
                session.write();
            }
            obligation(iteration, "s1", Collections.<String, String>emptyMap(),
                    "Detector#u63", Collections.<String>emptyList(), planted
                            ? Collections.singletonMap(Confirmation.id(guard),
                            Confirmation.INITIAL)
                            : Collections.<String, String>emptyMap());
            Composer.Composition composition = compose(iteration, writer, 4,
                    StaticScopeMap.empty());
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            String detail = "planted " + planted + ", constructing "
                    + constructing + ", second " + second + ": "
                    + decision.claim().gaps() + "\n" + composition.body();
            assertEquals(detail, row[3], decision.claim().kind());
            if (!planted || constructing) continue;
            assertTrue(detail, decision.claim().polarityDecides());
            ClaimPolicy.Outcome witness = decision.outcomes().get(
                    decision.claim().valuationOrdinal());
            List<String> groups = new ArrayList<String>();
            for (String arm : composition.repaired(witness.selected()
                    .selector(), witness.selectedArms().keySet())) {
                groups.add(composition.arm(arm).groupId());
            }
            // The plant, or the observed arm that holds the reads to it.
            assertEquals(detail, 1, groups.size());
            assertTrue(detail, groups.get(0).equals("INITIAL|"
                    + SmtLowering.locationKey(bound)) || second
                    && groups.get(0).equals("observed:"
                    + SmtLowering.locationKey(bound)));
            // The recording's pairing there is any arm but the plant: the
            // reconfiguration's arm, taken, re-pairs nothing.
            List<String> recording = new ArrayList<String>();
            for (String arm : composition.armSelectors()) {
                if (reconf.id().equals(composition.arm(arm).groupId())
                        && arm.contains("__" + ordinal(witness.selected()
                        .selector()) + "__")) {
                    recording.add(arm);
                }
            }
            assertEquals(detail, 1, recording.size());
            assertEquals(detail, Collections.emptyList(), composition.repaired(
                    witness.selected().selector(), recording));
        }
    }

    /**
     * The recorded arm is the pairing the run took, or there is none and the
     * claim is blocked by name.  (a) The observed writer wrote again after
     * the read: its arm is the write read, not the later one.  (b) Two reads
     * of one location saw two writes, which no writer arm is (each binds
     * both reads), and (p) a second read saw a version no row wrote: the
     * pins' arm, holding each read to its own join or pin, is the run,
     * whichever read came first.  (c) The one writer read has a block
     * stretched to its write of another location the run read from
     * another writer (and its body rests on a decision nothing states):
     * its selector would force that location's value too, so it is no arm
     * of the run, which is held by the pins' arm -- the run as recorded is
     * a world of the formula (hdfs-adhoc-16 HG5A).
     */
    @Test
    public void theRecordedArmIsTheWriteReadOrThePinsArm()
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
            assertFalse(shape + ": an arm is the recorded pairing",
                    composition.recordedPairings().isEmpty());
            assertEquals(shape + ": the pins' arm iff no writer's arm is "
                            + "the run", !"a".equals(shape),
                    composition.body().contains("observed_arm__"));
            assertFalse(shape + ": nothing blocks the claim " + decision
                    .claim().gaps(), decision.claim().blocked());
            assertEquals(shape + ": the run as it happened is healthy",
                    "unsat", decision.outcomes().get(0).answer().status());
            assertEquals(shape, ClaimKind.STATE_PAIRING_FLIPPED,
                    decision.claim().kind());
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
        // Each asked beside the marker, which moves: a condition over
        // nothing a witness moves is left out (Independence).
        session.decision(ANCHOR, "anchor#u4", true,
                "(and EXPR.00000000000000d1 " + MARKER + ")");
        session.decision(ANCHOR, "anchor#u5", true,
                "(and EXPR.00000000000000d2 " + MARKER + ")");
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
        // (`allKeys.values().toArray(...)`, one element per position).  The
        // snapshot's three members, in the order its table iterates them,
        // which is NOT the ascending one: what a traversal hands back is
        // the map's business and "ascending ints" is not a fact any
        // recording of a HashMap states.
        JsonObject held = snapshotBase("java/util/HashMap", "HASH", 3);
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
        // And phi reads the array cell the decision above compares.  That
        // cell holds what the store wrote, which nothing moves, so the
        // decision over it holds in every world and is left out
        // (Independence): phi's own read is the element read asked below.
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
                composition.body().contains(" 2)) 6)"));
        assertFalse("a decision over a cell nothing moves is left out",
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
        Set<String> reached = lowering.reachedSymbols(
                Collections.singletonList(guard));
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

    /**
     * A VIEW'S POSITION IS THE RUN'S ITERATION COUNT, and the chain states
     * it only where the chain's order is the one the map's class iterates
     * in (SOLR-18413 r9: a LinkedHashMap snapshot stated in hash order keyed
     * a lookup at another key).  The VM's snapshot states its members in
     * their iteration order and says which order that is; an
     * insertion-ordered class iterates in the chain's order after it; a
     * hash-ordered one keeps it through removals and updates, and a put of
     * another key may rebin it; a recording that states no order has none.
     * Where the order is not stated the positions are still a bijection
     * with the keys, in no order: position 0 may name the last key put, and
     * the map is named DIAGNOSTIC with why.  {order, members, program
     * mutations above the members (a negative removes that key), why the
     * chain does not state the order ("" it does)}.
     */
    @Test
    public void aViewPositionIsTheOrderItsClassIteratesIn() {
        Object[][] rows = {
                {"INSERTION", 2, new long[]{3L}, ""},
                {"HASH", 2, new long[]{}, ""},
                {"HASH", 2, new long[]{1L}, ""},
                {"HASH", 3, new long[]{-1L}, ""},
                {"HASH", 2, new long[]{-1L, 1L}, "HASH_INSERT"},
                {"HASH", 2, new long[]{3L}, "HASH_INSERT"},
                {"", -1, new long[]{1L, 2L}, "UNRECORDED"},
                {"HASH", 0, new long[]{3L, 4L}, "HASH_INSERT"}};
        for (Object[] row : rows) {
            int members = (Integer) row[1];
            JsonObject state = snapshotBase("java/util/HashMap",
                    (String) row[0], members);
            List<Long> keys = new ArrayList<Long>();
            for (long key = 1L; key <= Math.max(members, 0); key++) {
                state = relation("ASSOCIATIVE", "PUT", "java/util/HashMap",
                        state, integer("I", key), integer("I", key));
                keys.add(key);
            }
            for (long key : (long[]) row[2]) {
                state = key < 0L
                        ? relation("ASSOCIATIVE", "REMOVE",
                        "java/util/HashMap", state, integer("I", -key))
                        : relation("ASSOCIATIVE", "PUT", "java/util/HashMap",
                        state, integer("I", key), integer("I", key));
                if (key < 0L) {
                    keys.remove(Long.valueOf(-key));
                } else if (!keys.contains(key)) {
                    keys.add(key);
                }
            }
            SmtLowering lowering = new SmtLowering(
                    Collections.<String, VmTermLowering.Sort>emptyMap());
            lowering.begin("s0", SmtLowering.NO_JOIN, null);
            String view = lowering.dispatch(viewKey(state, 0), null, "view")
                    .text;
            assertEquals(java.util.Arrays.deepToString(row),
                    Collections.<String>emptyList(), lowering.openRefusals());
            List<String> facts = lowering.end();
            String why = (String) row[3];
            assertEquals(java.util.Arrays.deepToString(row),
                    why.isEmpty() ? Collections.<String>emptySet()
                            : Collections.singleton(ContainerSmtCodec
                            .ASSOC_VIEW_UNORDERED + ":" + why
                            + ":M_L'java/util/HashMap'_88 (java/util/HashMap)"
                            + "@s0"), lowering.diagnostics().keySet());
            String stated = why.isEmpty() ? "unsat" : "sat";
            assertEquals(java.util.Arrays.deepToString(row) + ": position 0 "
                            + "names the last key the chain put",
                    stated, answer(lowering, facts, "(= " + view + " "
                            + keys.get(keys.size() - 1) + ")"));
            assertEquals(java.util.Arrays.deepToString(row) + ": and the "
                            + "first", "sat", answer(lowering, facts,
                    "(= " + view + " " + keys.get(0) + ")"));
        }
    }

    /** What z3 answers a lowering's facts asked with one more question. */
    private String answer(SmtLowering lowering, List<String> facts,
                          String question) {
        List<String> asked = new ArrayList<String>();
        for (String fact : facts) asked.add(SmtNames.legalSymbols(fact));
        asked.add(SmtNames.legalSymbols(question));
        StringBuilder query = new StringBuilder(lowering.body(asked));
        for (String each : asked) {
            query.append("(assert ").append(each).append(")\n");
        }
        return solver().ask(query.toString(), null, false).status();
    }

    /** A snapshot's base, as the VM states its members' order and count;
     *  an empty order and a negative count are a recording that states
     *  neither. */
    private static JsonObject snapshotBase(String map, String order,
                                           int members) {
        JsonObject base = relation("ASSOCIATIVE", "SNAPSHOT_BASE", map,
                relation("ASSOCIATIVE", "STATE", map, symbol("M_L'" + map
                        + "'_88", map)));
        if (!order.isEmpty()) base.addProperty("order", order);
        if (members >= 0) base.addProperty("members", members);
        return base;
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
    public void aThreadOrdersItsOwnActivationsAndNothingElse()
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
        session.write(Endpoint.of(earlier, "Actor#put#3:WRITE",
                at("w#1", 0), 0), keys, 1L, "EXPR.v1.k");
        session.write(Endpoint.of(later, "Actor#put#4:WRITE",
                at("w#2", 0), 0), keys, 2L, "EXPR.v1.k");
        session.write(Endpoint.of(started, "Task#put#5:WRITE",
                at("w#3", 0), 0), keys, 3L, "EXPR.v1.k");
        session.target("true", false, true);
        session.write();

        edu.uva.liftlab.graphchecker.smt.Arms rule =
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null));
        assertFalse("two activations of one thread never interleave",
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
     * 1.79e12 "before" monotonic 4.5e9 made all 165 paths false).  Which
     * clock a cell reads is its row's statement, never its value's size.
     */
    @Test
    public void aNodeReadingTwoClocksOrdersEachClockOnItsOwn()
            throws Exception {
        Path iteration = folder.newFolder("two-clocks").toPath();
        Session session = new Session(iteration, "s0", false);
        String[][] cells = {
                {"CLOCK.wall.1", "M_J_wall_1", "1790500000000", Clock.WALL},
                {"CLOCK.mono", "M_J_mono", "1790500000400", Clock.MONOTONIC},
                {"CLOCK.wall.2", "M_J_wall_2", "1790500000900", Clock.WALL}};
        StringBuilder phi = new StringBuilder("(and");
        for (String[] cell : cells) {
            session.roots.add(RootMintRow.of("s0", ++session.seq, ANCHOR,
                    cell[0], cell[1], RootKind.CLOCK, RootCategory.CLOCK, cell[2], null, null,
                    true, Clock.of(1_000_000L, cell[3]), 0L));
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
        session.serial("5", "5", "8");
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
     * Constraint independence keeps what MOVES: a condition over nothing a
     * witness can move is left out, so one the composer cannot state -- a
     * substring of a block file's name, read from a tracked location -- does
     * not refuse the path (f4 visible-gs, sender-gs); the same condition over
     * the value phi reads, which the root moves, still does.  Java null is
     * no variable: every null check spells it alike, and sharing it kept 80
     * of the 145 conditions and reads of a SOLR-18406 path.  What a family
     * binds moves: a condition over an anchor handoff phi never names still
     * refuses (C1 review M2).  And sharing is no dependence: a condition
     * over a value that does not move, read where phi reads it, stays out
     * (SOLR-18413 r9: a closure over sharing kept 3479 conditions and
     * reads).
     */
    @Test
    public void aConditionPhiDoesNotRestOnDoesNotRefuseThePath()
            throws Exception {
        for (String shares : new String[]{"nothing", "location", "null",
                "handoff", "fixed"}) {
            boolean shared = "location".equals(shares)
                    || "handoff".equals(shares);
            boolean nulls = "null".equals(shares);
            Path iteration = folder.newFolder("independence-" + shares)
                    .toPath();
            Session session = new Session(iteration, "s0", false);
            session.serial("3", "0", "8");
            // What phi reads: a value the root moves, or one it does not.
            session.expression("EXPR.00000000000000a3", "fixed".equals(shares)
                    ? integer("I", 1001L)
                    : binary("-", symbol(SERIAL, "I"), integer("I", 1L)));
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
                    || "fixed".equals(shares)
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
                // Delivered by a producer the replay attests, so its family
                // binds it and no refusal of its own drops the path.
                Endpoint sender = Endpoint.of(PRODUCER, "Port#send#1:EXPORT",
                        at("send#1", 0), 0);
                session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
                        false, true);
                session.expression("EXPR.00000000000000a5",
                        integer("I", 5L));
                session.export(sender, "EXPR.00000000000000a5", "I", 1L, "5");
                session.attach(Endpoint.of(ANCHOR, "Port#recv#1:ATTACH",
                        at("recv#1", 0), 0), "vH_heard", "I", "5", sender);
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
     * node alike: JOIN, MINT, FREE or PIN, REFUSE; a refused join gives way
     * to the mint, else, where what it rests on can move, the read is FREE
     * and named with what it rests on ({@code SmtLowering#unbound}, a {@code
     * Composer.Concrete} FREE), else the pin.  One case per row:
     * <ul>
     *   <li>pin: the write refuses over nothing that moves, and the row
     *       states its value: the pin binds the read, and what the dropped
     *       join raised (its recorded reading, its cut) went with it;</li>
     *   <li>unstated: the same with no value stated: the path is refused,
     *       the join's refusal beside the read's;</li>
     *   <li>H1: the write is a call no lowering models over R, a declared
     *       root (the review's {@code parseInt(valueOf(R))} is R now,
     *       {@link #aMethodReturnIsItsCall}): the read is free, named with
     *       R, so phi {@code x != R} is satisfiable, a witness CONFIRM is to
     *       refute;</li>
     *   <li>H2a: the node's own projection lowers where the write refused:
     *       phi reads the projection, never the pinned constant;</li>
     *   <li>H2b: the write joins and a STATE family may re-pair the read,
     *       while the node's projection refuses: the read is free, named
     *       with the re-paired read it rests on;</li>
     *   <li>bound: the write refuses over a read of a field the reader
     *       alone writes, one of whose versions no row wrote (the VM's
     *       version bound dropped it): no read of it has another writer,
     *       so nothing moves and the pin binds (hdfs-17960 e1c);</li>
     *   <li>own: phi reads a version the reader wrote and one no row
     *       wrote: each arm would be one read's own pairing, with no
     *       HB-concurrent writer among them, so there is no family.</li>
     * </ul>
     */
    @Test
    public void theOneBindingRule() throws Exception {
        for (String name : new String[]{"pin", "unstated", "H1", "H2a",
                "H2b", "bound", "own"}) {
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
            LocationId field = LocationId.of(LocationKind.INSTANCE, "11",
                    "name");
            if ("bound".equals(name)) {
                // The reader parsed it: wrote v6, read it, then read v7,
                // whose write the bound dropped.
                refused = binary("+", read("INSTANCE_FIELD", field.owner(),
                        "name", 7L, "I"), unmodeled);
                session.expression("EXPR.00000000000000b4",
                        integer("I", 6L));
                session.write(Endpoint.of(reader, "Parser#end#7:WRITE",
                        at("w#3", 0), 0), field, 6L, "EXPR.00000000000000b4");
                for (long seen : new long[]{6L, 7L}) {
                    session.read(Endpoint.of(reader, "Parser#get#8:READ",
                                    at("r#" + seen, 0), 0), field, seen,
                            SmtLowering.locationKey(field) + "@v" + seen
                                    + "@s0", "I", Long.toString(seen));
                }
            }
            session.expression("EXPR.00000000000000b1", "H1".equals(name)
                    ? parsed : "H2b".equals(name) || "own".equals(name)
                    ? integer("I", 2L) : refused);
            session.write(Endpoint.of("own".equals(name) ? reader : first,
                    "TickA#set#4:WRITE", at("w#1", 0), 0), stamp, 2L,
                    "EXPR.00000000000000b1");
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
            long stamped = session.read(Endpoint.of(reader,
                            "Block#getStamp#29:READ", at("r#1", 0), 0),
                    stamp, 2L, symbol, "I",
                    "unstated".equals(name) ? null : "H1".equals(name) ? "3"
                            : "H2b".equals(name) || "own".equals(name) ? "2"
                            : "1001");
            JsonObject node = read("INSTANCE_FIELD", stamp.owner(), "value",
                    2L, "I");
            node.addProperty("readEventId", stamped);
            // own: then a version no row wrote, which phi compares with it.
            JsonObject later = read("INSTANCE_FIELD", stamp.owner(), "value",
                    9L, "I");
            later.add("concreteValue", integer("I", 9L));
            if ("own".equals(name)) {
                session.read(Endpoint.of(reader, "Block#getStamp#31:READ",
                                at("r#9", 0), 0), stamp, 9L,
                        key + "@v9@s0", "I", "9");
            }
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
                        "H2b".equals(name) || "own".equals(name) ? 2L
                                : 1001L));
            }
            session.expression("EXPR.00000000000000b3", binary(
                    "H1".equals(name) ? "!=" : "<", node, "own".equals(name)
                            ? later : symbol(SERIAL, "I")));
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
                    // what the join reads, through the expressions (M1).
                    Corpus explore = Corpus.read(iteration, null);
                    SmtLowering.Lowered explored = explore.lowering("s0")
                            .lower("EXPR.00000000000000b3");
                    assertFalse(name + ": no flip over the pin: " + explored,
                            explored.ok());
                    assertTrue(name + ": the join is still reached",
                            explore.expressionSymbols("s0",
                                    "EXPR.00000000000000b3")
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
                    assertEquals(name + ": the read is free", 1,
                            composition.disjuncts().size());
                    assertEquals(name + ": named with the root it rests "
                                    + "on: " + concrete(composition),
                            Collections.singletonList("FREE " + key
                                    + "@2= " + Collections.singletonList(
                                    SERIAL)), concrete(composition));
                    assertTrue(name + ": so the formula is satisfiable, a "
                                    + "witness CONFIRM is to judge",
                            ClaimPolicy.decide(composition, solver())
                                    .claim().kind()
                                    != ClaimKind.NO_SUPPORTED_WITNESS);
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
                case "bound":
                    assertEquals(name + ": no read of the field has another "
                                    + "writer, so the pin binds", 1,
                            composition.disjuncts().size());
                    assertTrue(name + ": phi reads the pinned symbol: " + arm,
                            arm.contains(SmtNames.legalSymbols(
                                    "(= " + symbol + " 1001)")));
                    break;
                case "own":
                    assertEquals(name + ": the path stands", 1,
                            composition.disjuncts().size());
                    assertFalse(name + ": arms that are each a read's own "
                                    + "pairing are no family: "
                                    + composition.body(),
                            composition.body().contains("state_family__")
                                    || composition.body().contains(
                                    "observed_arm__"));
                    break;
                default:
                    assertEquals(name + ": the read is free", 1,
                            composition.disjuncts().size());
                    assertEquals(name + ": named with the re-paired read "
                                    + "it rests on: " + concrete(composition),
                            Collections.singletonList("FREE " + key
                                    + "@2= [read " + key + "@2]"),
                            concrete(composition));
            }
        }
    }

    /** What a composition rests on concretely, one "KIND subject=value
     *  [movesWith]" each. */
    private static List<String> concrete(Composer.Composition composition) {
        List<String> rows = new ArrayList<String>();
        for (Composer.Concrete row : composition.concrete()) {
            rows.add(row.kind + " " + row.subject + "=" + row.value + " "
                    + row.movesWith);
        }
        return rows;
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
     *   <li>moving: the same over R is a free value, named with R: a pin
     *       would carry a moved R through the call as a constant;</li>
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
            boolean composed = !"no-call".equals(name);
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
                assertEquals(name + ": free, named with the root it rests on",
                        Collections.singletonList("FREE call:" + RETURNED
                                + "= " + Collections.singletonList(
                                SERIAL)), concrete(composition));
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
     * undecided until the guard went inside the lambdas.  And a query that
     * reads no map's order gets maps that keep none, with no lambda at all
     * (hdfs-11741 L1: two fatal-observing paths still undecided).  {what the
     * state shows, the guard side that contradicts it, whether it reads the
     * order}.
     */
    @Test
    public void aGuardedRemovalIsDecided() {
        Z3 solver = solver();
        String empty = "(mkAssocState 0 ((as const (Array Value Bool)) false)"
                + " ((as const (Array Value Value)) (VRef nullRef))"
                + " ((as const (Array Int Value)) (VRef nullRef))"
                + " ((as const (Array Value Int)) (- 1)))";
        String states = "\n(declare-const x Int)"
                + "\n(define-fun s () AssocState (assoc_remove_if"
                + " (assoc_put (assoc_put " + empty
                + " (VInt 1) (VInt 10)) (VInt 2) (VInt 20))"
                + " (VInt 1) (< x 5)))"
                + "\n(define-fun grown () AssocState"
                + " (assoc_put s (VInt 3) (VInt 30)))\n";
        String[][] cases = {
            {"(= (assoc_key_at grown 0) (VInt 2))", "(>= x 5)", "true"},
            {"(= (assoc_position_of grown (VInt 3)) 1)", "(>= x 5)", "true"},
            {"(= (assoc_size grown) 3)", "(< x 5)", "false"},
            {"(not (assoc_has grown (VInt 1)))", "(>= x 5)", "false"},
        };
        for (String[] shown : cases) {
            String asked = states + "(assert " + shown[0] + ")";
            String query = String.join("\n", SmtNames.reachedPreamble(
                    VmTermLowering.preamble(),
                    Collections.singletonList(asked))) + asked;
            assertEquals("a lambda only where the order is read: " + shown[0],
                    Boolean.parseBoolean(shown[2]), query.contains("lambda"));
            Z3.Answer holds = solver.ask(query,
                    Collections.<String>emptyList(), false);
            assertTrue("decided with the guard free: " + shown[0] + " "
                    + holds.status(), holds.decided() && holds.sat());
            Z3.Answer refuted = solver.ask(query + "\n(assert " + shown[1]
                    + ")", Collections.<String>emptyList(), false);
            assertTrue("and only on its own side: " + shown[1] + " "
                    + refuted.status(), refuted.decided() && !refuted.sat());
        }
    }

    /**
     * A stream's stated result (VM SymStream) lowers as its chain: a guarded
     * append or put is there exactly where its guard holds, a PIN's guard is
     * required wherever its state is lowered, and a list's contains is a
     * disjunction over the positions its chain can fill -- refused by name
     * over a chain with no exact base.  {asked, sat?}.
     */
    @Test
    public void aStreamsStatedResultLowersAsItsChain() {
        Z3 solver = solver();
        JsonObject n = vmLeaf("SymbolExpression", "n", "I");
        JsonObject root = relation("INDEXED", "STATE", symbol(
                "M_L'java/util/ArrayList'_3", "java/util/ArrayList"));
        // [7 where n < 5, 8 where n >= 2].
        JsonObject list = guarded(relation("INDEXED", "APPEND_IF",
                guarded(relation("INDEXED", "APPEND_IF",
                        relation("INDEXED", "SNAPSHOT_BASE", root),
                        integer("I", 7L)),
                        binary("<", n, integer("I", 5L))),
                integer("I", 8L)), binary(">=", n, integer("I", 2L)));
        JsonObject set = guarded(relation("ASSOCIATIVE", "PUT_IF",
                relation("ASSOCIATIVE", "SNAPSHOT_BASE", null),
                integer("I", 5L), integer("Z", 1L)),
                binary("<", n, integer("I", 5L)));
        String chains = streamQuery(
                new String[] {"list_size", "read0", "contains8", "set5"},
                relation("INDEXED", "SIZE", "I", list),
                relation("INDEXED", "READ", "I", list, integer("I", 0L)),
                relation("INDEXED", "CONTAINS", "Z", list, integer("I", 8L)),
                relation("ASSOCIATIVE", "CONTAINS", "Z", set,
                        integer("I", 5L)));
        // The same list where the run held n < 4.
        String pinned = streamQuery(new String[] {"pinned_size"},
                relation("INDEXED", "SIZE", "I", guarded(relation("INDEXED",
                        "PIN", list), binary("<", n, integer("I", 4L)))));
        String[][] cases = {
            {chains, "(and (= n 3) (= list_size 2))", "sat"},
            {chains, "(and (= n 7) (= list_size 2))", "unsat"},
            {chains, "(and (= n 1) (= list_size 1))", "sat"},
            {chains, "(and (= n 7) (= read0 8))", "sat"},
            {chains, "(and (= n 3) (= read0 8))", "unsat"},
            {chains, "(and (= n 1) contains8)", "unsat"},
            {chains, "(and (= n 3) contains8)", "sat"},
            {chains, "(and (= n 7) set5)", "unsat"},
            {chains, "(and (= n 1) set5)", "sat"},
            {pinned, "(and (= n 4) (= pinned_size 2))", "unsat"},
            {pinned, "(and (= n 3) (= pinned_size 2))", "sat"},
        };
        for (String[] asked : cases) {
            Z3.Answer answer = solver.ask(asked[0] + "\n(assert " + asked[1]
                    + ")", Collections.<String>emptyList(), false);
            assertTrue(asked[1] + " " + answer.status(), answer.decided()
                    && answer.sat() == "sat".equals(asked[2]));
        }
        // A list whose chain stands on no exact base bounds no position.
        String refusal = "";
        try {
            streamQuery(new String[] {"unbounded"}, relation("INDEXED",
                    "CONTAINS", "Z", root, integer("I", 8L)));
        } catch (AssertionError refused) {
            refusal = refused.getMessage();
        }
        assertTrue("a contains over an unbounded chain: " + refusal,
                refusal.contains(
                        "ContainerRelation:INDEXED:CONTAINS:unbounded-chain"));
    }

    /**
     * A muted body's choices lower as the guards it stated and its facts as
     * pins (VM model guards): MATCHES is whether the value at a key, null
     * where absent, is the expected cell; PEEK a queue's head or null and
     * POLL the queue without it, decided by a stated size and refused by
     * name over none; an UNKNOWN cell is free, and a read at another literal
     * key passes a guarded put; a query whose chain stands on no stated base
     * answers what its call stated it returned -- pinned where nothing it
     * rests on moves, free where its key does or where the stage may re-pair
     * the read it rests on -- and one over a stated base is its chain's,
     * whatever it states; asked of another object, a query states no answer.
     * {asked, sat?}.
     */
    @Test
    public void aModelsChoiceIsItsGuardAndItsFactAPin() {
        Z3 solver = solver();
        JsonObject n = vmLeaf("SymbolExpression", "n", "I");
        JsonObject opaque = relation("ASSOCIATIVE", "STATE", symbol(
                "M_L'java/util/HashMap'_3", "java/util/HashMap"));
        // {n -> 7} over a stated empty base.
        JsonObject map = relation("ASSOCIATIVE", "PUT", relation(
                "ASSOCIATIVE", "SNAPSHOT_BASE", opaque), n, integer("I", 7L));
        JsonObject base = relation("INDEXED", "SNAPSHOT_BASE", null);
        JsonObject queue = relation("INDEXED", "APPEND", base,
                integer("I", 7L));
        JsonObject maybe = guarded(relation("INDEXED", "APPEND_IF", base,
                integer("I", 7L)), binary("<", n, integer("I", 5L)));
        String models = streamQuery(new String[] {"absent5", "seven5",
                        "head", "polled", "drained"},
                relation("ASSOCIATIVE", "MATCHES", "Z", map,
                        integer("I", 5L), vmNull()),
                relation("ASSOCIATIVE", "MATCHES", "Z", map,
                        integer("I", 5L), integer("I", 7L)),
                relation("INDEXED", "PEEK", "I", queue),
                relation("INDEXED", "SIZE", "I",
                        relation("INDEXED", "POLL", queue)),
                relation("INDEXED", "SIZE", "I",
                        relation("INDEXED", "POLL", base)));
        // A head that is there where n < 5, and null -- no Int -- elsewhere.
        String unsized = streamQuery(new String[] {"maybeHead"},
                relation("INDEXED", "PEEK", "I", maybe));
        String facts = streamQuery(new String[] {"opaqueRead", "chainRead",
                        "opaqueHas"},
                answered(relation("ASSOCIATIVE", "READ", "I", opaque,
                        integer("I", 5L)), integer("I", 11L), 1L),
                answered(relation("ASSOCIATIVE", "READ", "I", map,
                        integer("I", 5L)), integer("I", 12L), 2L),
                answered(relation("ASSOCIATIVE", "CONTAINS", "Z", opaque,
                        n), integer("Z", 1L), 3L));
        // The same membership, where a witness may move its key.
        String moving = streamQuery(joined("n", "", null),
                new String[] {"movedHas"},
                answered(relation("ASSOCIATIVE", "CONTAINS", "Z", opaque,
                        n), integer("Z", 1L), 4L));
        // A membership over a state read: pinned where the stage holds the
        // read to the version it observed, free where it may re-pair it.
        SmtLowering.SessionJoin observed = joined("", "MAP/9#-3",
                opaque);
        JsonObject stateRead = read("MAP_STATE", 9L, -3L, 2L, "L");
        String held = streamQuery(SmtLowering.repairing(observed,
                        (location, event) -> false, (reader, writer) -> false),
                new String[] {"heldHas"}, answered(relation("ASSOCIATIVE",
                        "CONTAINS", "Z", stateRead, n), integer("Z", 1L), 5L));
        String repaired = streamQuery(SmtLowering.repairing(observed,
                        (location, event) -> true, (reader, writer) -> false),
                new String[] {"repairedHas"}, answered(relation("ASSOCIATIVE",
                        "CONTAINS", "Z", stateRead, n), integer("Z", 1L), 6L));
        // {5 -> 7, 6 -> what a callback never run would have stored where
        // n < 5}.
        JsonObject unknownCell = relation("ASSOCIATIVE", "UNKNOWN", "L",
                null);
        unknownCell.addProperty(ContainerSmtCodec.ANSWER, 7L);
        JsonObject filled = guarded(relation("ASSOCIATIVE", "PUT_IF",
                relation("ASSOCIATIVE", "PUT", relation("ASSOCIATIVE",
                        "SNAPSHOT_BASE", opaque), integer("I", 5L),
                        integer("I", 7L)), integer("I", 6L), unknownCell),
                binary("<", n, integer("I", 5L)));
        String cells = streamQuery(new String[] {"nine6"},
                relation("ASSOCIATIVE", "MATCHES", "Z", filled,
                        integer("I", 6L), integer("I", 9L)));
        String passed = streamQuery(new String[] {"read5"},
                relation("ASSOCIATIVE", "READ", "I", filled,
                        integer("I", 5L)));
        assertFalse("a read at another literal key lowers a guarded put: "
                + passed, passed.contains("assoc_put_if"));
        JsonObject other = SmtLowering.asOf(answered(relation("ASSOCIATIVE",
                "READ", "I", opaque, integer("I", 5L)), integer("I", 11L),
                8L), map);
        assertFalse("another object's query states the run's answer",
                other.has("concreteValue")
                        || other.has(ContainerSmtCodec.ANSWER));
        String[][] cases = {
            {models, "(and (= n 5) absent5)", "unsat"},
            {models, "(and (= n 4) absent5)", "sat"},
            {models, "(and (= n 5) seven5)", "sat"},
            {models, "(and (= n 4) seven5)", "unsat"},
            {models, "(= head 7)", "sat"},
            {models, "(not (= head 7))", "unsat"},
            {models, "(= polled 0)", "sat"},
            {models, "(not (= polled 0))", "unsat"},
            {models, "(= drained 0)", "sat"},
            {unsized, "(and (= n 3) (= maybeHead 7))", "sat"},
            {unsized, "(= n 7)", "unsat"},
            {facts, "(= opaqueRead 11)", "sat"},
            {facts, "(not (= opaqueRead 11))", "unsat"},
            {facts, "(and (= n 5) (= chainRead 7))", "sat"},
            {facts, "(= chainRead 12)", "unsat"},
            {facts, "(not opaqueHas)", "unsat"},
            {moving, "(not movedHas)", "sat"},
            {moving, "movedHas", "sat"},
            {held, "(not heldHas)", "unsat"},
            {repaired, "(not repairedHas)", "sat"},
            {repaired, "repairedHas", "sat"},
            {cells, "(and (= n 3) nine6)", "sat"},
            {cells, "(and (= n 3) (not nine6))", "sat"},
            {cells, "(and (= n 7) nine6)", "unsat"},
            {passed, "(= read5 7)", "sat"},
            {passed, "(not (= read5 7))", "unsat"},
        };
        for (String[] asked : cases) {
            Z3.Answer answer = solver.ask(asked[0] + "\n(assert " + asked[1]
                    + ")", Collections.<String>emptyList(), false);
            assertTrue(asked[1] + " " + answer.status(), answer.decided()
                    && answer.sat() == "sat".equals(asked[2]));
        }
        assertTrue("a pin is named for an unsat core",
                facts.contains(":named pinned_answer__"));
        String refusal = "";
        try {
            streamQuery(new String[] {"unstated"}, relation("INDEXED",
                    "SIZE", "I", relation("INDEXED", "POLL", relation(
                            "INDEXED", "STATE", symbol(
                                    "M_L'java/util/ArrayDeque'_4",
                                    "java/util/ArrayDeque")))));
        } catch (AssertionError refused) {
            refusal = refused.getMessage();
        }
        assertTrue("a poll over no stated size: " + refusal, refusal.contains(
                "ContainerRelation:INDEXED:POLL:unstated-size"));
    }

    /**
     * A map a stream collected by {@code toMap} (VM SymStream) lowers as the
     * merges its chain states: the second member's key where the first's
     * may equal it is put where {@code MATCHES} says it is absent, and where
     * it is present holds what the merge function answered, nothing where
     * it answered null, or a free cell where the run never called it.
     * {asked, sat?}.
     */
    @Test
    public void aCollectedMapIsItsMerges() {
        Z3 solver = solver();
        JsonObject n = vmLeaf("SymbolExpression", "n", "I");
        JsonObject m = vmLeaf("SymbolExpression", "m", "I");
        JsonObject first = relation("ASSOCIATIVE", "PUT", relation(
                "ASSOCIATIVE", "SNAPSHOT_BASE", relation("ASSOCIATIVE",
                        "STATE", symbol("M_L'java/util/HashMap'_5",
                                "java/util/HashMap"))), n, integer("I", 10L));
        JsonObject absent = relation("ASSOCIATIVE", "MATCHES", "Z", first, m,
                vmNull());
        JsonObject present = binary("==", absent, integer("Z", 0L));
        JsonObject second = guarded(relation("ASSOCIATIVE", "PUT_IF", first,
                m, integer("I", 20L)), absent);
        JsonObject unknownCell = relation("ASSOCIATIVE", "UNKNOWN", "L",
                null);
        unknownCell.addProperty(ContainerSmtCodec.ANSWER, 9L);
        JsonObject never = guarded(relation("ASSOCIATIVE", "PUT_IF", second,
                m, unknownCell), present);
        JsonObject merged = guarded(relation("ASSOCIATIVE", "PUT_IF", second,
                m, integer("I", 30L)), present);
        JsonObject removed = guarded(relation("ASSOCIATIVE", "REMOVE_IF",
                second, m), present);
        Map<String, VmTermLowering.Sort> keys =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        keys.put("n", VmTermLowering.Sort.INT);
        keys.put("m", VmTermLowering.Sort.INT);
        String maps = query(keys, SmtLowering.NO_JOIN, false,
                new String[] {"neverM", "mergedM", "removedHas",
                        "removedSize"},
                relation("ASSOCIATIVE", "READ", "I", never, m),
                relation("ASSOCIATIVE", "READ", "I", merged, m),
                relation("ASSOCIATIVE", "CONTAINS", "Z", removed, m),
                relation("ASSOCIATIVE", "SIZE", "I", removed));
        String[][] cases = {
            {"(and (not (= n m)) (= neverM 20))", "sat"},
            {"(and (not (= n m)) (not (= neverM 20)))", "unsat"},
            {"(and (= n m) (= neverM 77))", "sat"},
            {"(and (= n m) (= mergedM 30))", "sat"},
            {"(and (= n m) (not (= mergedM 30)))", "unsat"},
            {"(and (not (= n m)) (= mergedM 20))", "sat"},
            {"(and (= n m) removedHas)", "unsat"},
            {"(and (not (= n m)) removedHas (= removedSize 2))", "sat"},
            {"(and (= n m) (not (= removedSize 0)))", "unsat"},
        };
        for (String[] asked : cases) {
            Z3.Answer answer = solver.ask(maps + "\n(assert " + asked[0]
                    + ")", Collections.<String>emptyList(), false);
            assertTrue(asked[0] + " " + answer.status(), answer.decided()
                    && answer.sat() == "sat".equals(asked[1]));
        }
    }

    /**
     * A constant {@code Enum.valueOf} chose by a name (VM SymEnum) lowers to
     * that name, defined where it is one of the enum's constants -- a name
     * built by {@code toUpperCase} (Solr's {@code Replica.State.getState})
     * matched letter by letter: a compare of it is a compare of names, its
     * {@code toLowerCase} ({@code State.toString}) the chosen constant's,
     * its ordinal where the name stands among them, and a switch map's read
     * at that ordinal the case.  {asked, sat?}.
     */
    @Test
    public void anEnumConstantIsItsName() {
        Z3 solver = solver();
        JsonObject named = enumCall("valueOf", vmString("toUpperCase",
                symbol("s", "Ljava/lang/String;")), "pkg/State", "ACTIVE",
                "DOWN", "RECOVERING");
        JsonObject active = vmString("equals", vmLeaf("ConStringSymbolExp",
                "Y_L'String'_ACTIVE", "java/lang/String"), named);
        active.addProperty("_java_type", "Z");
        JsonObject text = vmString("equals", vmLeaf("ConStringSymbolExp",
                "Y_L'String'_active", "java/lang/String"),
                vmString("toLowerCase", named));
        text.addProperty("_java_type", "Z");
        JsonObject ordinal = enumCall("ordinal", named, null, "ACTIVE",
                "DOWN", "RECOVERING");
        // javac's switch map: ACTIVE -> 1, DOWN -> 2, RECOVERING -> 0.
        JsonObject map = relation("INDEXED", "SNAPSHOT_BASE", null);
        for (long entry : new long[] {1L, 2L, 0L}) {
            map = relation("INDEXED", "APPEND", map, integer("I", entry));
        }
        // A map the program filled with plain constants, keyed by name.
        JsonObject weights = relation("ASSOCIATIVE", "SNAPSHOT_BASE",
                relation("ASSOCIATIVE", "STATE", symbol(
                        "M_L'java/util/HashMap'_8", "java/util/HashMap")));
        weights = relation("ASSOCIATIVE", "PUT", weights, vmLeaf(
                "ConStringSymbolExp", "Y_L'String'_ACTIVE",
                "java/lang/String"), integer("I", 1L));
        weights = relation("ASSOCIATIVE", "PUT", weights, vmLeaf(
                "ConStringSymbolExp", "Y_L'String'_DOWN",
                "java/lang/String"), integer("I", 2L));
        String enums = query(Collections.singletonMap("s",
                VmTermLowering.Sort.STRING), SmtLowering.NO_JOIN, true,
                new String[] {"isActive", "isActiveText", "ord", "caseKey",
                        "weight"},
                active, text, ordinal, relation("INDEXED", "READ", "I", map,
                        ordinal), relation("ASSOCIATIVE", "READ", "I",
                        weights, named));
        String[][] cases = {
            {"(and isActive (= s \"active\"))", "sat"},
            {"(and isActive (= s \"AcTiVe\"))", "sat"},
            {"(and isActive (= s \"down\"))", "unsat"},
            {"(= s \"bogus\")", "unsat"},
            {"(= s \"activ\")", "unsat"},
            {"(and (= s \"down\") (= ord 1))", "sat"},
            {"(and (= s \"down\") (not (= ord 1)))", "unsat"},
            {"(and (= s \"Down\") (= caseKey 2))", "sat"},
            {"(and (= s \"down\") (not (= caseKey 2)))", "unsat"},
            {"(and isActiveText (= s \"ACTIVE\"))", "sat"},
            {"(and isActiveText (= s \"down\"))", "unsat"},
            {"(and (= s \"Down\") (= weight 2))", "sat"},
            {"(and (= s \"down\") (not (= weight 2)))", "unsat"},
            {"(and (= s \"active\") (= weight 1))", "sat"},
        };
        for (String[] asked : cases) {
            Z3.Answer answer = solver.ask(enums + "\n(assert " + asked[0]
                    + ")", Collections.<String>emptyList(), false);
            assertTrue(asked[0] + " " + answer.status(), answer.decided()
                    && answer.sat() == "sat".equals(asked[1]));
        }
    }

    /** {@code java/lang/Enum <method>}'s node as the VM states it: its
     *  argument (the name, or the constant), the class when {@code owner}
     *  names one, then the constants in ordinal order. */
    private static JsonObject enumCall(String method, JsonObject argument,
                                       String owner, String... constants) {
        JsonObject call = new JsonObject();
        call.addProperty("_type", "MethodExpression");
        call.addProperty("_name", "java/lang/Enum " + method);
        JsonArray arguments = new JsonArray();
        if (owner != null) {
            arguments.add(vmLeaf("ConStringSymbolExp", "Y_L'String'_"
                    + owner, "java/lang/String"));
        }
        arguments.add(argument);
        for (String constant : constants) {
            arguments.add(vmLeaf("ConStringSymbolExp", "Y_L'String'_"
                    + constant, "java/lang/String"));
        }
        call.add("_param_list", arguments);
        call.add("_res_exp", owner != null ? vmLeaf("ConStringSymbolExp",
                "Y_L'String'_" + constants[0], "java/lang/String")
                : integer("I", 0L));
        return call;
    }

    /**
     * The join of no session, where a witness may move {@code symbol} and
     * every version of {@code written}'s location wrote it.
     */
    private static SmtLowering.SessionJoin joined(final String symbol,
                                                  final String location,
                                                  final JsonObject written) {
        final SmtLowering.SessionJoin none = SmtLowering.NO_JOIN;
        return new SmtLowering.SessionJoin() {
            @Override
            public com.google.gson.JsonElement writeExpression(
                    String at, long version) {
                return location.equals(at) ? written
                        : none.writeExpression(at, version);
            }

            @Override
            public List<WriteRow> writes(String at) {
                return none.writes(at);
            }

            @Override
            public List<ReadRow> reads(String at) {
                return none.reads(at);
            }

            @Override
            public Set<String> mintedReadSymbols(long version) {
                return none.mintedReadSymbols(version);
            }

            @Override
            public Set<String> readSymbols(String at, long version) {
                return none.readSymbols(at, version);
            }

            @Override
            public boolean moves(String named) {
                return symbol.equals(named);
            }

            @Override
            public boolean repaired(String at, long readEvent) {
                return false;
            }

            @Override
            public boolean concurrent(OccurrenceAddress reader,
                                      OccurrenceAddress writer) {
                return false;
            }
        };
    }

    /** A query stating what its call returned, under its answer id. */
    private static JsonObject answered(JsonObject query, JsonObject value,
                                       long id) {
        query.add("concreteValue", value);
        query.addProperty(ContainerSmtCodec.ANSWER, id);
        return query;
    }

    /**
     * One query defining each of {@code names} as what its expression
     * lowers to over an Int symbol {@code n}, with every condition and
     * assertion the lowering states.
     */
    private static String streamQuery(String[] names,
                                      JsonObject... expressions) {
        return streamQuery(SmtLowering.NO_JOIN, names, expressions);
    }

    /** The same, under {@code join}. */
    private static String streamQuery(SmtLowering.SessionJoin join,
                                      String[] names,
                                      JsonObject... expressions) {
        return query(Collections.singletonMap("n", VmTermLowering.Sort.INT),
                join, false, names, expressions);
    }

    /** The same, over {@code declared} symbols; {@code defined}: each
     *  named term asserted defined where it is (its precondition). */
    private static String query(Map<String, VmTermLowering.Sort> declared,
                                SmtLowering.SessionJoin join, boolean defined,
                                String[] names, JsonObject... expressions) {
        SmtLowering lowering = new SmtLowering(
                new LinkedHashMap<String, VmTermLowering.Sort>(declared));
        lowering.begin("t", join, ExpressionTable.empty());
        List<String> texts = new ArrayList<String>();
        List<String> preconditions = new ArrayList<String>();
        StringBuilder definitions = new StringBuilder();
        for (int index = 0; index < names.length; index++) {
            boolean truth = "Z".equals(JsonFields.optionalString(
                    expressions[index], "_java_type"));
            VmTermLowering.Term term = lowering.dispatch(expressions[index],
                    truth ? VmTermLowering.Sort.BOOL
                            : VmTermLowering.Sort.INT, "test");
            texts.add(term.text);
            if (defined) preconditions.add(term.precondition);
            definitions.append("\n(define-fun ").append(names[index])
                    .append(truth ? " () Bool " : " () Int ")
                    .append(term.text).append(')');
        }
        // Read before end(), which closes the conjunction they belong to.
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        List<String> conditions = lowering.end();
        texts.addAll(conditions);
        texts.addAll(preconditions);
        StringBuilder query = new StringBuilder(lowering.body(texts));
        for (String fact : lowering.facts(texts)) {
            query.append("\n(assert ").append(fact).append(')');
        }
        conditions.addAll(preconditions);
        for (String condition : conditions) {
            query.append("\n(assert ").append(condition).append(')');
        }
        return query.append(definitions).toString();
    }

    /** A relation with its {@code guard}. */
    private static JsonObject guarded(JsonObject relation, JsonObject guard) {
        relation.add("guard", guard);
        return relation;
    }

    /**
     * The Strings a file name carries lower as Java computes them: a path's
     * parent is its prefix up to the last separator (File.getParent) and is
     * undefined -- Java throws -- without one; a long names itself in decimal
     * (blk_<id>_<gs>.meta).  finalize-gs a8 lost every path to these.  An
     * address is trimmed as String.trim cuts it, every character up to
     * U+0020 off both ends (b20h BlockRecoveryWorker-222's proxy URI).
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
        VmTermLowering.Term trimmed = lowering.dispatch(vmString("trim",
                path), VmTermLowering.Sort.STRING, "test");
        List<String> conditions = lowering.end();
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        List<String> texts = new ArrayList<String>(conditions);
        texts.addAll(Arrays.asList(parent.text, parent.precondition,
                name.text, trimmed.text));
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
                .append(")\n(define-fun trimmed () String ")
                .append(trimmed.text).append(')');
        String parentDefined = "(assert " + parent.precondition + ")";
        String[][] cases = {
            {"(and (= s \"a/b/c\") (= parent \"a/b\"))", "sat"},
            {"(and (= s \"a/b/c\") (= parent \"a\"))", "unsat"},
            {"(= s \"abc\")", "unsat"},
            {"(and (= n (- 12)) (= name \"-12\"))", "sat"},
            {"(and (= n (- 12)) (= name \"12\"))", "unsat"},
            {"(and (= s \" \\u{9}a b\\u{a}\") (= trimmed \"a b\"))", "sat", ""},
            {"(and (= s \" \\u{9}a b\\u{a}\") (= trimmed \"\\u{9}a b\"))",
                    "unsat", ""},
            {"(and (= s \" \\u{0} \") (= trimmed \"\"))", "sat", ""},
            {"(and (= s \"ab\") (not (= trimmed s)))", "unsat", ""},
        };
        for (String[] asked : cases) {
            // A trim is defined wherever its receiver is, a parent only
            // where the path has a separator.
            Z3.Answer answer = solver.ask(query + "\n"
                    + (asked.length > 2 ? "" : parentDefined) + "\n(assert "
                    + asked[0] + ")", Collections.<String>emptyList(), false);
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
                    lowering.reachedSymbols(Collections.singletonList(
                            text[0])).contains(deepest));
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

    // ------------------------------------------------------------------
    // 18. What CONFIRM holds a model to at a held leaf.
    // ------------------------------------------------------------------

    /**
     * What CONFIRM holds a model to: the value of each delivery into the
     * anchor that rests on no clock, as the text it arrives as; a floating
     * or char one is not rendered, a delivery elsewhere not held.
     */
    @Test
    public void aHeldLeafIsTheModelsTextRestingOnNoClock() {
        Map<String, ComposedFamilies.BoundLeaf> own = new LinkedHashMap<
                String, ComposedFamilies.BoundLeaf>();
        String[][] leaves = {
            {"c.num", "h_num", "J", ""}, {"c.str", "h_str",
                    "Ljava/lang/String;", ""},
            {"c.relay", "h_relay", "J", "h_num"},
            {"c.clock", "h_clock", "J", "clock"},
            {"c.late", "h_late", "J", "h_clock"},
            {"c.free", "h_free", "J", "h_unbound"},
            {"c.float", "h_float", "D", ""}, {"c.char", "h_char", "C", ""}};
        for (String[] leaf : leaves) {
            boolean clocked = "clock".equals(leaf[3]);
            own.put(leaf[0], new ComposedFamilies.BoundLeaf(leaf[1], leaf[2],
                    "occ.anchor", clocked, leaf[3].isEmpty() || clocked
                    ? Collections.<String>emptySet()
                    : Collections.singleton(leaf[3])));
        }
        own.put("c.elsewhere", new ComposedFamilies.BoundLeaf("h_elsewhere",
                "J", "occ.other", false, Collections.<String>emptySet()));
        Map<String, String> model = new LinkedHashMap<String, String>();
        model.put("h_num", "-5");
        model.put("h_str", "\"a\"\"b\\u{e9}\"");
        model.put("h_relay", "-5");
        model.put("h_clock", "9");
        model.put("h_late", "9");
        model.put("h_free", "3");
        model.put("h_float", "(fp #b0 #b01111111111 #x0000000000000)");
        model.put("h_char", "65");
        model.put("h_elsewhere", "8");
        Map<String, String> texts = ComposedFamilies.texts(
                Collections.singletonList(ComposedFamilies.ArmChoice.of(
                        "f", "g", new ArrayList<String>(own.keySet()), "s0",
                        Collections.<edu.uva.liftlab.graphchecker.smt.Arms
                                .Arm>emptyList(), own)), model,
                "occ.anchor");
        Map<String, String> expected = new LinkedHashMap<String, String>();
        expected.put("c.num", "-5");
        expected.put("c.str", "a\"bé");
        expected.put("c.relay", "-5");
        assertEquals("held: the anchor's deliveries resting on no clock and "
                + "on no delivery no arm binds; a floating or char one is "
                + "not rendered, a delivery elsewhere not held", expected,
                texts);
    }

    /** An integral's String.valueOf is its canonical rendering, exactly. */
    @Test
    public void anIntegralRendersCanonically() {
        Z3 solver = solver();
        String[][] readings = {{"\"-1727\"", "sat", "-1727"},
                {"\"0042\"", "unsat", ""}, {"\"+5\"", "unsat", ""},
                {"\"-0\"", "unsat", ""}};
        for (String[] reading : readings) {
            String query = "(set-logic ALL)\n"
                    + VmTermLowering.JAVA_INT_TO_STRING
                    + "\n(declare-const v Int)\n(assert (= (java_int_to_string"
                    + " v) " + reading[0] + "))\n";
            Z3.Answer answer = solver.ask(query,
                    Collections.singletonList("v"), false);
            assertEquals(reading[0], reading[1], answer.status());
            if (answer.sat()) {
                assertEquals(reading[0], reading[2], answer.values().get("v"));
            }
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
    /** Whether a composition names a loop bound's cut at the anchor
     *  (`loop-body-bound`, counted in a case's `bounded`). */
    private static boolean bounded(Composer.Composition composed) {
        for (GapRow gap : composed.gaps()) {
            if (gap.subject().equals(ANCHOR.render() + " "
                    + Composer.LOOP_BODY_BOUND + "=8")) {
                return true;
            }
        }
        return false;
    }

    private static Composer.Composition compose(Path iteration,
                                                OccurrenceAddress anchor,
                                                int maxValuations,
                                                StaticScopeMap scope)
            throws IOException {
        Composer.Composition composition = Composer.compose(
                Corpus.read(iteration, null), anchor, maxValuations, scope);
        // Every composition: one name, one assertion (z3 answers a name
        // defined twice with an error, hdfs-11741 m1).
        java.util.regex.Matcher named = java.util.regex.Pattern.compile(
                ":named ([^ )]+)").matcher(composition.body());
        Set<String> names = new LinkedHashSet<String>();
        while (named.find()) {
            assertTrue("named once: " + named.group(1),
                    names.add(named.group(1)));
        }
        return composition;
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

    /** What a written query or artifact writes. */
    private static String text(ArtifactIO.Body body) throws IOException {
        java.io.StringWriter written = new java.io.StringWriter();
        try (java.io.BufferedWriter output =
                     new java.io.BufferedWriter(written)) {
            body.writeTo(output);
        }
        return written.toString();
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
                    RootKind.MARKER, RootCategory.FAULT, recorded, null, null, true, null, 0L));
        }

        /** A boolean configuration, as the engine mints one. */
        void configuration(String recorded) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, CONFIG_ROOT, CONFIG,
                    RootKind.MARKER, RootCategory.CONFIG, recorded, null,
                    null, true, null, 0L));
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
                    RootKind.CLOCK, RootCategory.CLOCK, recorded, null, null, true, Clock.of(1_000_000L, Clock.WALL), 0L));
        }

        /** One decision, and the clock cells its predicate read. */
        void decision(OccurrenceAddress at, String site, String term,
                      String clockRoot, long reading) {
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, true, term,
                    Collections.singletonMap(clockRoot, reading)));
        }

        /** A declared counter, with its absolute window (a row's bounds
         *  are absolute; only a case's declaration is relative). */
        void serial(String recorded, String min, String max) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, SERIAL_ROOT,
                    SERIAL, RootKind.INTEGRAL, RootCategory.HOOK, recorded,
                    min, max, true, null, 0L));
        }

        /** Root id -> occurrence -> what this replay read the root at
         *  where it ran the occurrence concretely (its manifest's). */
        private final Map<String, Map<String, String>> readings =
                new LinkedHashMap<String, Map<String, String>>();

        /** The roots this replay found derived (its manifest's). */
        private final Set<String> derived = new LinkedHashSet<String>();

        /** The counter, read at PRODUCER, where this replay minted none. */
        void serialReadConcretely(String value) {
            readings.computeIfAbsent(SERIAL_ROOT,
                    root -> new LinkedHashMap<String, String>())
                    .put(PRODUCER.render(), value);
        }

        void expression(String ref, JsonObject node) {
            expressions.put(ref, node);
        }

        void export(Endpoint endpoint, String ref, long handle,
                    String recorded) {
            export(endpoint, ref, "Z", handle, recorded);
        }

        void export(Endpoint endpoint, String ref, String javaType,
                    long handle, String recorded) {
            exports.add(ExportRow.of(id, ++seq, endpoint, ref, javaType,
                    handle, recorded));
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
         * An attach an OBLIGATION answered: the mint was planted with
         * {@code answer} while its producer delivered {@code arrival}.
         */
        void answered(Endpoint endpoint, String symbol, String javaType,
                      String arrival, String answer, Endpoint producer) {
            attaches.add(AttachRow.of(id, ++seq, endpoint, symbol, javaType,
                    arrival, true, answer, producer, "corr-" + symbol,
                    producer == null ? "" : "HANDLE"));
        }

        /** One root, minted where the fixture says. */
        void root(OccurrenceAddress at, String rootId, String symbol,
                  RootKind kind, String recorded) {
            roots.add(RootMintRow.of(id, ++seq, at, rootId, symbol, kind,
                    kind == RootKind.CLOCK ? RootCategory.CLOCK
                            : kind == RootKind.MARKER ? RootCategory.FAULT
                            : RootCategory.HOOK,
                    recorded, null, null, true,
                    kind == RootKind.CLOCK
                ? Clock.of(1_000_000L, Clock.WALL) : null, 0L));
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

        /** @return the read's seq: the VM event its ReadFrom names
         *  ({@code readEventId}). */
        long read(Endpoint endpoint, LocationId location, long version,
                  String symbol, String javaType, String concrete) {
            reads.add(ReadRow.of(id, ++seq, endpoint, location, version,
                    symbol, javaType, concrete));
            return seq;
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
            decision(at, site, outcome, term, "");
        }

        /** One decision in a call from {@code via} (DecisionRow#via). */
        void decision(OccurrenceAddress at, String site, boolean outcome,
                      String term, String via) {
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, outcome, term,
                    Collections.<String, Long>emptyMap()).via(via));
        }

        void target(String phi, boolean observedFatal, boolean reached) {
            targets.add(TargetRow.of(id, ++seq, occurrence, anchorLabel, phi,
                    observedFatal, reached));
        }

        /** The label its target rows state ({@link #target}). */
        String anchorLabel = ANCHOR_SITE;

        /** A FORCE run's (PIPELINE §7.10): this session states it ran
         *  forced, its decision forced off the arm its operands took. */
        void forcedDecision(OccurrenceAddress at, String site, String term) {
            forced = true;
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, true, term,
                    Collections.<String, Long>emptyMap()).forced(false));
        }

        /** A FORCE run's target, standing at {@code at}. */
        void forcedTarget(long at, String phi) {
            forced = true;
            targets.add(TargetRow.of(id, at, occurrence, ANCHOR_SITE, phi,
                    false, true).forced());
        }

        /** Whether this session states it ran forced. */
        private boolean forced;

        /** A target standing at an earlier event (a helper decision's,
         *  runtime.RowPublication#decided). */
        void targetAt(long at, String phi, boolean observedFatal,
                      boolean reached) {
            targets.add(TargetRow.of(id, at, occurrence, ANCHOR_SITE, phi,
                    observedFatal, reached));
        }

        /** The row a loop bound's cut of {@code at} files
         *  (runtime.LoopAccounting#endAtCut). */
        void cut(OccurrenceAddress at, String detail) {
            gaps.add(GapRow.of(id, GapKind.BOUND_INSUFFICIENT,
                    GapClass.DIAGNOSTIC, at.render(), detail));
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
                    forced ? SessionManifest.Role.FORCED : explored
                            ? SessionManifest.Role.FOCUSED
                            : SessionManifest.Role.SEED,
                    explored || forced ? Collections.singletonList("OBL." + id)
                            : Collections.<String>emptyList())
                    .atClose(Collections.<String, Integer>emptyMap(),
                            readings, derived));
            // And the VERDICT, which the replay owns: a focused session
            // that states none settled nothing, and the composition asks
            // the session's own row rather than the wave's copy of it.
            RowCodec.writeAll(dir.obligations(), explored || forced
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
        if (answered == null) {
            session.attach(consumer, symbol, arrival, producer);
        } else {
            session.answered(consumer, symbol, "Z", arrival, answered,
                    producer);
        }
        // phi is published in the FATAL polarity by the runtime, healthy
        // sessions included; the composer never re-derives it.
        session.target(symbol, observedFatal, true);
        session.write();
    }

    /**
     * An object the VM named is a reference identity whatever its kind: an
     * instance's M_L'class'_rid and an array's A<type>_<rid>-<version>, one
     * identity at every version (hdfs-adhoc-50, round HG5A: a read of a
     * field holding an array stated "AL_42-0" and every path pinning it was
     * refused as placed nowhere).
     */
    @Test
    public void anArrayTheVmNamedIsOneReferenceIdentity() {
        Object[][] rows = {
                {"M_L'java/lang/Object'_17", 17L, "M_L'java/lang/Object'_17"},
                {"AL_42-0", 42L, "AL_42"},
                {"AL_42-3", 42L, "AL_42"},
                {"A[_7-0", 7L, "A[_7"},
                {"AL_x-0", -1L, "AL_x-0"},
                {"ALPHA_1-2", -1L, "ALPHA_1-2"},
                {"P_L'java/lang/Object'_", -1L, "P_L'java/lang/Object'_"},
        };
        for (Object[] row : rows) {
            String symbol = (String) row[0];
            assertEquals(symbol, row[1], VmRows.referencedObjectRid(symbol));
            assertEquals(symbol, row[2], VmRows.objectIdentity(symbol));
        }
        SmtLowering lowering = new SmtLowering(
                new LinkedHashMap<String, VmTermLowering.Sort>());
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        VmTermLowering.Term first = lowering.statedValue("AL_42-0", "L");
        VmTermLowering.Term later = lowering.statedValue("AL_42-3", "L");
        lowering.end();
        assertNotNull("an array identity is placed", first);
        assertEquals(VmTermLowering.Sort.REF, first.sort);
        assertEquals("one array, one identity", first.text, later.text);
    }
}
