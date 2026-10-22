package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import edu.uva.liftlab.graphchecker.smt.ScopedFixture;
import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Arm;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.ExpressionLogs;
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
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.explore.ExploreCodec;

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
import java.util.TreeSet;
import java.util.function.Supplier;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class ComposerTest {
    @org.junit.Before
    public void publishedViews() {
        System.setProperty(edu.uva.liftlab.graphchecker.causynth
                .LibraryCatalog.SYSTEM_DOORS, java.nio.file.Paths.get("src",
                "test", "resources", "published-views.jsonl")
                .toAbsolutePath().toString());
    }

    @org.junit.After
    public void noSystemDoors() {
        System.clearProperty(edu.uva.liftlab.graphchecker.causynth
                .LibraryCatalog.SYSTEM_DOORS);
    }

    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

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
    private static final String PLACEHOLDER =
            "M_I_field_REGION.target.in.count";
    private static final String NO_ROW = "M_I_field_REGION.target.in.absent";
    private static final String PLACEHOLDER_TWO =
            "M_I_field_REGION.target.in.count.port2";


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

        ClaimPolicy.Decision errored = ClaimPolicy.decide(composition,
                new Z3(erroringSolver(), 30000L, 8192));
        assertEquals("an error is not a finding",
                ClaimKind.NO_SUPPORTED_WITNESS, errored.claim().kind());
        assertTrue("and it is named",
                says(errored.claim().gaps(), GapKind.DECLARATION_MISSING,
                        "z3 answered a composed question with an error"));
        assertFalse("nothing about the recording is decided by it",
                errored.claim().polarityDecides());

        ClaimPolicy.Decision undecided = ClaimPolicy.decide(composition,
                new Z3(undecidingSolver(), 30000L, 8192));
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

        assertEquals("a warning is not the verdict", ClaimKind.MARKER_FLIPPED,
                ClaimPolicy.decide(composition, new Z3(warningSolver(),
                        30000L, 8192)).claim().kind());

        Path control = folder.newFolder("marker-control").toPath();
        for (String[] each : new String[][]{
                {"s0", "true", "2", "false"}, {"s1", "false", "0", "true"}}) {
            Session session = new Session(control, each[0],
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
        OccurrenceAddress sibling = occurrence("case/nn0", "REGION.saver",
                CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                frame("Saver#serializeSnapshotSection#8", 1));
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
            String[] port = {PLACEHOLDER, PLACEHOLDER_TWO};
            for (int activation = 0; activation < 2; activation++) {
                session.placeholder(Endpoint.of(
                                activation == 0 ? saver : sibling,
                                "INSTANCE_FIELD/counter#PLACEHOLDER#"
                                        + activation + ":READ",
                                at("count#" + activation, 0), 0),
                        counter, Long.parseLong(each[2]),
                        500L + activation, port[activation], "I", each[3]);
                session.expression("EXPR.0000000000000fe" + activation,
                        binary("!=", integer("I", 2L),
                                read("INSTANCE_FIELD", owner, "value",
                                        500L + activation, "I")));
            }
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
        assertEquals(1, armed.families().get(0).arms().size());
        for (Arm arm : armed.families().get(0).arms()) {
            assertTrue("an arm carries the delivering replay's valuation "
                            + "of the varied root its expression never "
                            + "names: " + arm.guardRoots(),
                    arm.guardRoots().contains(MARKER_ROOT));
        }
        assertTrue("both replays' values are in the two paths' arms",
                armed.body().contains("(= " + MARKER + " true)")
                        && armed.body().contains(
                        "(= " + MARKER + " false)"));

        Composer.Composition same = compose(agreed, 8);
        assertEquals(2, same.paths().size());
        assertFalse("nothing varied, so no path states a valuation of it",
                same.body().contains("(= " + MARKER + " "));
        assertEquals("and there is one question", 1,
                same.valuations().size());

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
        assertFalse("it blocks nothing", blocking(silent.gaps()));

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
        assertFalse("it blocks nothing", blocking(contradicted.gaps()));
    }

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

    private static void obligation(Path iteration, String sessionId,
                                   Map<String, String> roots)
            throws IOException {
        obligation(iteration, sessionId, roots, "nn#u1",
                Collections.<String>emptyList());
    }

    private static void obligation(Path iteration, String sessionId,
                                   Map<String, String> roots, String site,
                                   List<String> inherited)
            throws IOException {
        obligation(iteration, sessionId, roots, site, inherited, "");
    }

    private static void obligation(Path iteration, String sessionId,
                                   Map<String, String> roots, String site,
                                   List<String> inherited, String focused)
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
        focus.addProperty("focusedOccurrenceId", focused);
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
        focus.add("pairings", new com.google.gson.JsonObject());
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

    private static boolean blocking(List<GapRow> gaps) {
        for (GapRow gap : gaps) {
            if (gap.blocking()) return true;
        }
        return false;
    }

    private Path undecidingSolver() throws IOException {
        Path script = folder.newFile("z3-unknown.sh").toPath();
        Files.write(script, Arrays.asList("#!/bin/sh",
                "cat > /dev/null",
                "echo unknown",
                "echo '(:reason-unknown \"(incomplete quantifiers)\")'"));
        assertTrue("the fixture solver is executable",
                script.toFile().setExecutable(true));
        return ScopedFixture.of(script);
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
        return ScopedFixture.of(script);
    }

    @Test
    public void anExcludedModelIsNoModelOfTheNextComposition()
            throws Exception {
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
            Path capped = folder.newFile("z3-core-capped-" + row[0] + "-"
                    + row[1]).toPath();
            Files.write(capped, Arrays.asList("#!/bin/bash",
                    "input=$(cat)",
                    "case $input in",
                    "  *get-unsat-core*) echo unsat;"
                            + " echo '(error \"out of memory\")' ;;",
                    "  *) echo unsat ;;",
                    "esac"), StandardCharsets.UTF_8);
            assertTrue(capped.toFile().setExecutable(true));
            Z3.Answer noCore = new Z3(capped, 30000L, 8192).ask("",
                    Collections.<String>emptyList(), true);
            assertTrue(noCore.toString(), noCore.unsat() && !noCore.coreKnown());
            JsonObject unknown = ComposeMain.campaignClaim(next,
                    new ClaimPolicy.Decision(again.claim(), again.outcomes(),
                            noCore));
            assertEquals(detail + ": " + unknown, "UNSAT_CLOSED",
                    unknown.get("claim").getAsString());
            assertTrue(detail + ": " + unknown,
                    unknown.has("restsOnRefutationsKnown")
                    && !unknown.get("restsOnRefutationsKnown")
                    .getAsBoolean());
        }
    }

    @Test
    public void aCompositionOverTheSameInputsIsTakenNotMadeAgain()
            throws Exception {
        solver();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        String refuted = "{\"model\":{\"pathId\":\"elsewhere\",\"arms\":[],"
                + "\"assignment\":{}},\"reason\":\"r\"}";
        List<String> files = Arrays.asList("candidate.smt2",
                "candidate_composition_manifest.json", ComposeMain.CLAIM,
                CompositionInputs.FILE);
        for (String change : new String[] {"none", "refuted", "session",
                "midway"}) {
            Path root = folder.newFolder("reuse-" + change).toPath();
            Path iteration = root.resolve("iteration-0000");
            session(iteration, "s0", false, "false", producer, consumer,
                    "vh", "false", null, true, false, "EXPR.v1.marker");
            session(iteration, "s1", true, "true", producer, consumer,
                    "vh", "true", null, true, true, "EXPR.v1.marker");
            Files.write(root.resolve("static_scope_map.jsonl"), new byte[0]);
            Path runs = root.resolve("z3-runs");
            Path midway = root.resolve("midway");
            Path z3 = root.resolve("z3");
            Files.write(z3, Arrays.asList("#!/bin/bash",
                    "echo run >>'" + runs + "'",
                    "if rm '" + midway + "' 2>/dev/null; then",
                    "  echo '" + refuted + "' >>'"
                            + iteration.resolve(Refutations.FILE) + "'",
                    "fi",
                    "exec '" + z3() + "' \"$@\""), StandardCharsets.UTF_8);
            assertTrue(z3.toFile().setExecutable(true));
            if ("midway".equals(change)) Files.createFile(midway);
            Path attempt = root.resolve("attempt");
            ComposeMain.run(composeArguments(iteration, attempt, z3, null));
            assertEquals(change, ClaimKind.MARKER_FLIPPED.name(),
                    com.google.gson.JsonParser.parseString(new String(
                            Files.readAllBytes(attempt.resolve(
                                    ComposeMain.CLAIM)),
                            StandardCharsets.UTF_8)).getAsJsonObject()
                            .getAsJsonObject("claim").get("kind")
                            .getAsString());
            int attemptRuns = Files.readAllLines(runs).size();
            boolean stated = !"midway".equals(change);
            assertEquals(change + ": the attempt's inputs", stated,
                    Files.isRegularFile(attempt.resolve(
                            CompositionInputs.FILE)));
            if ("refuted".equals(change)) {
                Files.write(iteration.resolve(Refutations.FILE),
                        Collections.singletonList(refuted),
                        StandardCharsets.UTF_8);
            } else if ("session".equals(change)) {
                session(iteration, "s2", false, "false", producer, consumer,
                        "vh", "false", null, true, false, "EXPR.v1.marker");
            }
            Path last = root.resolve("final");
            String said = ComposeMain.run(composeArguments(iteration, last,
                    z3, attempt));
            boolean taken = "none".equals(change);
            assertEquals(change + ": " + said, taken,
                    said.startsWith("reused"));
            assertEquals(change + ": z3 ran", !taken,
                    Files.readAllLines(runs).size() > attemptRuns);
            for (String name : taken ? files : Collections.<String>emptyList()) {
                assertTrue(change + ": " + name, Arrays.equals(
                        Files.readAllBytes(attempt.resolve(name)),
                        Files.readAllBytes(last.resolve(name))));
            }
            assertTrue(change, Files.isRegularFile(last.resolve(
                    CompositionInputs.FILE)));
            assertEquals(change, taken, CompositionInputs.of(last)
                    .equals(CompositionInputs.of(attempt)));
        }
    }

    private static ComposeMain.Arguments composeArguments(
            Path iteration, Path out, Path z3, Path reuse) {
        List<String> argv = new ArrayList<String>(Arrays.asList(
                "--sessions", iteration.resolve(SessionDir.SESSIONS)
                        .toString(),
                "--anchor", ANCHOR.render(),
                "--static-scope-map", iteration.resolveSibling(
                        "static_scope_map.jsonl").toString(),
                "--output", out.resolve("candidate.smt2").toString(),
                "--manifest", out.resolve(
                        "candidate_composition_manifest.json").toString(),
                "--max-valuations", "8",
                "--z3", z3.toString(),
                "--z3-room-mb", "8192"));
        if (reuse != null) {
            argv.add("--reuse");
            argv.add(reuse.toString());
        }
        return ComposeMain.Arguments.parse(argv.toArray(new String[0]));
    }

    @Test
    public void aClaimIsJudgedOnThePathsItRestsOn() throws Exception {
        JsonObject expression = symbol(MARKER, "Z");
        for (String vh : new String[] {"M_Z_field_HOFF.key",
                "M_Z_field_HOFF.k'ey"}) {
            judgedOnItsPaths(vh, "PORT.key", PRODUCER, expression, "OPEN");
        }
        String content = ContentPort.of("SOLR_ZK", "/a.json", "/k");
        OccurrenceAddress role = OccurrenceAddress.of(PRODUCER.node(),
                OccurrenceAddress.ROLE_REGION + "OVERSEER_STATE_UPDATE",
                PRODUCER.context(), ExecutionIndex.empty());
        OccurrenceAddress late = OccurrenceAddress.of(PRODUCER.node(),
                "REGION.tick", CausalContext.of(Role.of("TICK"), "", 2),
                ExecutionIndex.empty());
        Object[][] rows = {
            {PRODUCER, expression, SmtLowering.Unbound.EXPORTED},
            {PRODUCER, constant("false"), SmtLowering.Unbound.CONSTANT},
            {PRODUCER, null, "OPEN"},
            {role, expression, SmtLowering.Unbound.EXPORTED},
            {role, constant("false"), SmtLowering.Unbound.CONSTANT},
            {role, null, "OPEN"},
            {late, constant("false"), SmtLowering.Unbound.BOUNDED},
            {late, expression, SmtLowering.Unbound.EXPORTED},
        };
        for (Object[] row : rows) {
            judgedOnItsPaths("M_Z_field_HOFF.leaf", content,
                    (OccurrenceAddress) row[0], (JsonObject) row[1],
                    (String) row[2]);
        }
    }

    private int judged;

    private void judgedOnItsPaths(String vh, String site,
                                  OccurrenceAddress heldBy,
                                  JsonObject exported, String settles)
            throws Exception {
        Path iteration = folder.newFolder("judged-" + judged++).toPath();
        List<JsonObject> recorded = new ArrayList<JsonObject>();
        for (String role : new String[] {"TICK", "IPC_HANDLER"}) {
            recorded.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(0L,
                    ScheduleEvent.Kind.WAKE, PRODUCER.node().render() + "|"
                            + CausalContext.of(Role.of(role), "", 1)
                            .render(), "tick." + role, 0, "", "")));
        }
        RowCodec.writeJsonl(iteration.resolve("recorded_schedule.jsonl"),
                recorded);
        Endpoint producer = Endpoint.of(PRODUCER, site,
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, site,
                at("attach#1", 0), 0);
        session(iteration, "s0", false, "false", producer, consumer, vh,
                "false", null, true, false, "EXPR.v1.marker");
        session(iteration, "s1", true, "true", producer, consumer, vh,
                "true", null, true, true, "EXPR.v1.marker");
        Endpoint unattested = Endpoint.of(heldBy, site,
                at("export#2", 0), 0);
        boolean refused = !"OPEN".equals(settles);
        session(iteration, "s2", true, "false", unattested, consumer, vh,
                "false", null, false, false, "EXPR.v1.marker", exported);
        Composer.Composition composition = compose(iteration, 8);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver());
        JsonObject sat = ComposeMain.campaignClaim(composition, decision);
        assertEquals(sat.toString(), "SAT_CANDIDATE",
                sat.get("claim").getAsString());
        assertFalse("the witness's own chain is closed: " + sat,
                sat.has("openChain"));
        JsonArray off = sat.getAsJsonArray("unboundOffWitness");
        assertEquals("s2's open link is stated: " + sat, refused ? 0 : 1,
                off == null ? 0 : off.size());
        if (!refused) {
            assertEquals(SmtNames.legalSymbols(vh), off.get(0)
                    .getAsJsonObject().get("symbol").getAsString());
        }

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
        String stated = "";
        for (Composer.Concrete row : next.concrete()) {
            if (row.subject.equals(vh) && SmtLowering.settled(row.kind)) {
                stated = row.kind;
            }
        }
        assertEquals(settles + ": " + next.concrete(), refused ? settles : "",
                stated);
        if (refused) {
            assertFalse(settles + " is no open link: " + unsat,
                    unsat.has("openChain"));
            assertEquals(unsat.toString(), "UNSAT_CLOSED",
                    unsat.get("claim").getAsString());
            String subject = SmtLowering.Unbound.BOUNDED.equals(settles)
                    ? heldBy.render() + " " + Composer.DAEMON_TICK_BOUND
                    + "=1" : heldBy.render();
            String word = SmtLowering.Unbound.BOUNDED.equals(settles)
                    ? "boundedByTick" : SmtLowering.Unbound.EXPORTED.equals(
                    settles) ? "exportedByRefusedProducer"
                    : "constantByRefusedProducer";
            boolean named = false;
            for (GapRow gap : next.gaps()) {
                named |= gap.detail().contains(word)
                        && gap.subject().equals(subject);
            }
            assertTrue(settles + " named: " + next.gaps(), named);
            return;
        }
        assertEquals(unsat.toString(), "UNSAT_CLOSED",
                unsat.get("claim").getAsString());
        JsonObject link = unsat.getAsJsonArray("openChain").get(0)
                .getAsJsonObject();
        assertEquals(SmtNames.legalSymbols(vh),
                link.get("symbol").getAsString());
        assertEquals("the producer its arrival names", heldBy.render(),
                link.get("producer").getAsString());
    }

    @Test
    public void aComposerHoldingNoRowsComposesTheFormulaOfOneHoldingAll()
            throws Exception {
        Path iteration = folder.newFolder("held").toPath();
        Endpoint producer = Endpoint.of(PRODUCER, "PORT.key",
                at("export#1", 0), 0);
        Endpoint consumer = Endpoint.of(ANCHOR, "PORT.key",
                at("attach#1", 0), 0);
        Endpoint writer = Endpoint.of(PRODUCER, "Keys#put#4:WRITE",
                at("w#1", 0), 0);
        Endpoint reader = Endpoint.of(ANCHOR, "Keys#get#5:READ",
                at("r#1", 0), 0);
        LocationId keys = LocationId.of(LocationKind.MAP, "21", "allKeys");
        String[][] runs = {{"s0", "false"}, {"s1", "true"}, {"s2", "false"}};
        for (String[] run : runs) {
            Session session = new Session(iteration, run[0],
                    !"s0".equals(run[0]));
            session.activation(PRODUCER);
            session.marker(run[1]);
            session.expression("EXPR.v1.marker", symbol(MARKER, "Z"));
            session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
            session.export(producer, "EXPR.v1.marker", 1L, run[1]);
            session.write(writer, keys, 1L, "EXPR.v1.marker");
            session.read(reader, keys, 1L, "read_k", run[1]);
            session.attach(consumer, "vh", run[1], producer);
            session.target("(and vh read_k)", false, true);
            session.write();
        }
        Corpus whole = Corpus.read(iteration, null);
        Corpus held = Corpus.holding(iteration, null, everSwept());
        Corpus room = Corpus.holding(iteration, null, () -> 0.0);
        Composer.Composition all = Composer.compose(whole, ANCHOR, 8,
                StaticScopeMap.empty());
        Composer.Composition some = Composer.compose(held, ANCHOR, 8,
                StaticScopeMap.empty());
        Composer.Composition kept = Composer.compose(room, ANCHOR, 8,
                StaticScopeMap.empty());
        assertTrue("the rows were let go of and read again",
                held.readAgain()[0] > 0);
        assertEquals("under the share nothing is let go of", 0L,
                room.readAgain()[0]);
        assertEquals("every row let go of before the body is lowered", 0L,
                room.held());
        assertEquals("the same formula held whole", all.body(),
                kept.body());
        assertEquals("three paths", 3, all.disjuncts().size());
        assertEquals("the same formula", all.body(), some.body());
        assertEquals("the same gaps", all.gaps(), some.gaps());
        assertEquals("the same families", all.families().toString(),
                some.families().toString());
        assertEquals("the same concrete rows", concreteRows(all),
                concreteRows(some));
    }

    private static java.util.function.DoubleSupplier everSwept() {
        double[] sweep = {1.0};
        return () -> sweep[0] += 1.0;
    }

    private static List<String> concreteRows(Composer.Composition composed) {
        List<String> rows = new ArrayList<String>();
        for (Composer.Concrete row : composed.concrete()) {
            rows.add(row.kind + " " + row.subject + " " + row.value + " "
                    + row.reason + " " + row.movesWith);
        }
        return rows;
    }

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

    @Test
    public void anExploredSessionsOwnRunIsClaimedBeforeAFaultlessMechanism()
            throws Exception {
        String phi = "(or (> " + CLOCK + " 1000) " + MARKER + ")";
        Object[][] table = {
            {"an explored replay ran the fault and observed the fatal",
                    true, ClaimKind.MARKER_FLIPPED, "true"},
            {"no explored replay observed it: fewest faults first",
                    false, ClaimKind.CLOCK_SKEW, null},
        };
        for (Object[] row : table) {
            boolean witnessed = (Boolean) row[1];
            Path iteration = folder.newFolder().toPath();
            for (String id : witnessed ? new String[] {"s0", "s1"}
                    : new String[] {"s0"}) {
                boolean explored = id.equals("s1");
                Session session = new Session(iteration, id, explored);
                session.marker(explored ? "true" : "false");
                session.clock("700");
                session.decision(ANCHOR, "anchor#u1", "(or (> " + CLOCK
                        + " 1000) (not (> " + CLOCK + " 1000)))",
                        CLOCK_ROOT, 700L);
                session.target(phi, explored, true);
                session.write();
            }
            ClaimPolicy.Decision decision = ClaimPolicy.decide(
                    compose(iteration, 8), solver());
            assertEquals((String) row[0], row[2], decision.claim().kind());
            assertEquals((String) row[0], row[3],
                    decision.claim().movedRoots().get(MARKER_ROOT));
        }
    }

    @Test
    public void anExploredSessionsOwnRunIsAskedWithItsObservedArms()
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
        LocationId keys = LocationId.of(LocationKind.MAP, "21", "allKeys");
        String taut = "(or " + MARKER + " (not " + MARKER + "))";
        Object[][] table = {
            {"the other writer declared first", true},
            {"the observed writer declared first", false},
        };
        for (Object[] row : table) {
            boolean otherFirst = (Boolean) row[1];
            Path iteration = folder.newFolder().toPath();
            for (String[] each : new String[][]{{"s0", "false"},
                    {"s1", "true"}}) {
                boolean explored = "true".equals(each[1]);
                Session session = new Session(iteration, each[0], explored);
                session.occurrence = reader;
                session.activation(reader);
                session.activation(first);
                session.activation(second);
                session.marker(each[1]);
                session.expression("EXPR.v1.observed", constant("false"));
                session.expression("EXPR.v1.other", constant("true"));
                session.decision(first, "first#u1", taut);
                session.decision(second, "second#u1", taut);
                Endpoint observed = Endpoint.of(first, "Handler#put#3:WRITE",
                        at("w#1", 0), 0);
                Endpoint other = Endpoint.of(second, "Heartbeat#put#7:WRITE",
                        at("w#1", 0), 0);
                if (otherFirst) {
                    session.write(other, keys, 2L, "EXPR.v1.other");
                    session.write(observed, keys, 1L, "EXPR.v1.observed");
                } else {
                    session.write(observed, keys, 1L, "EXPR.v1.observed");
                    session.write(other, keys, 2L, "EXPR.v1.other");
                }
                session.read(Endpoint.of(reader, "Reader#get#5:READ",
                        at("r#1", 0), 0), keys, 1L, "read_k", "false");
                session.target("(or " + MARKER + " read_k)", explored, true);
                session.write();
            }
            Composer.Composition composition = compose(iteration, reader, 4,
                    StaticScopeMap.empty());
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            String shape = (String) row[0];
            assertEquals(shape + ": " + decision.claim().gaps(),
                    ClaimKind.MARKER_FLIPPED, decision.claim().kind());
            assertEquals(shape, "true",
                    decision.claim().movedRoots().get(MARKER_ROOT));
            ClaimPolicy.Outcome claimed = decision.outcomes().get(
                    decision.claim().valuationOrdinal());
            assertEquals(shape + ": the explored session's own run",
                    "s1", claimed.selected().path().sessionId);
            assertTrue(shape + ": on its observed arm", composition.repaired(
                    claimed.selected().selector(),
                    claimed.selectedArms().keySet()).isEmpty());
        }
    }

    @Test
    public void aWorldAnExploredReplayRanToTheFatalIsAValuation()
            throws Exception {
        Object[][] table = {
            {"an explored replay ran the root at -2001 and observed the "
                    + "fatal", true, ClaimKind.MARKER_FLIPPED},
            {"no explored replay ran it: the formula's own model",
                    false, ClaimKind.FORMULA_SAT},
        };
        for (Object[] row : table) {
            boolean explored = (Boolean) row[1];
            Path iteration = folder.newFolder().toPath();
            for (String id : explored ? new String[] {"s0", "s1"}
                    : new String[] {"s0"}) {
                boolean ran = id.equals("s1");
                Session session = new Session(iteration, id, ran);
                session.serial(ran ? "-2001" : "0", "-600000", "600000");
                session.target("(= " + SERIAL + " (- 2001))", ran, true);
                session.write();
            }
            if (explored) {
                obligation(iteration, "s1", Collections.singletonMap(
                        SERIAL_ROOT, "-2001"));
            }
            Composer.Composition composition = compose(iteration, 8);
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            assertEquals((String) row[0] + ": " + decision.claim().gaps(),
                    row[2], decision.claim().kind());
            assertEquals((String) row[0], Collections.singletonMap(
                    SERIAL_ROOT, "-2001"), decision.claim().movedRoots());
            assertEquals((String) row[0] + ": offered right after the "
                    + "recording", explored, "-2001".equals(composition
                    .valuations().get(1).moved().get(SERIAL_ROOT)));
        }
    }

    private static long asked(Path log) throws IOException {
        return Files.readAllLines(log).size();
    }

    @Test
    public void theDecideBudgetIsANamedBoundNeverARefutation()
            throws Exception {
        Path iteration = folder.newFolder("decide-budget").toPath();
        Session seed = new Session(iteration, "s0", false);
        seed.marker("false");
        seed.target(MARKER, false, true);
        seed.write();
        Composer.Composition composition = compose(iteration, 4);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver(), 0L);
        assertFalse("no refutation on the bound: " + decision.formula(),
                decision.formula() != null && decision.formula().unsat());
        assertFalse("no witness on the bound",
                decision.claim().kind() == ClaimKind.MARKER_FLIPPED);
        assertTrue("and the bound is named: " + decision.claim().gaps(),
                says(decision.claim().gaps(), GapKind.ADMISSION_GAP,
                        "decide budget"));
        ClaimPolicy.Decision within = ClaimPolicy.decide(composition,
                solver());
        assertEquals("within it, the claim", ClaimKind.MARKER_FLIPPED,
                within.claim().kind());
        assertFalse(says(within.claim().gaps(), GapKind.ADMISSION_GAP,
                "decide budget"));
    }

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
    public void anUnstatedReadIsHeldUnlessItsSessionsReRunDidNotLand()
            throws Exception {
        LocationId keys = LocationId.of(LocationKind.INSTANCE, "Manager",
                "held");
        Endpoint read = Endpoint.of(ANCHOR, "Manager#get#3:READ",
                at("r#1", 0), 0);
        String subject = SmtLowering.locationKey(keys) + "@7";
        for (Object[] row : new Object[][]{
                {false, "HELD " + subject, "FREE " + subject},
                {true, "FREE " + subject, "HELD " + subject}}) {
            boolean uncaptured = (Boolean) row[0];
            Path iteration = folder.newFolder("unstated-read-" + uncaptured)
                    .toPath();
            Session session = new Session(iteration, "s0", true);
            session.read(read, keys, 7L, "read_k", "false");
            session.target("read_k", false, true);
            session.write();
            if (uncaptured) {
                Files.write(iteration.resolve(SessionDir.UNCAPTURED),
                        "s0\n".getBytes(StandardCharsets.UTF_8));
            }
            Composer.Composition composition = compose(iteration, 4);
            List<String> named = new ArrayList<String>();
            for (Composer.Concrete concrete : composition.concrete()) {
                named.add(concrete.kind + " " + concrete.subject);
            }
            assertTrue(uncaptured + ": " + named, named.contains(row[1]));
            assertFalse(uncaptured + ": " + named, named.contains(row[2]));
        }
    }


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
            Session other = new Session(iteration, "s1", true);
            other.serial("7", "-600000", "600000");
            other.target("(and (< " + SERIAL + " 0) (not (< " + SERIAL
                    + " 0)))", false, true);
            other.write();
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
                assertEquals("all three moved, and the root the path never "
                                + "names stays where the run left it: "
                                + decision.claim().movedRoots(),
                        new LinkedHashSet<String>(Arrays.asList("ROOT.M_ONE",
                                "ROOT.M_TWO", "ROOT.M_THREE")),
                        decision.claim().movedRoots().keySet());
            }
            assertFalse(decision.claim().blocked());
        }
    }

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
    public void aJumpedClockCellNoPathNamesIsNoMovedRoot() throws Exception {
        Path idle = folder.newFolder("clock-idle").toPath();
        for (String id : new String[] {"s0", "s1"}) {
            Session session = new Session(idle, id, "s1".equals(id));
            session.clock("700");
            session.roots.add(RootMintRow.of(id, ++session.seq, ANCHOR,
                    "ROOT.IDLE", "clock_idle", RootKind.CLOCK,
                    RootCategory.CLOCK, "705", null, null, true,
                    Clock.of(1_000_000L, Clock.WALL), 0L));
            session.decision(ANCHOR, "anchor#u1", "(or (> " + CLOCK
                    + " 1000) (not (> " + CLOCK + " 1000)))", CLOCK_ROOT,
                    700L);
            if ("s1".equals(id)) {
                session.decision(ANCHOR, "anchor#u2", "(or (> clock_idle 0) "
                        + "(not (> clock_idle 0)))", "ROOT.IDLE", 705L);
            }
            session.target("(> " + CLOCK + " 1000)", false, true);
            session.write();
        }
        Composer.Composition composition = compose(idle, 4);
        Composer.Disjunct own = null;
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            if ("s0".equals(disjunct.path().sessionId)) own = disjunct;
        }
        assertTrue("both readings are cells of the clock: "
                        + composition.clockCells(),
                composition.clockCells().containsAll(
                        Arrays.asList(CLOCK, "clock_idle")));
        Map<String, String> model = new LinkedHashMap<String, String>();
        model.put(CLOCK, "5000");
        model.put("clock_idle", "9000");
        ClaimPolicy.Outcome jumped = new ClaimPolicy.Outcome(
                composition.free(0), Collections.<String>emptyList(),
                Z3.Answer.decided("sat", model),
                own,
                Collections.<String, ComposedFamilies.ArmChoice>emptyMap());
        assertEquals("the cell the path rests on is moved; the one only the "
                        + "clock's order moved is no plant of the witness",
                Collections.singleton(CLOCK),
                ClaimPolicy.movedRoots(composition, jumped).keySet());
    }

    @Test
    public void aWitnessWithoutPolarityIsNotAFinding() throws Exception {
        Path iteration = folder.newFolder("polarity").toPath();
        Session session = new Session(iteration, "s0", false);
        session.marker("false");
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

        Path skew = folder.newFolder("clock-skew").toPath();
        Session skewed = new Session(skew, "s0", false);
        skewed.clock("700");
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


    @Test
    public void anHbConcurrentWriterIsAnAlternativeAndAnAncestorIsNot()
            throws Exception {
        Path iteration = folder.newFolder("state").toPath();
        OccurrenceAddress reader = occurrence("case/dn0", "REGION.read",
                CausalContext.of(Endpoint.of(UPSTREAM, "PORT.rpc",
                        at("call#1", 0), 0).id(), "case/client/read"),
                frame("Reader#run#4", 0));
        OccurrenceAddress concurrent = occurrence("case/dn0",
                "REGION.heartbeat", CausalContext.of(Role.of("HEARTBEAT_TICK"), "", 1),
                frame("Heartbeat#run#9", 0));
        LocationId keys = LocationId.of(LocationKind.MAP, "21", "allKeys");
        LocationId aliased = LocationId.of(LocationKind.MAP,
                "BlockTokenSecretManager", "allKeys");

        Session session = new Session(iteration, "s0", false);
        session.occurrence = reader;
        session.activation(reader);
        session.activation(concurrent);
        session.activation(UPSTREAM);
        session.marker("false");
        session.expression("EXPR.v1.rpc", symbol(MARKER, "Z"));
        session.export(Endpoint.of(UPSTREAM, "PORT.rpc", at("call#1", 0), 0),
                "EXPR.v1.rpc", 1L, "false");
        session.expression("EXPR.v1.first", symbol(MARKER, "Z"));
        session.expression("EXPR.v1.second", symbol(MARKER, "Z"));
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
        assertFalse("an ancestor of the reader is not an alternative",
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null))
                        .concurrent(reader, UPSTREAM, "s0"));
        assertTrue("a heartbeat tick beside it is",
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null))
                        .concurrent(reader, concurrent, "s0"));
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
        assertFalse(compose(iteration, reader, 4, StaticScopeMap.empty())
                .body().contains("deleted5@w1"));
    }

    @Test
    public void aLongEnumChoicesDefinednessIsAFactWhereItsCompareIsStated() {
        Map<String, VmTermLowering.Sort> declared =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        declared.put("s", VmTermLowering.Sort.STRING);
        SmtLowering lowering = new SmtLowering(declared);
        JsonObject state = enumValueOf("s");
        JsonArray named = state.getAsJsonArray("_param_list");
        named.set(1, vmString("toUpperCase", vmLeaf("SymbolExpression", "s",
                "Ljava/lang/String;")));
        while (named.size() > 2) named.remove(2);
        for (char constant = 'A'; constant <= 'L'; constant++) {
            named.add(vmLeaf("ConStringSymbolExp", "Y_L'String'_STATE_OF_A_"
                    + "LONG_NAMED_CONSTANT_" + constant, "java/lang/String"));
        }
        VmTermLowering.Term term = lowering.dispatch(vmString("equals",
                vmLeaf("ConStringSymbolExp", "Y_L'String'_STATE_OF_A_LONG_"
                        + "NAMED_CONSTANT_A", "java/lang/String"), state),
                VmTermLowering.Sort.BOOL, "t");
        assertTrue(lowering.openRefusals().toString(),
                lowering.openRefusals().isEmpty());
        lowering.assertPlain(term.precondition);
        String compare = term.text;
        List<String> facts = lowering.facts(Collections.singletonList(
                compare));
        assertTrue(compare + " " + facts, facts.stream().anyMatch(fact
                -> fact.contains("defined_dag__")));
    }

    @Test
    public void aHeldEnumNameIsTheValueOfAReadThatDoesNotMove() {
        Object[][] table = {
                {"no write row states its version", false, false, true},
                {"a write row states it: the read's join", true, false, true},
                {"a family re-pairs the read: its own value", true, true,
                        false},
        };
        for (Object[] row : table) {
            String name = (String) row[0];
            boolean stated = (Boolean) row[1];
            boolean repaired = (Boolean) row[2];
            JsonObject node = read("INSTANCE", 99L, 96L, 3913L, "L");
            node.addProperty(VmRows.WRITER_SET_COMPLETE, true);
            node.getAsJsonObject(VmRows.OBSERVED_VERSION).add("expression",
                    vmLeaf("ConStringSymbolExp", "Y_L'String'_OPEN",
                            "java/lang/String"));
            JsonObject copy = read("INSTANCE", 733L, 48L, 6053L, "L");
            copy.addProperty(VmRows.WRITER_SET_COMPLETE, true);
            copy.getAsJsonObject(VmRows.OBSERVED_VERSION).add("expression",
                    node);
            String key = SmtLowering.locationKey(copy.getAsJsonObject(
                    "location"));
            SmtLowering lowering = new SmtLowering(
                    new LinkedHashMap<String, VmTermLowering.Sort>());
            lowering.begin("s0", SmtLowering.repairing(
                    new SmtLowering.SessionJoin() {
                        @Override
                        public JsonElement writeExpression(String location,
                                                           long version) {
                            return stated && key.equals(location)
                                    && version == 6053L ? node : null;
                        }

                        @Override
                        public List<WriteRow> writes(String location) {
                            return Collections.<WriteRow>emptyList();
                        }

                        @Override
                        public List<ReadRow> reads(String location) {
                            return Collections.<ReadRow>emptyList();
                        }

                        @Override
                        public Set<String> mintedReadSymbols(long version) {
                            return Collections.<String>emptySet();
                        }

                        @Override
                        public Set<String> readSymbols(String location,
                                                       long version) {
                            return Collections.<String>emptySet();
                        }

                        @Override
                        public boolean moves(String symbol) {
                            return false;
                        }

                        @Override
                        public boolean repaired(String location, long event) {
                            return false;
                        }

                        @Override
                        public boolean concurrent(OccurrenceAddress reader,
                                                  OccurrenceAddress writer) {
                            return false;
                        }
                    }, (location, event) -> repaired && key.equals(location),
                    (reader, writer) -> false), null);
            VmTermLowering.Term term = lowering.dispatch(vmString("equals",
                    vmLeaf("ConStringSymbolExp", "Y_L'String'_OPEN",
                            "java/lang/String"), copy),
                    VmTermLowering.Sort.BOOL, "t");
            List<String> refusals = lowering.openRefusals();
            assertEquals(name + ": " + term.text, VmTermLowering.Sort.BOOL,
                    term.sort);
            if ((Boolean) row[3]) {
                assertTrue(name + ": " + refusals, refusals.isEmpty());
                assertTrue(name + ": " + term.text,
                        term.text.contains("\"OPEN\""));
            } else {
                assertFalse(name + ": a read that moves is never its recorded"
                        + " name: " + term.text, term.text.contains(
                        "(= \"OPEN\" \"OPEN\")"));
            }
        }
    }

    @Test
    public void anUntakenFatalOnAnUnmodeledOperationHoldsWhereNothingItRestsOnMoved()
            throws Exception {
        String opened = "EXPR.0000000000000a01";
        String way = "Gate#isOpened#u3";
        String clocked = "(and (not " + opened + ") (> " + CLOCK + " 0))";
        Object[][] table = {
                {"it rests on nothing that moves", "(not " + opened + ")",
                        "", ClaimKind.NO_SUPPORTED_WITNESS},
                {"it rests on a marker too", "(and (not " + opened + ") "
                        + MARKER + ")", "", ClaimKind.MARKER_FLIPPED},
                {"another run took the fatal", "(not " + opened + ")",
                        "taken", null},
                {"the way guard's other arm", "(or " + opened + " " + MARKER
                        + ")", "way", ClaimKind.MARKER_FLIPPED},
                {"it rests on a clock", clocked, "clock", null},
        };
        for (Object[] row : table) {
            String name = (String) row[0];
            String shape = (String) row[2];
            Path iteration = folder.newFolder("unmodeled-" + name.replace(' ',
                    '-').replace("'", "")).toPath();
            List<String> ids = "taken".equals(shape)
                    ? Arrays.asList("s0", "s1")
                    : Collections.singletonList("s0");
            for (String id : ids) {
                boolean took = "s1".equals(id);
                Session session = new Session(iteration, id, took);
                session.marker(took ? "true" : "false");
                if ("clock".equals(shape)) session.clock("5");
                session.expression(opened, vmString("equals", vmLeaf(
                        "ConStringSymbolExp", "Y_L'String'_OPEN",
                        "java/lang/String"), vmLeaf("SymbolExpression",
                        "M_L'org/x/State'_412", "Lorg/x/State;")));
                if ("way".equals(shape)) {
                    session.decision(ANCHOR, way, false, (String) row[1]);
                    session.target("true", false, false);
                } else {
                    session.target((String) row[1], took, true);
                }
                session.write();
            }
            Path map = iteration.resolve(StaticScopeMap.FILE);
            Files.write(map, Collections.singletonList("{\"kind\":\""
                    + StaticScopeMap.SITE_KIND + "\",\"role\":\""
                    + StaticScopeMap.TARGET_SITE + "\",\"regionId\":\""
                    + ANCHOR.regionId() + "\",\"siteId\":\"T#1\","
                    + "\"guards\":[\"" + ANCHOR_SITE + "\",\"" + way
                    + "\"]}"), StandardCharsets.UTF_8);
            Composer.Composition composition = compose(iteration, ANCHOR, 4,
                    StaticScopeMap.read(map));
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            if ("taken".equals(shape)) {
                boolean free = false;
                for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
                    free |= "sat".equals(outcome.answer().status())
                            && "s1".equals(outcome.selected().path()
                            .sessionId);
                }
                assertTrue(name + ": the run that took it stays free: "
                        + decision.outcomes(), free);
                assertNotEquals(name, ClaimKind.NO_SUPPORTED_WITNESS,
                        decision.claim().kind());
                continue;
            }
            if ("clock".equals(shape)) {
                assertTrue(name + ": named, not held: "
                                + composition.gaps(),
                        says(composition.gaps(), GapKind.UNSTATED_VALUE,
                                "the clock or unminted value " + CLOCK));
                continue;
            }
            assertEquals(name + ": " + decision.claim().gaps(), row[3],
                    decision.claim().kind());
            if (row[3] == ClaimKind.MARKER_FLIPPED) {
                assertEquals(name + ": the claim names what moved",
                        Collections.singletonMap(MARKER_ROOT, "true"),
                        decision.claim().movedRoots());
            }
        }
    }

    private static JsonObject enumValueOf(String leaf) {
        JsonObject valueOf = new JsonObject();
        valueOf.addProperty("_type", "MethodExpression");
        valueOf.addProperty("_name", "java/lang/Enum valueOf");
        valueOf.addProperty("_java_type", "Lorg/x/State;");
        JsonArray arguments = new JsonArray();
        arguments.add(vmLeaf("ConStringSymbolExp", "Y_L'String'_org.x.State",
                "java/lang/String"));
        arguments.add(vmLeaf("SymbolExpression", leaf, "Ljava/lang/String;"));
        arguments.add(vmLeaf("ConStringSymbolExp", "Y_L'String'_ACTIVE",
                "java/lang/String"));
        arguments.add(vmLeaf("ConStringSymbolExp", "Y_L'String'_DOWN",
                "java/lang/String"));
        valueOf.add("_param_list", arguments);
        return valueOf;
    }

    private static JsonObject stored(JsonObject value) {
        JsonObject put = relation("ASSOCIATIVE", "PUT", "java/util/Map",
                relation("ASSOCIATIVE", "SNAPSHOT_BASE", "java/util/HashMap",
                        null), integer("I", 5L), value);
        return binary("==", relation("ASSOCIATIVE", "READ",
                "java/util/ArrayList", put, integer("I", 5L)), vmNull());
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
        LocationId reserves = LocationId.of(LocationKind.MAP, "50", "-3");
        session.roots.add(RootMintRow.of(id, ++session.seq, reserver,
                "ROOT.RESERVED", RESERVED, RootKind.CLOCK, RootCategory.CLOCK,
                Long.toString(seed - 1_000L), null, null, true, Clock.of(1L, Clock.MONOTONIC), 0L));
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

    @Test
    public void aReadMayRunBeforeAConcurrentWriteAndSeeTheValueBeforeIt()
            throws Exception {
        OccurrenceAddress reader = occurrence("case/f1", "REGION.sync",
                CausalContext.of(Role.of("OM_HANDLER"), "", 1),
                frame("LearnerHandler#run#1", 0));
        OccurrenceAddress startup = occurrence("case/f1", "REGION.start",
                CausalContext.of(Role.of("PEER_START"), "", 1),
                frame("QuorumPeer#start#1", 0));
        OccurrenceAddress apply = occurrence("case/f1", "REGION.apply",
                CausalContext.of(Role.of("COMMIT"), "", 1),
                frame("CommitProcessor#run#1", 0));
        LocationId zxid = LocationId.of(LocationKind.INSTANCE, "30", "24");
        Object[][] table = {
            {"the predecessor's writer runs before the reader, the write"
                    + " between them beside it", apply, true},
            {"the write between them runs before the reader too", startup,
                    false},
        };
        for (int row = 0; row < table.length; row++) {
            Path at = folder.newFolder("eligible" + row).toPath();
            Session session = new Session(at, "s0", false);
            session.occurrence = reader;
            session.activation(reader, "thread#sync", false);
            session.activation(startup, "thread#sync", false);
            session.activation(apply, "thread#apply", false);
            session.expression("EXPR.z", constant("1"));
            session.write(Endpoint.of(startup, "DataTree#load#1:WRITE",
                    at("w#1", 0), 0), zxid, 1L, "EXPR.z");
            session.write(Endpoint.of((OccurrenceAddress) table[row][1],
                    "DataTree#processTxn#2:WRITE", at("w#2", 0), 0), zxid,
                    2L, "EXPR.z");
            session.write(Endpoint.of(apply, "DataTree#processTxn#3:WRITE",
                    at("w#3", 0), 0), zxid, 3L, "EXPR.z");
            session.read(Endpoint.of(reader, "LearnerHandler#sync#4:READ",
                    at("r#1", 0), 0), zxid, 3L, "read_z", "1");
            session.target("read_z", false, true);
            session.write();
            Set<Long> versions = new TreeSet<Long>();
            for (WriteRow write : Corpus.read(at, null).eligibleWrites("s0",
                    SmtLowering.locationKey(zxid), 3L, reader)) {
                versions.add(write.version());
            }
            assertEquals((String) table[row][0], table[row][2],
                    versions.contains(1L));
        }
    }

    @Test
    public void twoOccurrencesUnderOneMessageAreConcurrentThoughItsSenderIsUnknown()
            throws Exception {
        OccurrenceAddress sender = occurrence("case/l3", "REGION.handler",
                CausalContext.of("unknown-endpoint", "ZK_QUORUM/test"),
                frame("LearnerHandler#run#1", 0));
        Endpoint message = Endpoint.of(sender, "PORT.uptodate",
                at("send#1", 0), 0);
        OccurrenceAddress reader = occurrence("case/f1", "REGION.sync",
                CausalContext.of(message.id(), "ZK_QUORUM/test"),
                frame("LearnerHandler#run#2", 0));
        OccurrenceAddress sibling = occurrence("case/f1", "REGION.apply",
                CausalContext.of(message.id(), "ZK_QUORUM/test"),
                frame("CommitProcessor#run#1", 0));
        Endpoint handed = Endpoint.of(reader, "PORT.inform", at("send#2", 0),
                0);
        OccurrenceAddress child = occurrence("case/o4", "REGION.observe",
                CausalContext.of(handed.id(), "ZK_QUORUM/test"),
                frame("Observer#run#1", 0));
        Path iteration = folder.newFolder("siblings").toPath();
        Session session = new Session(iteration, "s0", false);
        session.occurrence = reader;
        session.activation(sender, "thread#leader", false);
        session.activation(reader, message);
        session.activation(sibling, message);
        session.activation(child, handed);
        session.target("true", false, true);
        session.write();
        edu.uva.liftlab.graphchecker.smt.Arms arms =
                new edu.uva.liftlab.graphchecker.smt.Arms(
                        Corpus.read(iteration, null));
        Object[][] table = {
            {"two occurrences one message started, its sender's own start"
                    + " unknown", sibling, true},
            {"an occurrence a message of the reader started", child, false},
        };
        for (Object[] row : table) {
            assertEquals((String) row[0], row[2], arms.concurrent(reader,
                    (OccurrenceAddress) row[1], "s0"));
        }
    }

    @Test
    public void aMessageNoCompatibleRunAttestsIsHeldAtItsOwnRunsArrival()
            throws Exception {
        Endpoint sent = Endpoint.of(PRODUCER, "PORT.held", at("export#1", 0),
                0);
        Endpoint got = Endpoint.of(ANCHOR, "PORT.held", at("attach#1", 0), 0);
        for (boolean own : new boolean[] {false, true}) {
            Path iteration = folder.newFolder("held-" + own).toPath();
            session(iteration, "s0", false, "false", sent, got, "vh", "false",
                    null, false, false, "EXPR.v1.vh", null);
            session(iteration, "s1", true, "false", sent, got, "vh", "false",
                    null, own, false, "EXPR.v1.vh", own ? symbol(MARKER, "Z")
                            : null);
            session(iteration, "s2", true, "true", sent, got, "vh", "true",
                    null, true, true, "EXPR.v1.vh");
            obligation(iteration, "s1", Collections.<String, String>emptyMap(),
                    "a#u1", Collections.<String>emptyList());
            obligation(iteration, "s2", Collections.<String, String>emptyMap(),
                    "b#u1", Collections.<String>emptyList());
            Composer.Composition composition = compose(iteration, ANCHOR, 4,
                    StaticScopeMap.empty());
            Composer.Disjunct path = null;
            for (Composer.Disjunct each : composition.disjuncts()) {
                if (each.path().sessionId.equals("s1")) path = each;
            }
            assertNotNull(own + ": the path is composed, not refused: "
                    + composition.gaps(), path);
            String pairing = composition.recordedPairing(path.selector());
            assertEquals(own + ": its own arm, else its own arrival: "
                    + composition.body(), !own, composition.body().contains(
                    "(=> " + path.selector() + " (= vh false))"));
            assertEquals(own + ": " + pairing, own, pairing != null
                    && pairing.contains("message_arm__"));
        }
    }

    @Test
    public void aReadInTheOccurrenceItsWorldFlippedIsOnTheFatalPath()
            throws Exception {
        OccurrenceAddress flipped = occurrence("case/dn0", "REGION.sync",
                CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                frame("Handler#sync#2", 0));
        OccurrenceAddress other = occurrence("case/dn0", "REGION.other",
                CausalContext.of(Role.of("HEARTBEAT_TICK"), "", 1),
                frame("Heartbeat#run#9", 0));
        LocationId zxid = LocationId.of(LocationKind.INSTANCE, "30", "zxid");
        Path iteration = folder.newFolder("flip-path").toPath();
        Map<OccurrenceAddress, ReadRow> reads =
                new LinkedHashMap<OccurrenceAddress, ReadRow>();
        for (String id : new String[] {"s0", "s1"}) {
            Session session = new Session(iteration, id, id.equals("s1"));
            session.activation(flipped);
            session.activation(other);
            session.expression("EXPR.v1.z", integer("J", 1L));
            session.write(Endpoint.of(other, "Heartbeat#set#3:WRITE",
                    at("w#1", 0), 0), zxid, 1L, "EXPR.v1.z");
            int at = 1;
            for (OccurrenceAddress reader : new OccurrenceAddress[] {flipped,
                    other}) {
                session.read(Endpoint.of(reader, "Read#zxid#" + at + ":READ",
                        at("r#" + at, 0), 0), zxid, 1L, "zxid_" + at++, "J",
                        "1");
            }
            session.target(id.equals("s1") ? "true" : "false",
                    id.equals("s1"), true);
            session.write();
        }
        obligation(iteration, "s1", Collections.<String, String>emptyMap(),
                "Handler#sync#u50", Collections.<String>emptyList(),
                flipped.id());
        Corpus corpus = Corpus.read(iteration, null);
        for (ReadRow read : corpus.session("s1").reads()) {
            reads.put(read.endpoint().occurrence(), read);
        }
        Composer.Composition composition = compose(iteration, ANCHOR, 4,
                StaticScopeMap.empty());
        Composer.Disjunct path = null;
        for (Composer.Disjunct each : composition.disjuncts()) {
            if (each.path().sessionId.equals("s1")) path = each;
        }
        assertNotNull(composition.gaps().toString(), path);
        assertEquals(Composer.Composition.FatalPath.FLIP,
                composition.onFatalPath(path, reads.get(flipped)));
        assertNull(composition.onFatalPath(path, reads.get(other)));
    }

    private static JsonObject putCommit(JsonObject state, long generation) {
        return relation("ASSOCIATIVE", "PUT", "java/util/Map", state,
                integer("J", generation), symbol(
                        "M_L'org/apache/solr/core/IndexCommitWrapper'_"
                                + (100L + generation),
                        "org/apache/solr/core/IndexCommitWrapper"));
    }

    @Test
    public void aClockAnArrivalCarriesMovesUnderItsOwnArmBeforeAnyFault()
            throws Exception {
        OccurrenceAddress reader = occurrence("case/dn0", "REGION.report",
                CausalContext.of(Role.of("IPC_HANDLER"), "", 1),
                frame("Master#report#4", 0));
        OccurrenceAddress activating = occurrence("case/dn0",
                "REGION.activate", CausalContext.of(Role.of("MASTER"), "", 1),
                frame("Master#run#2", 0));
        Endpoint sent = Endpoint.of(PRODUCER, "PORT.time", at("export#1", 0),
                0);
        LocationId active = LocationId.of(LocationKind.INSTANCE, "10",
                "activeTime");
        Object[][] table = {
                {"carried", "(> vh read_t1)", ClaimKind.CLOCK_SKEW},
                {"a fault also reaches it", "(or (> vh read_t1) " + MARKER
                        + ")", ClaimKind.CLOCK_SKEW},
                {"only a fault reaches it", MARKER, ClaimKind.MARKER_FLIPPED},
        };
        for (Object[] row : table) {
            String name = (String) row[0];
            Path iteration = folder.newFolder("carried-" + name.replace(' ',
                    '-')).toPath();
            Session session = new Session(iteration, "s0", false);
            session.occurrence = reader;
            session.activation(reader);
            session.activation(activating);
            session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
                    false, true);
            session.marker("false");
            session.root(PRODUCER, "ROOT.T0", "clock_t0", RootKind.CLOCK,
                    "700");
            session.decision(PRODUCER, "nn#u1", "(or (> clock_t0 0) (not "
                    + "(> clock_t0 0)))", "ROOT.T0", 700L);
            session.expression("EXPR.v1.t0", symbol("clock_t0", "J"));
            session.export(sent, "EXPR.v1.t0", "J", 1L, "700");
            session.root(activating, "ROOT.T1", "clock_t1", RootKind.CLOCK,
                    "800");
            session.decision(activating, "activate#u1", "(or (> clock_t1 0) "
                    + "(not (> clock_t1 0)))", "ROOT.T1", 800L);
            session.expression("EXPR.v1.zero", integer("J", 0L));
            session.expression("EXPR.v1.t1", symbol("clock_t1", "J"));
            session.writes.add(WriteRow.initial("s0", ++session.seq,
                    Endpoint.of(activating, "Master#<clinit>#1:INITIAL",
                            at("w#0", 0), 0), active, 1L, "EXPR.v1.zero",
                    "J"));
            session.write(Endpoint.of(activating, "Master#activate#9:WRITE",
                    at("w#1", 0), 0), active, 2L, "EXPR.v1.t1");
            session.attach(Endpoint.of(reader, "PORT.time", at("attach#1",
                    0), 0), "vh", "J", "700", sent);
            session.read(Endpoint.of(reader, "Master#activeTime#5:READ",
                    at("r#1", 0), 0), active, 2L, "read_t1", "J", "800");
            session.target((String) row[1], false, true);
            session.write();

            Composer.Composition composition = compose(iteration, reader, 4,
                    StaticScopeMap.empty());
            String pairing = composition.recordedPairing(
                    composition.disjuncts().get(0).selector());
            assertTrue(name + ": the arrival is held by its own run's arm: "
                    + pairing, pairing.contains("message_arm__"));
            assertFalse(name + ": not by the value it carried, which the "
                    + "producer's clock moves: " + pairing,
                    pairing.contains("(= vh 700)"));
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            assertEquals(name + ": " + decision.claim().gaps(), row[2],
                    decision.claim().kind());
            if (row[2] != ClaimKind.CLOCK_SKEW) continue;
            String moved = decision.claim().movedRoots().get("clock_t0");
            assertNotNull(name + ": the producer's clock carries the skew: "
                    + decision.claim().movedRoots(), moved);
            assertTrue(name + ": past the reading the report is compared "
                    + "with: " + moved, Long.parseLong(moved.trim()) > 800L);
            assertFalse(name + ": the nearer world injects no fault: "
                    + decision.claim().movedRoots(),
                    decision.claim().movedRoots().containsKey(MARKER_ROOT));
        }
    }

    @Test
    public void aCellTheRecordingNeverReadIsPlacedByAnotherNodesReadingOfTheSameJvmClock()
            throws Exception {
        Object[][] table = {
                {"the same JVM clock", Clock.WALL, ClaimKind.CLOCK_SKEW},
                {"another JVM clock", Clock.MONOTONIC,
                        ClaimKind.NO_SUPPORTED_WITNESS},
        };
        for (Object[] row : table) {
            String name = (String) row[0];
            Path iteration = folder.newFolder("placed-" + name.replace(' ',
                    '-')).toPath();
            Session seed = new Session(iteration, "s0", false);
            seed.root(PRODUCER, "ROOT.T1", "clock_t1", RootKind.CLOCK, "700");
            seed.target("false", false, true);
            seed.write();
            Session rerun = new Session(iteration, "s1", true);
            rerun.root(PRODUCER, "ROOT.T1", "clock_t1", RootKind.CLOCK, "900");
            rerun.roots.add(RootMintRow.of("s1", ++rerun.seq, ANCHOR,
                    "ROOT.T0", "clock_t0", RootKind.CLOCK, RootCategory.CLOCK,
                    "950", null, null, true,
                    Clock.of(1_000_000L, (String) row[1]), 0L));
            rerun.decision(ANCHOR, "anchor#u1", "(or (> clock_t0 2000) (not "
                    + "(> clock_t0 2000)))", "ROOT.T0", 950L);
            rerun.target("(> clock_t0 2000)", false, true);
            rerun.write();

            Composer.Composition composition = compose(iteration, 4);
            ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                    solver());
            assertEquals(name + ": " + decision.claim().gaps(), row[2],
                    decision.claim().kind());
            if (row[2] != ClaimKind.CLOCK_SKEW) continue;
            String floor = null;
            for (RootDomain domain : composition.roots()) {
                if (domain.rootId().equals("ROOT.T0")) floor = domain.min();
            }
            assertEquals(name + ": the seed's reading of the other node's "
                    + "cell, plus the time the rerun's host ran between the "
                    + "two", "750", floor);
            String moved = decision.claim().movedRoots().get("clock_t0");
            assertNotNull(name + ": the claim names the cell it moved: "
                    + decision.claim().movedRoots(), moved);
            assertTrue(name + ": " + moved,
                    Long.parseLong(moved.trim()) > 2000L);
        }
    }

    @Test
    public void aMessageArmRestingOnACellWithNoInstantIsNoOption()
            throws Exception {
        Endpoint sent = Endpoint.of(PRODUCER, "PORT.time", at("export#1", 0),
                0);
        Object[][] table = {
                {"the same JVM clock", Clock.WALL,
                        ClaimKind.MESSAGE_PAIRING_FLIPPED},
                {"another JVM clock", Clock.MONOTONIC,
                        ClaimKind.NO_SUPPORTED_WITNESS},
        };
        for (Object[] row : table) {
            String name = (String) row[0];
            Path iteration = folder.newFolder("arm-" + name.replace(' ',
                    '-')).toPath();
            Session seed = new Session(iteration, "s0", false);
            seed.activation(PRODUCER, "thread#" + PRODUCER.regionId(), false,
                    true);
            seed.root(PRODUCER, "ROOT.T1", "clock_t1", RootKind.CLOCK, "700");
            seed.expression("EXPR.v1.c", integer("J", 700L));
            seed.export(sent, "EXPR.v1.c", "J", 1L, "700");
            seed.attach(Endpoint.of(ANCHOR, "PORT.time", at("attach#1", 0),
                    0), "vh", "J", "700", sent);
            seed.target("(> vh 2000)", false, true);
            seed.write();
            Session rerun = new Session(iteration, "s1", true);
            rerun.activation(PRODUCER, "thread#" + PRODUCER.regionId(), true,
                    true);
            rerun.root(PRODUCER, "ROOT.T1", "clock_t1", RootKind.CLOCK, "900");
            rerun.roots.add(RootMintRow.of("s1", ++rerun.seq, PRODUCER,
                    "ROOT.T0", "clock_t0", RootKind.CLOCK, RootCategory.CLOCK,
                    "950", null, null, true,
                    Clock.of(1_000_000L, (String) row[1]), 0L));
            rerun.decision(PRODUCER, "nn#u1", "(or (> clock_t0 0) (not (> "
                    + "clock_t0 0)))", "ROOT.T0", 950L);
            rerun.expression("EXPR.v1.t0", symbol("clock_t0", "J"));
            rerun.export(sent, "EXPR.v1.t0", "J", 1L, "950");
            rerun.attach(Endpoint.of(ANCHOR, "PORT.time", at("attach#1", 0),
                    0), "vh", "J", "950", sent);
            rerun.write();

            ClaimPolicy.Decision decision = ClaimPolicy.decide(
                    compose(iteration, 4), solver());
            assertEquals(name + ": " + decision.claim().gaps(), row[2],
                    decision.claim().kind());
            if (row[2] == ClaimKind.MESSAGE_PAIRING_FLIPPED) {
                assertNotNull(name + ": the claim names the cell it moved: "
                                + decision.claim().movedRoots(),
                        decision.claim().movedRoots().get("clock_t0"));
            }
        }
    }

    @Test
    public void aWireLeafIsHeldToItsTextOnlyWhereTheClaimMovedWhatItCarries() {
        Set<String> none = Collections.<String>emptySet();
        Map<String, ComposedFamilies.BoundLeaf> leaves =
                new LinkedHashMap<String, ComposedFamilies.BoundLeaf>();
        leaves.put("c-moved", new ComposedFamilies.BoundLeaf("v_moved", "J",
                ANCHOR.id(), false, none, Collections.singleton(MARKER_ROOT)));
        leaves.put("c-recorded", new ComposedFamilies.BoundLeaf("v_recorded",
                "J", ANCHOR.id(), false, none, none));
        leaves.put("c-clocked", new ComposedFamilies.BoundLeaf("v_clocked",
                "J", ANCHOR.id(), true, none,
                Collections.singleton(MARKER_ROOT)));
        leaves.put("c-nested", new ComposedFamilies.BoundLeaf("v_nested",
                "J", ANCHOR.id(), false, Collections.singleton("v_moved"),
                none));
        ComposedFamilies.ArmChoice arm = ComposedFamilies.ArmChoice.of(
                "message_family__0", "g", Collections.<String>emptyList(), "s0",
                Collections.<edu.uva.liftlab.graphchecker.smt.Arms.Arm>
                        emptyList(), leaves);
        Map<String, String> model = new LinkedHashMap<String, String>();
        model.put("v_moved", "5");
        model.put("v_recorded", "6");
        model.put("v_clocked", "7");
        model.put("v_nested", "8");
        Object[][] table = {
            {"a fault moved", Collections.singleton(MARKER_ROOT),
                    "{c-moved=5, c-nested=8}"},
            {"nothing moved", none, "{}"},
        };
        for (Object[] row : table) {
            @SuppressWarnings("unchecked")
            Set<String> moved = (Set<String>) row[1];
            assertEquals(row[0] + ": a leaf the model does not state (a "
                            + "recording's text, a clock's reading) is no "
                            + "edge CONFIRM holds", row[2],
                    ComposedFamilies.texts(Collections.singletonList(arm),
                            model, ANCHOR.id(), moved).toString());
        }
    }

    @Test
    public void theInitialIsTheWriterAtVersionZero() throws Exception {
        String map = "java/util/concurrent/ConcurrentHashMap";
        LocationId pools = LocationId.of(LocationKind.MAP, "21", "-3");
        for (String variant : new String[]{"concurrent", "constructor",
                "constructor-caller", "started-in-constructor", "own-thread",
                "unrowed-between", "read-after-its-own-write"}) {
            boolean moves = "concurrent".equals(variant)
                    || "started-in-constructor".equals(variant);
            long observed = "unrowed-between".equals(variant) ? 3L : 2L;
            boolean own = "read-after-its-own-write".equals(variant);
            LocationId size = LocationId.of(LocationKind.INSTANCE, "21",
                    "count");
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
            if (own) {
                session.read(Endpoint.of(writer, "Pools#size#9:READ",
                        at("w#3", 0), 0), pools, observed,
                        "MAP_STATE/21#-3@v" + observed + "@s0", "L", null);
                session.expression("EXPR.0000000000000012",
                        integer("I", 1L));
                session.writes.add(WriteRow.of("s0", ++session.seq,
                        Endpoint.of(writer, "Pools#count#11:WRITE",
                                at("w#4", 0), 0), size, 9L,
                        "EXPR.0000000000000012", "I"));
            }
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
            if (own) {
                session.read(Endpoint.of(reader, "Pools#count#13:READ",
                        at("r#2", 0), 0), size, 9L, "count_v9", "I", "1");
            }
            session.expression("EXPR.0000000000000060", binary("==",
                    answered, vmNull()));
            session.target("EXPR.0000000000000060", false, true);
            session.write();

            edu.uva.liftlab.graphchecker.smt.Arms arms =
                    new edu.uva.liftlab.graphchecker.smt.Arms(
                            Corpus.read(iteration, null));
            assertEquals(variant, moves || "read-after-its-own-write".equals(
                    variant) ? 2 : 1, arms.stateArms(asking, "s0",
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
        assertTrue("an occurrence nothing places is concurrent with all",
                rule.concurrent(earlier, started, "s0"));
        assertTrue("a symbolic straight-line region is attested",
                rule.attested("s0", later));
    }

    @Test
    public void everyStringOperationTheVmCarriesIsJavasOwn() {
        StringRows rows = new StringRows(solver());
        JsonObject s = vmLeaf("SymbolExpression", "s", "java/lang/String");
        JsonObject t = vmLeaf("SymbolExpression", "t", "java/lang/String");
        JsonObject n = vmLeaf("SymbolExpression", "n", "I");
        JsonObject m = vmLeaf("SymbolExpression", "m", "I");
        JsonObject k = vmLeaf("SymbolExpression", "k", "I");
        String abc = "abcabc";
        for (String x : new String[] {"ca", "", "bc", "abcabcd"}) {
            for (int at : new int[] {-1, 0, 2, 6, 7}) {
                rows.check(vmString("startsWith", s, t, n), abc, x, at, 0, 0,
                        () -> abc.startsWith(x, at));
                rows.check(vmString("indexOf", s, t, n), abc, x, at, 0, 0,
                        () -> abc.indexOf(x, at));
                rows.check(vmString("lastIndexOf", s, t, n), abc, x, at, 0,
                        0, () -> abc.lastIndexOf(x, at));
            }
            rows.check(vmString("indexOf", s, t), abc, x, 0, 0, 0,
                    () -> abc.indexOf(x));
            rows.check(vmString("lastIndexOf", s, t), abc, x, 0, 0, 0,
                    () -> abc.lastIndexOf(x));
            rows.check(vmString("compareTo", s, t), abc, x, 0, 0, 0,
                    () -> abc.compareTo(x));
        }
        for (String x : new String[] {"", "a"}) {
            for (int at : new int[] {-1, 0, 1}) {
                rows.check(vmString("startsWith", s, t, n), "", x, at, 0, 0,
                        () -> "".startsWith(x, at));
                rows.check(vmString("indexOf", s, t, n), "", x, at, 0, 0,
                        () -> "".indexOf(x, at));
                rows.check(vmString("lastIndexOf", s, t, n), "", x, at, 0, 0,
                        () -> "".lastIndexOf(x, at));
            }
        }
        for (String x : new String[] {"abd", "ab", "b", "abcd", "ABC"}) {
            rows.check(vmString("compareTo", s, t), "abc", x, 0, 0, 0,
                    () -> "abc".compareTo(x));
        }
        String[][] cases = {{"true", "TRUE"}, {"true", "tRuE"}, {"true", "tru"},
                {"true", "truex"}, {"", ""}, {"", "a"}, {"k", "\u212a"},
                {"s", "\u017f"}, {"i", "\u0130"}, {"i", "\u0131"},
                {"i", "j"}, {"x-1", "X-1"}};
        for (String[] pair : cases) {
            rows.check(vmString("equalsIgnoreCase", s, VmExpressionIr
                    .stringConstant(pair[0])), pair[1], "", 0, 0, 0,
                    () -> pair[1].equalsIgnoreCase(pair[0]));
            rows.check(vmString("equalsIgnoreCase", VmExpressionIr
                    .stringConstant(pair[0]), t), "", pair[1], 0, 0, 0,
                    () -> pair[0].equalsIgnoreCase(pair[1]));
        }
        String wide = "a\ud83d\ude00ba";
        for (int point : new int[] {'a', 0x1F600, 0xD83D, -1, 0x110000}) {
            rows.check(vmString("indexOf", s, n), wide, "", point, 0, 0,
                    () -> wide.indexOf(point));
            rows.check(vmString("indexOf", s, n, m), wide, "", point, 1, 0,
                    () -> wide.indexOf(point, 1));
            rows.check(vmString("lastIndexOf", s, n), wide, "", point, 0, 0,
                    () -> wide.lastIndexOf(point));
            rows.check(vmString("lastIndexOf", s, n, m), wide, "", point, 2,
                    0, () -> wide.lastIndexOf(point, 2));
        }
        JsonObject b = vmLeaf("ConstExpr", "C_I_98", "I");
        rows.check(vmString("indexOf", s, b, m), abc, "", 0, 2, 0,
                () -> abc.indexOf('b', 2));
        rows.check(vmString("lastIndexOf", s, b), abc, "", 0, 0, 0,
                () -> abc.lastIndexOf('b'));
        rows.check(vmString("indexOf", s, vmLeaf("ConstExpr", "C_I_128512",
                "I")), wide, "", 0, 0, 0, () -> wide.indexOf(0x1F600));
        int[][] regions = {{1, 1, 2}, {4, 1, 2}, {1, 1, 3}, {-1, 1, 0},
                {6, 4, 0}, {6, 4, 1}, {2, 1, -1}, {0, -1, 0}};
        for (int[] region : regions) {
            rows.check(vmString("regionMatches", s, n, t, m, k), abc, "xbcx",
                    region[0], region[1], region[2],
                    () -> abc.regionMatches(region[0], "xbcx", region[1],
                            region[2]));
        }
        rows.check(vmString("regionMatches", s, vmLeaf("ConstExpr", "C_Z_0",
                "Z"), n, t, m, k), abc, "xbcx", 1, 1, 2,
                () -> abc.regionMatches(false, 1, "xbcx", 1, 2));
        for (int[] range : new int[][] {{1, 3}, {0, 6}, {3, 2}, {-1, 2},
                {2, 7}}) {
            rows.check(vmString("subSequence", s, n, m), abc, "", range[0],
                    range[1], 0,
                    () -> abc.subSequence(range[0], range[1]).toString());
        }

        Map<String, VmTermLowering.Sort> declared =
                new LinkedHashMap<String, VmTermLowering.Sort>();
        declared.put("s", VmTermLowering.Sort.STRING);
        declared.put("t", VmTermLowering.Sort.STRING);
        declared.put("n", VmTermLowering.Sort.INT);
        declared.put("f", VmTermLowering.Sort.BOOL);
        SmtLowering lowering = new SmtLowering(declared);
        lowering.begin("row", SmtLowering.NO_JOIN, ExpressionTable.empty());
        lowering.dispatch(vmString("regionMatches", s, vmLeaf(
                "SymbolExpression", "f", "Z"), n, s, n, n), null, "row");
        lowering.dispatch(vmString("equalsIgnoreCase", s, t), null, "row");
        String refusals = lowering.openRefusals().toString();
        assertTrue(refusals, refusals.contains("regionMatches:IGNORE_CASE"));
        assertTrue(refusals,
                refusals.contains("equalsIgnoreCase:NO_LITERAL_SIDE"));
        lowering.end();
    }

    private static final class StringRows {
        private final Z3 solver;

        StringRows(Z3 solver) {
            this.solver = solver;
        }

        void check(JsonObject expression, String s, String t, long n, long m,
                   long k, Supplier<Object> java) {
            Object expected;
            try {
                expected = java.get();
            } catch (RuntimeException thrown) {
                expected = null;
            }
            Map<String, VmTermLowering.Sort> declared =
                    new LinkedHashMap<String, VmTermLowering.Sort>();
            declared.put("s", VmTermLowering.Sort.STRING);
            declared.put("t", VmTermLowering.Sort.STRING);
            for (String name : new String[] {"n", "m", "k"}) {
                declared.put(name, VmTermLowering.Sort.INT);
            }
            SmtLowering lowering = new SmtLowering(declared);
            lowering.begin("row", SmtLowering.NO_JOIN,
                    ExpressionTable.empty());
            VmTermLowering.Term term = lowering.dispatch(expression, null,
                    "row");
            String row = expression + " at s=" + literal(s) + " t="
                    + literal(t) + " n=" + n + " m=" + m + " k=" + k;
            assertTrue(row + ": " + lowering.openRefusals(),
                    lowering.openRefusals().isEmpty());
            List<String> facts = new ArrayList<String>(lowering.end());
            facts.add(term.precondition);
            Set<String> read = SmtNames.symbols(term.text + " "
                    + String.join(" ", facts), new LinkedHashSet<String>());
            String[] values = {literal(s), literal(t), integer(n), integer(m),
                    integer(k)};
            for (int index = 0; index < values.length; index++) {
                String name = String.valueOf("stnmk".charAt(index));
                if (read.contains(name)) {
                    facts.add("(= " + name + " " + values[index] + ")");
                }
            }
            List<String> texts = new ArrayList<String>(facts);
            texts.add(term.text);
            StringBuilder query = new StringBuilder(lowering.body(texts));
            for (String fact : facts) {
                query.append("(assert ").append(fact).append(")\n");
            }
            if (expected == null) {
                assertEquals(row + " is no world", "unsat",
                        ask(query.toString()));
                return;
            }
            String value = expected instanceof String
                    ? literal((String) expected)
                    : expected instanceof Integer
                    ? integer((Integer) expected) : expected.toString();
            assertEquals(row + " is defined, " + expected, "sat",
                    ask(query + "(assert (= " + term.text + " " + value
                            + "))\n"));
            assertEquals(row + " is " + expected + " alone", "unsat",
                    ask(query + "(assert (not (= " + term.text + " " + value
                            + ")))\n"));
        }

        private String ask(String query) {
            return solver.ask(query, Collections.<String>emptyList(), false)
                    .status();
        }

        private static String integer(long value) {
            return value < 0 ? "(- " + -value + ")" : Long.toString(value);
        }

        private static String literal(String text) {
            StringBuilder literal = new StringBuilder("\"");
            for (char c : text.toCharArray()) {
                if (c == '"') {
                    literal.append("\"\"");
                } else if (c < 32 || c > 126) {
                    literal.append("\\u{").append(Integer.toHexString(c))
                            .append('}');
                } else {
                    literal.append(c);
                }
            }
            return literal.append('"').toString();
        }
    }

    private static JsonObject splitElement(JsonObject receiver,
                                           String delimiter, int index) {
        JsonObject call = new JsonObject();
        call.addProperty("_type", "MethodExpression");
        call.addProperty("_name", "java/lang/String splitElement");
        call.addProperty("_java_type", "Ljava/lang/String;");
        JsonArray params = new JsonArray();
        params.add(receiver);
        params.add(vmLeaf("ConStringSymbolExp", "Y_L'String'_" + delimiter,
                "java/lang/String"));
        params.add(integer("I", index));
        call.add("_param_list", params);
        call.add("_res_exp", vmLeaf("ConStringSymbolExp", "Y_L'String'_x",
                "java/lang/String"));
        return call;
    }

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
        JsonObject empty = relation("ASSOCIATIVE", "SNAPSHOT_BASE", null);
        JsonObject all = relation("ASSOCIATIVE", "PUT_ALL", empty,
                relation("ASSOCIATIVE", "PUT", empty, integer("J", 5L), n));
        List<String> texts = new ArrayList<String>();
        for (JsonObject expression : Arrays.asList(
                vmString("substring", s, n), vmString("charAt", s, n),
                vmString("indexOf", s, c), vmString("lastIndexOf", s, s),
                vmString("startsWith", s, s, n), vmString("indexOf", s, n, n),
                vmString("lastIndexOf", s, s, n),
                vmString("lastIndexOf", s, n), vmString("compareTo", s, s),
                vmString("regionMatches", s, n, s, n, n),
                vmString("equalsIgnoreCase", s,
                        VmExpressionIr.stringConstant("Ok")),
                vmString("subSequence", s, n, n),
                vmString("toString", c), splitElement(s, ",", 1),
                vmString("toLowerCase", s), vmString("toUpperCase", s),
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

    private static String ordinal(String selector) {
        String[] parts = selector.split("__");
        return parts.length < 2 ? "" : parts[1];
    }

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
            JsonObject later = read("INSTANCE_FIELD", stamp.owner(), "value",
                    9L, "I");
            later.add("concreteValue", integer("I", 9L));
            if ("own".equals(name)) {
                session.read(Endpoint.of(reader, "Block#getStamp#31:READ",
                                at("r#9", 0), 0), stamp, 9L,
                        key + "@v9@s0", "I", "9");
            }
            if ("H2a".equals(name) || "H2b".equals(name)) {
                node.getAsJsonObject("observedVersion").add("expression",
                        "H2a".equals(name) ? integer("I", 1001L)
                                : binary("-", symbol(NO_ROW, "I"),
                                integer("I", 1L)));
            }
            if (!"unstated".equals(name) && !"H1".equals(name)) {
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
                    assertEquals(name + ": the read is free", 1,
                            composition.disjuncts().size());
                    assertTrue(name + ": the write's refusal is named, "
                                    + "beside the read's own",
                            says(gaps, GapKind.UNSTATED_VALUE,
                                    "did not lower")
                                    && says(gaps, GapKind.UNSTATED_VALUE,
                                    "the read is free, over-approximated")
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

    private static List<String> concrete(Composer.Composition composition) {
        List<String> rows = new ArrayList<String>();
        for (Composer.Concrete row : composition.concrete()) {
            rows.add(row.kind + " " + row.subject + "=" + row.value + " "
                    + row.movesWith);
        }
        return rows;
    }

    private static JsonObject answered(JsonObject query, JsonObject value,
                                       long id) {
        query.add("concreteValue", value);
        query.addProperty(ContainerSmtCodec.ANSWER, id);
        return query;
    }

    private static String streamQuery(String[] names,
                                      JsonObject... expressions) {
        return streamQuery(SmtLowering.NO_JOIN, names, expressions);
    }

    private static String streamQuery(SmtLowering.SessionJoin join,
                                      String[] names,
                                      JsonObject... expressions) {
        return query(Collections.singletonMap("n", VmTermLowering.Sort.INT),
                join, false, names, expressions);
    }

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

    private static JsonObject guarded(JsonObject relation, JsonObject guard) {
        relation.add("guard", guard);
        return relation;
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

    private static Composer.Composition compose(Path iteration,
                                                OccurrenceAddress anchor,
                                                int maxValuations,
                                                StaticScopeMap scope)
            throws IOException {
        Composer.Composition composition = Composer.compose(
                Corpus.holding(iteration, null, everSwept()), anchor,
                maxValuations, scope);
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
        return new Z3(z3, 30000L, 8192);
    }

    private static Path z3() {
        Path z3 = Paths.get("/usr/local/bin/z3");
        return Files.isExecutable(z3) ? z3 : Paths.get("z3");
    }

    private static String fatalArm(Composer.Composition composition) {
        for (String line : composition.body().split("\n")) {
            if (line.contains("path_fatal__0")) return line;
        }
        return "";
    }

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

    private static boolean says(List<GapRow> gaps, GapKind kind,
                                String fragment) {
        for (GapRow gap : gaps) {
            if (gap.kind() == kind && gap.detail().contains(fragment)) {
                return true;
            }
        }
        return false;
    }

    private static OccurrenceAddress occurrence(String node, String region,
                                                CausalContext context,
                                                Frame... frames) {
        return OccurrenceAddress.of(NodeId.of(node, 0), region, context,
                ExecutionIndex.of(Arrays.asList(frames)));
    }

    private static Frame frame(String callSite, int iteration) {
        return Frame.of(callSite, iteration);
    }

    private static ExecutionIndex at(String callSite, int iteration) {
        return ExecutionIndex.of(Collections.singletonList(
                Frame.of(callSite, iteration)));
    }

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

    private static JsonObject vmNull() {
        return symbol("N", "");
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

    private static JsonObject read(String kind, long owner, long slot,
                                   long version, String javaType) {
        return read(kind, Long.toString(owner), Long.toString(slot),
                version, javaType);
    }

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

    private static JsonObject fieldRead(String ownerClass, long offset,
                                        JsonObject owner,
                                        JsonObject concreteValue) {
        return fieldRead(ownerClass, offset, "L", owner, concreteValue);
    }

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

    private static JsonObject relation(String shape, String operation,
                                       JsonObject receiver,
                                       JsonObject... arguments) {
        return relation(shape, operation, "java/util/ArrayList", receiver,
                arguments);
    }

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

    private static String text(ArtifactIO.Body body) throws IOException {
        java.io.StringWriter written = new java.io.StringWriter();
        try (java.io.BufferedWriter output =
                     new java.io.BufferedWriter(written)) {
            body.writeTo(output);
        }
        return written.toString();
    }

    private static JsonObject integer(String javaType, long value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_java_type", javaType);
        node.addProperty("_exp", "Y_" + javaType + "_" + value);
        return node;
    }

    private static final class Session {
        private final Path iteration;
        private final String id;
        private final boolean explored;
        private OccurrenceAddress occurrence = ANCHOR;
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

        private ObligationResult settled;

        void settles(ObligationResult row) {
            settled = row;
        }

        void refused(String detail) {
            settled = ObligationResult.of("OBL." + id,
                    Verdict.NOT_ADMITTED, id, detail);
        }

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
                    instrumented, threadKey, ActivationRow.ClaimKind.NONE, null));
        }

        void activation(OccurrenceAddress at, Endpoint anchorProducer) {
            activations.add(ActivationRow.of(id, at,
                    explored ? "task-flip" : "task-seed", explored, true,
                    "thread#" + at.regionId(), ActivationRow.ClaimKind.NONE,
                    anchorProducer));
        }

        void marker(String recorded) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, MARKER_ROOT, MARKER,
                    RootKind.MARKER, RootCategory.FAULT, recorded, null, null, true, null, 0L));
        }

        void clock(String recorded) {
            roots.add(RootMintRow.of(id, ++seq, ANCHOR, CLOCK_ROOT, CLOCK,
                    RootKind.CLOCK, RootCategory.CLOCK, recorded, null, null, true, Clock.of(1_000_000L, Clock.WALL), 0L));
        }

        void decision(OccurrenceAddress at, String site, String term,
                      String clockRoot, long reading) {
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, true, term,
                    Collections.singletonMap(clockRoot, reading)));
        }

        void serial(String recorded, String min, String max) {
            roots.add(RootMintRow.of(id, ++seq, PRODUCER, SERIAL_ROOT,
                    SERIAL, RootKind.INTEGRAL, RootCategory.HOOK, recorded,
                    min, max, true, null, 0L));
        }

        private final Map<String, Map<String, String>> readings =
                new LinkedHashMap<String, Map<String, String>>();

        private final Set<String> derived = new LinkedHashSet<String>();

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

        void attach(Endpoint endpoint, String symbol, String javaType,
                    String arrival, Endpoint producer, String correlation) {
            attaches.add(AttachRow.of(id, ++seq, endpoint, symbol, javaType,
                    arrival, false, null, producer, correlation,
                    producer == null ? "" : "HANDLE"));
        }

        void answered(Endpoint endpoint, String symbol, String javaType,
                      String arrival, String answer, Endpoint producer) {
            attaches.add(AttachRow.of(id, ++seq, endpoint, symbol, javaType,
                    arrival, true, answer, producer, "corr-" + symbol,
                    producer == null ? "" : "HANDLE"));
        }

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

        long read(Endpoint endpoint, LocationId location, long version,
                  String symbol, String javaType, String concrete) {
            reads.add(ReadRow.of(id, ++seq, endpoint, location, version,
                    symbol, javaType, concrete));
            return seq;
        }

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

        void decision(OccurrenceAddress at, String site, boolean outcome,
                      String term, String via) {
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, outcome, term,
                    Collections.<String, Long>emptyMap()).via(via));
        }

        void target(String phi, boolean observedFatal, boolean reached) {
            targets.add(TargetRow.of(id, ++seq, occurrence, anchorLabel, phi,
                    observedFatal, reached, null));
        }

        String anchorLabel = ANCHOR_SITE;

        void forcedDecision(OccurrenceAddress at, String site, String term) {
            forced = true;
            decisions.add(DecisionRow.of(id, ++seq, at, site,
                    decisions.size() + 1, true, term,
                    Collections.<String, Long>emptyMap()).forced(false));
        }

        void forcedTarget(long at, String phi) {
            forced = true;
            targets.add(TargetRow.of(id, at, occurrence, ANCHOR_SITE, phi,
                    false, true, null).forced());
        }

        private boolean forced;

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
            ExpressionLogs.write(dir.expressions(), expressions);
            RowCodec.writeManifest(dir.manifest(), SessionManifest.of(id,
                    forced ? SessionManifest.Role.FORCED : explored
                            ? SessionManifest.Role.FOCUSED
                            : SessionManifest.Role.SEED,
                    explored || forced
                            ? Collections.singletonList(settled.obligationId())
                            : Collections.<String>emptyList())
                    .atClose(Collections.<String, Integer>emptyMap(),
                            readings, derived,
                            Collections.<String, String>emptyMap(),
                            Collections.<String>emptySet(),
                            Collections.<String>emptySet(),
                            Collections.<String>emptySet()));
            RowCodec.writeAll(dir.obligations(), explored || forced
                            ? Collections.singletonList(settled)
                            : Collections.<ObligationResult>emptyList(),
                    RowCodec::writeObligationResult);
        }
    }

    private void session(Path iteration, String id, boolean explored,
                         String marker, Endpoint producer, Endpoint consumer,
                         String symbol, String arrival, String answered,
                         boolean attestProducer, boolean observedFatal,
                         String ref) throws IOException {
        session(iteration, id, explored, marker, producer, consumer, symbol,
                arrival, answered, attestProducer, observedFatal, ref,
                symbol(MARKER, "Z"));
    }

    private void session(Path iteration, String id, boolean explored,
                         String marker, Endpoint producer, Endpoint consumer,
                         String symbol, String arrival, String answered,
                         boolean attestProducer, boolean observedFatal,
                         String ref, JsonObject exported) throws IOException {
        Session session = new Session(iteration, id, explored);
        session.activation(PRODUCER, "thread#" + PRODUCER.regionId(),
                explored, attestProducer);
        session.marker(marker);
        session.expression(ref, exported == null ? symbol(MARKER, "Z")
                : exported);
        if (attestProducer) {
            session.decision(PRODUCER, "nn#u1", "(or " + MARKER + " (not "
                    + MARKER + "))");
        }
        if (exported != null) session.export(producer, ref, 1L, marker);
        if (answered == null) {
            session.attach(consumer, symbol, arrival, producer);
        } else {
            session.answered(consumer, symbol, "Z", arrival, answered,
                    producer);
        }
        session.target(symbol, observedFatal, true);
        session.write();
    }
}
