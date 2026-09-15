package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
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
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
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
    /** What a case declares: a v1 selector, resolved against the seed. */
    private static final String TARGET_SELECTOR =
            "hdfs-case/dn0#epoch0/region/REGION.target#1";
    /** The NameNode's key rotation: a daemon tick, nobody's request. */
    private static final OccurrenceAddress PRODUCER = occurrence("hdfs-case/nn0",
            "REGION.rotate", CausalContext.of(Role.KEY_MANAGER_TICK, 1),
            "o.a.h.h.s.b.BlockManager#run#8");
    /** The data node's fatal read: its own DataXceiver op. */
    private static final OccurrenceAddress TARGET = occurrence("hdfs-case/dn0",
            "REGION.target", CausalContext.of(Role.DATA_XCEIVER, 1),
            "o.a.h.h.s.d.DataXceiver#run#12");
    /** addKeys on the same node: started by the rotation's own delivery. */
    private static final OccurrenceAddress WRITER = occurrence("hdfs-case/dn0",
            "REGION.addkeys", CausalContext.of(exportedId(),
                    "DatanodeProtocol#registerDatanode"),
            "o.a.h.h.s.d.BPServiceActor#offerService#41");

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    // ---- (1) depth: one decision per wave -----------------------------

    @Test
    public void nestedGuardChainDeepensOneDecisionPerWave() throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("depth").toPath();
        OccurrenceAddress target = TARGET;
        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, false);
        seed.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER, "false",
                null, null, true);
        seed.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        // if (a) if (b) throw: the recording took not-a and never reached b.
        // The predicate is published the way the VM publishes one over a
        // propagated value: a REFERENCE into the session's expression
        // table, which the one lowering resolves for the flip query too.
        seed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        seed.decision(target, "Guard#u8", 1, false, "EXPR.0000000000000001");
        // A CONCRETE branch beside it: no predicate, so nothing to flip.
        seed.decision(target, "Concrete#u3", 1, false, "");
        seed.flush();
        // What the wave may flip in the anchor is the guard set of the
        // annotated target, and nothing else (CLOSURE-V2 SS1/SS3).
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8", "Guard#u19"));

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
        Path results = out.resolve("obligation_results.jsonl");
        Files.write(results, new byte[0]);

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
        // The focus row is its own file.  execution_task_plan.jsonl is the
        // PLAN's name, and the workload session opener decodes whatever
        // stands under it, so a focus row written there killed every
        // obligation replay with "execution task requires sourceKey".
        assertFalse("the solver writes no plan",
                Files.exists(worker.directory.resolve(
                        "execution_task_plan.jsonl")));
        JsonObject focus = RowCodec.readJsonl(worker.directory.resolve(
                ObligationSolverMain.FOCUSED_TASK)).get(0);
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
        flipped.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "true", null, null, true);
        flipped.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        flipped.decision(target, "Guard#u8", 1, true, "M_MARKER");
        flipped.decision(target, "Guard#u19", 1, false, "(> M_COUNT 5)");
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
            // An arm SOME session of the epoch already took is not asked for
            // again, whichever session holds the row and whichever prefix it
            // was taken under: the seed took Guard#u8 false and the flip
            // replay took it true, so both arms of that site are attested
            // and a replay of either collects nothing the corpus lacks.  On
            // laneA6 wave 1 this was the marker decision flipped BACK to
            // true out of the wave-0 replays: nine minutes each.
            assertFalse("an arm the corpus already holds is not re-flipped: "
                            + sites, "Guard#u8".equals(obligation.siteId()));
        }
        boolean held = false;
        for (GapRow gap : RowCodec.readAll(wave1.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            held |= gap.cls() == GapClass.DIAGNOSTIC
                    && gap.subject().startsWith("Guard#u8#1 -> ")
                    && gap.detail().contains("arm already recorded by");
        }
        assertTrue("and the wave says which session holds it", held);
        // The deeper obligation carries the earlier wave's answer in its own
        // prefix: it needs the marker true AND the count above five.
        Obligation deeper = named(next, "Guard#u19");
        assertNotNull(deeper);
        Worker second = solve(iteration, wave1, deeper, out, "w1");
        assertEquals(Verdict.SAT_MODEL_READY, second.verdict);
        assertEquals("true",
                second.obligation.rootAssignments().get("CASE.MARKER"));
        assertTrue(Integer.parseInt(
                second.obligation.rootAssignments().get("CASE.COUNT")) > 5);
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
        seed.activation(target, false);
        seed.activation(producer, false);
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
        // The consumer received it in that replay too, running concretely:
        // R-I2 admits an arm only from a run whose OWN pairing named this
        // consumer, which is what makes a family the deliveries of one
        // interaction rather than of one port.
        rotated.activation(target, false);
        rotated.root(producer, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "119995", null, null, false);
        rotated.decision(producer, "Rotate#u3", 1, true, "(> M_SERIAL 0)");
        rotated.constant("e.119995", "119995");
        rotated.export(exported, "e.119995", 12L, "119995");
        rotated.attach(attached, "M_HOFF_KEY", "119995", exported);
        rotated.decision(producer, "After#u9", 1, true,
                "(> M_SERIAL 1000000)");
        rotated.flush();
        scopeMap(iteration,
                targetSite("REGION.target", "Throw#u30", "Lookup#u8"),
                scopeSite(StaticScopeMap.EXPORT_SITE, "REGION.rotate",
                        "PBHelper#convert#9", "PBHelper#convert", "", "",
                        "XCH.resp.block-key-id", "Rotate#u3"));

        Path out = tree.newFolder("family-out").toPath();
        Path results = out.resolve("obligation_results.jsonl");
        Path wave0 = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null, results, wave0, 0);
        List<Obligation> proposed = obligations(wave0);
        // The producer ran symbolically in the rotated session, so it is a
        // task of its own -- the NN rotation is explored as a worker, not as
        // the consumer's companion.  What it may flip is the guard set of the
        // EXPORT it is in the closure for: the rotation decision that decides
        // the delivery, and not the decision it took AFTER putting the value
        // on the wire, which no delivery can depend on (CLOSURE-V2 SS3).
        List<String> sites = new ArrayList<String>();
        for (Obligation obligation : proposed) sites.add(obligation.siteId());
        assertTrue("the export's own guard is an obligation: " + sites,
                sites.contains("Rotate#u3"));
        assertFalse("a decision after the export is no guard of it: " + sites,
                sites.contains("After#u9"));
        Obligation consumerFlip = named(proposed, "Lookup#u8");
        assertNotNull("the consumer's own flip is proposed", consumerFlip);
        Worker worker = solve(iteration, wave0, consumerFlip, out, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, worker.verdict);
        assertTrue("the control is producible",
                worker.obligation.unproducible().isEmpty());
        assertEquals("119995", worker.obligation.answers().get(attached.id()));

        // The negative control: a flip that needs a value no producer of this
        // corpus delivers is UNSAT, not answered out of the family.
        Path other = tree.newFolder("family-unsat").toPath();
        Session lone = new Session(other, "s-seed");
        lone.activation(target, false);
        lone.activation(producer, false);
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
        boolean named = false;
        for (GapRow gap : RowCodec.readAll(worker.directory
                .resolve("gaps.jsonl"), RowCodec::readGap)) {
            named |= gap.kind() == GapKind.UNPRODUCIBLE_ANSWER
                    && gap.subject().contains("XCH.req.key-id");
        }
        assertTrue("the obligation announces the control it invented", named);
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
        open.root(target, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL, "7",
                null, null, true);
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
    }

    // ---- (5) the closure holds the writer of every version read -------

    @Test
    public void closureHoldsTheWriterOfAReadVersionAndTheWireProducer()
            throws Exception {
        Path iteration = tree.newFolder("closure").toPath();
        OccurrenceAddress target = TARGET;
        OccurrenceAddress writer = WRITER;
        OccurrenceAddress producer = PRODUCER;
        // Memory Indexing: the map is owned by the endpoint that allocated
        // it, never by a session address (IDENTITY-V3 SS5).
        LocationId allKeys = LocationId.allocated(at(writer,
                        Endpoint.allocationSite("BlockTokenSecretManager",
                                "<init>", 4, false),
                        "BlockTokenSecretManager#<init>#4"),
                LocationKind.MAP, "allKeys");
        Endpoint exported = at(producer, "XCH.resp.block-key-id",
                "PBHelper#convert#9");
        Endpoint attached = at(writer, "XCH.resp.block-key-id",
                "PBHelper#convert#9");

        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, false);
        seed.activation(writer, false);
        seed.activation(producer, false);
        seed.constant("e.119992", "119992");
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.export(exported, "e.119992", 11L, "119992");
        seed.attach(attached, "M_HOFF_KEY", "119992", exported);
        seed.write(at(writer, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 12, true), "BlockTokenSecretManager"
                        + "#addKeys#12"), allKeys, 5L, "e.stored");
        seed.read(at(target, Endpoint.stateSite("BlockTokenSecretManager",
                        "retrieveDataEncryptionKey", 8, false),
                        "BlockTokenSecretManager"
                                + "#retrieveDataEncryptionKey#8"), allKeys,
                5L, "M_READ_KEY", "119992");
        // What makes this occurrence an anchor: the predicate whose fatal arm
        // the composition asks about, over the value it read.
        seed.target(target, "BlockTokenSecretManager"
                + "#retrieveDataEncryptionKey#8", "(= M_READ_KEY 0)");
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
        ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, target, map);
        List<String> focused = new ArrayList<String>();
        for (Task task : plan.tasks) focused.add(task.focused().render());
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
        for (GapRow gap : plan.gaps) {
            assertFalse(gap.kind() == GapKind.TOPOLOGY_DIVERGENCE);
        }

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
        other.activation(target, false);
        other.activation(confused, false);
        other.activation(producer, false);
        other.constant("e.119992", "119992");
        other.symbolic("e.stored", "M_HOFF_KEY");
        other.export(exported, "e.119992", 11L, "119992");
        other.attach(at(confused, "XCH.resp.block-key-id",
                "PBHelper#convert#9"), "M_HOFF_KEY", "119992", exported);
        other.write(at(confused, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 12, true), "BlockTokenSecretManager"
                        + "#addKeys#12"), allKeys, 5L, "e.stored");
        other.read(at(confused, Endpoint.stateSite("BlockTokenSecretManager",
                        "get", 3, false), "BlockTokenSecretManager#get#3"),
                allKeys, 5L, "M_READ_KEY", "119992");
        other.target(confused, "BlockTokenSecretManager#get#3",
                "(= M_READ_KEY 0)");
        other.flush();
        ClosurePlanner.Plan divergent = ClosurePlanner.plan(
                Corpus.read(split, null), confused, map);
        List<String> divergentFocused = new ArrayList<String>();
        for (Task task : divergent.tasks) {
            divergentFocused.add(task.focused().render());
        }
        assertTrue("the closure follows the recorded pairing: "
                        + divergentFocused,
                divergentFocused.contains(producer.render()));
        boolean told = false;
        for (GapRow gap : divergent.gaps) {
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
        paired.activation(target, false);
        paired.activation(writer, false);
        paired.activation(producer, false);
        paired.constant("e.119992", "119992");
        paired.export(exported, "e.119992", 11L, "119992");
        paired.attach(attached, "M_HOFF_KEY", "119992", exported);
        paired.flush();
        Session repaired = new Session(twoWays, "s-two");
        repaired.activation(writer, false);
        repaired.activation(producer, false);
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

        // R-I7 against R-I6: a STATE reader that joined ANOTHER writer in
        // another session is not a replacement, it is that family's second
        // arm.  A flip is expected to change which writer delivers -- that
        // is what the flip is for -- so reading it as a contradiction forked
        // an epoch over the arm the wave had just asked for.  "Opened by
        // another session" means nothing for a state slot.
        Path arms = tree.newFolder("closure-state-arms").toPath();
        OccurrenceAddress otherWriter = occurrence("hdfs-case/dn0",
                "REGION.deletekeys", CausalContext.of(Role.CLIENT, 4),
                "o.a.h.h.s.d.BPServiceActor#offerService#77");
        Endpoint reader = at(target, Endpoint.stateSite(
                "BlockTokenSecretManager", "get", 3, false),
                "BlockTokenSecretManager#get#3");
        Session firstArm = new Session(arms, "s-seed");
        firstArm.activation(target, false);
        firstArm.activation(writer, false);
        firstArm.symbolic("e.a", "M_A");
        firstArm.write(at(writer, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 12, true), "BlockTokenSecretManager"
                        + "#addKeys#12"), allKeys, 5L, "e.a");
        firstArm.read(reader, allKeys, 5L, "M_READ_KEY", "119992");
        firstArm.flush();
        Session flipping = new Session(arms, "s-flip");
        flipping.activation(target, true);
        flipping.activation(otherWriter, true);
        flipping.symbolic("e.b", "M_B");
        flipping.write(at(otherWriter, Endpoint.stateSite(
                        "BlockTokenSecretManager", "removeKeys", 19, true),
                        "BlockTokenSecretManager#removeKeys#19"), allKeys,
                9L, "e.b");
        flipping.read(reader, allKeys, 9L, "M_READ_KEY_2", "0");
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

        // A region the workload never RETAINED: its activation is all there
        // is of it, no endpoint of it exists, so no slot can ever name it.
        // The epoch has to be re-cut with it instrumented (SS8 case 2).
        Path unseen = tree.newFolder("closure-unretained").toPath();
        OccurrenceAddress lightweight = occurrence("hdfs-case/dn0",
                "REGION.notretained", CausalContext.of(Role.DATA_XCEIVER, 2),
                "o.a.h.h.s.d.DataXceiver#run#44");
        Session partial = new Session(unseen, "s-seed");
        partial.activation(target, false);
        partial.lightweight(lightweight);
        partial.read(at(target, Endpoint.stateSite("BlockTokenSecretManager",
                        "get", 3, false), "BlockTokenSecretManager#get#3"),
                allKeys, 5L, "M_READ_KEY", "119992");
        partial.flush();
        SlotTable.Reconciliation grown = new SlotTable().reconcile(
                Corpus.read(unseen, null),
                Collections.singleton(target.id()), 3);
        assertTrue("a region with no detailed row forks the epoch",
                grown.replaced);
        boolean asked = false;
        for (GapRow gap : grown.gaps) {
            asked |= gap.kind() == GapKind.TOPOLOGY_DIVERGENCE
                    && gap.cls() == GapClass.BLOCKING
                    && gap.detail().equals(
                            "retained set must grow: REGION.notretained");
        }
        assertTrue("and it names the region INSTRUMENT must retain", asked);

        // A DEGRADED occurrence's region slot is ROLE.<ROLE>: the scope was
        // lost, so there is no region of the static graph to retain and no
        // epoch to cut.  What it states is the lineage.
        Path roleOnly = tree.newFolder("closure-role").toPath();
        OccurrenceAddress lost = occurrence("hdfs-case/dn0",
                "ROLE.IPC_HANDLER", CausalContext.of(Role.IPC_HANDLER),
                "o.a.h.ipc.Server$Handler#run#1");
        Session degraded = new Session(roleOnly, "s-seed");
        degraded.activation(target, false);
        degraded.lightweight(lost);
        degraded.flush();
        SlotTable.Reconciliation roleGap = new SlotTable().reconcile(
                Corpus.read(roleOnly, null),
                Collections.singleton(target.id()), 4);
        assertFalse("a role is not a region, so nothing can retain it and "
                + "no epoch is cut", roleGap.replaced);
        boolean lineage = false;
        for (GapRow gap : roleGap.gaps) {
            lineage |= gap.kind() == GapKind.LINEAGE_LOST
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.detail().contains("ROLE.IPC_HANDLER");
        }
        assertTrue("and the lost scope is named as one", lineage);

        // R-I6: two occurrences of ONE code point that a replay ran BOTH are
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
        bothRan.activation(firstRequest, false);
        bothRan.activation(secondRequest, false);
        bothRan.flush();
        assertFalse("two requests at one code point are growth",
                new SlotTable().reconcile(Corpus.read(requests, null),
                        Collections.singleton(firstRequest.id()), 5)
                        .replaced);

        Path instead = tree.newFolder("closure-instead").toPath();
        Session ranIt = new Session(instead, "s-seed");
        ranIt.activation(firstRequest, false);
        ranIt.flush();
        Session ranOther = new Session(instead, "s-flip");
        ranOther.activation(secondRequest, true);
        ranOther.flush();
        assertTrue("a replay that did not run the member and ran another "
                        + "context in its place IS a replacement",
                new SlotTable().reconcile(Corpus.read(instead, null),
                        Collections.singleton(firstRequest.id()), 6)
                        .replaced);

        // An occurrence the corpus names ONLY in a write row -- no
        // activation, no decision -- cannot be a task: there is no recorded
        // run to focus a replay on.  It used to reach Task.of with an empty
        // seedSessionId and abort the whole wave with
        // "seedSessionId is required"; the closure now refuses it by name.
        Path unrun = tree.newFolder("closure-unrun").toPath();
        OccurrenceAddress ghost = occurrence("hdfs-case/dn0",
                "REGION.unrun", CausalContext.of(Role.DATA_XCEIVER, 7),
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
        ClosurePlanner.Plan withGhost = ClosurePlanner.plan(
                Corpus.read(unrun, null), target, map);
        for (Task task : withGhost.tasks) {
            assertFalse("an occurrence no session ran is not a task",
                    task.focused().id().equals(ghost.id()));
            assertFalse("and a task always names the recording it was "
                    + "planned from", task.seedSessionId().isEmpty());
        }
        boolean unplannable = false;
        for (GapRow gap : withGhost.gaps) {
            unplannable |= gap.kind() == GapKind.ADMISSION_GAP
                    && gap.cls() == GapClass.BLOCKING
                    && gap.subject().equals(ghost.render())
                    && gap.detail().contains("no replay can be focused");
        }
        assertTrue("and the refusal names it", unplannable);

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
        stated.activation(target, false);
        stated.activation(writer, false);
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
        ClosurePlanner.Plan lowered = ClosurePlanner.plan(
                Corpus.read(viaRef, null), target, map);
        for (GapRow gap : lowered.gaps) {
            assertFalse("the anchor's own read is what its phi rests on: "
                            + gap.detail(),
                    gap.subject().equals(refRead.toString())
                            && gap.detail().contains("no admitted path"));
        }

        theClosureHasOneRoot(iteration, writer);

        // CLOSURE-V2 SS2: the closure grows by the STATIC write sites of the
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
                "REGION.deferring", CausalContext.of(Role.CLIENT, 1),
                "o.a.h.h.s.n.SnapshotManager#deleteSnapshot#7");
        OccurrenceAddress undeclared = occurrence("hdfs-case/dn0",
                "REGION.undeclared", CausalContext.of(Role.CLIENT, 2),
                "o.a.h.h.s.n.SnapshotManager#renameSnapshot#7");
        LocationId counter = LocationId.allocated(at(writer,
                        Endpoint.allocationSite("SnapshotManager", "<init>",
                                4, false), "SnapshotManager#<init>#4"),
                LocationKind.INSTANCE, "24");
        Session apart = new Session(aside, "s-seed");
        apart.activation(target, false);
        apart.activation(writer, false);
        apart.activation(deferring, false);
        apart.activation(undeclared, false);
        apart.symbolic("e.count", "M_COUNT_IN");
        apart.symbolic("EXPR.0000000000000003", "M_MARKER", "Z");
        apart.symbolic("EXPR.0000000000000004", "M_READ_COUNT");
        apart.root(deferring, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "true", null, null, true);
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
        apart.decision(target, "Section#u61", 1, true,
                "EXPR.0000000000000004");
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
        // there is no run to focus (INTERACTION-ID SS8 case 2).
        boolean grow = false;
        for (GapRow gap : RowCodec.readAll(asideWave.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            grow |= gap.kind() == GapKind.ADMISSION_GAP
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.subject().equals("REGION.neverran")
                    && gap.detail().contains("retained set would have to "
                            + "grow");
        }
        assertTrue("the unrun candidate region is named", grow);

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
        loop.activation(target, false);
        loop.activation(writer, false);
        loop.symbolic("e.first", "M_FIRST");
        loop.symbolic("e.second", "M_SECOND");
        loop.write(at(writer, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 12, true), "BlockTokenSecretManager"
                        + "#addKeys#12"), allKeys, 5L, "e.first");
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

    /** The slots one reconciliation opened, for an assertion to look at. */
    private static List<SlotTable.Slot> slotsOf(
            SlotTable.Reconciliation reconciliation) {
        return new ArrayList<SlotTable.Slot>(reconciliation.opened);
    }

    // ---- (5b) the closure has ONE root: the case's declared anchor -------

    /**
     * Folded into the closure case: a wave's roots are the anchor and nothing
     * else (HANDOVER SS1.5).  The seed replay's task plan was a second source
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
                null, iteration.resolve("results.jsonl"),
                iteration.resolve(StaticScopeMap.FILE), waveDir, 0,
                "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.Bounds.defaults());
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

        // A declared anchor the seed session never ran: BLOCKING, and the
        // refusal names the address rather than leaving "no tasks".
        Path elsewhere = tree.newFolder("roots-absent").toPath();
        Session only = new Session(elsewhere, "s-seed");
        only.activation(WRITER, false);
        only.flush();
        Path absentWave = tree.newFolder("roots-absent-wave").toPath();
        ExploreMain.plan(elsewhere, TARGET.render(), null,
                elsewhere.resolve("results.jsonl"),
                elsewhere.resolve(StaticScopeMap.FILE), absentWave, 0,
                "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.Bounds.defaults());
        boolean named = false;
        for (GapRow gap : RowCodec.readAll(absentWave.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            named |= gap.kind() == GapKind.ADMISSION_GAP
                    && gap.cls() == GapClass.BLOCKING
                    && gap.subject().equals(TARGET.render())
                    && gap.detail().contains("published no activation");
        }
        assertTrue("the anchor's absence is BLOCKING and named", named);
    }

    // ---- driving the stage the way the campaign drives it -------------

    /**
     * One wave, planned from the case's own selector as the stage does, over
     * the static map the epoch published beside its sessions.
     */
    private JsonObject plan(Path iteration, String selector, Path domains,
                            Path results, Path waveDir, int wave)
            throws IOException {
        return ExploreMain.plan(iteration, selector, domains, results,
                iteration.resolve(StaticScopeMap.FILE), waveDir, wave,
                "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.Bounds.defaults());
    }

    /**
     * The epoch's static scope map, as PLAN publishes it (CLOSURE-V2 SS4).
     *
     * <p>Written as the artifact's own text, so what these cases exercise is
     * the published shape and not a builder's idea of it.</p>
     */
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

    /** The annotated target and the branches it is control-dependent on. */
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
     *                 SS2), which is what makes the conjunct
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
        seed.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                recorded, null, null, true);
        seed.decision(TARGET, "Guard#u8", 1, outcome, term);
        seed.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"));
        Path out = tree.newFolder(name + "-out").toPath();
        Path results = out.resolve("obligation_results.jsonl");
        Files.write(results, new byte[0]);
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
            boolean refused = false;
            for (GapRow gap : RowCodec.readAll(
                    solved.directory.resolve("gaps.jsonl"),
                    RowCodec::readGap)) {
                refused |= gap.cls() == GapClass.BLOCKING
                        && gap.detail().contains(
                                "the recording's own valuation");
            }
            assertTrue("and the refusal is named", refused);
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

    private Worker solve(Path iteration, Path waveDir, Obligation proposal,
                         Path out, String name) throws IOException {
        return solve(iteration, null, waveDir, proposal, out, name);
    }

    /** One worker, given the same case declaration the wave was planned under. */
    private Worker solve(Path iteration, Path domains, Path waveDir,
                         Obligation proposal, Path out, String name)
            throws IOException {
        Path worker = out.resolve(name);
        ObligationSolverMain.solve(iteration, domains,
                waveDir.resolve("obligations.jsonl"),
                proposal.obligationId(), worker, Paths.get("z3"), 10_000L);
        List<ObligationResult> rows = RowCodec.readAll(
                worker.resolve("obligation_result.jsonl"),
                ExploreCodec::readResult);
        assertEquals(1, rows.size());
        List<Obligation> solved = RowCodec.readAll(
                worker.resolve("obligation.jsonl"),
                ExploreCodec::readObligation);
        assertEquals(1, solved.size());
        assertTrue("the query is published whatever the verdict",
                Files.size(worker.resolve("obligation_query.smt2")) > 0);
        return new Worker(rows.get(0).verdict(), solved.get(0), worker);
    }

    private static void record(Path results, ObligationResult result)
            throws IOException {
        Files.write(results, (RowCodec.toLine(
                        ExploreCodec.writeResult(result))
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
                        CausalContext.of(Role.KEY_MANAGER_TICK, 1),
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

    /** One session of a synthetic corpus, written in the contract's layout. */
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

        /**
         * The lightweight entry hook's row: this region RAN, and nothing
         * else about it can exist because it was never retained.
         */
        private void lightweight(OccurrenceAddress occurrence) {
            activation(occurrence, false, false);
        }

        private void activation(OccurrenceAddress occurrence, boolean focused,
                                boolean instrumented) {
            activations.add(ActivationRow.of(sessionId, occurrence,
                    "task-" + occurrence.regionId(), focused, instrumented,
                    "fixture#" + occurrence.node().node(), null));
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

        private void root(OccurrenceAddress occurrence, String rootId,
                          String symbol, RootKind kind, String recorded,
                          String min, String max, boolean declared) {
            roots.add(RootMintRow.of(sessionId, ++seq, occurrence, rootId,
                    symbol, kind, recorded, min, max, declared));
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
                    "corr-" + endpoint.siteIndex().hash()));
        }

        private void write(Endpoint endpoint, LocationId location,
                           long version, String ref) {
            writes.add(WriteRow.of(sessionId, ++seq, endpoint, location,
                    version, ref, "I"));
        }

        private void read(Endpoint endpoint, LocationId location,
                          long version, String symbol, String concrete) {
            reads.add(ReadRow.of(sessionId, ++seq, endpoint, location, version,
                    symbol, "I", concrete));
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

        /** One literal the VM recorded as a delivered constant. */
        private void constant(String ref, String value) {
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("_exp", "C_I_" + value);
            expression.addProperty("_java_type", "I");
            expressions.put(ref, expression);
        }

        private void flush() throws IOException {
            dir.create();
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
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
        }
    }
}
