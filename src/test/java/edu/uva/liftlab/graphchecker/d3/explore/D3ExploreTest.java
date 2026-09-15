package edu.uva.liftlab.graphchecker.d3.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.Frame;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.NodeId;
import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootDomain;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.Task;
import edu.uva.liftlab.graphchecker.d3.contract.Verdict;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

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
public class D3ExploreTest {
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
        seed.decision(target, "Guard#u8", 1, false, "M_MARKER");
        seed.flush();

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
        Worker worker = solve(iteration, wave0, proposed.get(0), out, "w0");
        assertEquals(Verdict.SAT_MODEL_READY, worker.verdict);
        assertEquals("true",
                worker.obligation.rootAssignments().get("CASE.MARKER"));

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
                Verdict.VALIDATED, "s-flip", "the flip ran"));

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
        }
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

        Path out = tree.newFolder("family-out").toPath();
        Path results = out.resolve("obligation_results.jsonl");
        Path wave0 = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null, results, wave0, 0);
        List<Obligation> proposed = obligations(wave0);
        // The producer ran symbolically in the rotated session, so it is a
        // task of its own and its own decisions are flips too -- the NN
        // rotation is explored as a worker, not as the consumer's companion.
        List<String> sites = new ArrayList<String>();
        for (Obligation obligation : proposed) sites.add(obligation.siteId());
        assertTrue("the rotation's own decisions are obligations: " + sites,
                sites.contains("Rotate#u3") && sites.contains("After#u9"));
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
        Path domains = declared.resolve("root-domains.jsonl");
        RowCodec.writeAll(domains, Collections.singletonList(RootDomain.of(
                        "CASE.SERIAL", RootKind.INTEGRAL, "7", "+4", "+5")),
                ExploreCodec::writeDomain);
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

        Corpus corpus = Corpus.read(iteration, null);
        ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, target);
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
                Corpus.read(split, null), confused);
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
        assertTrue("a consumer paired with another producer is a replacement",
                contradiction.replaced);
        boolean blocking = false;
        for (GapRow gap : contradiction.gaps) {
            blocking |= gap.kind() == GapKind.TOPOLOGY_DIVERGENCE
                    && gap.cls() == GapClass.BLOCKING
                    && gap.detail().contains("already paired");
        }
        assertTrue("and it is BLOCKING: the campaign opens an epoch",
                blocking);

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
    }

    // ---- driving the stage the way the campaign drives it -------------

    /** One wave, planned from the case's own selector as the stage does. */
    private JsonObject plan(Path iteration, String selector, Path domains,
                            Path results, Path waveDir, int wave)
            throws IOException {
        return ExploreMain.plan(iteration,
                Collections.singletonList(selector), domains, results,
                waveDir, wave, "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.Bounds.defaults());
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
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "SymbolExpression");
            expression.addProperty("_exp", symbol);
            expression.addProperty("_java_type", "I");
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
