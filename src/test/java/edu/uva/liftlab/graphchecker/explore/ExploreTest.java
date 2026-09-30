package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ObligationDir;
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
import edu.uva.liftlab.graphchecker.contract.Hole;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import org.junit.Assume;
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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
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
        // Three more declared roots the recording minted, none of them named
        // by any predicate of the seed's own path: the rotation's tick,
        // whose guard a LATER session flips; a clock; and one root no term
        // ever reaches.  A world is inherited whole, so the wave that
        // extends one has to find every root of it minted here -- an
        // assignment is planted at the recording's mint and nowhere else.
        seed.root(PRODUCER, "CASE.TICK", "M_TICK", RootKind.INTEGRAL, "1",
                "0", "10", true);
        seed.root(target, "CASE.NOW", "M_NOW", RootKind.CLOCK, "1000",
                null, null, true);
        seed.root(target, "CASE.SPARE", "M_SPARE", RootKind.INTEGRAL, "3",
                "0", "10", true);
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
        seed.activation(WRITER, false);
        seed.activation(PRODUCER, false);
        seed.constant("e.119992", "119992");
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.export(ROTATED, "e.119992", 11L, "119992");
        seed.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        seed.write(STORED, ALL_KEYS, 5L, "e.stored");
        seed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        seed.flush();
        // What the wave may flip in the anchor is the guard set of the
        // declared target, and nothing else (PIPELINE §7.2).
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
        flipped.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "true", null, null, true);
        flipped.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        flipped.decision(target, "Guard#u8", 1, true, "M_MARKER");
        flipped.decision(target, "Guard#u19", 1, false, "(> M_COUNT 5)");
        // A replay records every instrumented occurrence it ran, so what the
        // target's factor received and wrote is here as it was in the seed:
        // the flip changed nothing the target received.
        flipped.activation(WRITER, false);
        flipped.activation(PRODUCER, false);
        flipped.constant("e.119992", "119992");
        flipped.symbolic("e.stored", "M_HOFF_KEY");
        flipped.export(ROTATED, "e.119992", 11L, "119992");
        flipped.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        flipped.write(STORED, ALL_KEYS, 5L, "e.stored");
        flipped.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
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
                Verdict.NOT_ADMITTED, "",
                "the focused occurrence's own prefix did not match"));
        Session other = new Session(iteration, "s-flip-2");
        other.activation(target, true);
        other.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "true", null, null, true);
        other.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
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
        boolean owedOnce = false;
        for (GapRow gap : RowCodec.readAll(wave2.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            owedOnce |= gap.cls() == GapClass.DIAGNOSTIC
                    && gap.subject().equals("Guard#u19#1 -> true")
                    && gap.detail().contains("already answered NOT_ADMITTED")
                    && gap.detail().contains("owed once per planned "
                            + "occurrence");
        }
        assertTrue("and the wave says which answer settled it", owedOnce);
        boolean moved = false;
        for (GapRow gap : RowCodec.readAll(wave2.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            moved |= gap.kind() == GapKind.ADDRESS_UNSTABLE
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.subject().equals("task-REGION.spare")
                    && gap.detail().contains("answered at 2 addresses");
        }
        assertTrue("and a planned task answered at two addresses is named",
                moved);

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
        // its path exists in, and the query states the parent's flipped
        // conjunct -- without which the model would answer for a path that
        // run never had.
        Session world = new Session(iteration, "s-other-prefix");
        world.activation(target, true);
        world.activation(PRODUCER, true);
        world.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "true", null, null, true);
        world.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        world.root(PRODUCER, "CASE.TICK", "M_TICK", RootKind.INTEGRAL, "7",
                "0", "10", true);
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
        refused.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "true", null, null, true);
        refused.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL,
                "0", "0", "10", true);
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
        String query = new String(Files.readAllBytes(
                nested.directory.resolve("obligation_query.smt2")), "UTF-8");
        assertTrue("and the query ASSERTS the parent's flipped conjunct, so "
                        + "the model answers for the world this path is in: "
                        + query, query.contains("(> r_CASE_TICK 3)"));

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
        zed.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER, "true",
                null, null, true);
        zed.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
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
                Collections.singletonMap("CASE.MARKER", "true"),
                Collections.<String, String>emptyMap());

        // Y: nn0's rotation flipped.  Its rows AT THE TARGET are the seed's,
        // letter for letter; what its world changed is the STRUCTURE of what
        // addKeys received -- one handoff fewer, because the rotation it was
        // held to delivered one key less -- and addKeys writes what the
        // target reads.  (11741: four attaches instead of five.)
        Session wye = new Session(iteration, "s-world-y");
        wye.activation(PRODUCER, true);
        wye.activation(target, false);
        wye.activation(WRITER, false);
        wye.root(PRODUCER, "CASE.TICK", "M_TICK", RootKind.INTEGRAL, "7",
                "0", "10", true);
        wye.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER, "false",
                null, null, true);
        wye.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        wye.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        wye.constant("e.kept", "119992");
        wye.decision(PRODUCER, "Rotate#u5", 1, true, "(> M_TICK 3)");
        wye.decision(target, "Guard#u8", 1, false, "EXPR.0000000000000001");
        wye.decision(target, "Concrete#u3", 1, false, "");
        // No attach here at all: the rotation it was held to delivered
        // nothing, so addKeys stored what it already had.
        wye.write(STORED, ALL_KEYS, 5L, "e.kept");
        wye.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        wye.answered(ObligationResult.of("OBL.world-y", Verdict.ADMITTED,
                "s-world-y", "the focused prefix reproduced"));
        wye.flush();
        worker(iteration, "obligations-0001", "ob-world-y", "OBL.world-y",
                "s-world-y", PRODUCER, "Rotate#u5",
                Collections.singletonMap("CASE.TICK", "7"),
                Collections.<String, String>emptyMap());

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
        unmoved.activation(target, false);
        unmoved.activation(WRITER, false);
        unmoved.root(BALANCER, "CASE.MOVE", "M_MOVE", RootKind.INTEGRAL, "2",
                "0", "10", true);
        unmoved.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "false", null, null, true);
        unmoved.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        unmoved.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        unmoved.symbolic("e.stored", "M_HOFF_KEY");
        unmoved.constant("e.887766", "887766");
        unmoved.decision(BALANCER, "Balance#u2", 1, true, "(> M_MOVE 1)");
        unmoved.decision(target, "Guard#u8", 1, false,
                "EXPR.0000000000000001");
        unmoved.decision(target, "Concrete#u3", 1, false, "");
        unmoved.export(ROTATED, "e.887766", 11L, "887766");
        unmoved.attach(DELIVERED, "M_HOFF_KEY", "887766", ROTATED);
        unmoved.write(STORED, ALL_KEYS, 5L, "e.stored");
        unmoved.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "887766");
        unmoved.answered(ObligationResult.of("OBL.world-w", Verdict.ADMITTED,
                "s-world-w", "the focused prefix reproduced"));
        unmoved.flush();
        worker(iteration, "obligations-0001", "ob-world-w", "OBL.world-w",
                "s-world-w", BALANCER, "Balance#u2",
                Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap());

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
                        + "factor member received: one handoff fewer",
                worlds.attachesOn("s-seed", WRITER).size() - 1,
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
            for (JsonObject row : RowCodec.readJsonl(found.focusedTask())) {
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
        ExploreMain.plan(iteration, TARGET_SELECTOR, null, results,
                iteration.resolve(StaticScopeMap.FILE), shallow, 5, "epoch0",
                ClosurePlanner.DEFAULT_MAX_TASKS,
                new ObligationFactory.Bounds(
                        ObligationFactory.DEFAULT_MAX_PATHS_PER_TASK,
                        ObligationFactory.DEFAULT_MAX_FLIPS_PER_PATH, 0),
                false);
        for (Obligation obligation : obligations(shallow)) {
            assertFalse("no obligation is cut from a world deeper than the "
                            + "bound: " + obligation,
                    Corpus.pathId("s-world-y", target)
                            .equals(obligation.pathId()));
        }
        boolean stated = false;
        for (GapRow gap : RowCodec.readAll(shallow.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            stated |= gap.kind() == GapKind.ADMISSION_GAP
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.subject().endsWith("max-world-depth=0");
        }
        assertTrue("and the bound states what it left unread", stated);
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
     * A case that asks about ONE occurrence stops at its first witness: an
     * admitted replay that observed the fatal at the declared occurrence ends
     * the exploration (owner 2026-09-28: hdfs-11741, hdfs-17899-bug2), and a
     * case that does not ask so keeps exploring.
     */
    @Test
    public void aWitnessAtTheDeclaredOccurrenceEndsTheExploration()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("witness").toPath();
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER, "false",
                null, null, true);
        seed.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        seed.decision(TARGET, "Guard#u8", 1, false, "EXPR.0000000000000001");
        seed.flush();
        Session fatal = new Session(iteration, "s-fatal");
        fatal.activation(TARGET, true);
        fatal.fatal(TARGET, "Throw#u30", "true");
        fatal.answered(ObligationResult.of("OBL.s-fatal", Verdict.ADMITTED,
                "s-fatal", "the focused prefix reproduced"));
        fatal.flush();
        scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                "Guard#u8"));
        Path out = tree.newFolder("witness-out").toPath();
        Path results = out.resolve("obligation_results.jsonl");
        Files.write(results, new byte[0]);

        Path asked = out.resolve("asked");
        assertEquals("OBLIGATIONS_PROPOSED", plan(iteration, TARGET_SELECTOR,
                null, results, asked, 1).get("state").getAsString());
        assertFalse(obligations(asked).isEmpty());

        Path stopped = out.resolve("stopped");
        JsonObject manifest = ExploreMain.plan(iteration, TARGET_SELECTOR,
                null, results, iteration.resolve(StaticScopeMap.FILE),
                stopped, 1, "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.Bounds.defaults(), true);
        assertEquals("WITNESSED", manifest.get("state").getAsString());
        assertTrue(obligations(stopped).isEmpty());
        boolean named = false;
        for (GapRow gap : RowCodec.readAll(stopped.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            named |= gap.subject().startsWith("s-fatal at ")
                    && gap.cls() == GapClass.DIAGNOSTIC;
        }
        assertTrue("the stop names the witness", named);
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
        seed.activation(TARGET, false);
        seed.activation(WRITER, false);
        seed.activation(PRODUCER, false);
        seed.activation(BALANCER, false);
        seed.activation(READER, false);
        seed.activation(SIDECAR, false);
        seed.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER, "false",
                null, null, true);
        seed.root(PRODUCER, "CASE.TICK", "M_TICK", RootKind.INTEGRAL, "1",
                "0", "10", true);
        seed.root(BALANCER, "CASE.MOVE", "M_MOVE", RootKind.INTEGRAL, "1",
                "0", "10", true);
        seed.root(SIDECAR, "CASE.SEND", "M_SEND", RootKind.INTEGRAL, "1",
                "0", "10", true);
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
                Collections.singletonMap("CASE.TICK", "7"),
                Collections.<String, String>emptyMap());
        worker(iteration, "obligations-0000", "ob-aside", "OBL.aside",
                "s-aside", BALANCER, "Balance#u2",
                Collections.singletonMap("CASE.MOVE", "2"),
                Collections.<String, String>emptyMap());
        worker(iteration, "obligations-0000", "ob-both", "OBL.both",
                "s-up-and-aside", PRODUCER, "Rotate#u5",
                Collections.singletonMap("CASE.TICK", "7"),
                Collections.<String, String>emptyMap(),
                Collections.singletonList(new Corpus.Flip(BALANCER.id(),
                        "Balance#u2", 1, true, "OBL.aside")));
        worker(iteration, "obligations-0000", "ob-factor", "OBL.factor",
                "s-through-factor", SIDECAR, "Send#u4",
                Collections.singletonMap("CASE.SEND", "0"),
                Collections.<String, String>emptyMap());

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
        Path results = out.resolve("obligation_results.jsonl");
        Files.write(results, new byte[0]);
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
     * guard's own root, and one more write to the state it reads, do.
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
        // session, Near#u2, Far#u4, writes of the map, writes of the qop,
        // handoffs to a co-reader of the map
        String[][] sessions = {
            {"s-seed", "true", "true", "1", "1", "0"},
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
            session.root(TARGET, "CASE.A", "M_A", RootKind.INTEGRAL, "0",
                    "0", "10", true);
            session.root(TARGET, "CASE.B", "M_B", RootKind.INTEGRAL, "0",
                    "0", "10", true);
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
            session.flush();
        }
        Corpus corpus = Corpus.read(iteration, null);
        Task task = ClosurePlanner.taskOf(corpus,
                ClosurePlanner.taskId(TARGET));
        assertNotNull(task);
        String seed = dependence(corpus, task, "s-seed", "Guard#u8");
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
        assertFalse("and so is one more write to the state it reads",
                seed.equals(dependence(corpus, task, "s-more", "Guard#u8")));
        // The wave names an obligation once: a solver reading the corpus
        // mid-wave (a larger factor, another dependence) keeps that id.
        ObligationFactory.Candidate located = ObligationFactory.locate(corpus,
                Obligation.of("OBL.as-the-wave-named-it", task.taskId(),
                        Corpus.pathId("s-seed", TARGET), "Guard#u8", 1, true,
                        Collections.<String, String>emptyMap(),
                        Collections.<String, String>emptyMap(),
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
                session.target(TARGET, "BlockTokenSecretManager"
                        + "#retrieveDataEncryptionKey#8", "(= M_READ_KEY 0)");
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
            ClosurePlanner.Plan plan = ClosurePlanner.plan(
                    Corpus.read(iteration, null), TARGET,
                    ClosurePlanner.DEFAULT_MAX_TASKS, map);
            boolean task = false;
            for (Task planned : plan.tasks) {
                task |= planned.focused().equals(producer);
            }
            String lineage = "";
            for (GapRow gap : plan.gaps) {
                if (!gap.subject().equals(producer.render())) continue;
                assertEquals("never BLOCKING while a session ran it: "
                        + gap.detail(), GapClass.DIAGNOSTIC, gap.cls());
                if (gap.kind() == GapKind.LINEAGE_LOST) lineage = gap.detail();
            }
            String label = producer.regionId() + " captured=" + captured
                    + " focused=" + focused + " recorded=" + recorded;
            String tick = "";
            for (GapRow gap : plan.gaps) {
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
                boolean incomplete = false;
                for (GapRow gap : RowCodec.readAll(
                        wave.resolve("gaps.jsonl"), RowCodec::readGap)) {
                    incomplete |= gap.cls() == GapClass.BLOCKING
                            && gap.subject().equals(producer.render());
                }
                assertTrue("so at the fixpoint the closure is incomplete",
                        incomplete);
            }
        }
    }

    /** What the guard at {@code siteId} depends on in one session's path of
     *  the task ({@link ObligationFactory#dependence}). */
    private static String dependence(Corpus corpus, Task task,
                                     String sessionId, String siteId) {
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
        session.activation(TARGET, false);
        session.activation(WRITER, false);
        session.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "false", null, null, true);
        session.symbolic("EXPR.0000000000000001", "M_MARKER", "Z");
        session.constant("e.kept", "119992");
        session.decision(TARGET, "Guard#u8", 1, false,
                "EXPR.0000000000000001");
        session.write(STORED, ALL_KEYS, 5L, "e.kept");
        session.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        session.answered(ObligationResult.of("OBL." + sessionId,
                Verdict.ADMITTED, sessionId, "the focused prefix reproduced"));
        session.flush();
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
        // The recording mints the producer's own root: every instrumented
        // region of the seed runs symbolically ({@code Arms#attested}), so
        // the rotation that put a serial on the wire minted it.  That row
        // is also where any replay would PLANT a value of it -- the mint's
        // occurrence, which the focused set of an obligation assigning this
        // root has to hold.  Declared, because a serial a rotation moved is
        // the case's whole hypothesis (11741 declares SERIAL_NO +0..+3):
        // undeclared it is pinned to this reading, and then no arm a
        // rotation delivered under another reading is available at all.
        seed.root(producer, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "119992", null, null, true);
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

    // ---- (3b) a codec's String hole is answered with a delivered String --

    /**
     * WIRE-CODEC §6.4: a flip that needs another String at a decode is
     * answered with one a run's producer delivered in that same message,
     * spelled as its JSON string literal, which the replay plants verbatim.
     * An export of another message at the producer's endpoint is no
     * delivery of it: asking for that String is UNSAT.
     */
    @Test
    public void aStringHoleIsAnsweredWithAStringItsMessageDelivered()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Hole hole = Hole.of("SOLR_JSON", Arrays.<Object>asList("c", "state"),
                0);
        String message = "SOLR_ZK /collections/c/state.json@5";
        Endpoint exported = at(PRODUCER, "kv:state", "hole#5ac1");
        Endpoint attached = at(TARGET, "kv:state", "hole#5ac1");
        String[][] asks = {{"down", "\"down\""}, {"gone", ""}};
        for (String[] ask : asks) {
            Path iteration = tree.newFolder("hole-" + ask[0]).toPath();
            Session seed = new Session(iteration, "s-seed");
            seed.activation(TARGET, false);
            seed.activation(PRODUCER, false);
            seed.expression("e.active", VmExpressionIr.stringConstant(
                    "active"));
            seed.hole(exported, attached, "e.active", "active", hole,
                    message);
            seed.decision(TARGET, "Lookup#u8", 1, false,
                    "(= M_HOFF_STATE \"" + ask[0] + "\")");
            seed.flush();
            Session other = new Session(iteration, "s-down");
            other.activation(PRODUCER, true);
            other.answered(ObligationResult.of("OBL.s-down",
                    Verdict.ADMITTED, "s-down", "the prefix reproduced"));
            other.activation(TARGET, false);
            other.expression("e.gone", VmExpressionIr.stringConstant("gone"));
            other.expression("e.down", VmExpressionIr.stringConstant("down"));
            // Another version of the store, at the same endpoint.
            other.exports.add(ExportRow.of("s-down", ++other.seq, exported,
                    "e.gone", "Ljava/lang/String;", 0L, "\"gone\"", hole,
                    "SOLR_ZK /collections/c/state.json@4"));
            other.hole(exported, attached, "e.down", "down", hole, message);
            other.flush();
            scopeMap(iteration, targetSite("REGION.target", "Throw#u30",
                    "Lookup#u8"));
            Path out = tree.newFolder("hole-" + ask[0] + "-out").toPath();
            Path wave0 = out.resolve("obligations-0000");
            plan(iteration, TARGET_SELECTOR, null,
                    out.resolve("results.jsonl"), wave0, 0);
            Worker worker = solve(iteration, wave0,
                    named(obligations(wave0), "Lookup#u8"), out, "w0");
            if (ask[1].isEmpty()) {
                assertEquals(ask[0] + ": no run delivered it in this message",
                        Verdict.UNSAT, worker.verdict);
                continue;
            }
            assertEquals(Verdict.SAT_MODEL_READY, worker.verdict);
            assertEquals("the delivered String, as its JSON string literal",
                    ask[1], worker.obligation.answers().get(attached.id()));
        }
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

        // A root the flip depends on is not always minted where the flip
        // is.  11741's SERIAL_NO is the NameNode's, read by the balancer,
        // so the FOCUSED SET holds the MINT's occurrence too: an assignment
        // is planted where the run mints it and nowhere else, and a mint
        // running unfocused reads the recording's value under an obligation
        // asking for another one.
        Path elsewhere = tree.newFolder("minted-elsewhere").toPath();
        Session across = new Session(elsewhere, "s-seed");
        across.activation(target, false);
        across.activation(PRODUCER, false);
        across.root(PRODUCER, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "7", null, null, true);
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
        replayed.root(target, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "7", null, null, true);
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
        boolean unmintableNamed = false;
        for (GapRow gap : RowCodec.readAll(unmintable.directory
                .resolve("gaps.jsonl"), RowCodec::readGap)) {
            unmintableNamed |= gap.kind() == GapKind.ASSIGNMENT_UNMINTABLE
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && gap.subject().equals(orphan.obligationId())
                    && gap.detail().equals("CASE.SERIAL");
        }
        assertTrue("the obligation is named, and so is the root",
                unmintableNamed);

        // A clock has no domain either, and is not pinned for it: it is free
        // with a floor.  What the focus row states for one is the SKEW the
        // replay adds to the instant it reads for itself -- never the
        // recording's instant, which no other execution ever reads -- so it
        // is written apart from the values a mint writes.
        Path ticking = tree.newFolder("clock").toPath();
        Session ticks = new Session(ticking, "s-seed");
        ticks.activation(target, false);
        ticks.root(target, "CASE.NOW", "M_NOW", RootKind.CLOCK, "700",
                null, null, true);
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
        String tickedQuery = new String(Files.readAllBytes(ticked.directory
                .resolve("obligation_query.smt2")), "UTF-8");
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
        both.root(target, "CASE.NOW", "M_NOW", RootKind.CLOCK, "700",
                null, null, true);
        both.root(target, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "182907", null, null, true);
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

            ClosurePlanner.Plan plan = ClosurePlanner.plan(
                    Corpus.read(iteration, null), TARGET,
                    ClosurePlanner.DEFAULT_MAX_TASKS, StaticScopeMap.empty());
            List<String> focused = new ArrayList<String>();
            for (Task task : plan.tasks) focused.add(task.focused().render());
            assertTrue("the store's writer: " + focused,
                    focused.contains(WRITER.render()));
            assertEquals("the state the read saw through the store: "
                    + focused, referent, focused.contains(cleaner.render()));
        }
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
        ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, target, ClosurePlanner.DEFAULT_MAX_TASKS, map);
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
        spread.activation(target, false);
        spread.activation(writer, false);
        spread.activation(producer, false);
        spread.activation(sibling, false);
        spread.activation(foreignWriter, false);
        spread.activation(foreignExporter, false);
        spread.activation(elsewhereOnly, false);
        spread.activation(otherMap, false);
        spread.activation(coReader, false);
        spread.constant("e.other", "7");
        spread.write(at(otherMap, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 12, true), "BlockTokenSecretManager"
                        + "#addKeys#12"), LocationId.of(LocationKind.MAP, "34",
                "allKeys"), 6L, "e.other");
        spread.read(at(coReader, Endpoint.stateSite("BlockTokenSecretManager",
                        "retrieveDataEncryptionKey", 8, false),
                        "BlockTokenSecretManager"
                                + "#retrieveDataEncryptionKey#8"), allKeys,
                5L, "M_READ_KEY_2", "119992");
        spread.constant("e.119992", "119992");
        spread.symbolic("e.stored", "M_HOFF_KEY");
        spread.export(exported, "e.119992", 11L, "119992");
        spread.attach(attached, "M_HOFF_KEY", "119992", exported);
        spread.write(at(writer, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 12, true), "BlockTokenSecretManager"
                        + "#addKeys#12"), allKeys, 5L, "e.stored");
        spread.read(at(target, Endpoint.stateSite("BlockTokenSecretManager",
                        "retrieveDataEncryptionKey", 8, false),
                        "BlockTokenSecretManager"
                                + "#retrieveDataEncryptionKey#8"), allKeys,
                5L, "M_READ_KEY", "119992");
        spread.target(target, "BlockTokenSecretManager"
                + "#retrieveDataEncryptionKey#8", "(= M_READ_KEY 0)");
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
        ClosurePlanner.Plan scoped = ClosurePlanner.plan(
                Corpus.read(perNode, null), target, ClosurePlanner.DEFAULT_MAX_TASKS, spreadMap);
        Map<String, String> scopedWhy = new LinkedHashMap<String, String>();
        for (Task task : scoped.tasks) {
            scopedWhy.put(task.focused().render(),
                    scoped.why.get(task.taskId()));
        }
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
        assertEquals("while the producer the rows paired stays a member: "
                        + scopedWhy, ClosurePlanner.CLOSURE_MEMBER,
                scopedWhy.get(producer.render()));
        boolean saidNeverRan = false;
        boolean saidNotHere = false;
        for (GapRow gap : scoped.gaps) {
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
        rests.activation(target, false);
        rests.activation(writer, false);
        rests.activation(producer, false);
        rests.activation(scanning, false);
        rests.activation(farExpiry, false);
        rests.symbolic("e.scan", "M_SCANNED", "L");
        rests.symbolic("e.stored", "M_HOFF_KEY");
        // What the rotation DELIVERED: a projection out of the map, over
        // the version the scan left it at, as the VM publishes it.
        rests.expression("e.exported", guardedRead(nnKeys, 25L, "L",
                leaf("M_HOFF_KEY", "I"), 30L));
        rests.write(scanned, nnKeys, 25L, "e.scan", "L");
        rests.export(exported, "e.exported", 11L, "119992");
        rests.attach(attached, "M_HOFF_KEY", "119992", exported);
        rests.write(at(writer, Endpoint.stateSite("BlockTokenSecretManager",
                        "addKeys", 12, true), "BlockTokenSecretManager"
                        + "#addKeys#12"), allKeys, 5L, "e.stored");
        rests.read(at(target, Endpoint.stateSite("BlockTokenSecretManager",
                        "retrieveDataEncryptionKey", 8, false),
                        "BlockTokenSecretManager"
                                + "#retrieveDataEncryptionKey#8"), allKeys,
                5L, "M_READ_KEY", "119992");
        rests.target(target, "BlockTokenSecretManager"
                + "#retrieveDataEncryptionKey#8", "(= M_READ_KEY 0)");
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
        ClosurePlanner.Plan viaState = ClosurePlanner.plan(
                Corpus.read(restsOnState, null), target, ClosurePlanner.DEFAULT_MAX_TASKS, restsMap);
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
                Corpus.read(split, null), confused, ClosurePlanner.DEFAULT_MAX_TASKS, map);
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
        held.activation(target, false);
        held.activation(writer, false);
        held.activation(producer, false);
        held.constant("e.119992", "119992");
        held.export(exported, "e.119992", 11L, "119992");
        held.attach(attached, "M_HOFF_KEY", "119992", exported);
        held.flush();
        Session wrongWorld = new Session(unadmitted, "s-unadmitted");
        wrongWorld.activation(writer, true);
        wrongWorld.activation(producer, true);
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
        ranOther.answered(ObligationResult.of("OBL.s-flip", Verdict.ADMITTED,
                "s-flip", "the focused prefix reproduced"));
        ranOther.flush();
        assertTrue("a replay that did not run the member and ran another "
                        + "context in its place IS a replacement",
                new SlotTable().reconcile(Corpus.read(instead, null),
                        Collections.singleton(firstRequest.id()), 6)
                        .replaced);

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
            seedBoth.activation(firstRequest, false);
            seedBoth.activation(secondRequest, false);
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
        // With two members held there, a context the closure does NOT hold
        // is still a replacement when it ran the code point alone, and still
        // growth beside a member that ran.
        OccurrenceAddress stranger = occurrence("hdfs-case/dn0",
                "REGION.checksum",
                CausalContext.of("ffeeddccbbaa9988", "HDFS_SASL/checksum"),
                "o.a.h.h.s.d.DataXceiver#run#44");
        Path strangerAlone = tree.newFolder("closure-stranger-alone").toPath();
        Session seedTwo = new Session(strangerAlone, "s-seed");
        seedTwo.activation(firstRequest, false);
        seedTwo.activation(secondRequest, false);
        seedTwo.flush();
        Session ranStranger = new Session(strangerAlone, "s-flip");
        ranStranger.activation(stranger, true);
        ranStranger.answered(ObligationResult.of("OBL.s-flip",
                Verdict.ADMITTED, "s-flip", "the focused prefix reproduced"));
        ranStranger.flush();
        assertTrue("a code point the closure holds, run under no context "
                        + "it holds there, IS a replacement",
                new SlotTable().reconcile(Corpus.read(strangerAlone, null),
                        bothMembers, 8).replaced);
        Path strangerBeside = tree.newFolder("closure-stranger-beside")
                .toPath();
        Session seedThree = new Session(strangerBeside, "s-seed");
        seedThree.activation(firstRequest, false);
        seedThree.activation(secondRequest, false);
        seedThree.flush();
        Session ranBeside = new Session(strangerBeside, "s-flip");
        ranBeside.activation(secondRequest, true);
        ranBeside.activation(stranger, false);
        ranBeside.answered(ObligationResult.of("OBL.s-flip",
                Verdict.ADMITTED, "s-flip", "the focused prefix reproduced"));
        ranBeside.flush();
        assertFalse("beside a member that ran, another context is a second "
                        + "request",
                new SlotTable().reconcile(Corpus.read(strangerBeside, null),
                        bothMembers, 9).replaced);

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
        ClosurePlanner.Plan withGhost = ClosurePlanner.plan(
                Corpus.read(unrun, null), target, ClosurePlanner.DEFAULT_MAX_TASKS, map);
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
                Corpus.read(viaRef, null), target, ClosurePlanner.DEFAULT_MAX_TASKS, map);
        for (GapRow gap : lowered.gaps) {
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
        // there is no run to focus (PIPELINE §7.2).
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
        container.activation(target, false);
        container.activation(writer, false);
        container.activation(expiring, false);
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
        Set<String> says = lowering.reachedSymbols(mapGuard,
                new LinkedHashSet<String>(), new LinkedHashSet<String>());
        assertFalse("and the text does not SAY the read behind it, which is "
                        + "what a query binds its variables by: " + says,
                says.contains(mapState));
        Set<String> restsOn = new LinkedHashSet<String>();
        lowering.reachedSymbols(mapGuard, new LinkedHashSet<String>(),
                restsOn);
        assertTrue("it RESTS ON it, which is what the closure demands: "
                + restsOn, restsOn.contains(mapState));
        // And what the state the guard rests on IS: the shape its WRITER
        // delivers, which is what a query must declare the v_C variable at.
        // The read row states javaType "L" -- the reference whose state was
        // read -- so a query that took the sort off the row asserted an
        // AssocState chain over a Ref and z3 answered the obligation
        // `(error "Sorts Ref and AssocState are incompatible")`.
        assertEquals("the writer of the state delivers its shape",
                "AssocState", lowering.lower("e.map").sort());
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
        ClosurePlanner.Plan demanded = ClosurePlanner.plan(vC, target, ClosurePlanner.DEFAULT_MAX_TASKS,
                ofAllKeys);
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
        for (GapRow gap : demanded.gaps) {
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
                null, iteration.resolve("results.jsonl"),
                iteration.resolve(StaticScopeMap.FILE), waveDir, 0,
                "epoch0", ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.Bounds.defaults(), false);
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
                ObligationFactory.Bounds.defaults(), false);
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
        clocked.root(TARGET, "CASE.NOW", "M_NOW", RootKind.CLOCK, "1000",
                null, null, true);
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
        other.root(TARGET, "CASE.NOW", "M_NOW", RootKind.CLOCK, "1000",
                null, null, true);
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
        boolean named = false;
        for (GapRow gap : RowCodec.readAll(asIs.directory.resolve(
                "gaps.jsonl"), RowCodec::readGap)) {
            named |= gap.kind() == GapKind.ADMISSION_GAP
                    && gap.cls() == GapClass.DIAGNOSTIC
                    && ExploreCodec.EXPLORATION.equals(gap.sessionId())
                    && gap.detail().contains("clock margin")
                    && gap.detail().contains("(< 1500 clk_");
        }
        assertTrue("and the wave says which atom it could not reach", named);

        // The inherited flip.
        Path iteration = tree.newFolder("inherited-margin").toPath();
        // The recording: the rotation read its clock and took neither arm
        // the child was later held to, and the target never reached the
        // guard this obligation flips.
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.activation(PRODUCER, false);
        seed.root(PRODUCER, "CASE.NOW", "M_NOW", RootKind.CLOCK, "1000",
                null, null, true);
        seed.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "false", null, null, true);
        seed.root(TARGET, "CASE.OTHER", "M_OTHER", RootKind.MARKER,
                "false", null, null, true);
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
        child.root(PRODUCER, "CASE.NOW", "M_NOW", RootKind.CLOCK, "1000",
                null, null, true);
        child.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "false", null, null, true);
        child.root(TARGET, "CASE.OTHER", "M_OTHER", RootKind.MARKER,
                "false", null, null, true);
        child.decision(PRODUCER, "Before#u3", 1, true,
                notBefore("200000", "M_NOW"));
        child.decision(PRODUCER, "Rotate#u5", 1, true,
                notBefore("100000", "M_NOW"));
        child.decision(TARGET, "Guard#u8", 1, false, "M_MARKER");
        child.decision(TARGET, "Deeper#u9", 1, false, "M_OTHER");
        child.answered(ObligationResult.of("OBL.inherit", Verdict.ADMITTED,
                "s-inherit", "the focused prefix reproduced"));
        child.flush();
        worker(iteration, "obligations-0000", "ob-inherit", "OBL.inherit",
                "s-inherit", PRODUCER, "Rotate#u5",
                Collections.<String, String>emptyMap(),
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

    // ---- (6a) a flip no replay can plant is refused before its replay --

    /**
     * A model that assigns no root, moves no clock and answers no handoff
     * asks for a replay of the world its path already ran: it takes the
     * other arm only through which writer a read observes, which no replay
     * sets.  SOLR-18413 r5: all 67 focused replays were such, each ended
     * NOT_ADMITTED after 10 to 22 minutes; now the solver says so.
     */
    @Test
    public void aFlipOnlyAnotherWriterTakesIsRefusedBeforeItsReplay()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = twoWriters("empty-world");
        Path out = tree.newFolder("empty-world-out").toPath();
        Path wave = out.resolve("obligations-0000");
        plan(iteration, TARGET_SELECTOR, null,
                out.resolve("results.jsonl"), wave, 0);
        Obligation lookup = named(obligations(wave), "Lookup#u8");
        assertNotNull(lookup);
        Worker worker = solve(iteration, wave, lookup, out, "w0");
        assertTrue("the other writer is the flip's only way: "
                + query(worker), query(worker).contains("wchoice_"));
        assertEquals(detail(worker), Verdict.NOT_ADMITTED, worker.verdict);
        assertTrue(detail(worker), detail(worker).startsWith("EMPTY_WORLD: "
                + "the model assigns no root, moves no clock and answers no "
                + "handoff, so the replay it asks for runs the world of "
                + "s-seed again")
                && detail(worker).contains("wchoice_"));
        assertEquals("and no replay is asked for", 0L, Files.size(
                worker.directory.resolve(ObligationDir.FOCUSED_TASK)));
    }

    /**
     * One question, one answer.  An obligation's id drifts as sessions land
     * (its dependence's factor grows); its question -- the query as asked
     * and the world it plants -- does not, and a question answered under
     * another id is not asked again (SOLR-18413 r5: 185 questions asked 717
     * times).  The planner's question is the one its solver asks.
     */
    @Test
    public void aQuestionAnsweredUnderAnotherIdIsNotAskedAgain()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = twoWriters("asked-once");
        Path out = tree.newFolder("asked-once-out").toPath();
        Path wave0 = out.resolve("obligations-0000");
        Path results = out.resolve("results.jsonl");
        plan(iteration, TARGET_SELECTOR, null, results, wave0, 0);
        Obligation lookup = named(obligations(wave0), "Lookup#u8");
        String planned = new String(Files.readAllBytes(wave0.resolve(
                ExploreMain.QUESTIONS_FILE)), StandardCharsets.UTF_8);
        Worker worker = solve(iteration, wave0, lookup, out, "w0");
        String asked = new String(Files.readAllBytes(worker.directory
                .resolve(ObligationDir.QUESTION)), StandardCharsets.UTF_8)
                .trim();
        assertEquals("the planner's question is the one its solver asked",
                lookup.obligationId() + "\t" + asked + "\n", planned);
        // The same question, answered by an earlier wave under an id that
        // has since drifted.
        Path earlier = Files.createDirectories(iteration.resolve(
                "obligations-0000").resolve("OB.drifted"));
        Files.write(earlier.resolve(ObligationDir.QUESTION),
                (asked + "\n").getBytes(StandardCharsets.UTF_8));
        Files.write(results, (RowCodec.toLine(RowCodec.writeObligationResult(
                ObligationResult.of("OB.drifted", Verdict.NOT_ADMITTED, "",
                        "refused"))) + "\n").getBytes(StandardCharsets.UTF_8));
        Path wave1 = out.resolve("obligations-0001");
        plan(iteration, TARGET_SELECTOR, null, results, wave1, 1);
        assertNull("an answered question is not asked again",
                named(obligations(wave1), "Lookup#u8"));
        assertEquals("", new String(Files.readAllBytes(wave1.resolve(
                ExploreMain.QUESTIONS_FILE)), StandardCharsets.UTF_8));
        boolean named = false;
        for (GapRow gap : RowCodec.readAll(wave1.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            named |= gap.detail().startsWith("question " + asked
                    + " already answered NOT_ADMITTED by an earlier wave, as "
                    + "obligation OB.drifted");
        }
        assertTrue("and the settled question is named", named);
    }

    /** A target read of a map two concurrent addKeys wrote, recorded taking
     *  the first write: {@code Lookup#u8} takes the other arm only if the
     *  read took the other writer's. */
    private Path twoWriters(String name) throws IOException {
        Path iteration = tree.newFolder(name).toPath();
        // A second addKeys, started by a request of its own.
        OccurrenceAddress again = occurrence("hdfs-case/dn0",
                "REGION.addkeys", CausalContext.of(Role.of("KEY_UPDATE"), "",
                        2), "o.a.h.h.s.d.BPServiceActor#offerService#41");
        Session seed = new Session(iteration, "s-seed");
        seed.activation(TARGET, false);
        seed.activation(WRITER, false);
        seed.activation(again, false, true, "fixture#key-updater");
        seed.constant("e.1", "1");
        seed.constant("e.2", "2");
        seed.write(STORED, ALL_KEYS, 5L, "e.1");
        seed.write(at(again, Endpoint.stateSite("BlockTokenSecretManager",
                "addKeys", 12, true), "BlockTokenSecretManager#addKeys#12"),
                ALL_KEYS, 6L, "e.2");
        seed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "1");
        seed.decision(TARGET, "Lookup#u8", 1, false, "(= M_READ_KEY 2)");
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
        seed.activation(TARGET, false);
        seed.activation(WRITER, false);
        seed.activation(PRODUCER, false);
        seed.root(PRODUCER, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL,
                "119992", null, null, true);
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
        rotated.activation(WRITER, false);
        rotated.activation(TARGET, false);
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
        timed.activation(TARGET, false);
        timed.activation(WRITER, false);
        timed.activation(PRODUCER, false);
        timed.root(PRODUCER, "CASE.NOW", "M_NOW", RootKind.CLOCK, "119992",
                null, null, true);
        timed.symbolic("e.now", "M_NOW");
        timed.symbolic("e.stored", "M_HOFF_KEY");
        timed.export(ROTATED, "e.now", 11L, "119992");
        timed.attach(DELIVERED, "M_HOFF_KEY", "119992", ROTATED);
        timed.write(STORED, ALL_KEYS, 5L, "e.stored");
        timed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        timed.decision(TARGET, "Lookup#u8", 1, false,
                "(= M_READ_KEY 119995)");
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
        seed.root(TARGET, "CASE.NOW", "M_NOW", RootKind.CLOCK, "1000",
                null, null, true);
        seed.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "false", null, null, true);
        seed.root(TARGET, "CASE.OTHER", "M_OTHER", RootKind.MARKER,
                "false", null, null, true);
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
        child.root(TARGET, "CASE.NOW", "M_NOW", RootKind.CLOCK, "5000",
                null, null, true);
        child.root(TARGET, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "false", null, null, true);
        child.root(TARGET, "CASE.OTHER", "M_OTHER", RootKind.MARKER,
                "false", null, null, true);
        child.decision(TARGET, "Expiry#u15", 1, true,
                notBefore("200000", "M_NOW"));
        child.decision(TARGET, "Guard#u8", 1, false, "M_MARKER");
        child.decision(TARGET, "Deeper#u9", 1, false, "M_OTHER");
        child.answered(ObligationResult.of("OBL.later", Verdict.ADMITTED,
                "s-later", "the focused prefix reproduced"));
        child.flush();
        worker(iteration, "obligations-0000", "ob-later", "OBL.later",
                "s-later", TARGET, "Expiry#u15",
                Collections.<String, String>emptyMap(),
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
                query.contains("(and (>= clk_CASE_NOW_s_later 5000) (<= "
                        + "clk_CASE_NOW_s_later 2592005000))"));
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
            only.root(TARGET, "CASE.NOW", "M_NOW", RootKind.CLOCK, "5000",
                    null, null, true);
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
        return new String(Files.readAllBytes(
                worker.directory.resolve("obligation_query.smt2")),
                java.nio.charset.StandardCharsets.UTF_8);
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
                ObligationFactory.Bounds.defaults(), false);
    }

    /**
     * The epoch's static scope map, as PLAN publishes it (SYMBOL-SCOPE §3).
     *
     * <p>Written as the artifact's own text, so what these cases exercise is
     * the published shape and not a builder's idea of it.</p>
     */
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
        seed.activation(TARGET, false);
        seed.activation(enclosing, false);
        seed.activation(holder, false);
        seed.activation(unrelated, false);
        seed.activation(ambient, false, false);
        seed.symbolic("e.stored", "M_HOFF_KEY");
        seed.write(stored, ALL_KEYS, 5L, "e.stored");
        seed.read(LOOKED_UP, ALL_KEYS, 5L, "M_READ_KEY", "119992");
        seed.target(TARGET, "BlockTokenSecretManager"
                + "#retrieveDataEncryptionKey#8", "(= M_READ_KEY 0)");
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
        Map<String, String> blind = why(ClosurePlanner.plan(
                Corpus.read(iteration, null), TARGET, ClosurePlanner.DEFAULT_MAX_TASKS,
                StaticScopeMap.read(mapFile)));
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
        ClosurePlanner.Plan plan = ClosurePlanner.plan(
                Corpus.read(iteration, null), TARGET,
                ClosurePlanner.DEFAULT_MAX_TASKS,
                StaticScopeMap.read(mapFile));
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
                // THE WAVE'S, and DIAGNOSTIC.  "This flip does not depend
                // on the declared roots on this prefix" is a fact about
                // the question the wave asked and about no execution, so
                // it is not a blocking defect and it is not filed under
                // the session whose path the flip was cut from -- which
                // for a wave-0 flip is the SEED, whose ledger then said
                // the recording had a blocking defect and made
                // campaign_write_gaps exit 3.
                refused |= gap.cls() == GapClass.DIAGNOSTIC
                        && ExploreCodec.EXPLORATION.equals(gap.sessionId())
                        && gap.detail().contains(
                                "the recording's own valuation");
            }
            assertTrue("and the refusal is named, as the wave's own "
                    + "diagnostic", refused);
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
                RowCodec::readObligationResult);
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
        /** What this replay SETTLED, as its own obligations.jsonl states. */
        private final List<ObligationResult> answered = new ArrayList<>();
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
                    symbol, kind, recorded, min, max, declared,
                    kind == RootKind.CLOCK ? 1_000_000L : 0L));
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

        /** A codec's String hole: the producer's export of it and this
         *  run's decode, paired by the envelope of one message. */
        private void hole(Endpoint producer, Endpoint consumer, String ref,
                          String text, Hole hole, String message) {
            String literal = "\"" + text + "\"";
            exports.add(ExportRow.of(sessionId, ++seq, producer, ref,
                    "Ljava/lang/String;", 0L, literal, hole, message));
            attaches.add(AttachRow.of(sessionId, ++seq, consumer,
                    "M_HOFF_STATE", "Ljava/lang/String;", literal, false, null,
                    producer, message, AttachRow.ENVELOPE, hole));
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
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
            // The fixture STATES the role, as a campaign's own session
            // manifest does.
            boolean focused = false;
            for (ActivationRow activation : activations) {
                if (activation.focused()) focused = true;
            }
            RowCodec.writeManifest(dir.manifest(),
                    SessionManifest.of(sessionId,
                            focused ? SessionManifest.Role.FOCUSED
                                    : SessionManifest.Role.SEED,
                            focused ? Collections.singletonList(
                                    "OBL." + sessionId)
                                    : Collections.<String>emptyList()));
        }
    }
}
