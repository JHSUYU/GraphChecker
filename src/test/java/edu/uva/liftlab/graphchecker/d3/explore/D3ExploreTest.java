package edu.uva.liftlab.graphchecker.d3.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootDomain;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * Exploration, checked on the five things a corpus can say to it.
 *
 * <p>Each case is a synthetic corpus in the contract's own file layout: a
 * nested guard chain that deepens one decision per wave; a handoff bound by
 * arms that deliver literals; a handoff no producer delivers; a root the case
 * declares no domain for; and a read whose writer has to be in the closure.
 * The queries are solved by the same z3 the campaign uses, so an assertion
 * about SAT or UNSAT is an assertion about the query, not about a stub.</p>
 */
public class D3ExploreTest {
    private static final String TARGET =
            "hdfs-case/dn0#epoch0/region/REGION.target#1";
    private static final String WRITER =
            "hdfs-case/dn0#epoch0/region/REGION.addkeys#1";
    private static final String PRODUCER =
            "hdfs-case/nn0#epoch0/region/REGION.rotate#1";

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    // ---- (1) depth: one decision per wave -----------------------------

    @Test
    public void nestedGuardChainDeepensOneDecisionPerWave() throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("depth").toPath();
        OccurrenceAddress target = OccurrenceAddress.parse(TARGET);
        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, true);
        seed.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER, "false",
                null, null, true);
        seed.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        // if (a) if (b) throw: the recording took not-a and never reached b.
        seed.decision(target, "Guard#u8", 1, false, "M_MARKER");
        seed.flush();

        Path out = tree.newFolder("depth-out").toPath();
        JsonObject first = explore(iteration, target, out, 4);
        assertEquals("PENDING_RESULTS", first.get("state").getAsString());
        List<Obligation> wave0 = obligations(out, 0);
        assertEquals(1, wave0.size());
        assertEquals("Guard#u8", wave0.get(0).siteId());
        assertTrue(wave0.get(0).flippedOutcome());
        assertEquals("true",
                wave0.get(0).rootAssignments().get("CASE.MARKER"));

        // The runtime ran it: the flip took the first guard and recorded the
        // second one, which had never executed before.
        Session flipped = new Session(iteration, "s-flip");
        flipped.activation(target, true);
        flipped.root(target, "CASE.MARKER", "M_MARKER", RootKind.MARKER,
                "true", null, null, true);
        flipped.root(target, "CASE.COUNT", "M_COUNT", RootKind.INTEGRAL, "0",
                "0", "10", true);
        flipped.decision(target, "Guard#u8", 1, true, "M_MARKER");
        flipped.decision(target, "Guard#u19", 1, false, "(> M_COUNT 5)");
        flipped.flush();
        RowCodec.writeAll(out.resolve("wave-0000").resolve("results.jsonl"),
                Collections.singletonList(ObligationResult.of(
                        wave0.get(0).obligationId(), Verdict.VALIDATED,
                        "s-flip", "the flip ran")),
                ExploreCodec::writeResult);

        JsonObject second = explore(iteration, target, out, 4);
        assertEquals("PENDING_RESULTS", second.get("state").getAsString());
        List<Obligation> wave1 = obligations(out, 1);
        List<String> sites = new ArrayList<String>();
        for (Obligation obligation : wave1) sites.add(obligation.siteId());
        assertTrue("the deeper guard is a first-class obligation: " + sites,
                sites.contains("Guard#u19"));
        for (Obligation obligation : wave1) {
            assertFalse("a query is never asked twice",
                    obligation.obligationId().equals(
                            wave0.get(0).obligationId()));
        }
        // The deeper obligation carries the previous wave's answer in its own
        // prefix: it needs the marker true AND the count above five.
        Obligation deeper = named(wave1, "Guard#u19");
        assertEquals("true", deeper.rootAssignments().get("CASE.MARKER"));
        assertTrue(Integer.parseInt(
                deeper.rootAssignments().get("CASE.COUNT")) > 5);
    }

    // ---- (2) a handoff is answered only with what a producer delivers --

    @Test
    public void handoffIsAnsweredWithAValueSomeProducerDelivers()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("family").toPath();
        OccurrenceAddress target = OccurrenceAddress.parse(TARGET);
        OccurrenceAddress producer = OccurrenceAddress.parse(PRODUCER);
        Endpoint exported = Endpoint.of(producer, "XCH.resp.block-key-id", 1, 0);
        Endpoint attached = Endpoint.of(target, "XCH.resp.block-key-id", 1, 0);

        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, true);
        seed.activation(producer, false);
        seed.constant("e.119992", "119992");
        seed.export(exported, "e.119992", 11L, "119992");
        seed.attach(attached, "M_HOFF_KEY", "119992", exported);
        seed.decision(target, "Lookup#u8", 1, false, "(= M_HOFF_KEY 119995)");
        seed.flush();
        // A second recording of the same interaction delivered another id.
        Session rotated = new Session(iteration, "s-rot");
        rotated.activation(producer, false);
        rotated.constant("e.119995", "119995");
        rotated.export(exported, "e.119995", 12L, "119995");
        rotated.flush();

        Path out = tree.newFolder("family-out").toPath();
        explore(iteration, target, out, 2);
        List<Obligation> wave0 = obligations(out, 0);
        assertEquals(1, wave0.size());
        Obligation obligation = wave0.get(0);
        assertTrue("the control is producible", obligation.unproducible()
                .isEmpty());
        assertEquals("119995", obligation.answers().get(attached.id()));

        // The negative control: a flip that needs a value no producer of this
        // corpus delivers is UNSAT, not answered out of the family.
        Path other = tree.newFolder("family-unsat").toPath();
        Session lone = new Session(other, "s-seed");
        lone.activation(target, true);
        lone.activation(producer, false);
        lone.constant("e.119992", "119992");
        lone.export(exported, "e.119992", 11L, "119992");
        lone.attach(attached, "M_HOFF_KEY", "119992", exported);
        lone.decision(target, "Lookup#u8", 1, false, "(= M_HOFF_KEY 7)");
        lone.flush();
        Path unsatOut = tree.newFolder("family-unsat-out").toPath();
        explore(other, target, unsatOut, 2);
        assertTrue("no replay is spent on a value the system cannot make",
                obligations(unsatOut, 0).isEmpty());
        assertEquals(Verdict.UNSAT, closed(unsatOut, 0).get(0).verdict());
    }

    // ---- (3) a handoff no producer delivers is named ------------------

    @Test
    public void controlWithNoArmIsUnproducible() throws Exception {
        Assume.assumeTrue(z3Available());
        Path iteration = tree.newFolder("unproducible").toPath();
        OccurrenceAddress target = OccurrenceAddress.parse(TARGET);
        Endpoint attached = Endpoint.of(target, "XCH.req.key-id", 1, 0);
        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, true);
        // Unpaired: the value arrived from outside this corpus.
        seed.attach(attached, "M_HOFF_REQ", "119992", null);
        seed.decision(target, "Lookup#u8", 1, false, "(= M_HOFF_REQ 5)");
        seed.flush();

        Path out = tree.newFolder("unproducible-out").toPath();
        explore(iteration, target, out, 2);
        List<Obligation> wave0 = obligations(out, 0);
        assertEquals(1, wave0.size());
        assertEquals(Collections.singletonList(attached.id()),
                wave0.get(0).unproducible());
        assertEquals("5", wave0.get(0).answers().get(attached.id()));
        boolean named = false;
        for (GapRow gap : RowCodec.readAll(out.resolve("gaps.jsonl"),
                RowCodec::readGap)) {
            named |= gap.kind() == GapKind.UNPRODUCIBLE_ANSWER
                    && gap.subject().contains("XCH.req.key-id");
        }
        assertTrue("the obligation announces the control it invented", named);
    }

    // ---- (4) a root with no domain is pinned, here as in the composer --

    @Test
    public void rootWithoutADomainCannotBeMoved() throws Exception {
        Assume.assumeTrue(z3Available());
        OccurrenceAddress target = OccurrenceAddress.parse(TARGET);
        Path pinned = tree.newFolder("pinned").toPath();
        Session seed = new Session(pinned, "s-seed");
        seed.activation(target, true);
        seed.root(target, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL, "7",
                null, null, false);
        seed.decision(target, "Arrival#u8", 1, false, "(> M_SERIAL 10)");
        seed.flush();
        Path pinnedOut = tree.newFolder("pinned-out").toPath();
        explore(pinned, target, pinnedOut, 2);
        assertTrue(obligations(pinnedOut, 0).isEmpty());
        assertEquals(Verdict.UNSAT, closed(pinnedOut, 0).get(0).verdict());

        // Declared, the same flip is satisfiable inside the declared
        // domain, whose bounds the case states RELATIVE to the recording.
        Path declared = tree.newFolder("declared").toPath();
        Session open = new Session(declared, "s-seed");
        open.activation(target, true);
        open.root(target, "CASE.SERIAL", "M_SERIAL", RootKind.INTEGRAL, "7",
                null, null, true);
        open.decision(target, "Arrival#u8", 1, false, "(> M_SERIAL 10)");
        open.flush();
        Path domains = declared.resolve("root-domains.jsonl");
        RowCodec.writeAll(domains, Collections.singletonList(RootDomain.of(
                        "CASE.SERIAL", RootKind.INTEGRAL, "7", "+4", "+5")),
                ExploreCodec::writeDomain);
        Path declaredOut = tree.newFolder("declared-out").toPath();
        ExploreMain.run(declared, target, domains, declaredOut, 2,
                Paths.get("z3"), 10_000L, ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.DEFAULT_MAX_PER_TASK);
        List<Obligation> wave0 = obligations(declaredOut, 0);
        assertEquals(1, wave0.size());
        String moved = wave0.get(0).rootAssignments().get("CASE.SERIAL");
        assertTrue("free inside [11, 12], and nowhere else: " + moved,
                "11".equals(moved) || "12".equals(moved));
    }

    // ---- (5) the closure holds the writer of every version read -------

    @Test
    public void closureHoldsTheWriterOfAReadVersionAndTheWireProducer()
            throws Exception {
        Path iteration = tree.newFolder("closure").toPath();
        OccurrenceAddress target = OccurrenceAddress.parse(TARGET);
        OccurrenceAddress writer = OccurrenceAddress.parse(WRITER);
        OccurrenceAddress producer = OccurrenceAddress.parse(PRODUCER);
        LocationId allKeys = LocationId.of(LocationKind.MAP,
                "BlockTokenSecretManager", "allKeys");
        Endpoint exported = Endpoint.of(producer, "XCH.resp.block-key-id", 1, 0);
        Endpoint attached = Endpoint.of(writer, "XCH.resp.block-key-id", 1, 0);

        Session seed = new Session(iteration, "s-seed");
        seed.activation(target, true);
        seed.activation(writer, false);
        seed.activation(producer, false);
        seed.constant("e.119992", "119992");
        seed.export(exported, "e.119992", 11L, "119992");
        seed.attach(attached, "M_HOFF_KEY", "119992", exported);
        seed.write(Endpoint.of(writer, "BlockTokenSecretManager#addKeys#12"
                + ":WRITE", 1, 0), allKeys, 5L, "e.119992");
        seed.read(Endpoint.of(target, "BlockTokenSecretManager"
                + "#retrieveDataEncryptionKey#8:READ", 1, 0), allKeys, 5L,
                "M_READ_KEY", "119992");
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
    }

    // ---- fixtures -----------------------------------------------------

    private JsonObject explore(Path iteration, OccurrenceAddress anchor,
                               Path out, int maxWaves) throws IOException {
        return ExploreMain.run(iteration, anchor, null, out, maxWaves,
                Paths.get("z3"), 10_000L, ClosurePlanner.DEFAULT_MAX_TASKS,
                ObligationFactory.DEFAULT_MAX_PER_TASK);
    }

    private static List<Obligation> obligations(Path out, int wave)
            throws IOException {
        return RowCodec.readAll(wave(out, wave).resolve("obligations.jsonl"),
                ExploreCodec::readObligation);
    }

    private static List<ObligationResult> closed(Path out, int wave)
            throws IOException {
        return RowCodec.readAll(wave(out, wave).resolve("closed.jsonl"),
                ExploreCodec::readResult);
    }

    private static Path wave(Path out, int wave) {
        return out.resolve(String.format("wave-%04d", wave));
    }

    private static Obligation named(List<Obligation> obligations, String site) {
        for (Obligation obligation : obligations) {
            if (obligation.siteId().equals(site)) return obligation;
        }
        return null;
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
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<>();

        private Session(Path iteration, String sessionId) {
            this.dir = SessionDir.of(iteration, sessionId);
            this.sessionId = sessionId;
        }

        private void activation(OccurrenceAddress occurrence,
                                boolean focused) {
            activations.add(ActivationRow.of(sessionId, occurrence,
                    "task-" + occurrence.regionId(), focused));
        }

        private void decision(OccurrenceAddress occurrence, String site,
                              int ordinal, boolean outcome, String term) {
            decisions.add(DecisionRow.of(sessionId, occurrence, site, ordinal,
                    outcome, term, Collections.<String, Long>emptyMap()));
        }

        private void root(OccurrenceAddress occurrence, String rootId,
                          String symbol, RootKind kind, String recorded,
                          String min, String max, boolean declared) {
            roots.add(RootMintRow.of(sessionId, occurrence, rootId, symbol,
                    kind, recorded, min, max, declared));
        }

        private void export(Endpoint endpoint, String ref, long handle,
                            String recorded) {
            exports.add(ExportRow.of(sessionId, endpoint, ref, handle,
                    recorded));
        }

        private void attach(Endpoint endpoint, String symbol, String arrival,
                            Endpoint producer) {
            attaches.add(AttachRow.of(sessionId, endpoint, symbol, arrival,
                    false, null, producer, "corr-" + endpoint.ordinal()));
        }

        private void write(Endpoint endpoint, LocationId location,
                           long version, String ref) {
            writes.add(WriteRow.of(sessionId, endpoint, location, version,
                    ref));
        }

        private void read(Endpoint endpoint, LocationId location,
                          long version, String symbol, String concrete) {
            reads.add(ReadRow.of(sessionId, endpoint, location, version,
                    symbol, concrete));
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
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
        }
    }
}
