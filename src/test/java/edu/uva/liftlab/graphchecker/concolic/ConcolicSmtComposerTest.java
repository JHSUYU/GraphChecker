package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicSmtComposerTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void pollingWithoutASelectedOutputIsNotAnOccurrence() {
        RelationSummary producer = summary("POLL", "REGION.1@Test#1", 1,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject stutter = new JsonObject();
        stutter.add("outputExpressions", new JsonObject());

        assertFalse(ConcolicSmtComposer
                .belongsToSelectedOutputOccurrence(stutter,
                        producer.outputClosure()));
        assertTrue(ConcolicSmtComposer
                .belongsToSelectedOutputOccurrence(
                        producer.cases().get(0).getAsJsonObject(),
                        producer.outputClosure()));
    }


    @Test
    public void staleProducerGenerationRefusesAndFailsTheQueryClosed()
            throws Exception {
        // README SMT-1: no stale generation reaches candidate.smt2.  The
        // summary was traced under TEST_DRIVER/test#epoch0 and its own
        // binding names a producer occurrence minted by another source, so
        // composing it would let one node's - or one epoch's - value answer
        // for another's.
        String fatalInstance = "REGION.0@Test#call30";
        String staleProducer = "OTHER_SOURCE/region/REGION.1#1";
        JsonObject stale = protocolBinding("EDGE.STALE", staleProducer,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        RelationSummary producer = summary("STALE", staleProducer, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(stale));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(producer), stale);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonObject refusal = null;
        for (JsonElement element : result.manifest.getAsJsonArray(
                "finalStatusRefusals")) {
            JsonObject row = element.getAsJsonObject();
            if (ConcolicSmtComposer.PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY
                    .equals(row.get("code").getAsString())) {
                refusal = row;
            }
        }
        assertTrue(result.manifest.toString(), refusal != null);
        assertEquals("EDGE.STALE", refusal.get("subject").getAsString());
        assertTrue(refusal.toString(), refusal.get("detail").getAsString()
                .contains(staleProducer));
        // The artifact itself fails closed: the gate lives in the manifest
        // and the query is a separate file a later stage solves on its own.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
        assertTrue(result.manifest.getAsJsonArray("gaps").toString(),
                result.manifest.getAsJsonArray("gaps").toString().contains(
                        ConcolicSmtComposer
                                .PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY));
        // Still reported as the coverage fact it always was.
        assertTrue(result.manifest.toString(), result.manifest
                .getAsJsonArray("coverageGaps").toString().contains(
                        "SOURCE_EPOCH"));
    }

    @Test
    public void pathSetCompleteIsPublishedBesideEveryFinalStatus()
            throws Exception {
        // README GATE-1's acceptance check reads finalStatus and this member
        // together, so it exists on a ready composition, on one whose
        // producer declared an open path set, and on one that never started.
        assertTrue(exactGolden(10, "CLOSED").manifest
                .get(ConcolicSmtComposer.PATH_SET_COMPLETE).getAsBoolean());
        assertFalse(exactGolden(10, "PARTIAL").manifest
                .get(ConcolicSmtComposer.PATH_SET_COMPLETE).getAsBoolean());

        JsonObject fatal = fatalQuery("REGION.0@Test#target",
                targetConstraints());
        fatal.add("coverageGaps", new JsonArray());
        fatal.getAsJsonArray("coverageGaps").add(CoverageDivergence.of(
                CoverageDivergence.Kind.TARGET, "PATH_FLIP_REPLAY_NOT_ADMITTED",
                "QUERY.TEST.FATAL", "one target path was never replayed"));
        ConcolicSmtComposer.Result openTarget = composeFatal(
                "REGION.0@Test#target",
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal, null);
        assertFalse(openTarget.manifest.toString(), openTarget.manifest
                .get(ConcolicSmtComposer.PATH_SET_COMPLETE).getAsBoolean());

        ConcolicSmtComposer.Result absent = composeWithoutFatalQuery();
        assertEquals(absent.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                absent.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertFalse(absent.manifest.toString(), absent.manifest
                .get(ConcolicSmtComposer.PATH_SET_COMPLETE).getAsBoolean());
    }

    @Test
    public void guardedReadOnTheFatalPathRefusesWithNoEdgeBinding()
            throws Exception {
        // README STATE-1: a read consumed directly by the target's own
        // expression has no edge binding, so the binding-row half of the gate
        // never sees it.  Its bounded writer universe still retains the
        // rf_unknown arm, and an accepted witness may not rest on a writer
        // nothing recorded.
        String fatalInstance = "REGION.0@Test#call30";
        JsonArray candidates = new JsonArray();
        candidates.add(RecordedSharedStateFixtures.candidate("rf1", 11L,
                RecordedSharedStateFixtures.constant(1), null, 21L, 12L));
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(21L,
                "M_I_unknownWriter_7_24_r21"));
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        ownWriterVersions(envelope, "REGION.0", fatalInstance,
                "TASK.TARGET");
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        fatalInstance);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24, candidates);
        ownGuardedCandidates(guarded, "REGION.0", "TASK.TARGET");
        SharedStateEvidence.normalizeGuards(guarded);
        JsonArray constraints = new JsonArray();
        constraints.add(binary(guarded, "==", integer(1)));
        JsonObject fatal = fatalQuery(fatalInstance, constraints);
        JsonObject fatalPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        fatalPath.addProperty("sourceTaskId", "TASK.TARGET");
        fatalPath.add(SharedStateEvidence.RECORDED_FIELD,
                        RecordedSharedStateFixtures.recordedMember(envelope,
                                RecordedSharedStateFixtures.twoWriterLedger(),
                                "example.State#value"));

        ConcolicSmtComposer.Result result = composeFatal(fatalInstance,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal, null);

        // No edge was selected.  The target directly consumes the read, so
        // its existential SAT witness must choose one recorded writer.
        assertEquals(result.manifest.toString(), 0, result.manifest
                .getAsJsonArray("resolvedEdgeBindings").size());
        JsonArray refusals = result.manifest.getAsJsonArray(
                "finalStatusRefusals");
        assertEquals(refusals.toString(), 0, refusals.size());
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_sat_witness_known_writer__21__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(not rf_selector__21__rf_unknown)"));
        // The open universe remains explicit for completeness accounting.
        assertFalse(result.manifest.toString(), result.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertFalse(result.smtLib, result.smtLib.contains("(assert false)"));
    }

    @Test
    public void guardedReadUsesTheAuthoritativeVersionGuardWhenCandidateOmitsIt()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        JsonArray candidates = new JsonArray();
        JsonObject first = RecordedSharedStateFixtures.candidate("rf1", 11L,
                RecordedSharedStateFixtures.constant(1), null, 21L, 12L);
        // Runtime guarded-read rows can omit this duplicate while the
        // authoritative version store still records EMPTY_CONJUNCTION.
        first.remove("pathGuard");
        candidates.add(first);
        candidates.add(RecordedSharedStateFixtures.candidate("rf2", 12L,
                RecordedSharedStateFixtures.constant(2),
                RecordedSharedStateFixtures.guard("G"), 21L, 11L));
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(21L,
                "M_I_unknownWriter_7_24_r21"));

        ConcolicSmtComposer.Result result = guardedGolden(fatalInstance,
                "REGION.1@Test#call20", candidates, 1, true);

        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("recorded writer guard rf1 of read 21:null"));
        assertFalse(result.smtLib, result.smtLib.contains(
                ":named recorded_write_guard__21__rf1"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(=> rf_selector__21__rf1 false)"));
    }

    @Test
    public void openReadFromArmIsFiledApartFromAProvenOne() throws Exception {
        // README SMT-1 admits a *known* read-from arm.  A binding whose read
        // kept its rf_unknown arm still constrains the port, so it is an
        // authority; it is not the same authority, and the ledger and its
        // audit have to be able to say which one this run used.
        String fatalInstance = "REGION.0@Test#call30";
        JsonArray candidates = new JsonArray();
        candidates.add(RecordedSharedStateFixtures.candidate("rf1", 11L,
                RecordedSharedStateFixtures.constant(1), null, 21L, 12L));
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(21L,
                "M_I_unknownWriter_7_24_r21"));
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        fatalInstance);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24, candidates);
        ownGuardedCandidates(guarded, "REGION.0", "");
        SharedStateEvidence.normalizeGuards(guarded);
        JsonObject edge = binding("EDGE.ARM", "REGION.1@Test#call20",
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        edge.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        RelationSummary producer = summary("ARM", "REGION.1@Test#call20", 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(edge));
        JsonArray constraints = new JsonArray();
        constraints.add(binary(guarded, "==", integer(1)));
        // A second mention of the consumer port, so the ledger ranges over
        // the occurrence the arm above bound.
        constraints.add(binary(reference("REGION.0.in.0", "I"), ">",
                integer(-1)));
        JsonObject fatal = fatalQuery(fatalInstance, constraints, edge);
        fatal.getAsJsonArray("paths").get(0).getAsJsonObject()
                .add(SharedStateEvidence.RECORDED_FIELD,
                        RecordedSharedStateFixtures.recordedMember(envelope,
                                RecordedSharedStateFixtures.twoWriterLedger(),
                                "example.State#value"));

        ConcolicSmtComposer.Result result = composeFatal(fatalInstance,
                Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal,
                Collections.singletonList(edge));

        JsonArray ledger = result.manifest.getAsJsonArray(
                "selectedInputLedger");
        assertEquals(ledger.toString(), 1, ledger.size());
        JsonObject row = ledger.get(0).getAsJsonObject();
        assertEquals("REGION.0.in.0", row.get("portId").getAsString());
        assertEquals(ConcolicSmtComposer.READ_FROM_ARM_UNKNOWN,
                row.get("authority").getAsString());
        assertEquals(row.toString(),
                ConcolicSmtComposer.READ_FROM_ARM_UNKNOWN,
                row.getAsJsonArray("evidence").get(0).getAsJsonObject()
                        .get("authority").getAsString());
        JsonObject audit = result.manifest.getAsJsonObject(
                "selectedInputLedgerAudit");
        assertEquals(audit.toString(), 1,
                audit.get("unknownArmAuthorities").getAsInt());
        assertEquals(audit.toString(), 0,
                audit.get("missingOccurrences").getAsInt());
        // The exact-provenance golden files the same port under the proven
        // authority, which is what makes the row above a statement about this
        // binding and not about the ledger.
        JsonArray provenLedger = exactGolden(10, "CLOSED", true).manifest
                .getAsJsonArray("selectedInputLedger");
        JsonObject proven = null;
        for (JsonElement element : provenLedger) {
            JsonObject candidate = element.getAsJsonObject();
            if ("REGION.0.in.0".equals(
                    candidate.get("portId").getAsString())) {
                proven = candidate;
            }
        }
        assertTrue(provenLedger.toString(), proven != null);
        assertEquals(ConcolicSmtComposer.READ_FROM_ARM,
                proven.get("authority").getAsString());
    }


    @Test
    public void targetStateReadWithoutAuthorityFailsTheQueryClosed()
            throws Exception {
        // A state read the target performs whose recorded arm no authority
        // admitted, while the container it names is still selected evidence.
        String fatalInstance = "REGION.0@Test#call30";
        JsonObject candidateOnly = binding("EDGE.UNAUTHORIZED",
                "REGION.1@Test#call20", "REGION.1.out.0", fatalInstance,
                "REGION.0.in.0", 20, 30);
        candidateOnly.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        candidateOnly.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);

        ConcolicSmtComposer.Result result = composeFatal(fatalInstance,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                fatalQuery(fatalInstance, targetConstraints(), candidateOnly),
                null);

        assertTrue(result.manifest.toString(), result.manifest
                .getAsJsonArray("gaps").toString().contains(
                        ConcolicSmtComposer
                                .SELECTED_STATE_READ_WITHOUT_AUTHORITY));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void aRecordedExactReadAuthorizesAnExcludedTraceCandidate()
            throws Exception {
        // Same shape as the refusal above, except that the recorded session
        // states what the read DID take: one exact resolution over a writer
        // set the VM reported complete.  That resolution is the read's
        // authority, so the trace candidate it rules out is a decided
        // alternative, reported as coverage rather than refused.
        ConcolicSmtComposer.Result result = composeExcludedTraceCandidate(
                SharedStateEvidence.RESOLUTION_EXACT);

        assertTrue(result.manifest.toString(), !result.manifest
                .getAsJsonArray("gaps").toString().contains(
                        ConcolicSmtComposer
                                .SELECTED_STATE_READ_WITHOUT_AUTHORITY));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.manifest.toString(), result.manifest
                .getAsJsonArray("coverageGaps").toString().contains(
                        RecordedReadFrom.PROVENANCE_EXCLUDED));
        assertTrue(result.smtLib, !result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void aRecordedGuardedReadStillRefusesAnExcludedTraceCandidate()
            throws Exception {
        // The control: with the same read resolved GUARDED rather than
        // exactly, the session states no single version the read took, so the
        // excluded candidate is the missing authority it always was.
        ConcolicSmtComposer.Result result = composeExcludedTraceCandidate(
                SharedStateEvidence.RESOLUTION_GUARDED);

        assertTrue(result.manifest.toString(), result.manifest
                .getAsJsonArray("gaps").toString().contains(
                        ConcolicSmtComposer
                                .SELECTED_STATE_READ_WITHOUT_AUTHORITY));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
    }

    /**
     * One target state read the recorded session resolved with
     * {@code resolution}, and one trace candidate writer that same session
     * excluded.
     */
    private ConcolicSmtComposer.Result composeExcludedTraceCandidate(
            String resolution) throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String field = "example.State#value";
        JsonObject excluded = binding("EDGE.EXCLUDED",
                "REGION.1@Test#call20", "REGION.1.out.0", fatalInstance,
                "REGION.0.in.0", 20, 30);
        excluded.addProperty(RecordedReadFrom.EDGE_FIELD, field);
        excluded.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXCLUDED);
        JsonObject envelope = recordedReadEnvelope(fatalInstance, resolution);
        excluded.addProperty("locationKey",
                SharedStateEvidence.locationKey(envelope));

        JsonObject fatal = fatalQuery(fatalInstance, targetConstraints(),
                excluded);
        JsonObject record = SharedStateEvidence.versionsRecord(
                SharedStateEvidence.locationKey(envelope), envelope,
                RecordedSharedStateFixtures.identity("REGION.0", 1L));
        record.add("carrier",
                RecordedSharedStateFixtures.carrier(field, "I"));
        fatal.getAsJsonArray("paths").get(0).getAsJsonObject().add(
                SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.singletonList(record), null));

        return composeFatal(fatalInstance,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                fatal, null);
    }

    /** One location this reader read once, under {@code resolution}. */
    private static JsonObject recordedReadEnvelope(String readerOccurrence,
                                                   String resolution) {
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConSymbolExp");
        value.addProperty("_java_type", "I");
        value.addProperty("_exp", "0");
        JsonObject version = RecordedSharedStateFixtures.version(41L,
                "REGION.0", "TASK.0", value, null);
        version.addProperty("versionKind", "INITIAL");
        version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                readerOccurrence);
        JsonObject read = RecordedSharedStateFixtures.read(42L, resolution,
                "UNIQUE_VERSION", 41L, 1);
        read.addProperty("regionId", "REGION.0");
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                readerOccurrence);
        JsonArray versions = new JsonArray();
        versions.add(version);
        JsonArray reads = new JsonArray();
        reads.add(read);
        JsonObject envelope = RecordedSharedStateFixtures.versionsEnvelope(
                41L, 24, versions, reads);
        SharedStateEvidence.normalizeGuards(envelope);
        return envelope;
    }

    /** Whether one sweep entry names {@code prefix} about {@code port}. */
    private static boolean containsPrefixed(List<String> entries,
                                            String prefix, String port) {
        for (String entry : entries) {
            if (entry.startsWith(prefix) && entry.contains(port)) return true;
        }
        return false;
    }

    /** The composition of a run whose target query was never published. */
    private ConcolicSmtComposer.Result composeWithoutFatalQuery()
            throws Exception {
        Path directory = temporary.newFolder().toPath();
        Path summaryFile = directory.resolve("summaries.jsonl");
        Files.write(summaryFile, new byte[0]);
        Path regions = directory.resolve("regions.jsonl");
        writeJsonl(regions, region("REGION.0", true, false));
        Path runtimePlan = directory.resolve("runtime_plan.jsonl");
        Files.write(runtimePlan, RuntimePlanArtifact.encode(
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(region("REGION.0", true, false)))
                .getBytes(StandardCharsets.UTF_8));
        return ConcolicSmtComposer.compose(
                ConcolicSmtComposer.Arguments.parse(new String[]{
                        "--fatal-query",
                        directory.resolve("absent.jsonl").toString(),
                        "--summaries", summaryFile.toString(),
                        "--runtime-plan", runtimePlan.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString(),
                        "--fatal-region", "REGION.0",
                        "--occurrence-id", "REGION.0@Test#call30"}));
    }

    @Test
    public void canonicalCoverageKeepsStableCodeAndPerQueryIdentity() {
        JsonObject manifest = new JsonObject();
        JsonArray coverage = new JsonArray();
        String detail = "REGION_TARGET_EVENT_NOT_REACHED: free text";
        coverage.add(CoverageDivergence.of(CoverageDivergence.Kind.TARGET,
                "PATH_FLIP_REPLAY_NOT_ADMITTED", "QUERY.A", detail));
        coverage.add(CoverageDivergence.of(CoverageDivergence.Kind.TARGET,
                "PATH_FLIP_REPLAY_NOT_ADMITTED", "QUERY.B", detail));
        manifest.add("coverageGaps", coverage);
        manifest.add("recordedValueBindings", new JsonArray());
        manifest.add("recordedSessionModel", new JsonObject());

        JsonObject canonical = CanonicalSessionModel.of(manifest,
                new JsonArray(), new JsonArray(),
                "SOURCE/region/target#1");

        JsonArray gaps = canonical.getAsJsonArray("gaps");
        Set<String> subjects = new LinkedHashSet<>();
        int matching = 0;
        for (JsonElement element : gaps) {
            JsonObject gap = element.getAsJsonObject();
            if (!"COVERAGE".equals(gap.get("source").getAsString())) {
                continue;
            }
            matching++;
            assertEquals("PATH_FLIP_REPLAY_NOT_ADMITTED",
                    gap.get("code").getAsString());
            assertEquals(detail, gap.get("detail").getAsString());
            subjects.add(gap.get("subject").getAsString());
        }
        assertEquals(gaps.toString(), 2, matching);
        assertEquals(new LinkedHashSet<>(Arrays.asList("QUERY.A", "QUERY.B")),
                subjects);

        JsonObject summary = CoverageDivergence.summary(
                Arrays.asList(coverage.get(0).getAsJsonObject(),
                        coverage.get(1).getAsJsonObject()), true);
        assertEquals(2, summary.getAsJsonObject("classes")
                .get("TARGET").getAsInt());
        assertEquals(0, summary.get("unclassifiedCount").getAsInt());

        JsonObject unknown = new JsonObject();
        unknown.addProperty("kind", "FUTURE_COVERAGE_GAP");
        JsonObject unclassified = CoverageDivergence.summary(
                Collections.singletonList(unknown), true);
        assertEquals(0, unclassified.get("divergenceCount").getAsInt());
        assertEquals(1, unclassified.get("unclassifiedCount").getAsInt());
        assertEquals(CoverageDivergence.PARTIAL,
                unclassified.get("coverageState").getAsString());
        assertTrue(unclassified.get("retainedPartialRelation")
                .getAsBoolean());
    }

    @Test
    public void canonicalModelRetainsEveryCaseScopedSharedBinding() {
        JsonObject manifest = new JsonObject();
        JsonArray bindings = new JsonArray();
        for (int index = 0; index < 2; index++) {
            JsonObject exact = new JsonObject();
            exact.addProperty("kind", "RECORDED_EXACT_VALUE_BINDING");
            exact.addProperty("edgeId", "EDGE.EXACT.COLLISION");
            exact.addProperty("fromOccurrenceId",
                    "SOURCE/region/producer#1");
            exact.addProperty("toOccurrenceId",
                    "SOURCE/region/target#1");
            exact.addProperty("fromOutputPort", "P.out");
            exact.addProperty("toInputPort", "T.in");
            exact.addProperty("readEventId", 101L + index);
            exact.addProperty("fieldVersionId", 201L + index);
            exact.addProperty("caseGuard", "case_" + index);
            exact.addProperty("valueAssertion", "exact_" + index);
            bindings.add(exact);

            JsonObject guarded = new JsonObject();
            guarded.addProperty("kind",
                    "RECORDED_GUARDED_READ_PORT_BINDING");
            guarded.addProperty("edgeId", "EDGE.GUARDED.COLLISION");
            guarded.addProperty("toOccurrenceId",
                    "SOURCE/region/target#1");
            guarded.addProperty("toInputPort", "T.map");
            guarded.addProperty("readEventId", 301L + index);
            guarded.addProperty("caseGuard", "case_" + index);
            guarded.addProperty("valueAssertion", "guarded_" + index);
            bindings.add(guarded);
        }
        manifest.add("recordedValueBindings", bindings);
        manifest.add("recordedSessionModel", new JsonObject());

        JsonObject canonical = CanonicalSessionModel.of(manifest,
                new JsonArray(), new JsonArray(),
                "SOURCE/region/target#1");
        // Four distinct binding keys, so no case-scoped row collapses into
        // another: two exact edges and two guarded reads survive the census.
        JsonObject counts = canonical.getAsJsonObject("counts");
        assertEquals(canonical.toString(), 2,
                counts.get("exactBindings").getAsInt());
        assertEquals(canonical.toString(), 2,
                counts.get("guardedBindings").getAsInt());
    }






    @Test
    public void targetScopeExcludesTheWorkloadCatalogWhenRelationsAreEmpty() {
        String targetOccurrence = "cluster/dn#epoch1/region/REGION.0#38";
        String producerOccurrence = "cluster/driver#epoch0/region/REGION.1#3";
        JsonObject target = occurrencePlan("REGION.0", targetOccurrence);
        JsonObject producer = occurrencePlan("REGION.1", producerOccurrence);
        JsonObject unrelated = occurrencePlan("REGION.2",
                "cluster/other#epoch0/region/REGION.2#9");

        JsonObject fatal = new JsonObject();
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("occurrenceId", targetOccurrence);
        // The target query may embed session evidence from many occurrences.
        // It is evidence for the target formula, not authority to re-admit an
        // unrelated runtime-plan occurrence into this composition.
        JsonObject embeddedEvidence = new JsonObject();
        embeddedEvidence.add("unrelated", unrelated.deepCopy());
        fatal.add("recordedSharedState", embeddedEvidence);

        List<JsonObject> scoped = ConcolicSmtComposer.targetScopedPlanRows(
                Arrays.asList(unrelated, producer, target), fatal,
                Collections.<JsonObject>emptyList(),
                Collections.<RelationSummary>emptyList());

        List<String> occurrences = new ArrayList<>();
        for (JsonObject row : scoped) {
            occurrences.add(row.get("occurrenceId").getAsString());
        }
        assertEquals(occurrences.toString(), 1, occurrences.size());
        assertTrue(occurrences.contains(targetOccurrence));
    }

    @Test
    public void configuredSourceInSuppliedButUnloweredSummaryIsGlobal()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target";
        String sourceOccurrence = "REGION.1@Test#source";
        String sourceId = "TEST.CONFIGURED.SOURCE";
        String sourcePhase = publishPhase(sourceOccurrence);
        String raw = configuredRaw(sourcePhase, sourceId, "configured");
        RelationSummary source = summary("SOURCE", sourceOccurrence, 7,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject sourceRow = source.toJson();
        JsonObject sourceCase = sourceRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        SymbolicSourceEvidence.writeTo(sourceCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, sourceOccurrence,
                        "<Test: int source>", reference(raw, "I"), 1, false, null)));

        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference(raw, "I"), "==", integer(7)));
        ConcolicSmtComposer.Result result = composeFatal(fatalOccurrence,
                Collections.singletonList(RelationSummary.decode(sourceRow)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                fatalQuery(fatalOccurrence, constraints), null);

        assertEquals(result.smtLib, 1, occurrences(result.smtLib,
                "(declare-const source__"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(declare-const sym__fatal_"));
        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 1, roots.size());
        JsonObject root = roots.get(0).getAsJsonObject();
        assertEquals("TEST_DRIVER/test#epoch0",
                root.get("sourceKey").getAsString());
        assertEquals(sourceId,
                root.get("sourceId").getAsString());
        assertEquals(sourcePhase,
                root.get("sourcePhaseId").getAsString());
        assertEquals(sourceOccurrence,
                root.get("sourceOccurrenceId").getAsString());
        assertEquals("<Test: int source>",
                root.get("fieldSignature").getAsString());
        assertEquals("I", root.get("javaTypeDescriptor").getAsString());
        assertEquals("INT", root.get("sort").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + root.get("solverTerm").getAsString()
                        + " Int)"));
        String sourceTerm = root.get("solverTerm").getAsString();
        String javaIntDomain = "(and (<= (- 2147483648) " + sourceTerm
                + ") (<= " + sourceTerm + " 2147483647))";
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assert (! " + javaIntDomain
                        + " :named java_integral_domain_"));
        JsonObject fatalAssertion = result.manifest.getAsJsonObject(
                "fatalPathAssertion");
        assertEquals("fatal_path", fatalAssertion.get("name").getAsString());
        assertFalse(fatalAssertion.get("solverTerm").getAsString().isEmpty());
        assertFalse(result.manifest.has("operandBindingLedger"));
    }

    @Test
    public void configuredSourceMintedInA1IsGlobalInA2Guard()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#target-activation-source";
        String plannedOccurrence =
                "REGION.1@Test#planned-activation-source";
        String sourceId = "TEST.CONFIGURED.ACTIVATION_SOURCE";
        String sourcePhase = publishPhase(plannedOccurrence);
        String raw = configuredRaw(sourcePhase, sourceId, "activation");
        JsonObject firstHop = protocolBinding(
                "EDGE.ACTIVATION.SOURCE", plannedOccurrence,
                "REGION.1.out.0", targetOccurrence, "REGION.0.in.0");

        JsonObject row = summary("ACTIVATION.SOURCE", plannedOccurrence, 1,
                Collections.<String>emptyList(),
                Collections.singletonList(firstHop)).toJson();
        JsonArray cases = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        JsonObject a1 = cases.get(0).getAsJsonObject();
        a1.addProperty("caseId", "CASE.ACTIVATION.SOURCE.A1");
        a1.addProperty("occurrenceId", plannedOccurrence + "#a1");
        a1.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        a1.addProperty(PathObservation.PLANNED_OCCURRENCE_ID,
                plannedOccurrence);
        a1.getAsJsonObject("guard").getAsJsonArray("conditions").add(
                binary(reference(raw, "I"), ">=", integer(0)));
        SymbolicSourceEvidence.writeTo(a1,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, plannedOccurrence,
                        "<Test: int source>", reference(raw, "I"),
                        1, false, null)));

        JsonObject a2 = a1.deepCopy();
        a2.addProperty("caseId", "CASE.ACTIVATION.SOURCE.A2");
        a2.addProperty("sourceTaskId", "TASK.ACTIVATION.SOURCE.A2");
        a2.addProperty("occurrenceId", plannedOccurrence + "#a2");
        a2.addProperty(PathObservation.ACTIVATION_ORDINAL, 2);
        a2.remove(SymbolicSourceEvidence.FIELD);
        JsonArray a2Conditions = new JsonArray();
        a2Conditions.add(binary(reference(raw, "I"), "<=", integer(10)));
        a2.getAsJsonObject("guard").add("conditions", a2Conditions);
        assertFalse(a2.has("symbolicInputs"));
        assertFalse(a2.has(SymbolicSourceEvidence.FIELD));
        cases.add(a2);

        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference(raw, "I"), "==", integer(5)));
        ConcolicSmtComposer.Result result = compose(targetOccurrence,
                Collections.singletonList(RelationSummary.decode(row)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), constraints,
                firstHop);

        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 1, roots.size());
        String sourceTerm = roots.get(0).getAsJsonObject()
                .get("solverTerm").getAsString();
        assertEquals(result.smtLib, 1, occurrences(result.smtLib,
                "(declare-const " + sourceTerm + " Int)"));

        String a1Selector = RecordedSessionModel.caseSelector(
                RecordedSessionModel.caseOwner("REGION.1",
                        plannedOccurrence + "#a1",
                        "CASE.ACTIVATION.SOURCE.A1", 0));
        String a2Selector = RecordedSessionModel.caseSelector(
                RecordedSessionModel.caseOwner("REGION.1",
                        plannedOccurrence + "#a2",
                        "CASE.ACTIVATION.SOURCE.A2", 1));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> " + a1Selector + " (>= " + sourceTerm + " 0))"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> " + a2Selector + " (<= " + sourceTerm + " 10))"));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void repeatedMapUpdatesConsumeThePreviousSemanticOccurrence()
            throws Exception {
        String target = "TEST_DRIVER/test#epoch0/region/REGION.0#target";
        String planned = "TEST_DRIVER/test#epoch0/region/REGION.1#1";
        String output = "REGION.1.out.0";
        JsonObject edge = protocolBinding("EDGE.MAP.TIMELINE", planned,
                output, target, "REGION.0.in.0");

        JsonObject a1State = assocPut(assocStateSymbol(
                "M_L'java/util/HashMap'_59"), 1, 101);
        JsonObject row = summary("MAP.TIMELINE", planned, a1State,
                Collections.<String>emptyList(),
                Collections.singletonList(edge), "java.util.Map").toJson();
        JsonArray encoded = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        JsonObject a1 = encoded.get(0).getAsJsonObject();
        decorateMapOccurrence(a1, planned, 1, a1State);

        JsonObject a2State = assocPut(a1State, 2, 102);
        JsonObject a2 = a1.deepCopy();
        a2.getAsJsonObject("outputExpressions").add(output, a2State);
        decorateMapOccurrence(a2, planned, 2, a2State);

        JsonObject a3State = assocPut(a2State, 3, 103);
        JsonObject a3 = a1.deepCopy();
        a3.getAsJsonObject("outputExpressions").add(output, a3State);
        decorateMapOccurrence(a3, planned, 3, a3State);

        // Deliberately not activation order: the composer must use the
        // authoritative ordinal, not merge-array position.
        encoded.remove(0);
        encoded.add(a2);
        encoded.add(a1);
        encoded.add(a3);

        JsonArray constraints = new JsonArray();
        constraints.add(binary(mapGet(assocStateSymbol(
                "REGION.0.in.0"), 99), "==", nullRef()));
        ConcolicSmtComposer.Result result = compose(target,
                Collections.singletonList(RelationSummary.decode(row)),
                Arrays.asList(region("REGION.0", "java.util.Map", ""),
                        region("REGION.1", "", "java.util.Map")),
                constraints, edge);

        JsonArray predecessors = result.manifest
                .getAsJsonArray("occurrenceMapPredecessors");
        assertEquals(result.manifest.toString(), 2, predecessors.size());
        String a1Port = predecessors.get(0).getAsJsonObject()
                .get("fromPortTerm").getAsString();
        String a2Port = predecessors.get(1).getAsJsonObject()
                .get("fromPortTerm").getAsString();
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assoc_put " + a1Port + " "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assoc_put " + a2Port + " "));
        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("OccurrenceMap"));
    }

    @Test
    public void vmUnsignedShiftSpellingReachesFinalComposition()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target-vm-ushr";
        String sourceOccurrence = "REGION.1@Test#source-vm-ushr";
        String sourceId = "TEST.CONFIGURED.VM_USHR";
        String sourcePhase = publishPhase(sourceOccurrence);
        String raw = configuredRaw(sourcePhase, sourceId, "vm_ushr");
        RelationSummary source = summary("SOURCE.VM_USHR",
                sourceOccurrence, 7, Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject sourceRow = source.toJson();
        JsonObject sourceCase = sourceRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        SymbolicSourceEvidence.writeTo(sourceCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, sourceOccurrence,
                        "<Test: int source>", reference(raw, "I"),
                        1, false, null)));

        JsonObject vmUnsignedShift = binary(reference(raw, "I"), ">>u",
                integer(28));
        JsonArray constraints = new JsonArray();
        constraints.add(binary(vmUnsignedShift, "==", integer(15)));
        ConcolicSmtComposer.Result result = composeFatal(fatalOccurrence,
                Collections.singletonList(RelationSummary.decode(sourceRow)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                fatalQuery(fatalOccurrence, constraints), null);

        assertTrue(result.smtLib, result.smtLib.contains("4294967296"));
        assertTrue(result.smtLib, result.smtLib.contains("268435456"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    /**
     * HDFS-11741's shape: the declared read found a root the VM had already
     * propagated onto the field, so it NAMED it instead of minting.  The
     * named root keeps the SMT name and the guard its own mint gave it - it
     * is not re-minted - and the composition still publishes the writable
     * program field behind it.
     */
    @Test
    public void aNamedPropagatedRootStillMaterializesItsProgramField()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target";
        String sourceOccurrence = "REGION.1@Test#source";
        String sourceId = "TEST.CONFIGURED.SOURCE";
        String sourcePhase = publishPhase(sourceOccurrence);
        // Minted somewhere else entirely: no label of this phase is in it.
        String propagated = "M_I_22_field32";
        RelationSummary source = summary("SOURCE", sourceOccurrence,
                reference(propagated, "I"),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject sourceRow = source.toJson();
        JsonObject sourceCase = sourceRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        SymbolicSourceEvidence.writeTo(sourceCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, sourceOccurrence,
                        "<Test: int source>", reference(propagated, "I"), 1,
                        true, null)));

        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference(propagated, "I"), "==", integer(7)));
        ConcolicSmtComposer.Result result = composeFatal(fatalOccurrence,
                Collections.singletonList(RelationSummary.decode(sourceRow)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                fatalQuery(fatalOccurrence, constraints), null);

        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("ConfiguredSourceMaterializationConflict"));
        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 1, roots.size());
        JsonObject root = roots.get(0).getAsJsonObject();
        assertEquals(sourceId, root.get("sourceId").getAsString());
        assertEquals(sourceOccurrence,
                root.get("sourceOccurrenceId").getAsString());
        assertEquals("<Test: int source>",
                root.get("fieldSignature").getAsString());
        assertEquals("I", root.get("javaTypeDescriptor").getAsString());
        String sourceTerm = root.get("solverTerm").getAsString();
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + sourceTerm + " Int)"));
        // Naming, never re-minting: the term is the one the propagated
        // symbol already had, not a fresh configured-source root.
        assertFalse(sourceTerm, sourceTerm.startsWith("source__"));
        assertEquals(result.smtLib, 0, occurrences(result.smtLib,
                "(declare-const source__"));
        assertEquals(result.smtLib, 1, occurrences(result.smtLib,
                "(declare-const " + sourceTerm + " Int)"));
    }

    @Test
    public void aReusedBareRootAliasesItsUniqueImportedMint()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target-alias";
        String sourceOccurrence = "REGION.1@Test#source-alias";
        String sourceId = "TEST.CONFIGURED.SOURCE.ALIAS";
        String sourcePhase = publishPhase(sourceOccurrence);
        String minted = configuredRaw(sourcePhase, sourceId, "minted");
        String propagated = "M_I_43_field32";

        RelationSummary source = summary("SOURCE.ALIAS", sourceOccurrence,
                7, Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject sourceRow = source.toJson();
        JsonObject sourceCase = sourceRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        SymbolicSourceEvidence.writeTo(sourceCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, sourceOccurrence,
                        "<Test: int source>", reference(minted, "I"),
                        1, false, null)));

        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference(minted, "I"), "==",
                reference(propagated, "I")));
        constraints.add(binary(reference(propagated, "I"), "==",
                integer(7)));
        JsonObject fatal = fatalQuery(fatalOccurrence, constraints);
        // The second raw spelling is a read of the same configured source
        // entry, not a second mint.  Its semantic identity exactly matches
        // the imported non-reused event above.
        SymbolicSourceEvidence.writeTo(fatal,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, sourceOccurrence,
                        "<Test: int source>", reference(propagated, "I"),
                        1, true, null)));

        ConcolicSmtComposer.Result result = composeFatal(fatalOccurrence,
                Collections.singletonList(RelationSummary.decode(sourceRow)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal, null);

        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("ConfiguredSourceMaterializationConflict"));
        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 1, roots.size());
        String solverTerm = roots.get(0).getAsJsonObject()
                .get("solverTerm").getAsString();
        assertEquals(result.smtLib, 1, occurrences(result.smtLib,
                "(declare-const " + solverTerm + " Int)"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "sym__fatal_" + propagated));
    }

    @Test
    public void oneRawCannotMintAndNameDifferentConfiguredSources()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target-source-conflict";
        String sourceOccurrence = "REGION.1@Test#source-conflict";
        String sourcePhase = publishPhase(sourceOccurrence);
        String raw = configuredRaw(sourcePhase, "TEST.SOURCE.A", "raw");
        RelationSummary source = summary("SOURCE.CONFLICT",
                sourceOccurrence, reference(raw, "I"),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject sourceRow = source.toJson();
        JsonObject sourceCase = sourceRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        SymbolicSourceEvidence.writeTo(sourceCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, "TEST.SOURCE.A", sourceOccurrence,
                        "<Test: int source>", reference(raw, "I"),
                        1, false, null)));

        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference(raw, "I"), "==", integer(7)));
        JsonObject fatal = fatalQuery(fatalOccurrence, constraints);
        SymbolicSourceEvidence.writeTo(fatal,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        publishPhase(fatalOccurrence), "TEST.SOURCE.B",
                        fatalOccurrence, "<Test: int other>",
                        reference(raw, "I"), 1, true, null)));
        ConcolicSmtComposer.Result result = composeFatal(fatalOccurrence,
                Collections.singletonList(RelationSummary.decode(sourceRow)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal, null);

        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains("SymbolicSourceEvidenceMalformed"));
    }

    @Test
    public void missingCaseLocalTargetEventIsRejectedByCanonicalSchema()
            throws Exception {
        String occurrence = "REGION.0@Test#target";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        fatal.getAsJsonArray("paths").get(0).getAsJsonObject()
                .remove(PathObservation.TargetReachEvent.FIELD);

        try {
            composeFatal(occurrence,
                    Collections.<RelationSummary>emptyList(),
                    Arrays.asList(region("REGION.0", true, false)),
                    fatal, null);
            fail("a target path without its event must be malformed");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "attestation authority"));
        }
    }

    @Test
    public void legacyTargetQueryWithoutPathLocalWitnessIsRejected()
            throws Exception {
        String occurrence = "REGION.0@Test#legacy-target-query";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        fatal.addProperty("schemaVersion", 1);
        fatal.getAsJsonArray("paths").get(0).getAsJsonObject().remove(
                TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS);

        try {
            composeFatal(occurrence,
                    Collections.<RelationSummary>emptyList(),
                    Arrays.asList(region("REGION.0", true, false)),
                    fatal, null);
            fail("legacy query must not borrow the seed branch predicate");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "Unsupported canonical fatal query schema"));
        }
    }

    @Test
    public void directlyWitnessedRequiredTargetOutcomeIsAdmitted()
            throws Exception {
        String occurrence = "REGION.0@Test#target";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        JsonObject path = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        markRequiredTargetPath(path);
        fatal.getAsJsonObject("seedReplayContract")
                .add("source", path.getAsJsonObject(
                        TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS)
                        .deepCopy());

        ConcolicSmtComposer.Result result = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal, null);

        assertEquals(ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonObject attestation = result.manifest.getAsJsonArray(
                "targetReachLedger").get(0).getAsJsonObject();
        assertEquals(TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT,
                attestation.get("attestationRole").getAsString());
        assertFalse(attestation.get("outcome").getAsBoolean());
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void exactConcreteRequiredTargetNeedsNoPredicateOrFreeSymbol()
            throws Exception {
        String occurrence = "REGION.0@Test#concrete-target";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        JsonObject concrete = ExactConcreteBranchObservation.attested(
                "<Test: void consume()>#u1", "<Test: void consume()>",
                1, 1, false).toJson();
        fatal.remove("seedReplayContract");
        fatal.add(TargetReachPathQueryBuilder.TARGET_CONCRETE_OBSERVATION,
                concrete.deepCopy());
        JsonObject path = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        path.add("constraints", new JsonArray());
        path.remove(TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS);
        path.add(TargetReachPathQueryBuilder.TARGET_CONCRETE_OBSERVATION,
                concrete.deepCopy());
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder
                        .REQUIRED_CONCRETE_BRANCH_AUTHORITY);
        path.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);

        ConcolicSmtComposer.Result result = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal, null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertEquals(1, result.manifest.getAsJsonArray(
                "targetReachLedger").size());
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));

        path.getAsJsonObject(TargetReachPathQueryBuilder
                .TARGET_CONCRETE_OBSERVATION)
                .addProperty("sourceTakenOutcome", true);
        ConcolicSmtComposer.Result refused = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal, null);
        assertEquals(refused.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                refused.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(refused.manifest.toString(), refused.manifest.toString()
                .contains("SelectedConcreteTargetReachEventMismatch"));
    }

    @Test
    public void identicalTargetPredicatesRemainAlternativeCausalCases()
            throws Exception {
        String occurrence = "REGION.0@Test#target-alternatives";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        JsonObject first = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        first.addProperty("caseId", "TARGET.CASE.A");
        first.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        JsonObject second = first.deepCopy();
        second.addProperty("caseId", "TARGET.CASE.B");
        second.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        fatal.getAsJsonArray("paths").add(second);

        ConcolicSmtComposer.Result result = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal,
                null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named target_path_selector_partition"));
        String firstSelector = RecordedSessionModel.caseSelector(
                RecordedSessionModel.caseOwner("REGION.0", occurrence,
                        "TARGET.CASE.A", 0));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assert (! (=> " + firstSelector + " "));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert (! (= " + firstSelector + " "));
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
        }
    }

    @Test
    public void identicalProducerGuardsRemainAlternativeCausalCases()
            throws Exception {
        String target = "REGION.0@Test#producer-alternatives";
        String producer = "REGION.1@Test#producer-alternatives";
        JsonObject firstHop = protocolBinding("EDGE.PRODUCER.ALTERNATIVES",
                producer, "REGION.1.out.0", target, "REGION.0.in.0");
        JsonObject row = summary("PRODUCER.ALTERNATIVE.A", producer, 1,
                Collections.<String>emptyList(),
                Collections.singletonList(firstHop)).toJson();
        JsonArray cases = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        JsonObject second = cases.get(0).getAsJsonObject().deepCopy();
        second.addProperty("caseId", "CASE.PRODUCER.ALTERNATIVE.B");
        second.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        second.addProperty("sourceTaskId", "TASK.PRODUCER.ALTERNATIVE.B");
        second.getAsJsonObject("outputExpressions")
                .add("REGION.1.out.0", integer(2));
        cases.add(second);

        ConcolicSmtComposer.Result result = compose(target,
                Collections.singletonList(RelationSummary.decode(row)),
                firstHop);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        String firstSelector = RecordedSessionModel.caseSelector(
                RecordedSessionModel.caseOwner("REGION.1", producer,
                        "CASE.PRODUCER.ALTERNATIVE.A", 0));
        String secondSelector = RecordedSessionModel.caseSelector(
                RecordedSessionModel.caseOwner("REGION.1", producer,
                        "CASE.PRODUCER.ALTERNATIVE.B", 1));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assert (! (=> " + firstSelector + " "));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert (! (= " + firstSelector + " "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(= (+ (ite " + firstSelector + " 1 0) (ite "
                        + secondSelector + " 1 0)) 1)"));
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
        }
    }

    @Test
    public void fatalAbsenceDemandRetainsItsTargetCausalCase() {
        assertEquals("(and selected_case local_path)",
                ConcolicSmtComposer.selectedCasePathTerm(
                        "selected_case", "local_path"));
    }

    @Test
    public void targetPredicateMustEqualTheReplayRequiredPredicate()
            throws Exception {
        String occurrence = "REGION.0@Test#predicate-mismatch";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        JsonObject path = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        JsonArray mismatched = new JsonArray();
        mismatched.add(binary(reference("M_I_field_OTHER_GATE", "I"),
                ">", integer(0)));
        path.add("constraints", mismatched);

        ConcolicSmtComposer.Result result = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal,
                null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains("SelectedTargetPredicateMismatch:path:0"));
    }

    @Test
    public void targetPredicateMayUseTheSameBranchWithAReboundRpcExpression()
            throws Exception {
        String occurrence = "REGION.0@Test#rpc-rebound-predicate";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        JsonObject path = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();

        JsonObject reboundSource = binary(
                reference("M_I_field_REBOUND_RPC_VALUE", "I"),
                "<=", integer(7));
        JsonArray reboundConstraints = new JsonArray();
        reboundConstraints.add(BranchPredicateAlgebra.complement(
                reboundSource));
        path.add("constraints", reboundConstraints);

        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness reboundWitness = BranchWitness.vmPc(
                "<Test: void consume()>#u1", "<Test: void consume()>",
                1, 1, true, reboundSource, 0, metadata);
        path.add(TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS,
                reboundWitness.toJson());

        ConcolicSmtComposer.Result result = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal,
                null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void recordedSharedStateBecomesOneOrderDomainAndAReadCut()
            throws Exception {
        // Recorded writes, reads and ledger events reach the formula as one
        // order domain, rather than as one integer domain per channel.
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject outerToFatal = binding("EDGE.SHARED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        outerToFatal.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        outerToFatal.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        outerToFatal.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        RelationSummary outer = withRecordedSharedState(
                summary("OUTER", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(outerToFatal)));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(outer), outerToFatal);

        assertEquals(1, result.manifest.getAsJsonArray(
                "targetReachLedger").size());
        JsonObject targetAttestation = result.manifest.getAsJsonArray(
                "targetReachLedger").get(0).getAsJsonObject();
        assertTrue(targetAttestation.get("outcome").getAsBoolean());
        assertTrue(targetAttestation.get(
                "sourceObservedOutcome").getAsBoolean());
        assertFalse(targetAttestation.get(
                "desiredTakenOutcome").getAsBoolean());
        assertEquals("SOURCE_TARGET_REACH_EVENT",
                targetAttestation.get("attestationRole").getAsString());
        assertTrue(targetAttestation.get("caseGuard").getAsString(),
                targetAttestation.get("caseGuard").getAsString()
                        .startsWith("case_selector__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named target_reach_event"));
        // One position per recorded event, in one domain.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const event_position__11 Int)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const event_position__12 Int)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const event_position__21 Int)"));
        // Two writes related by a recorded cross-thread order stay ordered in
        // the projected slice.
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_order__11__12"));
        // The guarded read becomes an exactly-one choice plus a sparse cut.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const rf_selector__21__rf1 Bool)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const rf_selector__21__rf_unknown Bool)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_cut__21__11"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_cut_outside__21__11__12"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_choice__21"));
        // The same selectors decide the value and the writer's path guard,
        // so the choice is one family rather than an order model beside a
        // value model.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> rf_selector__21__rf1 (= rf_value__21"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_value__21__rf_unknown"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> rf_selector__21__rf2 (> "));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_write_guard__21__rf2"));
        // Exactly-one selection plus the per-arm implications above already
        // defines the read value.  Do not duplicate every (potentially large)
        // writer expression in a second nested ite chain.
        assertFalse(result.smtLib, result.smtLib.contains(
                ":named recorded_read_term__21"));

        // Every value binding points back to the evidence it came from, in
        // members a reader can check rather than in prose.
        JsonArray bindings = result.manifest.getAsJsonArray(
                "recordedValueBindings");
        assertEquals(bindings.toString(), 4, bindings.size());
        JsonObject firstArm = bindings.get(0).getAsJsonObject();
        assertEquals("rf_selector__21__rf1",
                firstArm.get("selector").getAsString());
        assertEquals(21L, firstArm.get("readEventId").getAsLong());
        assertEquals(11L, firstArm.get("fieldVersionId").getAsLong());
        assertEquals("INSTANCE_FIELD/7#24",
                firstArm.get("locationKey").getAsString());
        assertEquals("recorded_read_value__21__rf1",
                firstArm.get("valueAssertion").getAsString());
        assertTrue(firstArm.toString(),
                firstArm.get("writerExists").getAsBoolean());
        assertEquals("recorded_write_guard__21__rf2",
                bindings.get(1).getAsJsonObject()
                        .get("writerGuardAssertion").getAsString());
        assertFalse(bindings.get(2).toString(), bindings.get(2)
                .getAsJsonObject().get("writerExists").getAsBoolean());
        // An unknown arm makes the model an under-approximation, and the
        // closure member says that as the fact it is.
        assertFalse(result.manifest.toString(), result.manifest
                .get("recordedModelComplete").getAsBoolean());

        JsonObject recorded = result.manifest.getAsJsonObject(
                "recordedSessionModel");
        assertTrue(recorded.toString(),
                recorded.get("partial").getAsBoolean());
        assertEquals(RecordedSessionModel.KIND,
                recorded.get("kind").getAsString());
        assertEquals(3, recorded.get("orderedEvents").getAsInt());
        assertEquals(1, recorded.get("orderConstraints").getAsInt());
        assertEquals(1, recorded.get("guardedReads").getAsInt());
        assertTrue(recorded.getAsJsonObject("targetSlice")
                .get("reachesTarget").getAsBoolean());
        // Coverage findings never disable the downstream reach stage.
        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        // The selected edge itself still claims unknown-writer authority, so
        // that edge is not a final witness even though the formula excludes
        // the unknown arm from its existential recorded-writer query.
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(
                        ConcolicSmtComposer.FINAL_STATUS).getAsString());
        // Only the selected edge binding is refused; the formula-level read
        // is now restricted to its two recorded writers.
        Set<String> readFromSubjects = new LinkedHashSet<>();
        for (JsonElement element : result.manifest.getAsJsonArray(
                "finalStatusRefusals")) {
            JsonObject row = element.getAsJsonObject();
            if (ConcolicSmtComposer.SELECTED_READ_FROM_UNKNOWN_ARM.equals(
                    row.get("code").getAsString())) {
                readFromSubjects.add(row.get("subject").getAsString());
            }
        }
        assertEquals(result.manifest.toString(), 1, readFromSubjects.size());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(not rf_selector__21__rf_unknown)"));

        // Which arms replay could enforce is decided before the solve.
        JsonObject plan = recorded.getAsJsonArray("readCutGates").get(0)
                .getAsJsonObject();
        assertEquals(SparseReadCutGate.KIND, plan.get("kind").getAsString());
        assertTrue(plan.get("enforceable").getAsBoolean());
        assertEquals(2, plan.getAsJsonArray("gates").size());
        assertEquals(SparseReadCutGate.UNKNOWN_WRITER_SELECTED,
                plan.getAsJsonArray("refusals").get(0).getAsJsonObject()
                        .get("reason").getAsString());
        JsonObject choice = recorded.getAsJsonArray("readChoices").get(0)
                .getAsJsonObject();
        assertTrue(choice.getAsJsonArray("candidates").get(0)
                .getAsJsonObject().get("enforceable").getAsBoolean());
        assertFalse(choice.getAsJsonArray("candidates").get(2)
                .getAsJsonObject().get("enforceable").getAsBoolean());

        // The formula is emitted, and it says how complete it is.
        JsonObject divergence = result.manifest.getAsJsonObject(
                "divergence");
        assertEquals("PARTIAL",
                divergence.get("coverageState").getAsString());
        assertTrue(divergence.get("targetRelationUsable").getAsBoolean());
        assertTrue(divergence.get("retainedPartialRelation").getAsBoolean());
        assertEquals(1, divergence.getAsJsonObject("classes")
                .get("GATE").getAsInt());
    }

    @Test
    public void anAbsentRecordedSessionIsReportedNotAssumed()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject outerToFatal = binding("EDGE.SHARED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        RelationSummary outer = summary("OUTER", outerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(outerToFatal));

        JsonArray concreteTarget = new JsonArray();
        concreteTarget.add(binary(integer(1), ">", integer(0)));
        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(outer),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), concreteTarget,
                outerToFatal);

        JsonObject recorded = result.manifest.getAsJsonObject(
                "recordedSessionModel");
        assertEquals(0, recorded.get("orderedEvents").getAsInt());
        assertFalse(recorded.getAsJsonObject("targetSlice")
                .get("reachesTarget").getAsBoolean());
        // The absence is a named coverage finding, not a silent empty model.
        assertEquals(1,
                result.manifest.getAsJsonArray("coverageGaps").size());
        assertEquals(SessionTargetSlice.NO_RECORDED_TARGET_REFERENCE,
                result.manifest.getAsJsonArray("coverageGaps").get(0)
                        .getAsJsonObject().get("reason").getAsString());
        assertEquals("CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("UnresolvedRecordedEdgeBinding:EDGE.SHARED"));
        assertFalse(result.smtLib,
                result.smtLib.contains("event_position__"));

        // Folded from aCrossChannelOrderCycleIsRefusedBeforeSolving: a ledger
        // whose delivered relation closes a cycle through a field read-from,
        // program order and two value-handoff edges is one relation and one
        // cycle, not four channels that happen to disagree.  It is refused
        // before the solve rather than reasoned over.
        JsonObject cyclicToFatal = outerToFatal.deepCopy();
        cyclicToFatal.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        RelationSummary cyclic = withRecordedSharedState(
                summary("CYCLE", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(cyclicToFatal)),
                crossChannelCycleLedger());

        ConcolicSmtComposer.Result refused = compose(fatalInstance,
                Collections.singletonList(cyclic), cyclicToFatal);

        JsonObject cyclicModel = refused.manifest.getAsJsonObject(
                "recordedSessionModel");
        assertTrue(cyclicModel.toString(), cyclicModel
                .get("orderDomainFault").getAsString().contains("cycle"));
        assertEquals(0, cyclicModel.get("orderedEvents").getAsInt());
        assertEquals("CANDIDATE_WITH_GAPS",
                refused.manifest.get("state").getAsString());
        assertTrue(refused.manifest.toString(), refused.manifest.toString()
                .contains("RecordedOrderDomainCycle"));
        assertTrue(refused.manifest.toString(), refused.manifest.toString()
                .contains(RecordedSessionModel.ORDER_DOMAIN_CYCLE));
        assertTrue(refused.smtLib, refused.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void vmHandoffBindsTheExactConsumerCaseExpression()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.VMH", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        RelationSummary consumer = summary("VMH", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(firstHop));
        JsonObject row = consumer.toJson();
        JsonObject path = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        JsonArray handoffs = new JsonArray();
        handoffs.add(VmHandoffEvidence.event("REGION.1.in.0", 41L, 42L,
                reference("producer_guard_x", "I"), "TASK.VMHP",
                producerInstance));
        path.add(VmHandoffEvidence.FIELD, handoffs);

        // This producer is deliberately not in the ordinary lowered edge
        // closure.  Its exact task/case can only be recovered from the v3
        // RPC-header provenance carried beside the VM handle.
        RelationSummary producer = summary("VMHP", producerInstance, 10,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject producerRow = producer.toJson();
        JsonObject producerPath = producerRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases")
                .get(0).getAsJsonObject();
        producerPath.getAsJsonObject("guard")
                .getAsJsonArray("conditions").add(binary(
                        reference("producer_guard_x", "I"), ">",
                        integer(0)));
        JsonObject interaction = new JsonObject();
        interaction.addProperty("outputSiteId", "COMMUNICATION_EFFECT:test");
        interaction.addProperty("outputOccurrence", 1);
        interaction.addProperty("outputVersionOrdinal", 1);
        interaction.addProperty("replayOccurrence", 1);
        interaction.addProperty("interactionKind", "COMMUNICATION_EFFECT");
        interaction.addProperty("authority",
                "INSTRUMENTED_INTERACTION_SITE_V1");
        interaction.addProperty("portId", "REGION.1.in.0");
        interaction.addProperty("exportEventId", 41L);
        JsonArray interactions = new JsonArray();
        interactions.add(interaction);
        producerPath.add(RelationSummary.INTERACTION_EVENTS, interactions);
        producer = RelationSummary.decode(producerRow);

        JsonArray ledgerEvents = new JsonArray();
        ledgerEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.sender"));
        ledgerEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.1"));
        JsonArray ledgerOrder = new JsonArray();
        ledgerOrder.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        JsonObject ledger = RecordedSharedStateFixtures.ledgerEnvelope(
                ledgerEvents, ledgerOrder);
        path.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(ledger,
                                RecordedSharedStateFixtures.identity(
                                        "REGION.1", 1L))));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(RelationSummary.decode(row), producer),
                firstHop);

        String owner = RecordedSessionModel.caseOwner("REGION.1",
                consumerInstance, "CASE.VMH", 0);
        String selector = RecordedSessionModel.caseSelector(owner);
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> " + selector + " (= port__REGION_1_in_0__instance__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_order__41__42"));
        // Wave 3 A.  The handoff no longer restates the producer's path
        // conditions - its relation summary lowers those once - but it does
        // restate the lineage the row itself carries: this receive happened,
        // so the case the stated (task, occurrence) ran is selected.  The
        // producer case is looked up by that pair, never searched for.
        String producerOwner = RecordedSessionModel.caseOwner("REGION.1",
                producerInstance, "CASE.VMHP", 0);
        String producerSelector = RecordedSessionModel.caseSelector(
                producerOwner);
        String producerGuardLine = "";
        for (String line : result.smtLib.split("\\R")) {
            if (line.contains(":named vm_handoff_producer_guard_")) {
                producerGuardLine = line;
                break;
            }
        }
        assertFalse(result.smtLib, producerGuardLine.isEmpty());
        assertTrue(producerGuardLine, producerGuardLine.contains(
                "(=> " + selector + " " + producerSelector + ")"));
        if (z3Available()) {
            assertEquals("unsat", z3(assuming(result.smtLib, selector,
                    "(not " + producerSelector + ")")));
        }
        JsonArray bindings = result.manifest.getAsJsonArray(
                "recordedValueBindings");
        JsonObject vmBinding = null;
        for (JsonElement element : bindings) {
            JsonObject candidate = element.getAsJsonObject();
            if (VmHandoffEvidence.BINDING_KIND.equals(
                    candidate.get("kind").getAsString())) {
                vmBinding = candidate;
                break;
            }
        }
        assertTrue(bindings.toString(), vmBinding != null);
        assertTrue(vmBinding.get("valueAssertion").getAsString()
                .startsWith("bind_REGION_1_in_0"));
        assertEquals("recorded_order__41__42",
                vmBinding.get("orderAssertion").getAsString());
        assertEquals("TASK.VMHP", vmBinding
                .get(VmHandoffEvidence.PRODUCER_TASK_ID).getAsString());
        assertEquals(producerInstance, vmBinding
                .get(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID).getAsString());
        assertEquals(41L, vmBinding.get("localExportEventId").getAsLong());
        // The two producer strings stay on the ledger row as the path
        // provenance README RPC-1 asks the manifest to carry; the ledger also
        // names the cases the link was stated over.  No restated guard.
        assertFalse(vmBinding.toString(),
                vmBinding.has("producerGuardAssertion"));
        assertEquals(vmBinding.toString(), producerSelector,
                vmBinding.getAsJsonArray("producerCaseSelectors").get(0)
                        .getAsString());
        assertFalse(result.smtLib, result.smtLib.contains(
                "VM_HANDOFF_SOURCE_EQUALITY"));

        JsonObject canonical = result.manifest.getAsJsonObject(
                CanonicalSessionModel.MANIFEST_FIELD);
        // The handoff names both of its activations, so the census raises
        // no endpoint gap and leaves no resolved edge as a bare candidate.
        assertFalse(canonical.toString(), canonical.getAsJsonArray("gaps")
                .toString().contains(CanonicalSessionModel
                        .BINDING_ENDPOINT_UNAVAILABLE));
        JsonObject canonicalCounts = canonical.getAsJsonObject("counts");
        assertEquals(canonical.toString(), 0,
                canonicalCounts.get("candidateBindings").getAsInt());
        assertTrue(canonical.toString(),
                canonicalCounts.get("exactBindings").getAsInt() > 0);

        JsonObject missingOrderRow = row.deepCopy();
        JsonArray noOrderEvents = new JsonArray();
        noOrderEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.sender"));
        noOrderEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.1"));
        JsonObject noOrderLedger = RecordedSharedStateFixtures.ledgerEnvelope(
                noOrderEvents, new JsonArray());
        missingOrderRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject()
                .add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(noOrderLedger,
                                RecordedSharedStateFixtures.identity(
                                        "REGION.1", 1L))));
        ConcolicSmtComposer.Result missingOrder = compose(fatalInstance,
                Arrays.asList(RelationSummary.decode(missingOrderRow),
                        producer), firstHop);
        assertEquals(missingOrder.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                missingOrder.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertFalse(missingOrder.manifest.toString(), missingOrder.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertTrue(missingOrder.manifest.toString(), missingOrder.manifest
                .getAsJsonArray("finalStatusRefusals").toString().contains(
                        ConcolicSmtComposer.HANDOFF_ORDER_UNRECORDED));
        assertTrue(missingOrder.smtLib, missingOrder.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));

        // A producer task no imported case carries is no longer a refusal:
        // the value is the expression the receiver already holds, and the
        // producer strings are provenance.  Nothing is searched, so nothing
        // can be missing or ambiguous.
        JsonObject unknownProducerRow = row.deepCopy();
        unknownProducerRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject()
                .getAsJsonArray(VmHandoffEvidence.FIELD).get(0)
                .getAsJsonObject().addProperty(
                        VmHandoffEvidence.PRODUCER_TASK_ID, "TASK.MISSING");
        ConcolicSmtComposer.Result unknownProducer = compose(fatalInstance,
                Arrays.asList(RelationSummary.decode(unknownProducerRow),
                        producer), firstHop);
        assertEquals(unknownProducer.manifest.toString(), "CANDIDATE_READY",
                unknownProducer.manifest.get("state").getAsString());
        assertFalse(unknownProducer.manifest.toString(),
                unknownProducer.manifest.toString().contains(
                        "HANDOFF_PRODUCER_CASE"));
        JsonObject unknownBinding = null;
        for (JsonElement element : unknownProducer.manifest
                .getAsJsonArray("recordedValueBindings")) {
            JsonObject candidate = element.getAsJsonObject();
            if (VmHandoffEvidence.BINDING_KIND.equals(
                    candidate.get("kind").getAsString())) {
                unknownBinding = candidate;
                break;
            }
        }
        assertTrue(unknownProducer.manifest.toString(),
                unknownBinding != null);
        assertEquals("TASK.MISSING", unknownBinding
                .get(VmHandoffEvidence.PRODUCER_TASK_ID).getAsString());
        assertFalse(unknownBinding.toString(),
                unknownBinding.get("valueAssertion").getAsString()
                        .isEmpty());
    }

    @Test
    public void independentRpcProducerCasesDoNotShareARawHeapProjection()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#target";
        String producerAOccurrence = "REGION.1@Test#producerA";
        String producerBOccurrence = "REGION.1@Test#producerB";
        String portA = "REGION.0.in.0";
        String portB = "REGION.0.in.1";

        // These summaries came from separate JVM replay executions.  Their
        // serialized raw owner happens to have the same spelling, but that
        // does not make their heaps one snapshot.  A global field accessor
        // would state field(sharedOwner)=1 and field(sharedOwner)=2 and make
        // the otherwise legal pair of RPC producer paths inconsistent.
        JsonObject owner = constantReference("SHARED_REPLAY_OWNER",
                "Lexample/State;");
        JsonObject field = fieldAccess(owner, "example/State", 24, "I");
        RelationSummary producerA = summary("PRODUCER_A",
                producerAOccurrence, integer(1),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        RelationSummary producerB = summary("PRODUCER_B",
                producerBOccurrence, integer(2),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        producerA = withProducerGuardAndInteraction(producerA,
                binary(field.deepCopy(), "==", integer(1)), portA, 41L);
        producerB = withProducerGuardAndInteraction(producerB,
                binary(field.deepCopy(), "==", integer(2)), portB, 51L);

        JsonArray targetConstraints = new JsonArray();
        targetConstraints.add(binary(reference(portA, "I"), "<",
                reference(portB, "I")));
        JsonObject fatal = fatalQuery(targetOccurrence, targetConstraints);
        JsonObject targetPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        markRequiredTargetPath(targetPath);
        // Each producer hands over its own read of that same spelling.  The
        // handoff row states which producer sent it, and that is what keeps
        // the two projections apart now that no producer case is looked up.
        VmHandoffEvidence.writeTo(targetPath, Arrays.asList(
                VmHandoffEvidence.event(portA, 41L, 42L, field.deepCopy(),
                        "TASK.PRODUCER_A", producerAOccurrence),
                VmHandoffEvidence.event(portB, 51L, 52L, field.deepCopy(),
                        "TASK.PRODUCER_B", producerBOccurrence)));

        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.0"));
        events.add(RecordedSharedStateFixtures.event(51L,
                "HANDOFF_EXPORT", 103L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(52L,
                "HANDOFF_ATTACH", 104L, "REGION.0"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        order.add(RecordedSharedStateFixtures.edge(51L, 52L,
                "VALUE_HANDOFF"));
        targetPath.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        events, order),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 1L))));

        JsonObject targetRegion = region("REGION.0", true, false);
        targetRegion.getAsJsonArray("symbolicInputs")
                .add(port(portB, true, "int"));
        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Arrays.asList(producerA, producerB),
                Arrays.asList(targetRegion,
                        region("REGION.1", false, true)), fatal, null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertEquals(result.smtLib, 2, occurrences(result.smtLib,
                "(declare-fun container_field__"));
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
        }
    }

    @Test
    public void transportedObjectFieldKeepsItsConfiguredSourceValue()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#transported-field-target";
        String producerOccurrence = "REGION.1@Test#transported-field-source";
        String targetPort = "REGION.0.in.0";
        String sourceId = "TEST.NAMENODE.KEY_EXPIRY";
        String sourcePhase = publishPhase(producerOccurrence);
        String expiryRaw = configuredRaw(sourcePhase, sourceId, "expiry");
        JsonObject producerOwner = reference(
                "M_L_example_State_transport_owner", "Lexample/State;");
        JsonObject producerField = fieldAccess(producerOwner,
                "example/State", 24, "J");

        JsonObject rpc = protocolBinding("EDGE.TRANSPORTED.FIELD",
                producerOccurrence, "REGION.1.out.0", targetOccurrence,
                targetPort);
        RelationSummary producer = summary("TRANSPORTED_FIELD_SOURCE",
                producerOccurrence, producerOwner,
                Collections.<String>emptyList(),
                Collections.singletonList(rpc), "example.State");
        JsonObject producerRow = producer.toJson();
        JsonObject producerCase = producerRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        SymbolicSourceEvidence.writeTo(producerCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, producerOccurrence,
                        "<TestNameNode: long keyExpiry>",
                        reference(expiryRaw, "J"), 1, false, null)));
        producer = withProducerGuardAndInteraction(
                RelationSummary.decode(producerRow),
                binary(producerField, "==", reference(expiryRaw, "J")),
                targetPort, 41L);

        JsonObject targetOwner = reference(
                "M_L_field_" + targetPort + "_example/State",
                "Lexample/State;");
        JsonArray constraints = new JsonArray();
        constraints.add(binary(fieldAccess(targetOwner, "example/State", 24,
                "J"), "<", integer(100)));
        JsonObject fatal = fatalQuery(targetOccurrence, constraints, rpc);
        JsonObject targetPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        markRequiredTargetPath(targetPath);
        VmHandoffEvidence.writeTo(targetPath,
                Collections.singletonList(VmHandoffEvidence.event(
                        targetPort, 41L, 42L, producerOwner,
                        "TASK.TRANSPORTED_FIELD_SOURCE",
                        producerOccurrence)));
        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.0"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        targetPath.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        events, order),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 1L))));

        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", "example.State", ""),
                        region("REGION.1", "", "example.State")),
                fatal, Collections.singletonList(rpc));

        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 1, roots.size());
        String expiryTerm = roots.get(0).getAsJsonObject()
                .get("solverTerm").getAsString();
        assertEquals(result.smtLib, ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
            assertEquals(result.smtLib, "unsat", z3(assuming(result.smtLib,
                    "(>= " + expiryTerm + " 100)")));
        }
    }

    @Test
    public void twoRpcProducersAndMultipleTargetSourcesShareOneFatalFormula()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#nested-target";
        String producerAOccurrence = "REGION.1@Test#producer-A";
        String producerBOccurrence = "REGION.1@Test#producer-B";
        String portA = "REGION.0.in.0";
        String portB = "REGION.0.in.1";

        String sourceA = "TEST.RPC.PRODUCER.A";
        String sourceB = "TEST.RPC.PRODUCER.B";
        String sourceGate = "TEST.TARGET.GATE";
        String sourceOffset = "TEST.TARGET.OFFSET";
        String phaseA = publishPhase(producerAOccurrence);
        String phaseB = publishPhase(producerBOccurrence);
        String phaseGate = publishPhase(targetOccurrence) + ".GATE";
        String phaseOffset = publishPhase(targetOccurrence) + ".OFFSET";
        String rawA = configuredRaw(phaseA, sourceA, "a");
        String rawB = configuredRaw(phaseB, sourceB, "b");
        String rawGate = configuredRaw(phaseGate, sourceGate, "gate");
        String rawOffset = configuredRaw(phaseOffset, sourceOffset,
                "offset");

        RelationSummary producerA = summary("NESTED_PRODUCER_A",
                producerAOccurrence, reference(rawA, "I"),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        RelationSummary producerB = summary("NESTED_PRODUCER_B",
                producerBOccurrence, reference(rawB, "I"),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject producerARow = producerA.toJson();
        JsonObject producerACase = producerARow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        SymbolicSourceEvidence.writeTo(producerACase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        phaseA, sourceA, producerAOccurrence,
                        "<TestDataNode: int valueA>",
                        reference(rawA, "I"), 1, false, null)));
        producerA = withProducerGuardAndInteraction(
                RelationSummary.decode(producerARow),
                binary(reference(rawA, "I"), ">=", integer(0)), portA, 141L);

        JsonObject producerBRow = producerB.toJson();
        JsonObject producerBCase = producerBRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        SymbolicSourceEvidence.writeTo(producerBCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        phaseB, sourceB, producerBOccurrence,
                        "<TestDataNode: int valueB>",
                        reference(rawB, "I"), 1, false, null)));
        producerB = withProducerGuardAndInteraction(
                RelationSummary.decode(producerBRow),
                binary(reference(rawB, "I"), ">=", integer(0)), portB, 151L);

        // This is the nested target shape: the first two conditions are
        // NameNode-local prefix gates, while the final fatal predicate uses
        // both values attached from independent DataNode RPC producers.
        JsonArray targetConstraints = new JsonArray();
        targetConstraints.add(binary(reference(rawGate, "I"), ">",
                integer(0)));
        targetConstraints.add(binary(reference(rawOffset, "I"), ">=",
                integer(0)));
        targetConstraints.add(binary(
                binary(reference(portA, "I"), "+",
                        reference(rawGate, "I")),
                ">",
                binary(reference(portB, "I"), "+",
                        reference(rawOffset, "I"))));
        JsonObject fatal = fatalQuery(targetOccurrence, targetConstraints);
        JsonObject targetPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        markRequiredTargetPath(targetPath);
        // TargetReachPathQueryBuilder retains target-local declarations on
        // the fatal query root: they apply to every retained nested path for
        // this exact target occurrence, while handoffs remain path-local.
        SymbolicSourceEvidence.writeTo(fatal, Arrays.asList(
                SymbolicSourceEvidence.event(phaseGate, sourceGate,
                        targetOccurrence, "<TestNameNode: int gate>",
                        reference(rawGate, "I"), 1, false, null),
                SymbolicSourceEvidence.event(phaseOffset, sourceOffset,
                        targetOccurrence, "<TestNameNode: int offset>",
                        reference(rawOffset, "I"), 1, false, null)));
        VmHandoffEvidence.writeTo(targetPath, Arrays.asList(
                VmHandoffEvidence.event(portA, 141L, 142L,
                        reference(rawA, "I"), "TASK.NESTED_PRODUCER_A",
                        producerAOccurrence),
                VmHandoffEvidence.event(portB, 151L, 152L,
                        reference(rawB, "I"), "TASK.NESTED_PRODUCER_B",
                        producerBOccurrence)));

        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(141L,
                "HANDOFF_EXPORT", 201L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(142L,
                "HANDOFF_ATTACH", 202L, "REGION.0"));
        events.add(RecordedSharedStateFixtures.event(151L,
                "HANDOFF_EXPORT", 203L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(152L,
                "HANDOFF_ATTACH", 204L, "REGION.0"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(141L, 142L,
                "VALUE_HANDOFF"));
        order.add(RecordedSharedStateFixtures.edge(151L, 152L,
                "VALUE_HANDOFF"));
        targetPath.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        events, order),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 1L))));

        JsonObject targetRegion = region("REGION.0", true, false);
        targetRegion.getAsJsonArray("symbolicInputs")
                .add(port(portB, true, "int"));
        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Arrays.asList(producerA, producerB),
                Arrays.asList(targetRegion,
                        region("REGION.1", false, true)), fatal, null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 4, roots.size());
        String termA = "";
        String termB = "";
        String termGate = "";
        String termOffset = "";
        for (JsonElement element : roots) {
            JsonObject root = element.getAsJsonObject();
            String sourceId = root.get("sourceId").getAsString();
            String solverTerm = root.get("solverTerm").getAsString();
            if (sourceA.equals(sourceId)) termA = solverTerm;
            if (sourceB.equals(sourceId)) termB = solverTerm;
            if (sourceGate.equals(sourceId)) termGate = solverTerm;
            if (sourceOffset.equals(sourceId)) termOffset = solverTerm;
        }
        assertFalse(roots.toString(), termA.isEmpty());
        assertFalse(roots.toString(), termB.isEmpty());
        assertFalse(roots.toString(), termGate.isEmpty());
        assertFalse(roots.toString(), termOffset.isEmpty());
        if (z3Available()) {
            JsonObject reach = BooleanReachConditionExtractor.extract(
                    result.smtLib, result.manifest,
                    Arrays.asList(targetRegion,
                            region("REGION.1", false, true)),
                    new BooleanReachConditionExtractor.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);
            JsonArray models = reach.getAsJsonArray(
                    BooleanReachConditionExtractor
                            .SYMBOLIC_VARIABLE_MODELS);
            assertEquals(models.toString(), 1, models.size());
            JsonArray reported = models.get(0).getAsJsonObject()
                    .getAsJsonArray("variables");
            assertEquals(reported.toString(), 4, reported.size());
            Set<String> reportedSources = new LinkedHashSet<>();
            for (JsonElement element : reported) {
                JsonObject variable = element.getAsJsonObject();
                assertEquals("TEST_DRIVER/test#epoch0",
                        variable.get("sourceKey").getAsString());
                assertTrue(variable.toString(), variable.has("value"));
                reportedSources.add(
                        variable.get("sourceId").getAsString());
            }
            assertEquals(new LinkedHashSet<>(Arrays.asList(
                    sourceA, sourceB, sourceGate, sourceOffset)),
                    reportedSources);
            assertEquals(result.smtLib, "sat", z3(assuming(result.smtLib,
                    "(= " + termA + " 8)",
                    "(= " + termB + " 3)",
                    "(= " + termGate + " 1)",
                    "(= " + termOffset + " 0)")));
            // If either RPC handoff were merely correlated in a trace rather
            // than expression-connected, Z3 could choose unrelated target
            // port values and this deliberately false witness would be SAT.
            assertEquals(result.smtLib, "unsat", z3(assuming(result.smtLib,
                    "(= " + termA + " 1)",
                    "(= " + termB + " 8)",
                    "(= " + termGate + " 1)",
                    "(= " + termOffset + " 0)")));
        }
    }

    @Test
    public void targetPrefixPathsOwnTheirRpcHandoffsSeparately()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#two-paths";
        String producerAOccurrence = "REGION.1@Test#pathA";
        String producerBOccurrence = "REGION.1@Test#pathB";
        String port = "REGION.0.in.0";
        RelationSummary producerA = withProducerGuardAndInteraction(
                summary("TARGET_PATH_A", producerAOccurrence, 1,
                        Collections.<String>emptyList(),
                        Collections.<JsonObject>emptyList()),
                binary(integer(1), "==", integer(1)), port, 41L);
        RelationSummary producerB = withProducerGuardAndInteraction(
                summary("TARGET_PATH_B", producerBOccurrence, 2,
                        Collections.<String>emptyList(),
                        Collections.<JsonObject>emptyList()),
                binary(integer(1), "==", integer(1)), port, 41L);

        JsonObject portValue = reference(
                "M_I_field_" + port + "_example/Reply", "I");
        JsonObject replayOwner = constantReference(
                "SHARED_TARGET_REPLAY_OWNER", "Lexample/Target;");
        JsonObject replayField = fieldAccess(replayOwner,
                "example/Target", 24, "I");
        JsonArray firstConstraints = new JsonArray();
        firstConstraints.add(binary(replayField.deepCopy(), "==", integer(1)));
        firstConstraints.add(binary(portValue.deepCopy(), ">", integer(0)));
        JsonObject fatal = fatalQuery(targetOccurrence, firstConstraints);
        JsonObject first = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        first.addProperty("caseId", "TARGET.PATH.A");
        first.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        VmHandoffEvidence.writeTo(first,
                Collections.singletonList(VmHandoffEvidence.event(port, 41L,
                        42L, integer(1), "TASK.TARGET_PATH_A",
                        producerAOccurrence)));

        JsonObject second = first.deepCopy();
        second.addProperty("caseId", "TARGET.PATH.B");
        second.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        JsonArray secondConstraints = new JsonArray();
        secondConstraints.add(binary(replayField.deepCopy(), "==", integer(2)));
        secondConstraints.add(binary(portValue.deepCopy(), ">", integer(0)));
        second.add("constraints", secondConstraints);
        second.remove(VmHandoffEvidence.FIELD);
        VmHandoffEvidence.writeTo(second,
                // A fresh target replay starts its VM ledger from the same
                // small ids as path A.  Scope, not the raw integer, must keep
                // these two deliveries distinct through SMT and manifests.
                Collections.singletonList(VmHandoffEvidence.event(port, 41L,
                        42L, integer(2), "TASK.TARGET_PATH_B",
                        producerBOccurrence)));
        fatal.getAsJsonArray("paths").add(second);

        JsonArray firstEvents = new JsonArray();
        firstEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.1"));
        firstEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.0"));
        JsonArray secondEvents = new JsonArray();
        secondEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 103L, "REGION.1"));
        secondEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 104L, "REGION.0"));
        JsonArray firstOrder = new JsonArray();
        firstOrder.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        JsonArray secondOrder = new JsonArray();
        secondOrder.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        first.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        firstEvents, firstOrder),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 1L))));
        second.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        secondEvents, secondOrder),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 2L))));

        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Arrays.asList(producerA, producerB),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", false, true)), fatal, null);

        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("HANDOFF_CASE_SCOPE_MISSING"));
        assertEquals(result.manifest.toString(), 2,
                result.manifest.getAsJsonArray("recordedValueBindings")
                        .size());
        Set<Long> scopedExports = new LinkedHashSet<>();
        Set<String> handoffKeys = new LinkedHashSet<>();
        for (JsonElement element : result.manifest.getAsJsonArray(
                "recordedValueBindings")) {
            JsonObject binding = element.getAsJsonObject();
            assertEquals(41L,
                    binding.get("localExportEventId").getAsLong());
            scopedExports.add(binding.get("exportEventId").getAsLong());
            handoffKeys.add(binding.get("bindingKey").getAsString());
        }
        assertEquals(result.manifest.toString(), 2, scopedExports.size());
        assertEquals(result.manifest.toString(), 2, handoffKeys.size());
        assertEquals(result.smtLib, 2, occurrences(result.smtLib,
                "(declare-fun container_field__"));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
        }
    }

    @Test
    public void rootLevelTargetHandoffWithoutCaseOwnerFailsClosed()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#root-handoff";
        JsonObject fatal = fatalQuery(targetOccurrence,
                targetConstraints());
        VmHandoffEvidence.writeTo(fatal,
                Collections.singletonList(VmHandoffEvidence.event(
                        "REGION.0.in.0", 41L, 42L, integer(1),
                        "TASK.PRODUCER", "REGION.1@Test#producer")));

        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal,
                null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains("HANDOFF_CASE_SCOPE_MISSING"));
    }

    @Test
    public void composerTraversalUsesOnlyVmSelectedReadFromButKeepsRpc() {
        String fatalInstance = "REGION.0@Test#target";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject concrete = binding("EDGE.CONCRETE", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 1, 2);
        JsonObject candidate = concrete.deepCopy();
        candidate.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        JsonObject excluded = concrete.deepCopy();
        excluded.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXCLUDED);
        JsonObject exact = concrete.deepCopy();
        exact.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        JsonObject guarded = concrete.deepCopy();
        guarded.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        JsonObject rpc = protocolBinding("EDGE.RPC", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");

        // Replay scheduling keeps all observed channels available.
        assertTrue(AutomaticRegionEdge.summaryTraversalBinding(concrete));
        assertTrue(AutomaticRegionEdge.summaryTraversalBinding(candidate));
        assertTrue(AutomaticRegionEdge.summaryTraversalBinding(excluded));
        // SMT traversal is the provenance-aware, narrower gate.
        assertFalse(AutomaticRegionEdge.composerTraversalBinding(concrete));
        assertFalse(AutomaticRegionEdge.composerTraversalBinding(candidate));
        assertFalse(AutomaticRegionEdge.composerTraversalBinding(excluded));
        assertTrue(AutomaticRegionEdge.composerTraversalBinding(exact));
        assertTrue(AutomaticRegionEdge.composerTraversalBinding(guarded));
        assertTrue(AutomaticRegionEdge.composerTraversalBinding(rpc));
        // Graph closure may retain trusted candidates as topology, while the
        // value gate above remains exact/guarded-only.
        assertFalse(AutomaticRegionEdge
                .topologyOnlyCompositionBinding(concrete));
        assertTrue(AutomaticRegionEdge
                .topologyOnlyCompositionBinding(candidate));
        assertTrue(AutomaticRegionEdge
                .topologyOnlyCompositionBinding(excluded));
        assertFalse(AutomaticRegionEdge
                .topologyOnlyCompositionBinding(exact));
        assertFalse(AutomaticRegionEdge
                .topologyOnlyCompositionBinding(guarded));
        assertFalse(AutomaticRegionEdge
                .topologyOnlyCompositionBinding(rpc));
    }

    @Test
    public void onlyExactWireDeliveryLowersAsEquality() throws Exception {
        String target = "REGION.0@Test#wire-target";
        String producer = "REGION.1@Test#wire-producer";
        String port = "REGION.1.out.0";
        JsonObject wire = exactWireBinding("EDGE.WIRE", producer, port,
                target, port, "node/request/fetch#1", "7", "RESPONSE",
                40, 41);

        assertTrue(AutomaticRegionEdge.trustedWireEquality(wire));
        assertTrue(AutomaticRegionEdge
                .trustedRuntimeCompositionBinding(wire));

        JsonObject weak = wire.deepCopy();
        weak.addProperty("receiverEventSeq", 40);
        assertTrue(AutomaticRegionEdge.tracedExchangeCandidate(weak));
        assertFalse(AutomaticRegionEdge.trustedWireEquality(weak));
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeCompositionBinding(weak));

        JsonObject targetRegion = region("REGION.0", true, false);
        targetRegion.getAsJsonArray("symbolicInputs").get(0)
                .getAsJsonObject().addProperty("portId", port);
        RelationSummary source = summary("WIRE", producer, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(wire));
        ConcolicSmtComposer.Result result = compose(target,
                Collections.singletonList(source),
                Arrays.asList(targetRegion,
                        region("REGION.1", false, true)), wire);

        assertEquals(result.manifest.toString(), 1,
                result.manifest.getAsJsonArray(
                        "resolvedEdgeBindings").size());
        assertTrue(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_0_0"));
    }

    @Test
    public void exactWireTargetRetainsOnlyItsOwnedRequestPrefix()
            throws Exception {
        String port = "REGION.1.out.0";
        String request = "node/request/fetch#1";
        String target = "REGION.0@Test#target";
        JsonObject before = exactWireBinding("EDGE.BEFORE",
                "REGION.1@Test#before", port, "REGION.0@Test#consumer-1",
                port, request, "1", "REQUEST", 10, 11);
        JsonObject targetEdge = exactWireBinding("EDGE.TARGET",
                "REGION.1@Test#target-source", port, target, port, request,
                "2", "RESPONSE", 20, 21);
        JsonObject otherRequest = exactWireBinding("EDGE.OTHER",
                "REGION.1@Test#other", port, "REGION.0@Test#consumer-2",
                port, "node/request/other#1", "3", "REQUEST", 12, 13);
        JsonObject after = exactWireBinding("EDGE.AFTER",
                "REGION.1@Test#after", port, "REGION.0@Test#consumer-3",
                port, request, "4", "REQUEST", 30, 31);
        JsonObject unowned = exactWireBinding("EDGE.UNOWNED",
                "REGION.1@Test#missing", port, "REGION.0@Test#consumer-4",
                port, request, "5", "REQUEST", 14, 15);
        List<RelationSummary> summaries = Arrays.asList(
                summary("BEFORE", "REGION.1@Test#before", 1,
                        Collections.<String>emptyList(),
                        Collections.singletonList(before)),
                summary("TARGET", "REGION.1@Test#target-source", 2,
                        Collections.<String>emptyList(),
                        Collections.singletonList(targetEdge)),
                summary("OTHER", "REGION.1@Test#other", 3,
                        Collections.<String>emptyList(),
                        Collections.singletonList(otherRequest)),
                summary("AFTER", "REGION.1@Test#after", 4,
                        Collections.<String>emptyList(),
                        Collections.singletonList(after)),
                summary("UNOWNED", "REGION.1@Test#not-missing", 5,
                        Collections.<String>emptyList(),
                        Collections.singletonList(unowned)));
        JsonObject targetRegion = region("REGION.0", true, false);
        targetRegion.getAsJsonArray("symbolicInputs").get(0)
                .getAsJsonObject().addProperty("portId", port);

        ConcolicSmtComposer.Result result = compose(target, summaries,
                Arrays.asList(targetRegion,
                        region("REGION.1", false, true)), targetEdge);

        String resolved = result.manifest.getAsJsonArray(
                "resolvedEdgeBindings").toString();
        assertEquals(result.manifest.toString(), 2,
                result.manifest.getAsJsonArray(
                        "resolvedEdgeBindings").size());
        assertTrue(resolved, resolved.contains("EDGE.BEFORE"));
        assertTrue(resolved, resolved.contains("EDGE.TARGET"));
        assertFalse(resolved, resolved.contains("EDGE.OTHER"));
        assertFalse(resolved, resolved.contains("EDGE.AFTER"));
        assertFalse(resolved, resolved.contains("EDGE.UNOWNED"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_0_0"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_0_1"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_0_2"));
    }

    @Test
    public void untrustedRecursiveReadFromDoesNotDemandAProducer()
            throws Exception {
        for (String provenance : Collections.singletonList("")) {
            String fatalInstance = "REGION.0@Test#target";
            String consumerInstance = "REGION.1@Test#consumer";
            JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                    "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
            JsonObject upstream = binding("EDGE.UPSTREAM", "REGION.2@Test#p",
                    "REGION.2.out.0", consumerInstance,
                    "REGION.1.in.0", 1, 2);
            upstream.addProperty("fromRegion", "REGION.2");
            if (!provenance.isEmpty()) {
                upstream.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                        provenance);
            }
            RelationSummary consumer = summary("CONSUMER", consumerInstance,
                    10, Collections.singletonList("REGION.1.in.0"),
                    Arrays.asList(firstHop, upstream));

            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Collections.singletonList(consumer), firstHop);

            assertFalse(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "MissingExactProducerSummary:REGION.2"));
            assertFalse(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "DROPPED_CONFIRMED_EDGE_EVIDENCE"));
        }
    }

    @Test
    public void trustedTopologyReadFromSelectsASuppliedProducerOnly()
            throws Exception {
        for (String provenance : Arrays.asList(
                RecordedReadFrom.PROVENANCE_CANDIDATE,
                RecordedReadFrom.PROVENANCE_EXCLUDED)) {
            String fatalInstance = "REGION.0@Test#target";
            String consumerInstance = "REGION.1@Test#consumer";
            String producerInstance = "REGION.1@Test#producer";
            JsonObject firstHop = protocolBinding("EDGE.RPC",
                    consumerInstance, "REGION.1.out.0", fatalInstance,
                    "REGION.0.in.0");
            JsonObject upstream = binding("EDGE.UPSTREAM",
                    producerInstance, "REGION.1.out.0",
                    consumerInstance, "REGION.1.in.0", 1, 2);
            upstream.addProperty("fromRegion", "REGION.1");
            upstream.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                    provenance);
            RelationSummary consumer = summary("CONSUMER",
                    consumerInstance, 10,
                    Collections.singletonList("REGION.1.in.0"),
                    Arrays.asList(firstHop, upstream));
            RelationSummary producer = summary("PRODUCER",
                    producerInstance, 20,
                    Collections.<String>emptyList(),
                    Collections.<JsonObject>emptyList());

            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Arrays.asList(consumer, producer), firstHop);

            assertTrue(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "EDGE.UPSTREAM"));
            assertFalse("topology-only RF must not become a value equality\n"
                            + result.manifest,
                    result.manifest.getAsJsonArray("recordedValueBindings")
                            .toString().contains("EDGE.UPSTREAM"));
        }
    }

    @Test
    public void vmSelectedRecursiveReadFromStillDemandsItsProducer()
            throws Exception {
        for (String provenance : Arrays.asList(
                RecordedReadFrom.PROVENANCE_EXACT,
                RecordedReadFrom.PROVENANCE_GUARDED)) {
            String fatalInstance = "REGION.0@Test#target";
            String consumerInstance = "REGION.1@Test#consumer";
            JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                    "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
            JsonObject upstream = binding("EDGE.UPSTREAM", "REGION.2@Test#p",
                    "REGION.2.out.0", consumerInstance,
                    "REGION.1.in.0", 1, 2);
            upstream.addProperty("fromRegion", "REGION.2");
            upstream.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                    provenance);
            RelationSummary consumer = summary("CONSUMER", consumerInstance,
                    10, Collections.singletonList("REGION.1.in.0"),
                    Arrays.asList(firstHop, upstream));

            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Collections.singletonList(consumer), firstHop);

            assertTrue(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "MissingExactProducerSummary:REGION.2"));
        }
    }

    /**
     * Two closures of one producer occurrence both cover a demand; the one
     * that recorded values for more of its own ports answers it.
     *
     * <p>Answering by set equality took the closure that is exactly the
     * demand unconditionally, so an occurrence whose closure also holds the
     * in-region writes that feed the demanded port had every value it
     * recorded for them dropped without a word -- and the demanded port then
     * lowered as a local root rather than as the value those writes gave
     * it.</p>
     */
    @Test
    public void theProducerWithMoreRecordedEvidenceAnswersTheDemand()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER",
                producerInstance, "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject producerCopy = selected.deepCopy();
        producerCopy.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary exactSet = summary("EXACTSET",
                producerInstance + "#a1", 7, Collections.<String>emptyList(),
                Collections.singletonList(producerCopy));
        RelationSummary rich = widerSummary("RICH",
                producerInstance + "#a2", 7, true,
                Collections.singletonList(producerCopy.deepCopy()));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, exactSet, rich), firstHop);

        assertTrue(result.smtLib, result.smtLib.contains("CASE_RICH"));
        assertFalse(result.smtLib, result.smtLib.contains("CASE_EXACTSET"));
    }

    /**
     * Fail-closed: a wider closure that recorded nothing for its extra port
     * carries no more evidence, so the smaller closure still answers.
     */
    @Test
    public void aWiderClosureThatRecordedNothingExtraDoesNotOutrank()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER",
                producerInstance, "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject producerCopy = selected.deepCopy();
        producerCopy.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary exactSet = summary("EXACTSET",
                producerInstance + "#a1", 7, Collections.<String>emptyList(),
                Collections.singletonList(producerCopy));
        RelationSummary blind = widerSummary("BLIND",
                producerInstance + "#a2", 7, false,
                Collections.singletonList(producerCopy.deepCopy()));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, exactSet, blind), firstHop);

        assertTrue(result.smtLib, result.smtLib.contains("CASE_EXACTSET"));
        assertFalse(result.smtLib, result.smtLib.contains("CASE_BLIND"));
    }

    @Test
    public void readerSelectedReadFromUsesTheProducerCausalClosure()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER", producerInstance,
                "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject producerCopy = selected.deepCopy();
        producerCopy.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary producer = summary("PRODUCER", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(producerCopy));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, producer), firstHop);

        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("SelectedSummaryMissingExactEdgeBinding"));
        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("SelectedReadFromMissingProducerCausalEdge"));
        assertTrue(result.manifest.toString(), result.manifest
                .getAsJsonArray("resolvedEdgeBindings").toString()
                .contains("EDGE.READER"));
    }

    @Test
    public void readerSelectedReadFromRejectsAnIncompleteProducerTuple()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER", producerInstance,
                "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject candidate = selected.deepCopy();
        candidate.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary producerWithoutEdge = withoutCausalEdges(summary(
                "PRODUCER", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate)),
                "REGION.1.out.0");

        ConcolicSmtComposer.Result noEdge = compose(fatalInstance,
                Arrays.asList(consumer, producerWithoutEdge), firstHop);
        assertTrue(noEdge.manifest.toString(), noEdge.manifest.toString()
                .contains("SelectedReadFromMissingProducerCausalEdge:"
                        + "EDGE.READER"));

        RelationSummary wrongOccurrence = summary("WRONG",
                producerInstance + ".other", 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate));
        ConcolicSmtComposer.Result noOccurrence = compose(fatalInstance,
                Arrays.asList(consumer, wrongOccurrence), firstHop);
        assertTrue(noOccurrence.manifest.toString(),
                noOccurrence.manifest.toString().contains(
                        "MissingExactProducerSummary:REGION.1"));

        JsonObject missingOccurrence = selected.deepCopy();
        missingOccurrence.remove("fromOccurrenceId");
        missingOccurrence.addProperty("edgeId", "EDGE.NO_OCCURRENCE");
        RelationSummary missingOccurrenceConsumer = summary(
                "NO_OCCURRENCE_CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, missingOccurrence));
        ConcolicSmtComposer.Result noOccurrenceId = compose(fatalInstance,
                Arrays.asList(missingOccurrenceConsumer,
                        producerWithoutEdge), firstHop);
        assertTrue(noOccurrenceId.manifest.toString(),
                noOccurrenceId.manifest.toString().contains(
                        "UntrustedRecursiveEdgeBinding:EDGE.NO_OCCURRENCE"));

        JsonObject wrongPort = selected.deepCopy();
        wrongPort.addProperty("edgeId", "EDGE.WRONG_PORT");
        wrongPort.addProperty("fromOutputPort", "REGION.1.out.missing");
        RelationSummary wrongPortConsumer = summary("WRONG_PORT_CONSUMER",
                consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, wrongPort));
        ConcolicSmtComposer.Result noPort = compose(fatalInstance,
                Arrays.asList(wrongPortConsumer, producerWithoutEdge),
                firstHop);
        assertTrue(noPort.manifest.toString(), noPort.manifest.toString()
                .contains("MissingExactProducerSummary:REGION.1"));
    }

    @Test
    public void readerSelectedReadFromRejectsAmbiguousProducerSummaries()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER", producerInstance,
                "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject candidate = selected.deepCopy();
        candidate.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary first = summary("PRODUCER_A", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate));
        RelationSummary second = summary("PRODUCER_B", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, first, second), firstHop);

        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains("AmbiguousExactProducerSummary:REGION.1"));
        assertFalse(result.manifest.toString(), result.manifest
                .getAsJsonArray("resolvedEdgeBindings").toString()
                .contains("EDGE.READER"));
    }

    @Test
    public void droppedAuditIgnoresRuntimeCandidatesButRefusesSelectedExact()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference("REGION.0.in.0", "I"), "==",
                integer(1)));
        for (String provenance : Arrays.asList("",
                RecordedReadFrom.PROVENANCE_CANDIDATE,
                RecordedReadFrom.PROVENANCE_EXCLUDED)) {
            JsonObject runtimeOnly = binding("EDGE.RUNTIME", "REGION.1@Test#p",
                    "REGION.1.out.0", fatalInstance,
                    "REGION.0.in.0", 1, 2);
            if (!provenance.isEmpty()) {
                runtimeOnly.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                        provenance);
            }
            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Collections.<RelationSummary>emptyList(),
                    Arrays.asList(region("REGION.0", true, false),
                            region("REGION.1", false, true)), constraints,
                    Collections.singletonList(runtimeOnly));
            assertFalse(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "DROPPED_CONFIRMED_EDGE_EVIDENCE"));
        }

        String producerInstance = "REGION.1@Test#producer";
        JsonObject selected = binding("EDGE.SELECTED", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        RelationSummary producer = summary("SELECTED", producerInstance, 10,
                Collections.<String>emptyList(),
                Collections.singletonList(selected));
        ConcolicSmtComposer.Result refused = compose(fatalInstance,
                Collections.singletonList(producer),
                Collections.singletonList(
                        region("REGION.0", true, false)), constraints,
                selected);
        assertTrue(refused.manifest.toString(), refused.manifest.toString()
                .contains("DROPPED_CONFIRMED_EDGE_EVIDENCE:"));
        assertEquals(ConcolicSmtComposer.FINAL_REFUSED,
                refused.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
    }

    /**
     * A ledger that claims a partial order and delivers a cycle spanning a
     * field read-from, program order and an RPC value handoff.
     */
    private static JsonObject crossChannelCycleLedger() {
        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(11L, "FIELD_WRITE", 101L,
                "REGION.writerA"));
        events.add(RecordedSharedStateFixtures.event(21L, "FIELD_READ", 103L,
                "REGION.reader"));
        events.add(RecordedSharedStateFixtures.event(31L, "HANDOFF_EXPORT",
                103L, "REGION.reader"));
        events.add(RecordedSharedStateFixtures.event(32L, "HANDOFF_ATTACH",
                101L, "REGION.writerA"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(11L, 21L,
                "FIELD_READ_FROM"));
        order.add(RecordedSharedStateFixtures.edge(21L, 31L,
                "PROGRAM_ORDER"));
        order.add(RecordedSharedStateFixtures.edge(31L, 32L,
                "VALUE_HANDOFF"));
        order.add(RecordedSharedStateFixtures.edge(32L, 11L,
                "VALUE_HANDOFF"));
        return RecordedSharedStateFixtures.ledgerEnvelope(events, order);
    }

    /**
     * The four recorded read-from shapes, each solved by z3.
     *
     * <p>Each golden is a complete composition, and each row of its truth
     * table is a real solve of the emitted query with one extra assumption.
     * Reading the formula text would only prove that some string was written;
     * what has to hold is that the recorded model <em>decides</em> the target,
     * and only a solver can say that.</p>
     *
     * <table>
     *   <tr><td>exact</td><td>the proven writer's value, and no other</td></tr>
     *   <tr><td>guarded</td><td>each arm's own value; a false writer guard
     *   makes its arm infeasible</td></tr>
     *   <tr><td>unknown</td><td>a writer the order domain does not hold is
     *   not selectable, and the unknown arm constrains no value</td></tr>
     *   <tr><td>no candidate</td><td>the unknown arm is the only arm, and
     *   exactly-one forces it</td></tr>
     * </table>
     */
    @Test
    public void goldenRecordedModelsMatchTheirZ3TruthTables()
            throws Exception {
        Assume.assumeTrue(z3Available());

        // Exact: the session proved which write the read took, so the value
        // is an equality and there is no selector to choose.
        ConcolicSmtComposer.Result exact = exactGolden();
        assertEquals(exact.manifest.toString(), "CANDIDATE_READY",
                exact.manifest.get("state").getAsString());
        assertTrue(exact.smtLib, exact.smtLib.contains(
                ":named recorded_exact_order__11__21"));
        assertFalse(exact.smtLib, exact.smtLib.contains("rf_selector__"));
        // The port the recorded answer decided is bound once, by that answer.
        // The competing trace candidate is not composed beside it - which
        // would equate the two producers - and is not promoted into a
        // composition divergence merely because the trace retained it.
        assertFalse(exact.smtLib,
                exact.smtLib.contains("state_version_choice__"));
        assertFalse(exact.manifest.toString(), exact.manifest.toString()
                .contains("RECORDED_EVIDENCE_DECIDED_CONSUMER_PORT"));
        assertTrue(exact.manifest.toString(), exact.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertEquals("sat", z3(exact.smtLib));
        assertEquals("unsat", z3(ready(exactGolden(11)).smtLib));

        // Guarded: one selector family decides value, guard and cut.
        ConcolicSmtComposer.Result guarded = guardedGolden(1, true, true);
        // The selector family is composed and solved over recorded writers.
        // The selected edge still advertises unknown-writer provenance, so
        // that edge remains a final-artifact refusal.
        assertEquals(guarded.manifest.toString(), "CANDIDATE_READY",
                guarded.manifest.get("state").getAsString());
        assertEquals(guarded.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                guarded.manifest.get(
                        ConcolicSmtComposer.FINAL_STATUS).getAsString());
        assertFalse(guarded.manifest.toString(), guarded.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertEquals("sat", z3(guarded.smtLib));
        assertEquals("sat", z3(assuming(guarded.smtLib,
                "rf_selector__21__rf1")));
        // Changing the selected writer changes the target value formula: the
        // same target is unreachable through the other writer's expression.
        assertEquals("unsat", z3(assuming(guarded.smtLib,
                "rf_selector__21__rf2")));
        assertEquals("sat", z3(assuming(ready(guardedGolden(2, true, true))
                .smtLib, "rf_selector__21__rf2")));
        // The exported SAT query may not invent a writer for a value no
        // recorded writer produces.
        assertEquals("unsat", z3(assuming(ready(guardedGolden(99, true, true))
                .smtLib, "rf_selector__21__rf_unknown")));

        // A false guard makes the only recorded writer for value 2
        // infeasible; the unknown arm cannot rescue the witness.
        ConcolicSmtComposer.Result refuted = ready(
                guardedGolden(2, false, true));
        assertTrue(refuted.smtLib, refuted.smtLib.contains(
                ":named recorded_write_guard__21__rf2"));
        assertEquals("unsat", z3(assuming(refuted.smtLib,
                "rf_selector__21__rf2")));
        assertEquals("unsat", z3(refuted.smtLib));

        // Neither recorded write is in the order domain, and the existential
        // SAT query also excludes the unknown arm.
        ConcolicSmtComposer.Result unknown = ready(
                guardedGolden(1, true, false));
        assertTrue(unknown.smtLib, unknown.smtLib.contains(
                ":named recorded_write_absent__21__11"));
        assertEquals("unsat", z3(assuming(unknown.smtLib,
                "rf_selector__21__rf1")));
        assertEquals("unsat", z3(assuming(unknown.smtLib,
                "rf_selector__21__rf_unknown")));

        // No candidate: the location was watched and named no addressable
        // writer, so the only arm is the unknown one and it is forced.
        ConcolicSmtComposer.Result noCandidate = ready(noCandidateGolden());
        assertEquals("sat", z3(noCandidate.smtLib));
        assertEquals("unsat", z3(assuming(noCandidate.smtLib,
                "(not rf_selector__21__rf_unknown)")));


        // A partial recorded model can still be unsatisfiable, and the result
        // vocabulary must not read that as unreachability.  The same query
        // read as a closed model would say the opposite, which is exactly why
        // the closure facts have to travel with it.
        ConcolicSmtComposer.Result partial = ready(
                unsatisfiablePartialGolden());
        assertFalse(partial.manifest.toString(), partial.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertEquals("unsat", z3(partial.smtLib));
        JsonObject inconclusive = reachCondition(partial, partial.manifest);
        assertEquals("UNKNOWN",
                inconclusive.get("reachability").getAsString());
        assertEquals("INCONCLUSIVE_UNDERAPPROXIMATION",
                inconclusive.get("coverageConclusion").getAsString());
        JsonObject asClosed = partial.manifest.deepCopy();
        asClosed.addProperty("recordedModelComplete", true);
        JsonObject closedEvidence = new JsonObject();
        closedEvidence.addProperty("schemaVersion", 1);
        closedEvidence.addProperty("kind", "UNSAT_CLOSURE_EVIDENCE");
        closedEvidence.addProperty("authority",
                ConcolicSmtComposer.UNSAT_CLOSURE_AUTHORITY);
        closedEvidence.addProperty("recordedModelComplete", true);
        closedEvidence.addProperty("producerPathsClosed", true);
        closedEvidence.addProperty("targetPathsClosed", true);
        closedEvidence.addProperty("compositionCoverageClosed", true);
        closedEvidence.addProperty("finalStatusReady", true);
        closedEvidence.addProperty("targetCoverageGapCount", 0);
        closedEvidence.addProperty("compositionCoverageGapCount", 0);
        closedEvidence.add("partialProducerSummaryIds", new JsonArray());
        closedEvidence.addProperty(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, true);
        asClosed.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE,
                true);
        asClosed.add(ConcolicSmtComposer.UNSAT_CLOSURE_EVIDENCE,
                closedEvidence);
        asClosed.addProperty(ConcolicSmtComposer.FINAL_STATUS,
                ConcolicSmtComposer.FINAL_READY);
        assertEquals("UNREACHABLE", reachCondition(partial, asClosed)
                .get("reachability").getAsString());
    }

    /**
     * README CASE-1's acceptance condition for the resolved edge bindings.
     *
     * <p>One reader occurrence, two guarded cases, and a read-from edge only
     * the first of them resolved -- which is what the importer produces, since
     * it resolves every edge against the recorded read-from of that one path.
     * The arm that edge justifies must be asserted under the selector of the
     * case that observed it and under no other, or the second case's guard
     * would enable a writer that case never read.</p>
     */
    @Test
    public void caseLocalEdgeBindingGuardsOnlyItsOwnReadFromArm()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject arm = binding("EDGE.SHARED", producerInstance,
                "REGION.1.out.0", consumerInstance, "REGION.1.in.0", 1, 2);
        arm.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        arm.addProperty(RecordedReadFrom.EDGE_FIELD, "example.State#value");
        arm.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        arm.addProperty("fieldVersionId", 11);
        arm.addProperty("readEventId", 21);
        JsonObject candidate = arm.deepCopy();
        candidate.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);

        RelationSummary consumer = readerWithOneCaseOwningTheEdge(
                consumerInstance, firstHop, arm);
        RelationSummary producer = summary("PRODUCER", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, producer), firstHop);

        String owner = RecordedSessionModel.caseSelector(
                RecordedSessionModel.caseOwner("REGION.1", consumerInstance,
                        "CASE.OBSERVED", 0));
        String other = RecordedSessionModel.caseSelector(
                RecordedSessionModel.caseOwner("REGION.1", consumerInstance,
                        "CASE.UNOBSERVED", 1));
        assertFalse(owner.equals(other));
        // Both selectors exist and are partitioned, so "guarded by the owner"
        // is a statement about two live alternatives and not about a constant
        // the second case simply never got.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + other + " Bool)"));

        String valueAssertion = "";
        for (JsonElement element : result.manifest.getAsJsonArray(
                "recordedValueBindings")) {
            JsonObject evidence = element.getAsJsonObject();
            if ("EDGE.SHARED".equals(evidence.get("edgeId").getAsString())) {
                valueAssertion = evidence.get("valueAssertion").getAsString();
            }
        }
        assertFalse(result.manifest.toString(), valueAssertion.isEmpty());
        String asserted = assertionNamed(result.smtLib, valueAssertion);
        assertTrue(asserted, asserted.contains("(=> " + owner + " "));
        assertFalse(asserted, asserted.contains(other));
    }

    /** The body of the one named assertion, guard included. */
    private static String assertionNamed(String smtLib, String name) {
        int end = smtLib.indexOf(":named " + name + ")");
        assertTrue(smtLib, end >= 0);
        int start = smtLib.lastIndexOf("(assert (! ", end);
        assertTrue(smtLib, start >= 0);
        return smtLib.substring(start, end);
    }

    /**
     * One reader relation with two guarded cases, only the first of which
     * resolved {@code arm}.  The RPC hop both cases took stays at row level,
     * which is where a merge puts a binding every case agreed on.
     */
    private static RelationSummary readerWithOneCaseOwningTheEdge(
            String consumerInstance, JsonObject firstHop, JsonObject arm) {
        JsonObject row = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, arm)).toJson();
        JsonArray rowLevel = new JsonArray();
        rowLevel.add(firstHop.deepCopy());
        row.add("edgeBindings", rowLevel);
        JsonArray cases = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        JsonObject observed = cases.get(0).getAsJsonObject();
        observed.addProperty("caseId", "CASE.OBSERVED");
        observed.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        JsonArray owned = new JsonArray();
        owned.add(arm.deepCopy());
        observed.add("edgeBindings", owned);
        JsonObject unobserved = observed.deepCopy();
        unobserved.addProperty("caseId", "CASE.UNOBSERVED");
        unobserved.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        unobserved.addProperty("sourceTaskId", "TASK.CONSUMER.UNOBSERVED");
        unobserved.remove("edgeBindings");
        cases.add(unobserved);
        row.add(SharedStateEvidence.RECORDED_FIELD,
                readerRecordedState(consumerInstance,
                        arm.get("fromOccurrenceId").getAsString()));
        return RelationSummary.decode(row);
    }

    /** The exact read of one location this reader occurrence performed. */
    private static JsonObject readerRecordedState(String readerOccurrence,
                                                  String writerOccurrence) {
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_EXACT, "UNIQUE_VERSION", 11L);
        JsonObject reader = envelope.getAsJsonArray("reads").get(0)
                .getAsJsonObject();
        reader.addProperty("regionId", "REGION.1");
        reader.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                readerOccurrence);
        JsonObject writer = envelope.getAsJsonArray("versions").get(0)
                .getAsJsonObject();
        writer.addProperty("regionId", "REGION.1");
        writer.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                writerOccurrence);
        SharedStateEvidence.normalizeGuards(envelope);
        return RecordedSharedStateFixtures.recordedMember(envelope,
                RecordedSharedStateFixtures.twoWriterLedger(),
                "example.State#value");
    }

    @Test
    public void selectedInputAuthorityIsCaseLocal() {
        assertFalse(ConcolicSmtComposer.authorityCasesDefinitelyAmbiguous(
                Arrays.asList("case_a", "case_b")));
        assertTrue(ConcolicSmtComposer.authorityCasesDefinitelyAmbiguous(
                Arrays.asList("case_a", "case_a")));
        assertTrue(ConcolicSmtComposer.authorityCasesDefinitelyAmbiguous(
                Arrays.asList("true", "case_a")));
        assertEquals("(= (+ (ite case_a 1 0) (ite case_b 1 0)) 1)",
                ConcolicSmtComposer.exactlyOneAuthority(
                        Arrays.asList("case_a", "case_b")));
    }

    @Test
    public void recordedReadSupersedesValueFrontierRoot()
            throws Exception {
        ConcolicSmtComposer.Result result = exactGolden(10, "CLOSED", true);

        JsonObject target = null;
        for (JsonElement element
                : result.manifest.getAsJsonArray("selectedInputLedger")) {
            JsonObject row = element.getAsJsonObject();
            if ("REGION.0.in.0".equals(row.get("portId").getAsString())) {
                target = row;
                break;
            }
        }
        assertTrue(result.manifest.toString(), target != null);
        assertEquals(ConcolicSmtComposer.READ_FROM_ARM,
                target.get("authority").getAsString());
        assertEquals(target.toString(), 1,
                target.getAsJsonArray("evidence").size());
        assertEquals(target.toString(), ConcolicSmtComposer.READ_FROM_ARM,
                target.getAsJsonArray("evidence").get(0).getAsJsonObject()
                        .get("authority").getAsString());
        assertTrue(target.toString(), target.getAsJsonArray("uses")
                .get(0).getAsJsonObject().get("caseGuard").getAsString()
                .startsWith("case_selector__"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= (+ (ite true 1 0) (ite true 1 0)) 1)"));
        assertFalse(result.manifest.toString(), result.manifest
                .getAsJsonArray("gaps").toString().contains(
                        ConcolicSmtComposer.INPUT_AUTHORITY_AMBIGUOUS));
    }

    /** One unsatisfiable composition whose recorded model stays partial. */
    private ConcolicSmtComposer.Result unsatisfiablePartialGolden()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.PARTIAL", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        edge.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        RelationSummary producer = withRecordedSharedState(
                summary("PARTIAL", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge)));
        return composeTarget(fatalInstance, producer,
                binary(integer(0), "==", integer(1)), edge);
    }

    private static JsonObject reachCondition(
            ConcolicSmtComposer.Result result, JsonObject manifest)
            throws Exception {
        return BooleanReachConditionExtractor.extract(result.smtLib, manifest,
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1),
                8, 64).getAsJsonObject("reachCondition");
    }


    /**
     * The same result, once it is known to carry no composition gap.
     *
     * <p>A gapped query fails closed with a literal {@code false}, so every
     * row of a truth table read off one would be unsat for a reason that has
     * nothing to do with the recorded model. Pinning the state here is what
     * makes the unsat rows below evidence about read-from semantics.</p>
     */
    private static ConcolicSmtComposer.Result ready(
            ConcolicSmtComposer.Result result) {
        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertFalse(result.smtLib, result.smtLib.contains("(assert false)"));
        return result;
    }

    private ConcolicSmtComposer.Result exactGolden() throws Exception {
        return exactGolden(10);
    }

    private ConcolicSmtComposer.Result exactGolden(int value)
            throws Exception {
        return exactGolden(value, "CLOSED");
    }

    /**
     * One proven read-from, with the target asking for {@code value} and the
     * producer declaring {@code coverageState} about its own path set. A
     * {@code null} state is the relation that declared nothing.
     */
    private ConcolicSmtComposer.Result exactGolden(int value,
                                                   String coverageState)
            throws Exception {
        return exactGolden(value, coverageState, false);
    }

    private ConcolicSmtComposer.Result exactGolden(int value,
                                                   String coverageState,
                                                   boolean targetFrontier)
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.EXACT", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        edge.addProperty("fieldVersionId", 11);
        edge.addProperty("readEventId", 21);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        // A second writer of the same consumer port that nothing decided.
        // The recorded answer names the first one, so this candidate must be
        // dropped rather than composed - as an alternative it would contradict
        // the proof, and beside it the port would be bound twice and the two
        // producers equated.
        JsonObject competing = binding("EDGE.COMPETING", outerInstance,
                "REGION.1.out.1", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_EXACT, "UNIQUE_VERSION", 11L);
        // The selected edge and the VM version must name the same exact
        // producer occurrence; region/type similarity is not provenance.
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                        outerInstance);
        JsonObject read = envelope.getAsJsonArray("reads").get(0)
                .getAsJsonObject();
        read.addProperty("regionId", "REGION.0");
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                fatalInstance);
        SharedStateEvidence.normalizeGuards(envelope);
        RelationSummary producer = declaring(withRecorded(
                withCompetingOutput(summary("EXACT", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Arrays.asList(edge, competing))), envelope,
                RecordedSharedStateFixtures.twoWriterLedger()),
                coverageState);
        JsonObject producerRegion = region("REGION.1", true, true);
        producerRegion.getAsJsonArray("outputs").add(
                statePort("REGION.1.out.1", "int",
                        "<Test: int competing>"));
        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference("REGION.0.in.0", "I"), "==",
                integer(value)));
        JsonObject targetRegion = region("REGION.0", true, false);
        if (targetFrontier) {
            targetRegion.getAsJsonArray("symbolicInputs").get(0)
                    .getAsJsonObject().addProperty("dependencyRole",
                            DependencyRole.VALUE_FRONTIER);
        }
        return compose(fatalInstance, Collections.singletonList(producer),
                Arrays.asList(targetRegion, producerRegion), constraints, edge,
                competing);
    }

    /**
     * One undecided read of two competing writers.
     *
     * @param value        the value the target predicate asks the read for
     * @param satisfiable  whether the second writer's recorded path guard can
     *                     hold
     * @param orderedWrites whether the recorded ledger holds the two writes
     */
    private ConcolicSmtComposer.Result guardedGolden(
            int value, boolean satisfiable, boolean orderedWrites)
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonArray candidates = new JsonArray();
        candidates.add(RecordedSharedStateFixtures.candidate("rf1", 11L,
                RecordedSharedStateFixtures.constant(1), null, 21L, 12L));
        candidates.add(RecordedSharedStateFixtures.candidate("rf2", 12L,
                RecordedSharedStateFixtures.constant(2), satisfiable
                        ? RecordedSharedStateFixtures.guard("G")
                        : RecordedSharedStateFixtures.unsatisfiableGuard(),
                21L, 11L));
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(21L,
                "M_I_unknownWriter_7_24_r21"));
        return guardedGolden(fatalInstance, outerInstance, candidates, value,
                orderedWrites);
    }

    /** A watched location whose writers none of the evidence can name. */
    private ConcolicSmtComposer.Result noCandidateGolden() throws Exception {
        JsonArray candidates = new JsonArray();
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(21L,
                "M_I_unknownWriter_7_24_r21"));
        return guardedGolden("REGION.0@Test#call30", "REGION.1@Test#call20",
                candidates, 7, true);
    }

    private ConcolicSmtComposer.Result guardedGolden(
            String fatalInstance, String outerInstance, JsonArray candidates,
            int value, boolean orderedWrites) throws Exception {
        JsonObject edge = binding("EDGE.GUARDED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        edge.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        ownWriterVersions(envelope, "REGION.0", fatalInstance,
                "TASK.TARGET");
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        fatalInstance);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24, candidates);
        ownGuardedCandidates(guarded, "REGION.0", "TASK.TARGET");
        SharedStateEvidence.normalizeGuards(guarded);
        RelationSummary producer = summary("GUARDED",
                outerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(edge));
        JsonObject ledger = orderedWrites
                ? RecordedSharedStateFixtures.twoWriterLedger()
                : readOnlyLedger();
        JsonArray constraints = new JsonArray();
        constraints.add(binary(guarded, "==", integer(value)));
        JsonObject fatal = fatalQuery(fatalInstance, constraints, edge);
        JsonObject fatalPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        fatalPath.addProperty("sourceTaskId", "TASK.TARGET");
        fatalPath.add(SharedStateEvidence.RECORDED_FIELD,
                        RecordedSharedStateFixtures.recordedMember(envelope,
                                ledger, "example.State#value"));
        return composeFatal(fatalInstance, Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal,
                Collections.singletonList(edge));
    }

    /** A ledger that holds the read and neither of the two writes. */
    private static JsonObject readOnlyLedger() {
        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(21L, "FIELD_READ", 103L,
                "REGION.reader"));
        return RecordedSharedStateFixtures.ledgerEnvelope(events,
                new JsonArray());
    }

    private RelationSummary configuredSourceProducer(
            String occurrence, String sourceId, String field, String raw) {
        JsonObject row = summary("SOURCE.SELECTOR", occurrence, 9,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList()).toJson();
        JsonArray cases = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        JsonObject sourceSeven = cases.get(0).getAsJsonObject();
        sourceSeven.addProperty("caseId", "CASE.SOURCE.7");
        sourceSeven.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        sourceSeven.addProperty("sourceTaskId", "TASK.SOURCE.7");
        sourceSeven.getAsJsonObject("guard")
                .getAsJsonArray("conditions").add(binary(
                        reference(raw, "I"), "==", integer(7)));
        SymbolicSourceEvidence.writeTo(sourceSeven,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        publishPhase(occurrence), sourceId, occurrence,
                        field, reference(raw, "I"), 1, false, null)));
        JsonObject sourceNine = sourceSeven.deepCopy();
        sourceNine.addProperty("caseId", "CASE.SOURCE.9");
        sourceNine.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        sourceNine.addProperty("sourceTaskId", "TASK.SOURCE.9");
        JsonArray nineGuard = new JsonArray();
        nineGuard.add(binary(reference(raw, "I"), "==", integer(9)));
        sourceNine.getAsJsonObject("guard").add("conditions", nineGuard);
        cases.add(sourceNine);
        return RelationSummary.decode(row);
    }


    private static String publishPhase(String occurrence) {
        return "SOURCE_PHASE.PUBLISH."
                + CanonicalJson.sha256(occurrence).substring(0, 16);
    }

    private static String consumePhase(String occurrence) {
        return "SOURCE_PHASE.CONSUME."
                + CanonicalJson.sha256(occurrence).substring(0, 16);
    }

    private static String configuredRaw(String phase, String source,
                                        String suffix) {
        return "M_I_field_" + SymbolicSourceEvidence.engineLabelForPhase(
                phase, source) + "_" + suffix;
    }

    @Test
    public void observedCoverageRootAndProvenanceMustNameOneState()
            throws Exception {
        assertObservedCoverage("PARTIAL", "PARTIAL", true);
        assertObservedCoverage("SEED_ONLY", "SEED_ONLY", true);
        assertObservedCoverage("CLOSED", "PARTIAL", false);
        assertObservedCoverage("PARTIAL", "SEED_ONLY", false);
        assertObservedCoverage("CLOSED", "CLOSED", false);
    }

    @Test
    public void unsatClosureRequiresClosedProducerAndTargetPathSets() {
        RelationSummary closed = summary("UNSAT.CLOSED",
                "REGION.1@Test#closed", 1,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject fatal = new JsonObject();
        fatal.add("coverageGaps", new JsonArray());
        JsonObject complete = ConcolicSmtComposer.unsatClosureEvidence(
                true, Collections.singletonList(closed), fatal, true, 0);
        assertTrue(complete.toString(), complete.get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());

        RelationSummary partial = declaring(closed, "PARTIAL");
        JsonObject producerOpen = ConcolicSmtComposer.unsatClosureEvidence(
                true, Collections.singletonList(partial), fatal, true, 0);
        assertFalse(producerOpen.toString(), producerOpen.get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());
        assertEquals(1, producerOpen.getAsJsonArray(
                "partialProducerSummaryIds").size());

        JsonObject targetOpen = new JsonObject();
        JsonArray targetGaps = new JsonArray();
        targetGaps.add(CoverageDivergence.of(
                CoverageDivergence.Kind.TARGET,
                "PATH_FLIP_REPLAY_NOT_ADMITTED", "QUERY.TARGET", "miss"));
        targetOpen.add("coverageGaps", targetGaps);
        JsonObject targetIncomplete = ConcolicSmtComposer
                .unsatClosureEvidence(true,
                        Collections.singletonList(closed), targetOpen, true,
                        1);
        assertFalse(targetIncomplete.toString(), targetIncomplete.get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());
        assertEquals(1, targetIncomplete.get(
                "targetCoverageGapCount").getAsInt());

        assertFalse(ConcolicSmtComposer.unsatClosureEvidence(true,
                Collections.singletonList(closed), fatal, false, 0).get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());
    }

    private static void assertObservedCoverage(String rootState,
                                               String nestedState,
                                               boolean accepted)
            throws Exception {
        JsonObject summary = new JsonObject();
        summary.addProperty("pathCoverageState", rootState);
        JsonObject relation = new JsonObject();
        relation.addProperty("guardProjection",
                "SELECTIVE_SYMBOLIC_BRANCH_SLICE");
        JsonArray cases = new JsonArray();
        cases.add(new JsonObject());
        relation.add("cases", cases);
        summary.add("regionRelation", relation);

        JsonObject coverage = new JsonObject();
        coverage.addProperty("schemaVersion", 1);
        coverage.addProperty("kind", "OBSERVED_PATH_COVERAGE");
        coverage.addProperty("authority",
                "IMPORTED_VM_PATH_UNDERAPPROX_V1");
        coverage.addProperty("complete", false);
        coverage.addProperty("coverageState", nestedState);
        coverage.addProperty("constraintProjectionAuthority",
                "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1");
        coverage.addProperty("observedCaseCount", 1);
        coverage.addProperty("observedPathCount", 1);
        coverage.addProperty("observedPathSetHash", "HASH.ONE.PATH");
        try {
            ConcolicSmtComposer.requireObservedCoverage(summary, coverage);
            if (!accepted) fail("inconsistent observed coverage was accepted");
        } catch (IOException rejected) {
            if (accepted) throw rejected;
            assertTrue(rejected.getMessage(), rejected.getMessage().contains(
                    "Malformed observed-path"));
        }
    }

    /**
     * A second output of the same producer, carrying a different value.
     *
     * <p>It is what makes the competing candidate observable: if the recorded
     * answer's port were bound twice, the two producers would be equated and
     * 10 = 20 would make the whole query unsatisfiable.</p>
     */
    private static RelationSummary withCompetingOutput(
            RelationSummary summary) {
        JsonObject row = summary.toJson();
        JsonObject slice = emptySlice("REGION.1.out.1",
                "<Test: int competing>");
        OutputClosureContract second = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1", Collections.<String>emptyList(),
                "REGION.1.out.1", "<Test: int competing>", "REGION_OUTPUT",
                "int", slice);
        OutputClosureCodec.writeTo(row, OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(row), second)));
        row.getAsJsonObject("regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject().getAsJsonObject("outputExpressions")
                .add("REGION.1.out.1", integer(20));
        return RelationSummary.decode(row);
    }

    private static RelationSummary withoutCausalEdges(
            RelationSummary summary, String outputPort) {
        JsonObject row = summary.toJson();
        for (JsonElement element : row.getAsJsonObject(
                OutputClosureContract.FIELD).getAsJsonArray("members")) {
            JsonObject member = element.getAsJsonObject();
            if (outputPort.equals(member.getAsJsonObject("output")
                    .get("portId").getAsString())) {
                member.getAsJsonObject("slice").add("causalEdgeIds",
                        new JsonArray());
            }
        }
        return RelationSummary.decode(row);
    }

    /** The same relation, restating - or dropping - its declared coverage. */
    private static RelationSummary declaring(RelationSummary summary,
                                             String coverageState) {
        JsonObject row = summary.toJson();
        if (coverageState == null) {
            row.remove("pathCoverageState");
        } else {
            row.addProperty("pathCoverageState", coverageState);
        }
        return RelationSummary.decode(row);
    }

    private static RelationSummary withRecorded(RelationSummary summary,
                                                JsonObject envelope,
                                                JsonObject ledger) {
        JsonObject row = summary.toJson();
        row.add(SharedStateEvidence.RECORDED_FIELD,
                RecordedSharedStateFixtures.recordedMember(envelope, ledger,
                        "example.State#value"));
        return RelationSummary.decode(row);
    }

    private ConcolicSmtComposer.Result composeTarget(
            String fatalInstance, RelationSummary producer,
            JsonObject targetPredicate, JsonObject firstHop)
            throws Exception {
        JsonArray constraints = new JsonArray();
        constraints.add(targetPredicate);
        return compose(fatalInstance, Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), constraints,
                firstHop);
    }

    /** The same query with one extra assumption, for one truth-table row. */
    private static String assuming(String smtLib, String... assumptions) {
        int check = smtLib.lastIndexOf("(check-sat)");
        StringBuilder query = new StringBuilder(smtLib.substring(0, check));
        for (String assumption : assumptions) {
            query.append("(assert ").append(assumption).append(')')
                    .append(System.lineSeparator());
        }
        return query.append("(check-sat)").append(System.lineSeparator())
                .toString();
    }

    /** Runs one query through the real solver and returns its answer. */
    private static String z3(String smtLib) throws Exception {
        Process process = new ProcessBuilder("z3", "-smt2", "-in")
                .redirectErrorStream(true).start();
        process.getOutputStream().write(
                smtLib.getBytes(StandardCharsets.UTF_8));
        process.getOutputStream().close();
        String output = new String(readAll(process.getInputStream()),
                StandardCharsets.UTF_8).trim();
        process.waitFor();
        int newline = output.indexOf('\n');
        return newline < 0 ? output : output.substring(0, newline).trim();
    }

    private static byte[] readAll(java.io.InputStream stream)
            throws java.io.IOException {
        java.io.ByteArrayOutputStream buffer =
                new java.io.ByteArrayOutputStream();
        byte[] chunk = new byte[8192];
        int read;
        while ((read = stream.read(chunk)) >= 0) buffer.write(chunk, 0, read);
        return buffer.toByteArray();
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start()
                    .waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }

    /**
     * Decorates one merged relation with the shared state its executions
     * recorded: two competing writers of one location, a guarded read of it
     * in the target region, and the ledger that orders the two writers.
     */
    private static RelationSummary withRecordedSharedState(
            RelationSummary summary) {
        return withRecordedSharedState(summary,
                RecordedSharedStateFixtures.twoWriterLedger());
    }

    private static RelationSummary withRecordedSharedState(
            RelationSummary summary, JsonObject ledger) {
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        JsonObject summaryRow = summary.toJson();
        JsonObject selectedCase = summaryRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        ownWriterVersions(envelope, "REGION.1", summary.occurrenceId(),
                selectedCase.get("sourceTaskId").getAsString());
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty("regionId", "REGION.0");
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        "REGION.0@Test#call30");
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24);
        ownGuardedCandidates(guarded, "REGION.1",
                selectedCase.get("sourceTaskId").getAsString());
        SharedStateEvidence.normalizeGuards(guarded);
        // The guarded term rides with the writer's value, which is where the
        // composer's expression scan finds it.
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .add("expression", guarded);
        // The runtime records the declared field beside the VM's own location
        // identity, and a gate needs it: the location key does not survive
        // into a second session, and the field does.
        selectedCase.add(SharedStateEvidence.RECORDED_FIELD,
                RecordedSharedStateFixtures.recordedMember(envelope, ledger,
                        "example.State#value"));
        return RelationSummary.decode(summaryRow);
    }

    /** Gives the fixture's copied versions one exact selected case owner. */
    private static void ownWriterVersions(JsonObject envelope,
                                          String regionId,
                                          String occurrenceId,
                                          String taskId) {
        for (JsonElement element : envelope.getAsJsonArray("versions")) {
            JsonObject version = element.getAsJsonObject();
            version.addProperty("regionId", regionId);
            version.addProperty("taskId", taskId);
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    occurrenceId);
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    "TEST_DRIVER/test#epoch0");
        }
    }

    /** Aligns copied RF arms with the selected case owning their versions. */
    private static void ownGuardedCandidates(JsonObject guarded,
                                             String regionId,
                                             String taskId) {
        for (JsonElement element : guarded.getAsJsonArray("candidates")) {
            JsonObject candidate = element.getAsJsonObject();
            if (candidate.get("unknown").getAsBoolean()) continue;
            candidate.addProperty("regionId", regionId);
            candidate.addProperty("taskId", taskId);
        }
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries,
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries, regionRows,
                targetConstraints(), firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonArray constraints,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries, regionRows, constraints,
                null, firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonArray constraints,
            java.util.List<JsonObject> edgeValidations,
            JsonObject... firstHops) throws Exception {
        return composeFatal(fatalInstance, summaries, regionRows,
                fatalQuery(fatalInstance, constraints, firstHops),
                edgeValidations);
    }

    /**
     * OCC-1/HDFS-11741: a guarded MAP-state read whose arm set the VM had to
     * truncate at the path-condition byte cap has no arm the codec can
     * reconstruct, so it fails the formula closed -- even when a compact base
     * INITIAL arm survives beside the truncated one.  The earlier build
     * admitted such a read as a SAT under-approximation pinned to that INITIAL
     * version; that pin has been deleted (a real throw witness now lowers the
     * full recorded removeExpiredKeys writer set arm for arm), so a genuinely
     * truncated read is the honest fail-close it always was for a read with no
     * admissible arm.
     */
    @Test
    public void aTruncatedMapReadWithAnInitialArmStillFailsClosed()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        JsonObject guarded = mapReadWithInitialAndTruncatedArm(21L, 7L);
        JsonArray constraints = new JsonArray();
        // The throw predicate: allKeys.get(key) is null.
        constraints.add(binary(guarded, "==", nullRef()));
        JsonObject fatal = fatalQuery(fatalInstance, constraints);

        ConcolicSmtComposer.Result result = composeFatal(fatalInstance,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal, null);

        assertTrue("a truncated read has no admissible arm -> fail-closed: "
                + result.smtLib, result.smtLib.contains("(assert false)"));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertFalse("the deleted pin emits no pinned-initial coverage: "
                + result.manifest, result.manifest.toString()
                        .contains("RECORDED_MAP_READ_PINNED_INITIAL"));
        assertFalse("the deleted pin is no longer refused by name: "
                + result.manifest, result.manifest.toString()
                        .contains("SAT_WITNESS_UNDER_APPROXIMATION"));
    }

    /**
     * The same truncated map read WITHOUT a base INITIAL arm has no recorded
     * version compact enough to pin to, so it stays the hard fail-closed
     * refusal it always was.
     */
    @Test
    public void aTruncatedMapReadWithNoInitialArmStaysFailClosed()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        JsonObject guarded = mapReadWithOnlyTruncatedArm(22L, 8L);
        JsonArray constraints = new JsonArray();
        constraints.add(binary(guarded, "==", nullRef()));
        JsonObject fatal = fatalQuery(fatalInstance, constraints);

        ConcolicSmtComposer.Result result = composeFatal(fatalInstance,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal, null);

        assertTrue("no initial arm to pin -> still fail-closed: "
                + result.smtLib, result.smtLib.contains("(assert false)"));
        assertFalse("no pin was emitted",
                result.manifest.toString()
                        .contains("RECORDED_MAP_READ_PINNED_INITIAL"));
    }

    /** {@code (VRef nullRef)} as a recorded null literal. */
    private static JsonObject nullRef() {
        JsonObject n = new JsonObject();
        n.addProperty("_type", "ConstExpr");
        n.addProperty("_java_type", "L");
        n.addProperty("_exp", "N");
        return n;
    }

    private static JsonObject assocStateSymbol(String symbol) {
        JsonObject id = new JsonObject();
        id.addProperty("_type", "SymbolExpression");
        id.addProperty("_java_type", "java/util/HashMap");
        id.addProperty("_exp", symbol);
        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.add("arguments", new JsonArray());
        state.add("receiver", id);
        state.addProperty("_java_type", "L");
        return state;
    }

    private static JsonObject assocPut(JsonElement receiver, int key,
                                       int value) {
        JsonArray arguments = new JsonArray();
        arguments.add(integer(key));
        arguments.add(integer(value));
        JsonObject put = new JsonObject();
        put.addProperty("_type", "ContainerRelation");
        put.addProperty("shape", "ASSOCIATIVE");
        put.addProperty("operation", "PUT");
        put.addProperty("_java_type", "java/util/Map");
        put.add("receiver", receiver.deepCopy());
        put.add("arguments", arguments);
        return put;
    }

    private static void decorateMapOccurrence(
            JsonObject pathCase, String planned, int ordinal,
            JsonObject expression) {
        String occurrence = planned + "#a" + ordinal;
        String task = "TASK.MAP.TIMELINE.A" + ordinal;
        pathCase.addProperty("caseId", "CASE.MAP.TIMELINE.A" + ordinal);
        pathCase.addProperty("sourceTaskId", task);
        pathCase.addProperty("occurrenceId", occurrence);
        pathCase.addProperty(PathObservation.ACTIVATION_ORDINAL, ordinal);
        pathCase.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, planned);

        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", 59L);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 100L + ordinal);
        version.addProperty("versionKind", "STATE_PUT");
        version.addProperty("writerContextId", 200L + ordinal);
        version.addProperty("writerJavaThreadId", 300L + ordinal);
        version.addProperty("writerStep", ordinal);
        version.addProperty("regionId", "REGION.1");
        version.addProperty("taskId", task);
        version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                "TEST_DRIVER/test#epoch0");
        version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                occurrence);
        version.addProperty("volatileWrite", false);
        version.addProperty("fingerprintKind", "NONE");
        version.addProperty("fingerprint", 0L);
        version.add("expression", expression.deepCopy());
        version.add("pathGuard", null);
        version.addProperty("versionOrdinal", 1);
        version.addProperty("writerEventId", 100L + ordinal);
        JsonArray versions = new JsonArray();
        versions.add(version);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("selected", true);
        envelope.add("location", location);
        envelope.addProperty("writerSetComplete", true);
        envelope.addProperty("versionsDropped", 0);
        envelope.addProperty("serializationTruncated", false);
        envelope.addProperty("readsDropped", 0);
        envelope.addProperty("readLogTruncated", false);
        envelope.add("versions", versions);
        envelope.add("reads", new JsonArray());
        JsonObject record = SharedStateEvidence.versionsRecord(
                SharedStateEvidence.locationKey(envelope), envelope,
                RecordedEvidenceIdentity.of("", "workload#1", task,
                        occurrence, "TEST_DRIVER/test#epoch0", ordinal));
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        carrier.addProperty("declaringClass", "example.State");
        carrier.addProperty("fieldName", "values");
        carrier.addProperty("descriptor", "Ljava/util/Map;");
        carrier.addProperty("index", -1);
        carrier.addProperty("receiverObjectId", 77L);
        carrier.addProperty("fieldKey",
                "example.State#values:Ljava/util/Map;");
        record.add("carrier", carrier);
        pathCase.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.singletonList(record), null));
    }

    private static JsonObject truncated() {
        JsonObject t = new JsonObject();
        t.addProperty("_type", "TruncatedExpression");
        t.addProperty("expressionAuthority",
                "VM_SERIALIZATION_TRUNCATION_V1");
        t.addProperty("truncationKind", "PATH_CONDITION_RANGE_BYTE_LIMIT");
        return t;
    }

    /** {@code get(key)} over a map version expression. */
    private static JsonObject mapGet(JsonElement mapState, int key) {
        JsonObject keyExpr = new JsonObject();
        keyExpr.addProperty("_type", "ConstExpr");
        keyExpr.addProperty("_java_type", "I");
        keyExpr.addProperty("_exp", "Y_I_" + key);
        JsonArray args = new JsonArray();
        args.add(keyExpr);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ContainerRelation");
        read.addProperty("shape", "ASSOCIATIVE");
        read.addProperty("operation", "READ");
        read.add("arguments", args);
        read.add("receiver", mapState);
        read.addProperty("_java_type", "L");
        return read;
    }

    private JsonObject mapReadWithInitialAndTruncatedArm(long readEventId,
                                                         long owner) {
        JsonArray candidates = new JsonArray();
        // rf1: the INITIAL version -- get over the bare region-entry map.
        candidates.add(mapReadArm("rf1", 11L,
                mapGet(assocStateSymbol("M_L'java/util/HashMap'_" + owner),
                        534995622), readEventId, 12L));
        // rf2: a later version whose value expression the VM truncated.
        candidates.add(mapReadArm("rf2", 12L, mapGet(truncated(), 534995622),
                readEventId, 11L));
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(
                readEventId, "M_L_unknownWriter_" + owner + "_r"
                        + readEventId));
        return mapGuardedRead(readEventId, owner, candidates);
    }

    private JsonObject mapReadWithOnlyTruncatedArm(long readEventId,
                                                   long owner) {
        JsonArray candidates = new JsonArray();
        candidates.add(mapReadArm("rf1", 11L, mapGet(truncated(), 534995622),
                readEventId, 12L));
        candidates.add(mapReadArm("rf2", 12L, mapGet(truncated(), 534995622),
                readEventId, 11L));
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(
                readEventId, "M_L_unknownWriter_" + owner + "_r"
                        + readEventId));
        return mapGuardedRead(readEventId, owner, candidates);
    }

    private static JsonObject mapReadArm(String selector, long fieldVersionId,
                                         JsonElement value, long readEventId,
                                         long... competitors) {
        JsonObject candidate = RecordedSharedStateFixtures.candidate(
                selector, fieldVersionId, value, null, readEventId,
                competitors);
        candidate.addProperty("versionKind",
                fieldVersionId == 11L ? "INITIAL" : "STATE_PUT");
        return candidate;
    }

    private JsonObject mapGuardedRead(long readEventId, long owner,
                                      JsonArray candidates) {
        JsonObject node = RecordedSharedStateFixtures.guardedRead(
                readEventId, owner, SharedStateEvidence.MAP_STATE_SLOT,
                candidates);
        node.getAsJsonObject("location").addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        node.addProperty("_java_type", "L");
        SharedStateEvidence.normalizeGuards(node);
        return node;
    }

    private ConcolicSmtComposer.Result composeFatal(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonObject fatalRow,
            java.util.List<JsonObject> edgeValidations) throws Exception {
        Path directory = temporary.newFolder().toPath();
        Path fatal = directory.resolve("fatal.jsonl");
        Path summaryFile = directory.resolve("summaries.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("candidate.smt2");
        Path manifest = directory.resolve("manifest.json");

        writeJsonl(fatal, fatalRow);
        StringBuilder encoded = new StringBuilder();
        for (RelationSummary summary : summaries) {
            encoded.append(summary.toJson()).append('\n');
        }
        Files.write(summaryFile, encoded.toString().getBytes(
                StandardCharsets.UTF_8));
        writeJsonl(regions, regionRows.toArray(
                new JsonObject[regionRows.size()]));

        Path runtimePlan = directory.resolve("runtime_plan.jsonl");
        Files.write(runtimePlan, RuntimePlanArtifact.encode(
                java.util.Collections.<JsonObject>emptyList(),
                edgeValidations == null
                        ? java.util.Collections.<JsonObject>emptyList()
                        : edgeValidations,
                regionRows).getBytes(StandardCharsets.UTF_8));
        java.util.List<String> argv = new java.util.ArrayList<>(
                Arrays.asList(
                        "--fatal-query", fatal.toString(),
                        "--summaries", summaryFile.toString(),
                        "--runtime-plan", runtimePlan.toString(),
                        "--output", output.toString(),
                        "--manifest", manifest.toString(),
                        "--fatal-region", "REGION.0",
                        "--occurrence-id", fatalInstance));
        return ConcolicSmtComposer.compose(
                ConcolicSmtComposer.Arguments.parse(
                        argv.toArray(new String[argv.size()])));
    }

    /**
     * A producer whose closure also holds the in-region port that feeds the
     * demanded one, carrying a recorded value for it or not.
     */
    private static RelationSummary widerSummary(
            String id, String instance, int value, boolean recordsFeeder,
            java.util.List<JsonObject> bindings) {
        JsonObject demandedSlice = emptySlice("REGION.1.out.0",
                "<Test: int output>");
        JsonObject feederSlice = emptySlice("REGION.1.out.1",
                "<Test: int feeder>");
        JsonArray causalEdges = demandedSlice.getAsJsonArray("causalEdgeIds");
        for (JsonObject binding : bindings) {
            if ("REGION.1.out.0".equals(
                    binding.get("fromOutputPort").getAsString())) {
                causalEdges.add(binding.get("edgeId").getAsString());
            }
        }
        OutputClosureContract closure = OutputClosureCodec.merge(
                Arrays.asList(
                        OutputClosureCodec.singleton("REL.REGION.1",
                                "REGION.1", Collections.<String>emptyList(),
                                "REGION.1.out.0", "<Test: int output>",
                                "REGION_OUTPUT", "int", demandedSlice),
                        OutputClosureCodec.singleton("REL.REGION.1",
                                "REGION.1", Collections.<String>emptyList(),
                                "REGION.1.out.1", "<Test: int feeder>",
                                "REGION_OUTPUT", "int", feederSlice)));

        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", RelationSummary.SCHEMA_VERSION);
        row.addProperty("kind", RelationSummary.KIND);
        row.addProperty("summaryId", "SUMMARY." + id);
        row.addProperty("sourceKey", "TEST_DRIVER/test#epoch0");
        row.addProperty("regionId", "REGION.1");
        row.addProperty("occurrenceId", instance);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(row);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray encodedBindings = new JsonArray();
        for (JsonObject binding : bindings) {
            encodedBindings.add(binding.deepCopy());
        }
        row.add("edgeBindings", encodedBindings);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE." + id);
        path.addProperty("occurrenceId", instance);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        path.addProperty("sourceTaskId", "TASK." + id);
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", integer(value));
        // Fail-closed: a declared port the run recorded no value for counts
        // for nothing, so this producer cannot outrank one that produced
        // something.
        if (recordsFeeder) outputs.add("REGION.1.out.1", integer(value + 1));
        path.add("outputExpressions", outputs);
        JsonArray cases = new JsonArray();
        cases.add(path);
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        row.addProperty("pathCoverageState", "CLOSED");
        return RelationSummary.decode(row);
    }

    private static RelationSummary summary(
            String id, String instance, int value,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, integer(value), inputPorts, bindings);
    }

    private static RelationSummary summary(
            String id, String instance, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, output, inputPorts, bindings, "int");
    }

    private static RelationSummary summary(
            String id, String instance, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings, String outputJavaType) {
        JsonObject slice = emptySlice("REGION.1.out.0",
                "<Test: " + outputJavaType + " output>");
        JsonArray inputs = new JsonArray();
        for (String input : inputPorts) inputs.add(input);
        slice.add("inputPorts", inputs);
        JsonArray causalEdges = slice.getAsJsonArray("causalEdgeIds");
        for (JsonObject binding : bindings) {
            if ("REGION.1.out.0".equals(
                    binding.get("fromOutputPort").getAsString())) {
                causalEdges.add(binding.get("edgeId").getAsString());
            }
        }
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1", Collections.<String>emptyList(), "REGION.1.out.0",
                "<Test: " + outputJavaType + " output>", "REGION_OUTPUT",
                outputJavaType, slice);

        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", RelationSummary.SCHEMA_VERSION);
        row.addProperty("kind", RelationSummary.KIND);
        row.addProperty("summaryId", "SUMMARY." + id);
        row.addProperty("sourceKey", "TEST_DRIVER/test#epoch0");
        row.addProperty("regionId", "REGION.1");
        row.addProperty("occurrenceId", instance);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(row);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray encodedBindings = new JsonArray();
        for (JsonObject binding : bindings) {
            encodedBindings.add(binding.deepCopy());
        }
        row.add("edgeBindings", encodedBindings);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE." + id);
        path.addProperty("occurrenceId", instance);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        path.addProperty("sourceTaskId", "TASK." + id);
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", output);
        path.add("outputExpressions", outputs);
        JsonArray cases = new JsonArray();
        cases.add(path);
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        // What a closed worklist's merge declares, and what the acceptance
        // gate reads: this relation's own path set is the one it published.
        row.addProperty("pathCoverageState", "CLOSED");
        return RelationSummary.decode(row);
    }

    private static JsonObject emptySlice(String port, String cell) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        return slice;
    }

    private static JsonObject fatalQuery(
            String fatalInstance, JsonArray constraints,
            JsonObject... firstHops) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion",
                TargetReachPathQueryBuilder.SCHEMA_VERSION);
        fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        fatal.addProperty("queryKey", "QUERY.TEST.FATAL");
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("occurrenceId", fatalInstance);
        fatal.addProperty("sourceKey", "TEST_DRIVER/test#epoch0");
        fatal.addProperty("targetSiteId", "<Test: void consume()>#u1");
        fatal.addProperty("targetOccurrence", 1);
        fatal.addProperty("requiredTakenOutcome", false);
        fatal.addProperty("constraintAuthority",
                "RECORDED_TARGET_PREFIX_V1");
        JsonObject path = new JsonObject();
        path.add("constraints", constraints.deepCopy());
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        path.addProperty("desiredTakenOutcome", false);
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.SOURCE_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder.SOURCE_FATAL_BRANCH_AUTHORITY);
        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", "<Test: void consume()>#u1");
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        path.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        JsonArray paths = new JsonArray();
        paths.add(path);
        fatal.add("paths", paths);
        fatal.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        if (constraints.size() == 0) {
            throw new IllegalArgumentException(
                    "test fatal query requires a target predicate");
        }
        JsonElement requiredPredicate = constraints.get(
                constraints.size() - 1);
        BranchWitness witness = BranchWitness.vmPc(
                "<Test: void consume()>#u1", "<Test: void consume()>",
                1, 1, true, BranchPredicateAlgebra.complement(
                requiredPredicate),
                0, metadata);
        path.add(TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS,
                witness.toJson());
        fatal.add("seedReplayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), witness).toJson());
        LoopBoundPolicy.cfgBackedges(8).writeTo(fatal);

        JsonArray selectedTargetBindings = new JsonArray();
        for (JsonObject firstHop : firstHops) {
            selectedTargetBindings.add(firstHop.deepCopy());
        }
        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", fatalInstance);
        fatal.add("symbolicContext", context);
        fatal.add("selectedTargetBindings", selectedTargetBindings);
        return fatal;
    }

    /** Converts the fixture's seed-side attestation into an exact hit. */
    private static void markRequiredTargetPath(JsonObject path) {
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder.REQUIRED_FATAL_BRANCH_AUTHORITY);
        path.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);
        JsonArray constraints = path.getAsJsonArray("constraints");
        JsonObject witness = path.getAsJsonObject(
                TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS);
        witness.addProperty("sourceTakenOutcome", false);
        witness.add("sourceSatisfiedPredicate",
                constraints.get(constraints.size() - 1).deepCopy());
    }

    /** One non-constant target predicate for fixtures without a region port. */
    private static JsonArray targetConstraints() {
        JsonArray result = new JsonArray();
        result.add(binary(reference("M_I_field_TEST_TARGET_GATE", "I"),
                ">", integer(0)));
        return result;
    }

    private static JsonObject binding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort, long writer, long reader) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("toRegion", regionOf(toPort));
        binding.addProperty("fromOccurrenceId", fromInstance);
        binding.addProperty("toOccurrenceId", toInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toInputPort", toPort);
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("writerLaneId", "lane.writer");
        binding.addProperty("readerLaneId", "lane.reader");
        binding.addProperty("programOrderRequired", false);
        binding.addProperty("writerEventSeq", writer);
        binding.addProperty("readerEventSeq", reader);
        binding.addProperty("receiverObjectId", 7);
        return binding;
    }

    private static JsonObject protocolBinding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("state", "CANDIDATE_TRACED_RPC_EXCHANGE");
        binding.addProperty("evidenceKind",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        binding.addProperty("correlationAuthority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        binding.addProperty("transportKind", "HADOOP_IPC");
        binding.addProperty("fromRegion", regionOf(fromPort));
        binding.addProperty("fromOccurrenceId", fromInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toRegion", regionOf(toPort));
        binding.addProperty("toOccurrenceId", toInstance);
        binding.addProperty("toInputPort", toPort);
        return binding;
    }

    private static JsonObject exactWireBinding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort, String request, String attempt,
            String direction, long sent, long received) {
        JsonObject binding = protocolBinding(edgeId, fromInstance, fromPort,
                toInstance, toPort);
        int targetSeparator = toInstance.indexOf('@');
        if (targetSeparator > 0) {
            binding.addProperty("toRegion",
                    toInstance.substring(0, targetSeparator));
        }
        binding.addProperty("transportKind", "HTTP");
        binding.addProperty("exchangeSiteKey", "REGION.1");
        binding.addProperty("exchangeLeg", edgeId + "\n" + attempt + "\n"
                + direction);
        binding.addProperty("attemptId", attempt);
        binding.addProperty("requestKey", request);
        binding.addProperty("javaType", "int");
        binding.addProperty("direction", direction);
        binding.addProperty("protocolDirection", direction);
        binding.addProperty("handoffLeafPath", fromPort);
        binding.addProperty("senderEventSeq", sent);
        binding.addProperty("receiverEventSeq", received);
        return binding;
    }

    private static JsonObject region(
            String id, boolean hasInput, boolean hasOutput) {
        return region(id, hasInput ? "int" : "",
                hasOutput ? "int" : "");
    }

    private static JsonObject region(
            String id, String inputType, String outputType) {
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        if (!inputType.isEmpty()) {
            inputs.add(port(id + ".in.0", true, inputType));
        }
        region.add("symbolicInputs", inputs);
        JsonArray outputs = new JsonArray();
        if (!outputType.isEmpty()) {
            outputs.add(port(id + ".out.0", false, outputType));
        }
        region.add("outputs", outputs);
        return region;
    }

    private static JsonObject port(
            String id, boolean input, String javaType) {
        return statePort(id, javaType, input
                ? "<Test: " + javaType + " input>"
                : "<Test: " + javaType + " output>");
    }

    private static JsonObject statePort(
            String id, String javaType, String cell) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", id);
        port.addProperty("cell", cell);
        port.addProperty("javaType", javaType);
        return port;
    }

    private static JsonObject occurrencePlan(String region,
                                             String occurrence) {
        JsonObject row = new JsonObject();
        row.addProperty("regionId", region);
        row.addProperty("occurrenceId", occurrence);
        return row;
    }

    private static int occurrences(String value, String needle) {
        int count = 0;
        int at = 0;
        while ((at = value.indexOf(needle, at)) >= 0) {
            count++;
            at += needle.length();
        }
        return count;
    }



    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject reference(String symbol, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", symbol);
        return result;
    }

    private static JsonObject constantReference(String symbol,
                                                String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConSymbolExp");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", symbol);
        return result;
    }

    private static JsonObject fieldAccess(JsonObject owner,
                                          String ownerClass,
                                          int fieldOffset,
                                          String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "FieldAccessExpression");
        result.add("owner", owner.deepCopy());
        result.addProperty("ownerClass", ownerClass);
        result.addProperty("fieldOffset", fieldOffset);
        result.addProperty("_java_type", javaType);
        return result;
    }

    private static RelationSummary withProducerGuardAndInteraction(
            RelationSummary summary, JsonObject condition, String portId,
            long exportEventId) {
        JsonObject row = summary.toJson();
        JsonObject path = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        path.getAsJsonObject("guard").getAsJsonArray("conditions")
                .add(condition);
        JsonObject interaction = new JsonObject();
        interaction.addProperty("outputSiteId",
                "COMMUNICATION_EFFECT:test:" + portId);
        interaction.addProperty("outputOccurrence", 1);
        interaction.addProperty("outputVersionOrdinal", 1);
        interaction.addProperty("replayOccurrence", 1);
        interaction.addProperty("interactionKind", "COMMUNICATION_EFFECT");
        interaction.addProperty("authority",
                "INSTRUMENTED_INTERACTION_SITE_V1");
        interaction.addProperty("portId", portId);
        // README RPC-1: the producer's own export event is what identifies
        // this case as the sender, so the fixture has to carry the id the
        // matching handoff reference exports.
        interaction.addProperty("exportEventId", exportEventId);
        JsonArray interactions = new JsonArray();
        interactions.add(interaction);
        path.add(RelationSummary.INTERACTION_EVENTS, interactions);
        return RelationSummary.decode(row);
    }

    private static JsonObject binary(
            JsonObject left, String operator, JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static String regionOf(String port) {
        int marker = port.indexOf(".in.");
        return marker < 0 ? port.substring(0, port.indexOf(".out."))
                : port.substring(0, marker);
    }

    private static void writeJsonl(Path path, JsonObject... rows)
            throws Exception {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(row).append('\n');
        Files.write(path, value.toString().getBytes(StandardCharsets.UTF_8));
    }
}
