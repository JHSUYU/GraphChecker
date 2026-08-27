package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.Gson;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicSummaryImporterTest {
    private static final Gson GSON = new Gson();
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void selectedBranchWitnessesRecoverACompactTargetPath()
            throws Exception {
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));

        PathImport imported = importPath("compact-selected-path",
                pathTask(false), raw);

        assertEquals(1, imported.result.validSummaryCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertEquals("VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1",
                summary.get("pathConditionAuthority").getAsString());
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        assertEquals(1, summary.getAsJsonArray("branchMappings").size());
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        assertEquals(PathObservation.TargetReachEvent.KIND,
                summary.getAsJsonObject(
                        PathObservation.TargetReachEvent.FIELD)
                        .get("kind").getAsString());
    }

    /**
     * README's resource rule: an output site that ran past its bounded
     * version capacity is a named gap.  The runtime states the row
     * structurally on {@code outputVersionGaps}; the importer validates it
     * once at decode and carries it into {@code alignmentGaps} unchanged.
     */
    @Test
    public void boundedOutputVersionGapTravelsAsAStructuredRow()
            throws Exception {
        JsonObject raw = pathResult(true, true);
        JsonArray gaps = new JsonArray();
        gaps.add(outputVersionGap(11, 8));
        raw.add("outputVersionGaps", gaps);

        PathImport imported = importPath("bounded-output-version-gap",
                pathTask(false), raw);

        assertEquals(1, imported.result.validSummaryCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        JsonArray alignment = summary.getAsJsonArray("alignmentGaps");
        assertEquals(1, alignment.size());
        JsonObject gap = alignment.get(0).getAsJsonObject();
        assertEquals("OUTPUT_VERSION_ALIGNMENT_GAP",
                gap.get("kind").getAsString());
        assertEquals("BOUNDED_OUTPUT_VERSION_CAPACITY_V1",
                gap.get("authority").getAsString());
        assertEquals("BINDING.OUT", gap.get("captureBindingId")
                .getAsString());
        assertEquals(8, gap.get("versionCapacity").getAsInt());
        assertEquals(11, gap.get("versionsObserved").getAsInt());
        assertEquals(8, gap.get("versionsCaptured").getAsInt());
    }

    /**
     * The counts are ints stated by the layer that knows them.  A row that
     * states one of them any other way is a shape this importer does not
     * read, and is refused at decode instead of being half-read.
     */
    @Test
    public void malformedOutputVersionGapRowIsRefusedAtDecode()
            throws Exception {
        JsonObject raw = pathResult(true, true);
        JsonObject malformed = outputVersionGap(11, 8);
        // A number-shaped string is still not an int.
        malformed.addProperty("versionsObserved", "11");
        JsonArray gaps = new JsonArray();
        gaps.add(malformed);
        raw.add("outputVersionGaps", gaps);

        PathImport imported = importPath("bounded-output-version-malformed",
                pathTask(false), raw);

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals("OUTPUT_VERSION_GAP_ROW_MALFORMED",
                ArtifactIO.readJsonl(imported.diagnostics).get(0)
                        .get("code").getAsString());
    }

    @Test
    public void compactCaseMergesAuxiliaryConstraintsExactlyOnce()
            throws Exception {
        JsonObject raw = pathResult(true, true);
        JsonObject auxiliary = auxiliaryPathCondition(1_000_000);
        auxiliary.getAsJsonArray("pathConditionIndices").add(999_999);
        auxiliary.getAsJsonArray("conditions").add(
                auxiliaryContainerRelation("AUX.MAP.READ"));
        auxiliary.addProperty("conditionCount", 1);
        installAuxiliaryPathCondition(raw, auxiliary);

        PathImport imported = importPath("compact-branch-and-auxiliary",
                pathTask(false), raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertEquals("VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1",
                summary.get("pathConditionAuthority").getAsString());
        assertEquals(2, summary.getAsJsonArray("pathCondition").size());
        assertEquals(1_000_000,
                summary.get("pathConditionVmWatermark").getAsInt());
        assertEquals("BinaryExpression", summary.getAsJsonArray(
                "pathCondition").get(0).getAsJsonObject()
                .get("_type").getAsString());
        assertEquals("AUX.MAP.READ", summary.getAsJsonArray(
                "pathCondition").get(1).getAsJsonObject()
                .get("relationId").getAsString());
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
    }

    @Test
    public void relationOnlySeedImportsAuxiliaryWithoutABranchWitness()
            throws Exception {
        JsonObject raw = pathResult(false, true);
        JsonObject auxiliary = auxiliaryPathCondition(8);
        auxiliary.getAsJsonArray("pathConditionIndices").add(7);
        auxiliary.getAsJsonArray("conditions").add(
                auxiliaryContainerRelation("AUX.ONLY"));
        auxiliary.addProperty("conditionCount", 1);
        installAuxiliaryPathCondition(raw, auxiliary);
        installRootOutput(raw);

        PathImport imported = importPath("auxiliary-only-relation",
                relationOnlyTask(), raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        assertEquals("AUX.ONLY", summary.getAsJsonArray("pathCondition")
                .get(0).getAsJsonObject().get("relationId").getAsString());
        assertEquals(0, summary.getAsJsonArray("branchMappings").size());
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
    }

    @Test
    public void relationOnlySeedAcceptsAnEmptyAuxiliaryPath()
            throws Exception {
        JsonObject raw = pathResult(false, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(0));
        installRootOutput(raw);

        PathImport imported = importPath("empty-auxiliary-relation",
                relationOnlyTask(), raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertEquals(0, summary.getAsJsonArray("pathCondition").size());
        assertEquals(0, summary.getAsJsonArray("branchMappings").size());
        assertEquals(0, summary.get("pathConditionVmWatermark").getAsInt());
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
    }

    @Test
    public void configuredSymbolicSourceSurvivesExactImport()
            throws Exception {
        JsonObject task = pathTask(false);
        declareSymbolicSource(task);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task)));

        PathImport imported = importPath("configured-symbolic-source",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        JsonObject event = summary.getAsJsonArray(
                SymbolicSourceEvidence.FIELD).get(0).getAsJsonObject();
        assertTrue(event.get("rawSymbol").getAsString().contains(
                SymbolicSourceEvidence.engineLabelForPhase(
                        sourcePhaseId(task, 0),
                        "HDFS11741.NAMENODE.PROMOTED_KEY_ID")));
        assertEquals(task.get("occurrenceId").getAsString(),
                event.get("sourceOccurrenceId").getAsString());
    }

    @Test
    public void targetLocalSymbolicSourceSurvivesExactImport()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task)));

        PathImport imported = importPath("target-local-symbolic-source",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        JsonObject event = summary.getAsJsonArray(
                SymbolicSourceEvidence.FIELD).get(0).getAsJsonObject();
        assertEquals(task.get("occurrenceId").getAsString(),
                event.get("sourceOccurrenceId").getAsString());
        assertEquals(sourcePhaseId(task, 0),
                event.get("sourcePhaseId").getAsString());
    }

    @Test
    public void twoPublicationsOfOneSourceInOneOccurrenceStayDistinct()
            throws Exception {
        JsonObject task = twoSelectedSourcePhaseTask();
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0, 1);
        SymbolicSourceEvidence.writeTo(raw, Arrays.asList(
                symbolicSourceEvent(task, 0),
                symbolicSourceEvent(task, 1)));

        PathImport imported = importPath("two-source-phases", task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        JsonArray events = ArtifactIO.readJsonl(imported.output).get(0)
                .getAsJsonArray(SymbolicSourceEvidence.FIELD);
        assertEquals(2, events.size());
        assertFalse(events.get(0).getAsJsonObject().get("sourcePhaseId")
                .equals(events.get(1).getAsJsonObject().get(
                        "sourcePhaseId")));
    }

    @Test
    public void mintSiteWithoutRuntimeArraysIsIncomplete()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        raw.remove("configuredSourcePhaseObservations");
        raw.remove("configuredSourcePhaseGaps");

        assertIncomplete("source-phase-ledger-missing", task, raw,
                "SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MISSING");
    }

    @Test
    public void replayWithMissingPhaseLedgerIsRejectedAtAdmission()
            throws Exception {
        JsonObject task = pathTask(true);
        declareTargetSymbolicSource(task);
        JsonObject raw = pathResult(true, false);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task)));

        PathImport imported = importPath("replay-source-ledger-missing",
                task, raw);

        assertEquals(0, imported.result.validSummaryCount);
        JsonObject diagnostic = ArtifactIO.readJsonl(
                imported.diagnostics).get(0);
        assertEquals("PATH_REPLAY_ADMISSION_REJECTED",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString().contains(
                "SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MISSING"));
    }

    /**
     * {@code symbolizedInputs} carries one object row per entry of a declared
     * mint site.  A row the VM answered with an already propagated expression
     * ({@code reused}) is not a new root -- the expression it carries names
     * the root that produced it.
     */
    @Test
    public void symbolizedInputRowsCarryOnlyTheirNewRoots()
            throws Exception {
        JsonObject task = pathTask(false);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        JsonArray symbolized = new JsonArray();
        JsonObject minted = new JsonObject();
        minted.addProperty("sourceId", "TARGET.LOCAL");
        minted.addProperty("occurrenceId",
                task.get("occurrenceId").getAsString());
        minted.addProperty("siteId", "<Test: void run()>#u3");
        minted.addProperty("ordinal", 2);
        minted.addProperty("fieldSignature", "<Test: int keyId>");
        minted.addProperty("symbol", "MINTED.ROOT");
        minted.addProperty("reused", false);
        symbolized.add(minted);
        JsonObject propagated = minted.deepCopy();
        propagated.addProperty("symbol", "");
        propagated.addProperty("reused", true);
        symbolized.add(propagated);
        raw.add("symbolizedInputs", symbolized);

        PathImport imported = importPath("symbolized-input-rows", task, raw);

        JsonArray inputs = ArtifactIO.readJsonl(imported.output).get(0)
                .getAsJsonArray("symbolicInputs");
        assertEquals(String.valueOf(inputs), 1, inputs.size());
        assertEquals("MINTED.ROOT", inputs.get(0).getAsString());
    }

    /**
     * A declared configured source the replay reached and left with no root
     * of its own is named, not silent.
     *
     * <p>The runtime files no {@link SymbolicSourceEvidence} row for a read
     * that found an already propagated compound, and that is right: naming a
     * root that does not exist would be worse.  Saying nothing at all is how
     * the model value the declaration demanded disappears behind a result
     * that reads complete, so the importer names the entry it can see was
     * reached and never answered.  It stays a coverage gap: the relation the
     * execution did produce is admitted unchanged.</p>
     */
    @Test
    public void reachedConfiguredSourceWithNoRootIsNamed() throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        JsonArray symbolized = new JsonArray();
        symbolized.add(propagatedExpiryMint(task));
        raw.add("symbolizedInputs", symbolized);

        PathImport imported = importPath("configured-source-no-root",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        JsonObject diagnostic = ArtifactIO.readJsonl(
                imported.diagnostics).get(0);
        assertEquals("CONFIGURED_SOURCE_ROOT_NOT_MATERIALIZED",
                diagnostic.get("code").getAsString());
        String detail = diagnostic.get("detail").getAsString();
        assertTrue(detail, detail.contains("HDFS11741.KEY_EXPIRY"));
        assertTrue(detail, detail.contains("long expiryDate"));
        assertTrue(detail, detail.contains("materialized no symbolic root"));
    }

    /** The mint that did file its root is not named a second time as a gap.
     */
    @Test
    public void configuredSourceThatMintedItsRootIsNotNamed()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        JsonArray symbolized = new JsonArray();
        JsonObject minted = new JsonObject();
        minted.addProperty("sourceId",
                "HDFS11741.NAMENODE.PROMOTED_KEY_ID");
        minted.addProperty("occurrenceId",
                task.get("occurrenceId").getAsString());
        minted.addProperty("siteId", seedMethod() + "#u2");
        minted.addProperty("ordinal", 1);
        minted.addProperty("fieldSignature",
                "<org.apache.hadoop.security.token.delegation.DelegationKey: "
                        + "int keyId>");
        minted.addProperty("symbol", "MINTED.ROOT");
        minted.addProperty("reused", false);
        symbolized.add(minted);
        raw.add("symbolizedInputs", symbolized);

        PathImport imported = importPath("configured-source-with-root",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    /** A region-input root names no configured source, so this ledger never
     *  claimed to carry it and its absence from the ledger is not a gap. */
    @Test
    public void regionInputRootIsNotAConfiguredSourceGap() throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        JsonArray symbolized = new JsonArray();
        JsonObject local = new JsonObject();
        local.addProperty("symbol", "REGION.SEED.in.local");
        local.addProperty("reused", false);
        symbolized.add(local);
        raw.add("symbolizedInputs", symbolized);

        PathImport imported = importPath("region-input-root", task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    /** One reached mint site with no root of its own, as the runtime states
     *  it: the row carries the propagated expression it found. */
    private static JsonObject propagatedExpiryMint(JsonObject task) {
        JsonObject propagated = new JsonObject();
        propagated.addProperty("sourceId", "HDFS11741.KEY_EXPIRY");
        propagated.addProperty("occurrenceId",
                task.get("occurrenceId").getAsString());
        propagated.addProperty("siteId", seedMethod() + "#u7");
        propagated.addProperty("ordinal", 1);
        propagated.addProperty("fieldSignature",
                "<org.apache.hadoop.security.token.delegation.DelegationKey: "
                        + "long expiryDate>");
        propagated.addProperty("symbol", "");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "FieldAccessExpression");
        expression.addProperty("_java_type", "J");
        expression.addProperty("ownerClass",
                "org/apache/hadoop/hdfs/security/token/block/BlockKey");
        propagated.add("expression", expression);
        propagated.addProperty("reused", true);
        return propagated;
    }

    /** The pre-wave-4 plain-string entry is not an artifact shape this
     *  importer reads: the decode refuses it under its own named code. */
    @Test
    public void plainStringSymbolizedInputIsRefused() throws Exception {
        JsonObject task = pathTask(false);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        JsonArray symbolized = new JsonArray();
        symbolized.add("PLAIN.ROOT");
        raw.add("symbolizedInputs", symbolized);

        PathImport imported = importPath("plain-symbolized-input", task, raw);

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals("SYMBOLIZED_INPUT_ROW_MALFORMED",
                ArtifactIO.readJsonl(imported.diagnostics).get(0)
                        .get("code").getAsString());
    }

    /** {@code freeSymbols} is a required member: a result that never stated
     *  the C2 ledger cannot be read as one that reported no free root. */
    @Test
    public void resultWithoutFreeSymbolLedgerIsRefused() throws Exception {
        JsonObject task = pathTask(false);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        raw.remove(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD);

        PathImport imported = importPath("no-free-symbol-ledger", task, raw);

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals("FREE_SYMBOL_LEDGER_MISSING",
                ArtifactIO.readJsonl(imported.diagnostics).get(0)
                        .get("code").getAsString());
    }

    /**
     * C2 coverage travels with the case.  The composer reads this ledger off
     * every case-evidence row, so a result that reported no free root must
     * still hand the case an empty array rather than omit the member.
     */
    @Test
    public void freeSymbolsTravelFromTheRawResultOntoTheCase()
            throws Exception {
        JsonObject task = pathTask(false);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));

        PathImport silent = importPath("free-symbols-absent", task, raw);
        assertEquals(0, ArtifactIO.readJsonl(silent.output).get(0)
                .getAsJsonArray(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD)
                .size());

        JsonArray free = new JsonArray();
        JsonObject row = new JsonObject();
        row.addProperty("symbol", "free__site__occ__1");
        row.addProperty("vmSymbol", "M_I_free_1");
        row.addProperty("siteId", "<Test: void run()>#u9");
        row.addProperty("occurrenceId",
                task.get("occurrenceId").getAsString());
        row.addProperty("ordinal", 1);
        row.addProperty("javaType", "I");
        row.addProperty("reason", "no recorded lineage");
        free.add(row);
        raw.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, free);

        PathImport reported = importPath("free-symbols-reported", task, raw);

        JsonArray carried = ArtifactIO.readJsonl(reported.output).get(0)
                .getAsJsonArray(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD);
        assertEquals(String.valueOf(carried), 1, carried.size());
        assertEquals("free__site__occ__1", carried.get(0).getAsJsonObject()
                .get("symbol").getAsString());
        // A free root is a coverage report, never a refusal.
        assertEquals(0, reported.result.diagnosticCount);
    }

    /** A declared mint site the replay did not reach is a fact about this
     * execution, not a defect: nothing predicts which occurrences of a site
     * run, so an empty observation ledger is admitted. */
    @Test
    public void emptyPhaseObservationLedgerIsStillComplete()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        raw.add("configuredSourcePhaseObservations", new JsonArray());
        raw.remove(SymbolicSourceEvidence.FIELD);

        PathImport imported = importPath("source-phase-ledger-empty", task,
                raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    @Test
    public void duplicateSelectedPhaseObservationIsIncomplete()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        JsonObject duplicate = raw.getAsJsonArray(
                "configuredSourcePhaseObservations").get(0)
                .getAsJsonObject().deepCopy();
        duplicate.addProperty("observationIndex", 2);
        raw.getAsJsonArray("configuredSourcePhaseObservations")
                .add(duplicate);

        assertIncomplete("source-phase-ledger-duplicate", task, raw,
                "SYMBOLIC_SOURCE_PHASE_OBSERVATION_MISMATCH");
    }

    @Test
    public void runtimeSourcePhaseGapIsIncomplete() throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        JsonObject gap = new JsonObject();
        gap.addProperty("gapKind", "MISSING");
        gap.addProperty("phaseId", sourcePhaseId(task, 0));
        raw.getAsJsonArray("configuredSourcePhaseGaps").add(gap);

        assertIncomplete("source-phase-ledger-gap", task, raw,
                "SYMBOLIC_SOURCE_PHASE_RUNTIME_GAP");
    }

    @Test
    public void reusedRuntimeInvocationIdIsIncomplete() throws Exception {
        JsonObject task = twoSelectedSourcePhaseTask();
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0, 1);
        JsonArray observations = raw.getAsJsonArray(
                "configuredSourcePhaseObservations");
        observations.get(1).getAsJsonObject().addProperty("invocationId",
                observations.get(0).getAsJsonObject()
                        .get("invocationId").getAsLong());
        SymbolicSourceEvidence.writeTo(raw, Arrays.asList(
                symbolicSourceEvent(task, 0),
                symbolicSourceEvent(task, 1)));

        assertIncomplete("source-phase-invocation-reused", task, raw,
                "SYMBOLIC_SOURCE_PHASE_OBSERVATION_MISMATCH");
    }

    @Test
    public void aMintRecordedAtTheSecondCatalogSiteIsAdmitted()
            throws Exception {
        JsonObject task = twoSelectedSourcePhaseTask();
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0, 1);
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task, 1)));

        PathImport imported = importPath("only-second-source-phase", task,
                raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        assertTrue(ArtifactIO.readJsonl(imported.output).get(0)
                .get("relationallyComplete").getAsBoolean());
    }

    @Test
    public void compactCaseRejectsFractionalAuxiliaryIntegers()
            throws Exception {
        JsonObject raw = pathResult(false, true);
        JsonObject auxiliary = auxiliaryPathCondition(4);
        auxiliary.getAsJsonArray("pathConditionIndices").add(1.5);
        auxiliary.getAsJsonArray("conditions").add(
                auxiliaryContainerRelation("AUX.FRACTIONAL"));
        auxiliary.addProperty("conditionCount", 1);
        installAuxiliaryPathCondition(raw, auxiliary);
        installRootOutput(raw);

        assertIncomplete("fractional-auxiliary-index", relationOnlyTask(),
                raw, "AUXILIARY_PATH_CONDITION_MALFORMED:INDEX_0");

        JsonObject fractionalWatermark = pathResult(false, true);
        JsonObject watermarkAuxiliary = auxiliaryPathCondition(0);
        watermarkAuxiliary.addProperty("pathConditionWatermark", 0.5);
        installAuxiliaryPathCondition(fractionalWatermark,
                watermarkAuxiliary);
        installRootOutput(fractionalWatermark);
        assertIncomplete("fractional-auxiliary-watermark",
                relationOnlyTask(), fractionalWatermark,
                "AUXILIARY_PATH_CONDITION_MALFORMED:CARDINALITY");

        JsonObject fractionalCount = pathResult(false, true);
        JsonObject countAuxiliary = auxiliaryPathCondition(0);
        countAuxiliary.addProperty("conditionCount", 0.5);
        installAuxiliaryPathCondition(fractionalCount, countAuxiliary);
        installRootOutput(fractionalCount);
        assertIncomplete("fractional-auxiliary-count", relationOnlyTask(),
                fractionalCount,
                "AUXILIARY_PATH_CONDITION_MALFORMED:CARDINALITY");
    }

    @Test
    public void compactCaseRejectsWrongAuthorities()
            throws Exception {
        JsonObject raw = pathResult(false, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(0));
        raw.getAsJsonObject("engineSummary").addProperty(
                "pathConditionAuthority", "WRONG_AUTHORITY");
        installRootOutput(raw);

        assertIncomplete("wrong-omitted-path-authority", relationOnlyTask(),
                raw, "OMITTED_PATH_CONDITION_AUTHORITY_MISSING");

        JsonObject wrongAuxiliary = pathResult(false, true);
        JsonObject auxiliary = auxiliaryPathCondition(0);
        auxiliary.addProperty("authority", "WRONG_AUXILIARY_AUTHORITY");
        installAuxiliaryPathCondition(wrongAuxiliary, auxiliary);
        installRootOutput(wrongAuxiliary);
        assertIncomplete("wrong-auxiliary-authority", relationOnlyTask(),
                wrongAuxiliary,
                "AUXILIARY_PATH_CONDITION_MALFORMED:ENVELOPE");
    }

    @Test
    public void compactCaseRejectsSparseBranchAuxiliaryCollision()
            throws Exception {
        JsonObject raw = pathResult(true, true);
        JsonObject auxiliary = auxiliaryPathCondition(1_000_000);
        auxiliary.getAsJsonArray("pathConditionIndices").add(0);
        auxiliary.getAsJsonArray("conditions").add(
                auxiliaryContainerRelation("AUX.COLLISION"));
        auxiliary.addProperty("conditionCount", 1);
        installAuxiliaryPathCondition(raw, auxiliary);

        PathImport imported = importPath("sparse-auxiliary-collision",
                pathTask(false), raw);

        assertEquals(1, imported.result.validSummaryCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertFalse(summary.get("relationallyComplete").getAsBoolean());
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        assertEquals(1_000_000,
                summary.get("pathConditionVmWatermark").getAsInt());
        assertTrue(ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString().contains(
                        "AUXILIARY_PATH_CONDITION_CONFLICT:0"));
    }

    @Test
    public void compactCaseRefusesMissingOrTruncatedAuxiliaryEvidence()
            throws Exception {
        JsonObject missing = pathResult(true, true);
        installAuxiliaryPathCondition(missing, null);
        PathImport missingImport = importPath("missing-auxiliary-path",
                pathTask(false), missing);
        JsonObject missingSummary = ArtifactIO.readJsonl(
                missingImport.output).get(0);
        assertFalse(missingSummary.get("relationallyComplete").getAsBoolean());
        assertTrue(ArtifactIO.readJsonl(missingImport.diagnostics).get(0)
                .get("detail").getAsString().contains(
                        "AUXILIARY_PATH_CONDITION_MISSING"));

        JsonObject truncated = pathResult(true, true);
        JsonObject auxiliary = auxiliaryPathCondition(2);
        auxiliary.getAsJsonArray("pathConditionIndices").add(1);
        JsonObject marker = new JsonObject();
        marker.addProperty("_type", "TruncatedExpression");
        marker.addProperty("expressionAuthority",
                "VM_SERIALIZATION_TRUNCATION_V1");
        auxiliary.getAsJsonArray("conditions").add(marker);
        auxiliary.addProperty("conditionCount", 1);
        installAuxiliaryPathCondition(truncated, auxiliary);
        PathImport truncatedImport = importPath("truncated-auxiliary-path",
                pathTask(false), truncated);
        JsonObject truncatedSummary = ArtifactIO.readJsonl(
                truncatedImport.output).get(0);
        assertFalse(truncatedSummary.get("relationallyComplete")
                .getAsBoolean());
        assertEquals(1, truncatedSummary.getAsJsonArray(
                "pathCondition").size());
        assertTrue(ArtifactIO.readJsonl(truncatedImport.diagnostics).get(0)
                .get("detail").getAsString().contains(
                        "VM_EXPRESSION_SERIALIZATION_TRUNCATED:"
                                + "AUXILIARY_PATH_CONDITION:1"));
    }

    @Test
    public void targetPathWithoutTheExactRuntimeEventIsRefused()
            throws Exception {
        JsonObject missing = pathResult(true, true);
        missing.remove(PathObservation.TargetReachEvent.FIELD);
        PathImport missingImport = importPath("missing-target-event",
                pathTask(false), missing);
        assertEquals(0, missingImport.result.validSummaryCount);
        assertEquals("TARGET_REACH_EVENT_MISSING",
                ArtifactIO.readJsonl(missingImport.diagnostics).get(0)
                        .get("code").getAsString());

        JsonObject mismatched = pathResult(true, true);
        mismatched.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("occurrence", 2);
        PathImport mismatchImport = importPath("mismatched-target-event",
                pathTask(false), mismatched);
        assertEquals(0, mismatchImport.result.validSummaryCount);
        assertEquals("TARGET_REACH_EVENT_MISMATCH",
                ArtifactIO.readJsonl(mismatchImport.diagnostics).get(0)
                        .get("code").getAsString());
    }

    @Test
    public void exactRequiredTargetOutcomeOverridesTheSeedOutcome()
            throws Exception {
        JsonObject task = pathTask(false);
        JsonObject selectedBranch = task.getAsJsonArray("branches")
                .get(0).getAsJsonObject();
        selectedBranch.addProperty("selectedOccurrence", 1);
        selectedBranch.addProperty("requiredOutcome", false);

        PathImport imported = importPath("required-target-outcome", task,
                pathResult(true, false));

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertFalse(summary.getAsJsonObject(
                PathObservation.TargetReachEvent.FIELD)
                .get("outcome").getAsBoolean());
    }

    @Test
    public void requiredFatalOutcomeNeverOverridesLocalReplayContract()
            throws Exception {
        JsonObject replay = pathTask(true);
        JsonObject selectedBranch = replay.getAsJsonArray("branches")
                .get(0).getAsJsonObject();
        selectedBranch.addProperty("selectedOccurrence", 1);
        selectedBranch.addProperty("requiredOutcome", true);

        // The replay contract complements the source witness and therefore
        // requires false. The fresh execution instead repeats true; reaching
        // the independently selected fatal outcome cannot certify that this
        // local prefix flip happened.
        PathImport imported = importPath("required-fatal-replay-mismatch",
                replay, pathResult(true, true));

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals("BRANCH_REPLAY_MISMATCH",
                ArtifactIO.readJsonl(imported.diagnostics).get(0)
                        .get("code").getAsString());
        assertTrue(ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString().contains("wrong replay outcome"));
    }

    @Test
    public void selectedExploreWitnessSurvivesARelationOnlySeed()
            throws Exception {
        JsonObject task = pathTask(false);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        OutputClosureCodec.writeTo(task, OutputClosureCodec.singleton(
                "test/source/REGION.SEED", "REGION.SEED",
                Collections.singletonList("REGION.SEED.out.0"),
                "REGION.SEED.out.0", "<Test: int output>", "REGION_OUTPUT",
                "int", outputSlice("REGION.SEED.out.0",
                        "<Test: int output>")));
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));

        PathImport imported = importPath("relation-selected-branch",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        assertEquals(1, summary.getAsJsonArray("branchMappings").size());
        assertEquals("EXPLORE", summary.getAsJsonArray("branchMappings")
                .get(0).getAsJsonObject().get("policy").getAsString());
        assertEquals("VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1",
                summary.get("pathConditionAuthority").getAsString());
    }

    @Test
    public void inheritedLoopBoundAcceptsZeroAndRefusesAboveK()
            throws Exception {
        JsonObject task = pathTask(false);
        task.add(BoundedLoopComposition.PLAN_FIELD,
                retainedConditionLoop());

        PathImport zero = importPath("implicit-loop-zero", task.deepCopy(),
                pathResult(true, true));
        assertEquals(1, zero.result.validSummaryCount);
        JsonObject count = ArtifactIO.readJsonl(zero.output).get(0)
                .getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNTS)
                .get(0).getAsJsonObject();
        assertEquals(0, count.get(LoopBoundPolicy.LOOP_BODY_COUNT).getAsInt());
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                count.get(LoopBoundPolicy.LOOP_BODY_BOUND).getAsInt());
        // README LOOP-1: inheriting the core default K_L is not an
        // experiment-owned bound declaration.  The exact count stays on the
        // case, the row states no bound authority, and the absent
        // declaration is one named gap - the same reason and subject
        // BoundedLoopComposition.ofPlanRows raises for it.
        assertFalse(count.has(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY));
        JsonObject undeclared = ArtifactIO.readJsonl(zero.output).get(0)
                .getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS)
                .get(0).getAsJsonObject();
        assertEquals(BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED,
                undeclared.get("reason").getAsString());
        assertEquals(task.get("occurrenceId").getAsString() + "\n"
                        + helperMethod() + "#u4",
                undeclared.get("subject").getAsString());

        JsonObject beyond = pathResult(true, true);
        JsonObject bodies = new JsonObject();
        bodies.addProperty(helperMethod() + "#loop:u4",
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS + 1);
        beyond.add("loopBackedgeTraversals", bodies);
        PathImport refused = importPath("implicit-loop-above-bound",
                task.deepCopy(), beyond);
        assertEquals(0, refused.result.validSummaryCount);
        assertEquals(LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                ArtifactIO.readJsonl(refused.diagnostics).get(0)
                        .get("code").getAsString());
    }

    @Test
    public void seedOutcomeMismatchIsRejectedFailClosed()
            throws Exception {
        PathImport imported = importPath("wrong-seed-outcome",
                pathTask(false), pathResult(true, false));

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals(1, imported.result.diagnosticCount);
        assertEquals(0, ArtifactIO.readJsonl(imported.output).size());
        JsonObject diagnostic = ArtifactIO.readJsonl(
                imported.diagnostics).get(0);
        assertEquals("BRANCH_REPLAY_MISMATCH",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString()
                .contains("wrong outcome"));

        // Folded Phase 2 field acceptance: campaign completion is where the
        // trace's candidate writers meet the session's own answer.  The task
        // arrives carrying two equal-valued candidates and no decision; the
        // execution's recorded store proves one of them, and the summary the
        // composer will read says so per candidate.  Nothing about the
        // reader's local relation is involved in that.
        JsonObject task = pathTask(false);
        task.add("edgeBindings", candidateEdges());
        JsonObject raw = pathResult(true, true);
        JsonArray recorded = new JsonArray();
        recorded.add(RecordedSharedStateFixtures.versionsRecord(
                RecordedSharedStateFixtures.twoWriterEnvelope(
                        SharedStateEvidence.RESOLUTION_EXACT, "SYNC_ORDERED",
                        11L), "example.State#value"));
        raw.add("sharedFieldVersions", recorded);

        PathImport resolved = importPath("recorded-provenance", task, raw);

        assertEquals(1, resolved.result.validSummaryCount);
        JsonArray bindings = ArtifactIO.readJsonl(resolved.output).get(0)
                .getAsJsonArray("edgeBindings");
        assertEquals(RecordedReadFrom.PROVENANCE_EXACT,
                bindings.get(0).getAsJsonObject()
                        .get(RecordedReadFrom.EDGE_PROVENANCE).getAsString());
        assertEquals(RecordedReadFrom.PROVENANCE_EXCLUDED,
                bindings.get(1).getAsJsonObject()
                        .get(RecordedReadFrom.EDGE_PROVENANCE).getAsString());

        // With no recorded evidence the same task keeps both candidates and
        // the gap that names why, rather than acquiring a writer from the
        // equal concrete value both of them published.
        JsonObject unwatched = pathTask(false);
        unwatched.add("edgeBindings", candidateEdges());
        PathImport unresolved = importPath("no-recorded-provenance",
                unwatched, pathResult(true, true));

        JsonArray kept = ArtifactIO.readJsonl(unresolved.output).get(0)
                .getAsJsonArray("edgeBindings");
        for (int edge = 0; edge < kept.size(); edge++) {
            assertEquals(RecordedReadFrom.PROVENANCE_CANDIDATE,
                    kept.get(edge).getAsJsonObject()
                            .get(RecordedReadFrom.EDGE_PROVENANCE)
                            .getAsString());
            assertEquals("SHARED_STATE_NOT_SELECTED",
                    kept.get(edge).getAsJsonObject()
                            .get(RecordedReadFrom.EDGE_PROVENANCE_GAP)
                            .getAsString());
        }

    }

    @Test
    public void vmHandoffV4ExpressionAndProducerSurviveSummaryImport()
            throws Exception {
        // The exact destination expression travels with the VM ledger
        // reference.  Import keeps both case-local and performs no pairing.
        JsonObject rpcTask = pathTask(false);
        JsonObject rpcRaw = pathResult(true, true);
        JsonArray events = new JsonArray();
        JsonObject attachedExpression = new JsonObject();
        attachedExpression.addProperty("_type", "Int");
        attachedExpression.addProperty("_value", 17);
        events.add(VmHandoffEvidence.event("XCH.1.req.keyId", 41L, 42L,
                attachedExpression, "TASK.PRODUCER",
                "REGION.producer@Test#1"));
        rpcRaw.add(VmHandoffEvidence.FIELD, events);

        PathImport handoff = importPath("recorded-handoff", rpcTask, rpcRaw);

        JsonObject summary = ArtifactIO.readJsonl(handoff.output).get(0);
        assertEquals(1, VmHandoffEvidence.eventsOf(summary).size());
        assertEquals(41L, VmHandoffEvidence.eventsOf(summary).get(0)
                .get(VmHandoffEvidence.EXPORT_EVENT_ID).getAsLong());
        assertEquals(42L, VmHandoffEvidence.eventsOf(summary).get(0)
                .get(VmHandoffEvidence.ATTACH_EVENT_ID).getAsLong());
        assertEquals(VmHandoffEvidence.SCHEMA_VERSION,
                VmHandoffEvidence.eventsOf(summary).get(0)
                        .get("schemaVersion").getAsInt());
        assertEquals(attachedExpression,
                VmHandoffEvidence.eventsOf(summary).get(0)
                        .get(VmHandoffEvidence.EXPRESSION));
        assertEquals("TASK.PRODUCER",
                VmHandoffEvidence.eventsOf(summary).get(0)
                        .get(VmHandoffEvidence.PRODUCER_TASK_ID)
                        .getAsString());
        assertEquals("REGION.producer@Test#1",
                VmHandoffEvidence.eventsOf(summary).get(0)
                        .get(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID)
                        .getAsString());
    }

    @Test
    public void vmHandoffV4RequiresBothEndpointsExpressionAndProducer() {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "Int");
        expression.addProperty("_value", 23);
        JsonObject event = VmHandoffEvidence.event(
                "XCH.1.req.keyId", 43L, 44L, expression, "TASK.PRODUCER",
                "REGION.producer@Test#1");

        assertTrue(VmHandoffEvidence.isEvent(event));
        assertEquals(4, event.get("schemaVersion").getAsInt());
        assertEquals(expression, event.get(VmHandoffEvidence.EXPRESSION));
        assertEquals(44L, VmHandoffEvidence.attachEventOf(event));

        // README RPC-1: an export may be attached at several receivers, so a
        // row without its attach endpoint names no receive and cannot be
        // completed from anything else it carries.
        JsonObject missingAttach = event.deepCopy();
        missingAttach.remove(VmHandoffEvidence.ATTACH_EVENT_ID);
        assertFalse(VmHandoffEvidence.isEvent(missingAttach));
        assertEquals(0L, VmHandoffEvidence.attachEventOf(missingAttach));

        JsonObject missingExport = event.deepCopy();
        missingExport.remove(VmHandoffEvidence.EXPORT_EVENT_ID);
        assertFalse(VmHandoffEvidence.isEvent(missingExport));

        JsonObject missingExpression = event.deepCopy();
        missingExpression.remove(VmHandoffEvidence.EXPRESSION);
        assertFalse(VmHandoffEvidence.isEvent(missingExpression));

        JsonObject missingProducer = event.deepCopy();
        missingProducer.remove(VmHandoffEvidence.PRODUCER_TASK_ID);
        assertFalse(VmHandoffEvidence.isEvent(missingProducer));

        JsonObject missingOccurrence = event.deepCopy();
        missingOccurrence.remove(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID);
        assertFalse(VmHandoffEvidence.isEvent(missingOccurrence));

        JsonObject legacy = event.deepCopy();
        legacy.addProperty("schemaVersion", 3);
        assertFalse(VmHandoffEvidence.isEvent(legacy));

        JsonObject truncated = event.deepCopy();
        JsonObject bounded = new JsonObject();
        bounded.addProperty("_type", "TruncatedExpression");
        bounded.addProperty("expressionAuthority",
                "VM_SERIALIZATION_TRUNCATION_V1");
        truncated.add(VmHandoffEvidence.EXPRESSION, bounded);
        assertFalse(VmHandoffEvidence.isEvent(truncated));
    }


    /** The two candidate writers trace refinement retained for one read. */
    private static JsonArray candidateEdges() {
        JsonArray edges = new JsonArray();
        for (String writer : new String[]{"REGION.writerA", "REGION.writerB"}) {
            JsonObject edge = new JsonObject();
            edge.addProperty("edgeId", "RF." + writer);
            edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
            edge.addProperty("fromRegion", writer);
            edge.addProperty("toRegion", "REGION.reader");
            edge.addProperty("fromOccurrenceId",
                    RecordedSharedStateFixtures.occurrenceOf(writer));
            edge.addProperty("toOccurrenceId",
                    RecordedSharedStateFixtures.occurrenceOf(
                            "REGION.reader"));
            edge.addProperty(RecordedReadFrom.EDGE_FIELD,
                    "example.State#value");
            edge.addProperty(RecordedReadFrom.EDGE_SOURCE_KEY,
                    RecordedSharedStateFixtures.TEST_SOURCE);
            edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                    RecordedReadFrom.PROVENANCE_CANDIDATE);
            edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE_GAP,
                    "SHARED_STATE_NOT_SELECTED");
            edges.add(edge);
        }
        return edges;
    }

    /**
     * README Step 1: identical planned identity and schema adds a guarded
     * local case and a new cut writes {@code TOPOLOGY_DIVERGENCE}. A branch
     * site behind another outcome is expected to be absent from one local
     * case; only the region path worklist may classify global path coverage.
     * Nothing a run failed to observe removes evidence, and no refused row
     * leaves the delta silent.
     */
    @Test
    public void topologyDeltaClassifiesCasesCutsAndRefusals()
            throws Exception {
        JsonObject second = pathResult(true, true);
        second.addProperty("exceptionType", "java.io.IOException");
        PathImport cases = importPath("delta-local-cases", pathTask(false),
                pathResult(true, true), second);

        assertEquals(2, cases.result.validSummaryCount);
        java.util.List<JsonObject> rows = ArtifactIO.readJsonl(cases.delta);
        assertEquals(2, rows.size());
        JsonObject occurrence = deltaRow(rows, TopologyDelta.NEW_OCCURRENCE);
        assertEquals("test/source#epoch0",
                occurrence.get("sourceKey").getAsString());
        assertEquals(occurrence.get("plannedIdentityDigest").getAsString(),
                occurrence.get("observedIdentityDigest").getAsString());
        assertEquals(occurrence.get("plannedSchemaDigest").getAsString(),
                occurrence.get("observedSchemaDigest").getAsString());
        // The second case of one planned occurrence is a guarded local case,
        // never a second occurrence node.
        assertEquals("", deltaRow(rows, TopologyDelta.NEW_LOCAL_CASE)
                .get("gap").getAsString());

        // The same rule from the schema side.  This occurrence carried less
        // of its frozen schema than the plan demanded: it captured nothing
        // for the one output relation it was planned for.  Producing less is
        // never a new slot, so the topology is unchanged and the case is
        // published - and because a component the run did not state keeps the
        // planned value and is named instead, the row does not claim "same
        // topology" while its own schema digest says the opposite.
        java.util.List<JsonObject> unproduced = ArtifactIO.readJsonl(
                importPath("delta-unproduced-output", relationOnlyTask(),
                        pathResult(true, true)).delta);
        JsonObject producedNothing = deltaRow(unproduced,
                TopologyDelta.NEW_OCCURRENCE);
        assertEquals(producedNothing.get("plannedSchemaDigest").getAsString(),
                producedNothing.get("observedSchemaDigest").getAsString());
        assertTrue(producedNothing.toString(), producedNothing
                .getAsJsonArray("unobservedSchemaFields").toString()
                .contains("outputPorts"));

        // The frozen region contains a second semantic branch, but this one
        // case returns before reaching it.  This is not a per-case topology
        // gap: another case or an UNSAT terminal owns that global obligation.
        JsonObject twoBranchTask = pathTask(false);
        JsonObject tail = twoBranchTask.getAsJsonArray("branches")
                .get(0).getAsJsonObject().deepCopy();
        tail.addProperty("siteId", seedMethod() + "#u9");
        tail.addProperty("unitIndex", 9);
        tail.add("occurrences", new JsonArray());
        twoBranchTask.getAsJsonArray("branches").add(tail);
        java.util.List<JsonObject> caseLocal = ArtifactIO.readJsonl(
                importPath("delta-case-local-tail", twoBranchTask,
                        pathResult(true, true)).delta);
        for (JsonObject row : caseLocal) {
            assertFalse(row.toString(),
                    TopologyDelta.COVERAGE_GAP.equals(
                            row.get("deltaKind").getAsString()));
            assertFalse(row.toString(), row.toString().contains(
                    TopologyDelta.PLANNED_BRANCH_EVENT_NOT_OBSERVED));
        }

        // An execution whose identity the frozen plan does not contain
        // belongs to the next iteration's plan: it publishes a divergence and
        // no local case at all.
        JsonObject unplanned = pathTask(false);
        unplanned.addProperty("regionId", "REGION.UNPLANNED");
        java.util.List<JsonObject> diverged = ArtifactIO.readJsonl(
                importPath("delta-unplanned-activation", unplanned,
                        pathResult(true, true)).delta);

        JsonObject divergence = deltaRow(diverged,
                TopologyDelta.TOPOLOGY_DIVERGENCE);
        assertEquals("REGION.UNPLANNED",
                divergence.get("regionId").getAsString());
        assertEquals("UNKNOWN_REGION", divergence
                .getAsJsonArray("divergences").get(0).getAsJsonObject()
                .get("field").getAsString());
        for (JsonObject row : diverged) {
            String kind = row.get("deltaKind").getAsString();
            assertTrue(kind, !TopologyDelta.NEW_LOCAL_CASE.equals(kind)
                    && !TopologyDelta.NEW_OCCURRENCE.equals(kind));
        }

        // Importer admission owns a refused row. The topology classifier must
        // not duplicate the same gap under a second stage.
        PathImport refused = importPath("delta-refused", pathTask(false),
                pathResult(true, false));
        assertEquals(0, ArtifactIO.readJsonl(refused.delta).size());
        assertEquals("BRANCH_REPLAY_MISMATCH",
                ArtifactIO.readJsonl(refused.diagnostics).get(0)
                        .get("code").getAsString());
    }

    @Test
    public void topologyDeltaCarriesTheExplicitImportIterationIdentity()
            throws Exception {
        String iterationId = "iteration-0007";
        JsonObject task = pathTask(false);
        PathImport imported = importPath("delta-iteration-identity",
                iterationId, task, pathResult(true, true));
        String expectedPlanDigest = TopologyDelta.planDigest(
                Collections.singletonList(ExecutionTask.decode(task)));

        java.util.List<JsonObject> rows = ArtifactIO.readJsonl(imported.delta);
        assertFalse(rows.isEmpty());
        for (JsonObject row : rows) {
            assertEquals(iterationId,
                    row.get("iterationId").getAsString());
            assertEquals(expectedPlanDigest,
                    row.get("planDigest").getAsString());
        }
    }

    @Test
    public void importRefusesMissingIterationIdentity() throws Exception {
        try {
            importPath("delta-missing-iteration", " ", pathTask(false),
                    pathResult(true, true));
            fail("blank import iteration id was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("iteration id"));
        }
    }

    private static JsonObject deltaRow(java.util.List<JsonObject> rows,
                                       String deltaKind) {
        for (JsonObject row : rows) {
            if (deltaKind.equals(row.get("deltaKind").getAsString())) {
                return row;
            }
        }
        throw new AssertionError("no " + deltaKind + " row in " + rows);
    }

    private PathImport importPath(String name, JsonObject task,
                                  JsonObject... raws) throws Exception {
        return importPath(name, "test-" + name, task, raws);
    }

    private PathImport importPath(String name, String iterationId,
                                  JsonObject task, JsonObject... raws)
            throws Exception {
        Path directory = folder.newFolder(name).toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");
        Path delta = directory.resolve(TopologyDelta.FILE_NAME);
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.SEED");
        java.util.List<JsonObject> rows = new java.util.ArrayList<>();
        for (JsonObject row : raws) {
            row.addProperty("taskId", task.get("taskId").getAsString());
            rows.add(row);
        }
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(task));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, rows);
        return new PathImport(ConcolicSummaryImporter.importSummaries(
                results, tasks,
                ConcolicSummaryImporter.regionIds(
                        ArtifactIO.readJsonl(regions)),
                output, diagnostics, delta,
                iterationId), output, diagnostics, delta);
    }

    private void assertIncomplete(String name, JsonObject task,
                                  JsonObject raw, String issue)
            throws Exception {
        PathImport imported = importPath(name, task, raw);
        assertEquals(1, imported.result.validSummaryCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertFalse(summary.get("relationallyComplete").getAsBoolean());
        assertTrue(ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString().contains(issue));
    }

    /** The one demanded output a relation-only seed closes. */
    private static JsonObject outputSlice(String port, String cell) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        for (String member : new String[]{"sites", "staticSites", "methods",
                "causalEdgeIds", "captureBindings", "captureBindingIssues"}) {
            slice.add(member, new JsonArray());
        }
        return slice;
    }

    private static JsonArray retainedConditionLoop() {
        JsonObject loop = new JsonObject();
        loop.addProperty("enclosingMethod", helperMethod());
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID,
                helperMethod() + "#u4");
        loop.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID,
                helperMethod() + "#loop:u4");
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED);
        JsonArray sites = new JsonArray();
        sites.add(helperMethod() + "#u4");
        loop.add(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, sites);
        JsonArray loops = new JsonArray();
        loops.add(loop);
        return loops;
    }

    private static String helperMethod() {
        return "<test.Helper: void scan()>";
    }

    private static JsonObject pathTask(boolean replay) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", replay ? "TASK.REPLAY" : "TASK.SEED");
        task.addProperty("goalId", "GOAL.SEED");
        task.addProperty("regionId", "REGION.SEED");
        task.addProperty("sourceKey", "test/source#epoch0");
        task.addProperty("occurrenceId",
                "test/source#epoch0/region/REGION.SEED#1");
        task.addProperty("relationKey", "test/source/REGION.SEED");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", seedSite());
        branch.addProperty("method", seedMethod());
        branch.addProperty("unitIndex", 3);
        branch.addProperty("policy", "EXPLORE");
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("occurrence", 1);
        occurrence.addProperty("outcome", true);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence);
        branch.add("occurrences", occurrences);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        task.add("branches", branches);
        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId", seedSite());
        targetBranch.addProperty("occurrence", 1);
        task.add("targetBranch", targetBranch);
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        if (replay) {
            task.add("replayContract", BranchReplayContract.flip(
                    Collections.<BranchWitness>emptyList(),
                    branchWitness(true)).toJson());
        }
        return task;
    }

    private static JsonObject relationOnlyTask() {
        JsonObject task = pathTask(false);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        OutputClosureCodec.writeTo(task, OutputClosureCodec.singleton(
                "test/source/REGION.SEED", "REGION.SEED",
                Collections.singletonList("REGION.SEED.out.0"),
                "REGION.SEED.out.0", "<Test: int output>", "REGION_OUTPUT",
                "int", outputSlice("REGION.SEED.out.0",
                        "<Test: int output>")));
        return task;
    }

    /** Declaring a source is declaring its mint SITE.  There is no task-side
     * selection row any more: which occurrence of the site produced a value
     * is decided at replay, by the VM. */
    private static void declareSymbolicSource(JsonObject task) {
        appendPublishPhase(task, 1, 1L);
    }

    private static void declareTargetSymbolicSource(JsonObject task) {
        declareSymbolicSource(task);
        addTargetSourceInput(task);
    }

    private static void addTargetSourceInput(JsonObject task) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "CONCRETE");
        action.addProperty("portId", "TARGET.promotedKey");
        action.addProperty("symbol", "TARGET.promotedKey");
        action.addProperty("accessFieldSignature",
                "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>");
        task.getAsJsonArray("inputActions").add(action);
    }

    private static JsonObject symbolicSourceEvent(JsonObject task) {
        return symbolicSourceEvent(task, 0);
    }

    private static JsonObject symbolicSourceEvent(JsonObject task,
                                                  int phaseIndex) {
        String phaseId = sourcePhaseId(task, phaseIndex);
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "int");
        expression.addProperty("_exp", "M_I_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(phaseId,
                "HDFS11741.NAMENODE.PROMOTED_KEY_ID")
                + "_promoted_key");
        return SymbolicSourceEvidence.event(
                phaseId,
                "HDFS11741.NAMENODE.PROMOTED_KEY_ID",
                task.get("occurrenceId").getAsString(),
                "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>",
                expression, phaseIndex + 1, false, null);
    }

    private static JsonObject exactSourceRaw(JsonObject task) {
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task)));
        return raw;
    }

    /** Two entries of one mint site inside one occurrence. */
    private static JsonObject twoSelectedSourcePhaseTask() {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        appendPublishPhase(task, 2, 2L);
        return task;
    }

    private static void appendPublishPhase(JsonObject task, int ordinal,
                                           long eventSeq) {
        String field =
                "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>";
        appendSourcePhase(task,
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "HDFS11741.NAMENODE.PROMOTED_KEY_ID", field, 2,
                ordinal, eventSeq);
    }

    private static void appendSourcePhase(
            JsonObject task, ConfiguredSourcePhaseContract.Phase kind,
            String sourceId, String field, int unitIndex, int ordinal,
            long eventSeq) {
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                kind, sourceId, field, seedMethod(), unitIndex));
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        declarations).get(0);
        JsonObject phase =
                ConfiguredSourcePhaseContract.occurrence(decoded,
                        task.get("occurrenceId").getAsString(), ordinal,
                        eventSeq, 1L, eventSeq,
                        "<TestHook: void symbolize()>",
                        Collections.singletonList(1L));
        JsonArray phases = task.has(ConfiguredSourcePhaseContract.PLAN_FIELD)
                ? task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                : new JsonArray();
        phases.add(phase);
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
    }

    private static String sourcePhaseId(JsonObject task, int index) {
        return task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .get(index).getAsJsonObject().get("phaseId").getAsString();
    }

    /** The hook ledger, as the runtime states it: exactly the seven runtime
     * facts.  Everything else the row could carry restates the catalog row
     * {@code matchedPhaseId} already names, and is refused as an extra. */
    private static void installPhaseRuntimeLedger(
            JsonObject raw, JsonObject task, int... phaseIndexes) {
        JsonArray observations = new JsonArray();
        JsonArray catalog = task.getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD);
        for (int observationIndex = 0;
             observationIndex < phaseIndexes.length; observationIndex++) {
            JsonObject phase = catalog.get(phaseIndexes[observationIndex])
                    .getAsJsonObject();
            JsonObject observation = new JsonObject();
            observation.addProperty("schemaVersion", 1);
            observation.addProperty("kind",
                    "CONFIGURED_SOURCE_PHASE_OBSERVATION");
            observation.addProperty("authority",
                    "EXACT_ACTIVE_CALL_SITE_REPLAY_V1");
            observation.addProperty("observationIndex",
                    observationIndex + 1);
            observation.addProperty("matchedPhaseId",
                    phase.get("phaseId").getAsString());
            observation.addProperty("ownerCallId", 101L);
            observation.addProperty("invocationId",
                    200L + observationIndex);
            observations.add(observation);
        }
        raw.add("configuredSourcePhaseObservations", observations);
        raw.add("configuredSourcePhaseGaps", new JsonArray());
    }

    private static JsonObject outputVersionGap(int observed, int captured) {
        JsonObject gap = new JsonObject();
        gap.addProperty("schemaVersion", 1);
        gap.addProperty("kind", "OUTPUT_VERSION_ALIGNMENT_GAP");
        gap.addProperty("authority", "BOUNDED_OUTPUT_VERSION_CAPACITY_V1");
        gap.addProperty("captureBindingId", "BINDING.OUT");
        gap.addProperty("outputSiteId", seedSite());
        gap.addProperty("versionCapacity", 8);
        gap.addProperty("versionsObserved", observed);
        gap.addProperty("versionsCaptured", captured);
        gap.addProperty("reason", "BINDING.OUT ran past its bounded output"
                + " version capacity 8 at " + seedSite() + "; " + captured
                + " of " + observed + " observed version(s) were captured,"
                + " so this relation is a bounded prefix of the run and not"
                + " a closed one");
        return gap;
    }

    private static JsonObject pathResult(boolean includeMapping,
                                         boolean outcome) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("taskId", "TASK.SEED");
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");
        JsonObject engine = new JsonObject();
        engine.addProperty("complete", true);
        engine.addProperty("aborted", false);
        raw.add("engineSummary", engine);
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", new JsonArray());
        raw.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        raw.add("outputCaptures", new JsonArray());
        JsonArray mappings = new JsonArray();
        if (includeMapping) {
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", seedSite());
            mapping.addProperty("method", seedMethod());
            mapping.addProperty("unitIndex", 3);
            mapping.addProperty("occurrence", 1);
            mapping.addProperty("rawPathConditionBaseline", 0);
            mapping.addProperty("rawPathConditionSize", 1);
            mapping.add("witness", branchWitness(outcome).toJson());
            mappings.add(mapping);
        }
        raw.add("branchMappings", mappings);
        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", seedSite());
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", outcome);
        raw.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        // README PC-1: the VM no longer serializes an ambient path
        // condition, so the selected-branch plus bounded auxiliary channel
        // is the shape every raw result has.  Cases that need a different
        // auxiliary envelope overwrite this one.
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(
                includeMapping ? 1 : 0));
        return raw;
    }

    private static void installAuxiliaryPathCondition(
            JsonObject raw, JsonObject auxiliary) {
        JsonObject engine = raw.getAsJsonObject("engineSummary");
        engine.addProperty("active", true);
        engine.addProperty("pathConditionOmitted", true);
        engine.add("pathCondition", new JsonArray());
        engine.addProperty("pathConditionAuthority",
                "VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1");
        if (auxiliary != null) {
            // The marker serializer emits one entry per recorded condition,
            // so a fixture that did not state the count itself gets the one
            // its own conditions array implies.
            if (!auxiliary.has("emittedConditionCount")) {
                auxiliary.addProperty("emittedConditionCount",
                        auxiliary.getAsJsonArray("conditions").size());
            }
            engine.add("auxiliaryPathCondition", auxiliary);
        } else {
            engine.remove("auxiliaryPathCondition");
        }
    }

    /**
     * HDFS-11741 campaign-takeover-24: the balancer Dispatcher exported all
     * three declared SASL handshake leaves and the VM answered
     * {@code NOT_SYMBOLIC} for {@code blockPoolId} and {@code nonce}.  The
     * recorder admits that case on purpose, and
     * {@code hasCapturedDemandedOutput} admits it too, but
     * {@code outputExpressions} reported it as
     * {@code OUTPUT_CAPTURE_COUNT:<port>:0} -- a claim that the occurrence
     * never reached the site.  The relation was refused, the path planner
     * dropped it, and the Composer was never handed the one producer the
     * target's keyId comes from.  The refusal stands; it now says what it
     * found.
     */
    @Test
    public void aConcreteHandoffLeafIsPresentedNotUncaptured()
            throws Exception {
        JsonObject concrete = new JsonObject();
        concrete.addProperty("captureBindingId", "CAPTURE.leaf");
        concrete.addProperty("outputSiteId", LEAF_SITE);
        concrete.addProperty("outputOccurrence", 1);
        concrete.addProperty("outputVersionOrdinal", 1);
        concrete.addProperty("concreteLeaf", true);
        concrete.addProperty("primitiveValue", "BP-1-127.0.0.1-1");

        assertTrue("the VM answered this leaf concrete",
                ConcolicSummaryImporter.concreteHandoffLeaf(
                        leafSpec(OutputCaptureSpec.HANDOFF_BOUND_LEAF),
                        concrete));

        // Scoped to the handoff leaf: a heap write with no expression is
        // still an unobserved boundary and still counts as uncaptured.
        assertFalse("only a handoff leaf is presented without an expression",
                ConcolicSummaryImporter.concreteHandoffLeaf(
                        leafSpec(OutputCaptureSpec.FIELD_WRITE_STATE),
                        concrete));

        // A guarded capture failure recorded neither an expression nor the
        // VM's concrete answer, and stays uncaptured.
        JsonObject silent = new JsonObject();
        silent.addProperty("captureBindingId", "CAPTURE.leaf");
        silent.addProperty("outputSiteId", LEAF_SITE);
        silent.addProperty("outputOccurrence", 1);
        silent.addProperty("outputVersionOrdinal", 1);
        assertFalse("a guarded capture failure is not a presented leaf",
                ConcolicSummaryImporter.concreteHandoffLeaf(
                        leafSpec(OutputCaptureSpec.HANDOFF_BOUND_LEAF),
                        silent));

        // A row that names no activation-local occurrence carries no
        // exact boundary and is not presented evidence either.
        JsonObject unscoped = concrete.deepCopy();
        unscoped.addProperty("outputOccurrence", 0);
        assertFalse("a leaf without its occurrence is not an exact boundary",
                ConcolicSummaryImporter.concreteHandoffLeaf(
                        leafSpec(OutputCaptureSpec.HANDOFF_BOUND_LEAF),
                        unscoped));
    }

    /**
     * Once-only-root rule, second owner.  The recorder already refuses to
     * call an occurrence incomplete for a heap write whose recorded version
     * is an instance-level fact
     * ({@code ConcolicRegionRuntime#completeExactOutputBoundary}), and the
     * importer re-derives completeness independently over the same closure.
     * The two owners must answer alike: a per-iteration occurrence of a
     * {@code LOOP_BODY_ROOT} region that never sampled the once-entered write
     * owes no per-occurrence production of that port, so demanding a capture
     * count here imports every occurrence incomplete and the region can never
     * be composed.
     */
    @Test
    public void instanceScopedHeapWriteOwesNoPerOccurrenceCapture()
            throws Exception {
        PathImport imported = importPath("instance-scoped-write",
                heapWriteTask(true, false), heapWriteResult());

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertTrue("an occurrence that never sampled the once-entered write"
                        + " is not incomplete because of it",
                summary.get("relationallyComplete").getAsBoolean());
        // The relaxation admits the occurrence; it never invents a version.
        // The port is simply absent, which is what the composer reads as the
        // once-only rule rather than as a joint output-set mismatch.
        assertFalse("no expression is fabricated for the relaxed port",
                summary.getAsJsonObject("outputExpressions")
                        .has(HEAP_WRITE_PORT));
    }

    /** Fail-closed: only the explicit flag relaxes the demand. */
    @Test
    public void anUntaggedHeapWriteStillDemandsItsCapture()
            throws Exception {
        assertIncomplete("untagged-heap-write",
                heapWriteTask(false, false), heapWriteResult(),
                "OUTPUT_CAPTURE_COUNT:" + HEAP_WRITE_PORT + ":0");
    }

    /** Fail-closed: one writer that is not instance-scoped means some
     *  occurrence does owe this port, so the whole port stays demanded. */
    @Test
    public void oneUntaggedWriterKeepsTheWholePortDemanded()
            throws Exception {
        assertIncomplete("mixed-writers",
                heapWriteTask(true, true), heapWriteResult(),
                "OUTPUT_CAPTURE_COUNT:" + HEAP_WRITE_PORT + ":0");
    }

    /**
     * Fail-closed at the contract: the flag is only ever stamped on an exact
     * heap write, so a closure that states it on any other capture kind is
     * refused at decode and never reaches the importer's relaxation at all.
     */
    @Test
    public void theTagIsRefusedOnAnythingButAnExactHeapWrite()
            throws Exception {
        java.lang.reflect.Method decode =
                OutputCaptureSpec.class.getDeclaredMethod(
                        "decodeValidated", JsonObject.class);
        decode.setAccessible(true);
        JsonObject encoded = new JsonObject();
        encoded.addProperty("captureBindingId", "CAPTURE.leaf");
        encoded.addProperty("outputPort", "XCH.test.req.blockPoolId");
        encoded.addProperty("captureKind",
                OutputCaptureSpec.HANDOFF_BOUND_LEAF);
        encoded.addProperty("outputCell", "XCH.test.req.blockPoolId");
        encoded.addProperty("javaType", "java.lang.String");
        encoded.addProperty("occurrenceScope", "REGION_ACTIVATION");
        encoded.addProperty("outputSiteId", LEAF_SITE);
        encoded.addProperty("outputOccurrence", 1);
        encoded.addProperty(OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER, true);
        try {
            decode.invoke(null, encoded);
            fail("a handoff leaf may not claim an instance-scoped producer");
        } catch (java.lang.reflect.InvocationTargetException refused) {
            assertTrue(refused.getCause()
                    instanceof IllegalArgumentException);
            assertTrue(refused.getCause().getMessage().contains(
                    "instance-scoped producer requires an exact heap-write"));
        }
    }

    private static final String HEAP_WRITE_PORT = "REGION.SEED.out.write";
    private static final String HEAP_WRITE_CELL = "<test.Worker: int counter>";
    private static final String HEAP_WRITE_SITE =
            "FIELD_WRITE_STATE:" + seedMethod() + "#u7:" + HEAP_WRITE_CELL;

    /** One demanded heap-write port, written by one or two declared sites. */
    private static JsonObject heapWriteTask(boolean instanceScoped,
                                            boolean addUntaggedWriter) {
        JsonObject task = pathTask(false);
        task.remove("targetBranch");
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        JsonObject slice = outputSlice(HEAP_WRITE_PORT, HEAP_WRITE_CELL);
        JsonArray captures = slice.getAsJsonArray("captureBindings");
        captures.add(heapWriteCapture("CAPTURE.write", instanceScoped));
        if (addUntaggedWriter) {
            captures.add(heapWriteCapture("CAPTURE.second", false));
        }
        OutputClosureCodec.writeTo(task, OutputClosureCodec.singleton(
                "test/source/REGION.SEED", "REGION.SEED",
                Collections.singletonList(HEAP_WRITE_PORT),
                HEAP_WRITE_PORT, HEAP_WRITE_CELL, "HEAP_STATE",
                "int", slice));
        return task;
    }

    private static JsonObject heapWriteCapture(String bindingId,
                                               boolean instanceScoped) {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", bindingId);
        capture.addProperty("outputPort", HEAP_WRITE_PORT);
        capture.addProperty("captureKind", OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputCell", HEAP_WRITE_CELL);
        capture.addProperty("fieldSignature", HEAP_WRITE_CELL);
        capture.addProperty("javaType", "int");
        capture.addProperty("definitionMethod", seedMethod());
        capture.addProperty("definitionUnitIndex", 7);
        capture.addProperty("occurrenceScope", "REGION_ACTIVATION");
        capture.addProperty("outputSiteId", HEAP_WRITE_SITE);
        capture.addProperty("outputOccurrence", 1);
        if (instanceScoped) {
            capture.addProperty(
                    OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER, true);
        }
        return capture;
    }

    /** An occurrence that reached its exit without sampling the write. */
    private static JsonObject heapWriteResult() {
        JsonObject raw = pathResult(false, true);
        raw.remove(PathObservation.TargetReachEvent.FIELD);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(0));
        return raw;
    }

    /**
     * The marker serializer emits one entry per recorded condition -- a real
     * expression or a typed truncation marker -- so the auxiliary envelope's
     * three counts agree unconditionally.  A marker is a named coverage gap
     * on that path, carrying the VM's own truncation kind and the position
     * the marker states, and it fails that path closed without touching the
     * other activations of the same task.
     */
    @Test
    public void aTruncationMarkerNamesItsKindAndPosition() throws Exception {
        JsonObject auxiliary = auxiliaryPathCondition(8);
        JsonArray indices = auxiliary.getAsJsonArray("pathConditionIndices");
        JsonArray conditions = auxiliary.getAsJsonArray("conditions");
        indices.add(1);
        indices.add(2);
        conditions.add(branchPredicate(true));
        conditions.add(truncationMarker(
                "PATH_CONDITION_RANGE_BYTE_LIMIT", 1));
        auxiliary.addProperty("conditionCount", 2);
        auxiliary.addProperty("emittedConditionCount", 2);

        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliary);
        PathImport imported = importPath("marked-auxiliary-window",
                pathTask(false), raw);

        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertFalse("a marked condition still fails this path closed",
                summary.get("relationallyComplete").getAsBoolean());
        // The real expression that precedes every marker is kept: the window
        // is a genuine prefix, not a sample.
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        String detail = ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString();
        assertTrue("the gap names the VM's kind and position: " + detail,
                detail.contains("VM_EXPRESSION_SERIALIZATION_TRUNCATED:"
                        + "PATH_CONDITION_RANGE_BYTE_LIMIT:1"));
        assertFalse("agreeing counts are not a cardinality fault: " + detail,
                detail.contains(
                        "AUXILIARY_PATH_CONDITION_MALFORMED:CARDINALITY"));
    }

    /**
     * A run whose VM predates the marker serializer published a short array
     * with no way to tell a byte-capped window from a dropped one.  It is
     * refused under its own name -- no tolerance -- so a reader sees that the
     * run needs replacing rather than the schema.
     */
    @Test
    public void aLegacyEnvelopeWithoutEmittedCountIsRefusedByName()
            throws Exception {
        JsonObject auxiliary = auxiliaryPathCondition(8);
        auxiliary.getAsJsonArray("pathConditionIndices").add(1);
        auxiliary.getAsJsonArray("pathConditionIndices").add(2);
        auxiliary.getAsJsonArray("conditions").add(branchPredicate(true));
        auxiliary.addProperty("conditionCount", 2);
        auxiliary.addProperty("emittedConditionCount", 1);
        auxiliary.remove("emittedConditionCount");

        JsonObject raw = pathResult(true, true);
        installLegacyAuxiliaryPathCondition(raw, auxiliary);
        PathImport imported = importPath("legacy-auxiliary-window",
                pathTask(false), raw);

        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertFalse("a legacy envelope is not admitted",
                summary.get("relationallyComplete").getAsBoolean());
        String detail = ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString();
        assertTrue("the refusal names the legacy run: " + detail,
                detail.contains(
                        "AUXILIARY_PATH_CONDITION_LEGACY_NO_EMITTED_COUNT"));
    }

    private static JsonObject truncationMarker(String kind, int index) {
        JsonObject marker = new JsonObject();
        marker.addProperty("_type", "TruncatedExpression");
        marker.addProperty("_index", index);
        marker.addProperty("_code_position", "<test.Helper: void scan()>#u4");
        marker.addProperty("expressionAuthority",
                "VM_SERIALIZATION_TRUNCATION_V1");
        marker.addProperty("truncationKind", kind);
        return marker;
    }

    /** Installs an envelope exactly as a pre-marker VM published it. */
    private static void installLegacyAuxiliaryPathCondition(
            JsonObject raw, JsonObject auxiliary) {
        installAuxiliaryPathCondition(raw, auxiliary);
        raw.getAsJsonObject("engineSummary")
                .getAsJsonObject("auxiliaryPathCondition")
                .remove("emittedConditionCount");
    }

    private static final String LEAF_SITE =
            "HANDOFF_BOUND_LEAF:XCH.test:HANDSHAKE/blockPoolId";

    private static OutputCaptureSpec leafSpec(String captureKind)
            throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("captureBindingId", "CAPTURE.leaf");
        encoded.addProperty("outputPort", "XCH.test.req.blockPoolId");
        encoded.addProperty("captureKind", captureKind);
        encoded.addProperty("outputCell", "XCH.test.req.blockPoolId");
        encoded.addProperty("javaType", "java.lang.String");
        encoded.addProperty("occurrenceScope", "REGION_ACTIVATION");
        encoded.addProperty("outputSiteId", LEAF_SITE);
        encoded.addProperty("outputOccurrence", 1);
        java.lang.reflect.Method decode =
                OutputCaptureSpec.class.getDeclaredMethod(
                        "decodeValidated", JsonObject.class);
        decode.setAccessible(true);
        return (OutputCaptureSpec) decode.invoke(null, encoded);
    }

    private static JsonObject auxiliaryPathCondition(int watermark) {
        JsonObject auxiliary = new JsonObject();
        auxiliary.addProperty("schemaVersion", 1);
        auxiliary.addProperty("kind",
                "CONCOLIC_AUXILIARY_PATH_CONDITION");
        auxiliary.addProperty("active", true);
        auxiliary.addProperty("aborted", false);
        auxiliary.addProperty("pathConditionWatermark", watermark);
        auxiliary.addProperty("conditionCount", 0);
        auxiliary.add("pathConditionIndices", new JsonArray());
        auxiliary.add("conditions", new JsonArray());
        auxiliary.addProperty("authority",
                "VM_THREAD_AUXILIARY_PATH_CONDITION_V1");
        return auxiliary;
    }

    private static JsonObject auxiliaryContainerRelation(String relationId) {
        JsonObject relation = new JsonObject();
        relation.addProperty("_type", "ContainerRelation");
        relation.addProperty("relationId", relationId);
        relation.addProperty("kind", "ASSOCIATIVE_READ");
        return relation;
    }

    private static void installRootOutput(JsonObject raw) {
        JsonObject root = new JsonObject();
        root.addProperty("kind", "SYMBOLIC_EXPRESSION");
        root.add("expression", branchPredicate(true));
        raw.add("rootOutputExpression", root);
    }

    private static BranchWitness branchWitness(boolean outcome) {
        return BranchWitness.vmPc(seedSite(), seedMethod(), 3, 1, outcome,
                branchPredicate(outcome), 0, new JsonObject());
    }

    private static JsonObject branchPredicate(boolean outcome) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_exp", "REGION.SEED.in.value");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_exp", "Y_I_0");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_op", outcome ? ">" : "<=");
        predicate.add("_left", left);
        predicate.add("_right", right);
        return predicate;
    }

    private static String seedMethod() {
        return "<test.Worker: void run()>";
    }

    private static String seedSite() {
        return seedMethod() + "#u3";
    }

    private static final class PathImport {
        private final ConcolicSummaryImporter.ImportResult result;
        private final Path output;
        private final Path diagnostics;
        private final Path delta;

        private PathImport(ConcolicSummaryImporter.ImportResult result,
                           Path output, Path diagnostics, Path delta) {
            this.result = result;
            this.output = output;
            this.diagnostics = diagnostics;
            this.delta = delta;
        }
    }
}
