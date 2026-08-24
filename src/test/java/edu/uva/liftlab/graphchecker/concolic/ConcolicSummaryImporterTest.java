package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.Gson;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourceSelectorContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
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
    public void configuredSymbolicSourceAcceptsMultipleRequiredOutputs()
            throws Exception {
        JsonObject task = pathTask(false);
        declareSymbolicSource(task);
        JsonObject declaration = task.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).get(0).getAsJsonObject();
        declaration.remove("requiredOutputFieldSignature");
        JsonArray outputs = new JsonArray();
        outputs.add("<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: java.util.Map allKeys>");
        outputs.add("<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: org.apache.hadoop.hdfs.security.token.block.BlockKey currentKey>");
        declaration.add("requiredOutputFieldSignatures", outputs);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task)));

        PathImport imported = importPath("configured-symbolic-source-outputs",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        assertTrue(ArtifactIO.readJsonl(imported.output).get(0)
                .get("relationallyComplete").getAsBoolean());
    }

    @Test
    public void missingConfiguredSymbolicSourceMakesSeedIncomplete()
            throws Exception {
        JsonObject task = pathTask(false);
        declareSymbolicSource(task);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);

        PathImport imported = importPath("missing-configured-source",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertFalse(summary.get("relationallyComplete").getAsBoolean());
        assertTrue(ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString().contains(
                        "SYMBOLIC_SOURCE_EVIDENCE_MISSING"));
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
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        appendPublishPhase(task, 2, 2L);
        JsonObject secondDeclaration = task.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).get(0)
                .getAsJsonObject().deepCopy();
        JsonObject secondPhase = task.getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD).get(1)
                .getAsJsonObject();
        secondDeclaration.addProperty("sourcePhaseId",
                secondPhase.get("phaseId").getAsString());
        secondDeclaration.addProperty("sourcePhaseSiteId",
                secondPhase.get("siteId").getAsString());
        secondDeclaration.addProperty("sourcePhaseOrdinal",
                secondPhase.get("baselineOrdinal").getAsInt());
        task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD)
                .add(secondDeclaration);
        selectSourcePhases(task, sourcePhaseId(task, 0),
                sourcePhaseId(task, 1));
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
    public void selectedPhaseWithoutRuntimeArraysIsIncomplete()
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

    @Test
    public void emptySelectedPhaseObservationSequenceIsIncomplete()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        raw.add("configuredSourcePhaseObservations", new JsonArray());

        assertIncomplete("source-phase-ledger-empty", task, raw,
                "SYMBOLIC_SOURCE_PHASE_SELECTED_SEQUENCE_MISMATCH");
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
    public void exactObservationWithPhaseMetadataMismatchIsIncomplete()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        JsonObject raw = exactSourceRaw(task);
        raw.getAsJsonArray("configuredSourcePhaseObservations").get(0)
                .getAsJsonObject().addProperty("fieldSignature",
                "<Test: int other>");

        assertIncomplete("source-phase-ledger-mismatch", task, raw,
                "SYMBOLIC_SOURCE_PHASE_OBSERVATION_MISMATCH");
    }

    @Test
    public void reorderedSelectedPhaseSequenceIsIncomplete()
            throws Exception {
        JsonObject task = twoSelectedSourcePhaseTask();
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 1, 0);
        SymbolicSourceEvidence.writeTo(raw, Arrays.asList(
                symbolicSourceEvent(task, 0),
                symbolicSourceEvent(task, 1)));

        assertIncomplete("source-phase-ledger-reordered", task, raw,
                "SYMBOLIC_SOURCE_PHASE_SELECTED_SEQUENCE_MISMATCH");
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
    public void fullCatalogLandmarkBeforeOnlySelectedSecondIsAccepted()
            throws Exception {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        appendPublishPhase(task, 2, 2L);
        JsonObject source = task.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).get(0).getAsJsonObject();
        JsonObject second = task.getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD).get(1)
                .getAsJsonObject();
        source.addProperty("sourcePhaseId",
                second.get("phaseId").getAsString());
        source.addProperty("sourcePhaseSiteId",
                second.get("siteId").getAsString());
        source.addProperty("sourcePhaseOrdinal",
                second.get("baselineOrdinal").getAsInt());
        selectSourcePhases(task, sourcePhaseId(task, 1));
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
    public void selectorEvidenceAcceptsFieldlessCrossRegionConsumePhase()
            throws Exception {
        JsonObject task = pathTask(false);
        String sourceId = "HDFS11741.NAMENODE.CURRENT_KEY_ID";
        String field =
                "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>";
        appendSourcePhase(task, ConfiguredSourcePhaseContract.Phase.CONSUME,
                sourceId, "", 3, 1, 3L);
        String consumePhaseId = sourcePhaseId(task, 0);
        selectSourcePhases(task, consumePhaseId);
        String producerPhaseId = "SOURCE_PHASE.upstream-publish";
        String producerOccurrence = "cluster/nn0/source#1";
        JsonObject selector = ConfiguredSourceSelectorContract.exactInt(
                consumePhaseId, producerPhaseId, producerOccurrence,
                sourceId, field);
        JsonArray selectors = new JsonArray();
        selectors.add(selector);
        task.add(ConfiguredSourceSelectorContract.TASK_FIELD, selectors);
        ConfiguredSourceSelectorContract.Selector decoded =
                ConfiguredSourceSelectorContract.decode(task).get(0);
        String rawSymbol = ConfiguredSourceSelectorContract
                .expectedRawSymbolPrefix(producerPhaseId, sourceId, field)
                + "DelegationKey";
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        JsonArray evidence = new JsonArray();
        evidence.add(ConfiguredSourceSelectorContract.evidence(decoded,
                "TASK.UPSTREAM", rawSymbol, 17));
        raw.add(ConfiguredSourceSelectorContract.EVIDENCE_FIELD, evidence);

        PathImport imported = importPath("selector-phase-evidence", task,
                raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject admitted = ArtifactIO.readJsonl(imported.output).get(0)
                .getAsJsonArray(
                        ConfiguredSourceSelectorContract.EVIDENCE_FIELD)
                .get(0).getAsJsonObject();
        assertEquals(consumePhaseId,
                admitted.get("consumePhaseId").getAsString());
        assertEquals(producerPhaseId,
                admitted.get("producerPhaseId").getAsString());
    }

    @Test
    public void selectorEvidenceRejectsConsumePhaseWithWrongSourceId()
            throws Exception {
        JsonObject task = pathTask(false);
        String sourceId = "HDFS11741.NAMENODE.CURRENT_KEY_ID";
        String field =
                "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>";
        appendSourcePhase(task, ConfiguredSourcePhaseContract.Phase.CONSUME,
                "HDFS11741.OTHER.KEY_ID", "", 3, 1, 3L);
        String consumePhaseId = sourcePhaseId(task, 0);
        selectSourcePhases(task, consumePhaseId);
        JsonObject selector = ConfiguredSourceSelectorContract.exactInt(
                consumePhaseId, "SOURCE_PHASE.upstream-publish",
                "cluster/nn0/source#1", sourceId, field);
        JsonArray selectors = new JsonArray();
        selectors.add(selector);
        task.add(ConfiguredSourceSelectorContract.TASK_FIELD, selectors);
        ConfiguredSourceSelectorContract.Selector decoded =
                ConfiguredSourceSelectorContract.decode(task).get(0);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        JsonArray evidence = new JsonArray();
        evidence.add(ConfiguredSourceSelectorContract.evidence(decoded,
                "TASK.UPSTREAM", ConfiguredSourceSelectorContract
                        .expectedRawSymbolPrefix(
                                "SOURCE_PHASE.upstream-publish", sourceId,
                                field) + "DelegationKey", 17));
        raw.add(ConfiguredSourceSelectorContract.EVIDENCE_FIELD, evidence);

        assertIncomplete("selector-wrong-consume-source", task, raw,
                "CONFIGURED_SOURCE_CONSUME_PHASE_MISMATCH");
    }

    @Test
    public void targetSourceWithOutputAndInputBoundaryIsIncomplete()
            throws Exception {
        JsonObject task = pathTask(false);
        declareSymbolicSource(task);
        task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD).get(0)
                .getAsJsonObject().addProperty("requiredTargetInputPort",
                "TARGET.promotedKey");
        addTargetSourceInput(task);
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task)));

        assertIncomplete("target-source-dual-boundary", task, raw,
                "SYMBOLIC_SOURCE_DECLARATION_MALFORMED");
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
        assertEquals(LoopBoundPolicy.BOUND_FROM_POLICY,
                count.get(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY)
                        .getAsString());

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
    public void vmHandoffV3ExpressionAndProducerSurviveSummaryImport()
            throws Exception {
        // The exact destination expression travels with the VM ledger
        // reference.  Import keeps both case-local and performs no pairing.
        JsonObject rpcTask = pathTask(false);
        JsonObject rpcRaw = pathResult(true, true);
        JsonArray events = new JsonArray();
        JsonObject attachedExpression = new JsonObject();
        attachedExpression.addProperty("_type", "Int");
        attachedExpression.addProperty("_value", 17);
        events.add(VmHandoffEvidence.event("XCH.1.req.keyId", 41L,
                attachedExpression, "TASK.PRODUCER",
                "REGION.producer@Test#1"));
        rpcRaw.add(VmHandoffEvidence.FIELD, events);

        PathImport handoff = importPath("recorded-handoff", rpcTask, rpcRaw);

        JsonObject summary = ArtifactIO.readJsonl(handoff.output).get(0);
        assertEquals(1, VmHandoffEvidence.eventsOf(summary).size());
        assertEquals(41L, VmHandoffEvidence.eventsOf(summary).get(0)
                .get("exportEventId").getAsLong());
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
    public void vmHandoffV3RequiresExpressionAndExactProducer() {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "Int");
        expression.addProperty("_value", 23);
        JsonObject event = VmHandoffEvidence.event(
                "XCH.1.req.keyId", 43L, expression, "TASK.PRODUCER",
                "REGION.producer@Test#1");

        assertTrue(VmHandoffEvidence.isEvent(event));
        assertEquals(3, event.get("schemaVersion").getAsInt());
        assertEquals(expression, event.get(VmHandoffEvidence.EXPRESSION));

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
        legacy.addProperty("schemaVersion", 2);
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
                results, tasks, regions, output, diagnostics, delta,
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
                "REGION.SEED.out.0", "<Test: int output>", "REGION_OUTPUT",
                "int", outputSlice("REGION.SEED.out.0",
                        "<Test: int output>")));
        return task;
    }

    private static void declareSymbolicSource(JsonObject task) {
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId",
                "HDFS11741.NAMENODE.PROMOTED_KEY_ID");
        source.addProperty("fieldSignature",
                "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>");
        source.addProperty("requiredOutputFieldSignature",
                "<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: java.util.Map allKeys>");
        JsonArray sources = new JsonArray();
        sources.add(source);
        task.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        appendPublishPhase(task, 1, 1L);
        JsonObject phase = task.getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD).get(0)
                .getAsJsonObject();
        source.addProperty("sourcePhaseId",
                phase.get("phaseId").getAsString());
        source.addProperty("sourceOccurrenceId",
                task.get("occurrenceId").getAsString());
        source.addProperty("sourcePhaseSiteId",
                phase.get("siteId").getAsString());
        source.addProperty("sourcePhaseOrdinal",
                phase.get("baselineOrdinal").getAsInt());
        source.addProperty("sourceRole", "OUTPUT_RELATION");
        selectSourcePhases(task, phase.get("phaseId").getAsString());
    }

    private static void declareTargetSymbolicSource(JsonObject task) {
        declareSymbolicSource(task);
        JsonObject declaration = task.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).get(0).getAsJsonObject();
        declaration.remove("requiredOutputFieldSignature");
        declaration.addProperty("requiredTargetInputPort",
                "TARGET.promotedKey");
        declaration.addProperty("sourceRole", "TARGET_REACH");
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
                expression);
    }

    private static JsonObject exactSourceRaw(JsonObject task) {
        JsonObject raw = pathResult(true, true);
        installAuxiliaryPathCondition(raw, auxiliaryPathCondition(1));
        installPhaseRuntimeLedger(raw, task, 0);
        SymbolicSourceEvidence.writeTo(raw, Collections.singletonList(
                symbolicSourceEvent(task)));
        return raw;
    }

    private static JsonObject twoSelectedSourcePhaseTask() {
        JsonObject task = pathTask(false);
        declareTargetSymbolicSource(task);
        appendPublishPhase(task, 2, 2L);
        JsonObject secondDeclaration = task.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).get(0)
                .getAsJsonObject().deepCopy();
        JsonObject secondPhase = task.getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD).get(1)
                .getAsJsonObject();
        secondDeclaration.addProperty("sourcePhaseId",
                secondPhase.get("phaseId").getAsString());
        secondDeclaration.addProperty("sourcePhaseSiteId",
                secondPhase.get("siteId").getAsString());
        secondDeclaration.addProperty("sourcePhaseOrdinal",
                secondPhase.get("baselineOrdinal").getAsInt());
        task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD)
                .add(secondDeclaration);
        selectSourcePhases(task, sourcePhaseId(task, 0),
                sourcePhaseId(task, 1));
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
        java.util.Map<String, Object> declaration =
                ConfiguredSourcePhaseContract.declaration(
                        kind, sourceId, field, seedMethod(), unitIndex);
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        Collections.singletonList(declaration)).get(0);
        java.util.Map<String, Object> phase =
                ConfiguredSourcePhaseContract.occurrence(decoded,
                        task.get("occurrenceId").getAsString(), ordinal,
                        eventSeq, 1L, eventSeq,
                        "<TestHook: void symbolize()>",
                        Collections.singletonList(1L));
        JsonArray phases = task.has(ConfiguredSourcePhaseContract.PLAN_FIELD)
                ? task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                : new JsonArray();
        phases.add(GSON.toJsonTree(phase));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
    }

    private static String sourcePhaseId(JsonObject task, int index) {
        return task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .get(index).getAsJsonObject().get("phaseId").getAsString();
    }

    private static void selectSourcePhases(JsonObject task,
                                           String... phaseIds) {
        JsonArray selected = new JsonArray();
        for (String phaseId : phaseIds) selected.add(phaseId);
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD,
                selected);
    }

    private static void installPhaseRuntimeLedger(
            JsonObject raw, JsonObject task, int... phaseIndexes) {
        JsonArray observations = new JsonArray();
        java.util.Set<String> selected = new java.util.LinkedHashSet<>();
        for (com.google.gson.JsonElement element : task.getAsJsonArray(
                ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD)) {
            selected.add(element.getAsString());
        }
        JsonArray catalog = task.getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD);
        for (int observationIndex = 0;
             observationIndex < phaseIndexes.length; observationIndex++) {
            int phaseIndex = phaseIndexes[observationIndex];
            JsonObject phase = catalog.get(phaseIndex).getAsJsonObject();
            String phaseId = phase.get("phaseId").getAsString();
            String key = phase.get("phaseKind").getAsString() + "\n"
                    + phase.get("sourceId").getAsString() + "\n"
                    + phase.get("siteId").getAsString();
            int replayOrdinal = 0;
            for (int index = 0; index <= phaseIndex; index++) {
                JsonObject prior = catalog.get(index).getAsJsonObject();
                String priorKey = prior.get("phaseKind").getAsString() + "\n"
                        + prior.get("sourceId").getAsString() + "\n"
                        + prior.get("siteId").getAsString();
                if (key.equals(priorKey)) replayOrdinal++;
            }
            JsonObject observation = new JsonObject();
            observation.addProperty("schemaVersion", 1);
            observation.addProperty("kind",
                    "CONFIGURED_SOURCE_PHASE_OBSERVATION");
            observation.addProperty("authority",
                    "EXACT_ACTIVE_CALL_SITE_REPLAY_V1");
            observation.addProperty("observationIndex",
                    observationIndex + 1);
            observation.addProperty("phaseKind",
                    phase.get("phaseKind").getAsString());
            observation.addProperty("siteId",
                    phase.get("siteId").getAsString());
            observation.addProperty("replayOrdinal", replayOrdinal);
            observation.addProperty("sourceId",
                    phase.get("sourceId").getAsString());
            observation.addProperty("fieldSignature",
                    phase.get("fieldSignature").getAsString());
            observation.addProperty("matchedPhaseId", phaseId);
            observation.addProperty("ownerCallId", 101L);
            observation.addProperty("invocationId",
                    200L + observationIndex);
            observation.addProperty("declaredCallee",
                    phase.get("runtimeDeclaredCallee").getAsString());
            observation.addProperty("exactMatch", true);
            observation.addProperty("selectedPhase",
                    selected.contains(phaseId));
            observation.addProperty("orderMatched", true);
            observations.add(observation);
        }
        raw.add("configuredSourcePhaseObservations", observations);
        raw.add("configuredSourcePhaseGaps", new JsonArray());
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
        JsonArray path = new JsonArray();
        if (includeMapping) path.add(branchPredicate(outcome));
        engine.add("pathCondition", path);
        raw.add("engineSummary", engine);
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", new JsonArray());
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
            engine.add("auxiliaryPathCondition", auxiliary);
        }
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
