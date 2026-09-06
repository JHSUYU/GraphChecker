package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Path;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSummaryImporterTest {
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
        assertEquals(activationOccurrence(task, 1),
                event.get("sourceOccurrenceId").getAsString());
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
        setActivation(second, 2);
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
        JsonObject refusedTask = pathTask(false);
        addSeedPrefix(refusedTask, true);
        JsonObject refusedRaw = pathResult(true, false);
        addConcretePrefix(refusedRaw, false);
        PathImport refused = importPath("delta-refused", refusedTask,
                refusedRaw);
        assertEquals(0, ArtifactIO.readJsonl(refused.delta).size());
        assertEquals("BRANCH_REPLAY_MISMATCH",
                ArtifactIO.readJsonl(refused.diagnostics).get(0)
                        .get("code").getAsString());
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

    /** Adds one exact control event before the independently selected goal. */
    private static void addSeedPrefix(JsonObject task, boolean outcome) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", seedMethod() + "#u2");
        branch.addProperty("method", seedMethod());
        branch.addProperty("unitIndex", 2);
        branch.addProperty("policy", "PATH_ASSUMPTION");
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("occurrence", 1);
        occurrence.addProperty("outcome", outcome);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence);
        branch.add("occurrences", occurrences);
        task.getAsJsonArray("branches").add(branch);
    }

    /** Runtime observation of that prefix while its symbolic gate is closed. */
    private static void addConcretePrefix(JsonObject raw, boolean outcome) {
        JsonObject observation = new JsonObject();
        observation.addProperty("siteId", seedMethod() + "#u2");
        observation.addProperty("sourceTakenOutcome", outcome);
        JsonArray observations = new JsonArray();
        observations.add(observation);
        raw.add("concreteBranchWitnesses", observations);
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
                activationOccurrence(task, 1),
                "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>",
                expression, phaseIndex + 1, false, null);
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

    private static JsonObject pathResult(boolean includeMapping,
                                         boolean outcome) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("schemaVersion", 1);
        raw.addProperty("taskId", "TASK.SEED");
        setActivation(raw, 1);
        raw.addProperty("relationallyComplete", true);
        raw.addProperty(PathObservation.TARGET_REACHED, true);
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

    private static void setActivation(JsonObject raw, int ordinal) {
        String planned = "test/source#epoch0/region/REGION.SEED#1";
        raw.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, planned);
        raw.addProperty(PathObservation.ACTIVATION_ORDINAL, ordinal);
        raw.addProperty("occurrenceId", planned + "#a" + ordinal);
    }

    private static String activationOccurrence(JsonObject task, int ordinal) {
        return task.get("occurrenceId").getAsString() + "#a" + ordinal;
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
