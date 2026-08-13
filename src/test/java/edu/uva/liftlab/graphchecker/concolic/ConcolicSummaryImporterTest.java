package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.BoundedOutputVersions;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.NavigableMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ConcolicSummaryImporterTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void loopBoundCutNeverBecomesComposableRelation()
            throws Exception {
        Path directory = folder.newFolder("cut-import").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.CUT");
        task.addProperty("goalId", "GOAL.CUT");
        task.addProperty("regionId", "REGION.CUT");
        task.addProperty("sourceKey", "test/source#epoch0");
        task.addProperty("occurrenceId",
                "test/source#epoch0/region/REGION.CUT#1");
        task.addProperty("relationKey", "test/source/REGION.CUT");
        task.addProperty("relationContractHash", "CONTRACT.CUT");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.CUT");

        JsonObject cut = new JsonObject();
        cut.addProperty("event", "CONCOLIC_REGION_RESULT");
        cut.addProperty("taskId", "TASK.CUT");
        cut.addProperty("exitKind", "CUT");
        cut.addProperty("exceptionType", "");
        JsonObject pathCut = new JsonObject();
        pathCut.addProperty("kind", "LOOP_BOUND");
        pathCut.addProperty("backedgeId", "<L: void run()>#backedge:u4->u1");
        pathCut.addProperty("maxBackedgeTraversals", 8);
        pathCut.addProperty("maxLoopBodyIterations", 8);
        pathCut.addProperty("attemptedTraversal", 4);
        pathCut.addProperty("reason", "MAX_LOOP_BODY_ITERATIONS_REACHED");
        cut.add("pathCut", pathCut);
        // Even a VM-complete prefix must not be admitted as a relation.
        JsonObject engine = new JsonObject();
        engine.addProperty("complete", true);
        engine.addProperty("aborted", false);
        engine.add("pathCondition", new JsonArray());
        cut.add("engineSummary", engine);
        cut.add("unresolvedInputs", new JsonArray());
        cut.add("branchMappings", new JsonArray());

        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(task));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(cut));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.rawResultCount);
        assertEquals(0, imported.validSummaryCount);
        assertEquals(1, imported.diagnosticCount);
        assertEquals(0, ArtifactIO.readJsonl(output).size());
        List<JsonObject> rejected = ArtifactIO.readJsonl(diagnostics);
        assertEquals("LOOP_BOUND_PATH_CUT",
                rejected.get(0).get("code").getAsString());
    }

    @Test
    public void aServiceLoopResourceCapIsNamedByItsOwnLedger()
            throws Exception {
        // The replay resource cap and the unroll bound cut for opposite
        // reasons.  Reporting the cap under the unroll bound's name -- with an
        // empty body, because the unroll field was never written -- is the
        // ledger confusion the split exists to prevent.
        PathImport imported = importPath("resource-cap", pathTask(false),
                resourceCapResult(false));

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals(0, ArtifactIO.readJsonl(imported.output).size());
        JsonObject diagnostic = ArtifactIO.readJsonl(
                imported.diagnostics).get(0);
        assertEquals("REPLAY_LOOP_RESOURCE_CAP",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString()
                .contains("<L: void offerService()>#loop:u38"));
    }

    @Test
    public void theResourceCapOutranksTheUnrollBoundInTheDiagnostic()
            throws Exception {
        // The runtime publishes the resource cut first when both fire; the
        // reader must agree with it, or the two disagree about one run.
        PathImport imported = importPath("both-cuts", pathTask(false),
                resourceCapResult(true));

        assertEquals("REPLAY_LOOP_RESOURCE_CAP", ArtifactIO.readJsonl(
                imported.diagnostics).get(0).get("code").getAsString());
    }

    @Test
    public void capturedOutputBeforeResourceCapImportsAsBoundedCompletion()
            throws Exception {
        PathImport imported = importOutputPath("captured-resource-cap",
                outputBoundaryTask(2), resourceCapOutputResult(2));

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertTrue(summary.get("normalExit").getAsBoolean());
        assertTrue(summary.get("boundedExit").getAsBoolean());
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        assertEquals(2,
                summary.getAsJsonObject("outputExpressions").size());
    }

    @Test
    public void resourceCapKeepsCapturedPortsAndNamesMissingPorts()
            throws Exception {
        PathImport imported = importOutputPath("missing-resource-output",
                outputBoundaryTask(2), resourceCapOutputResult(1));

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(1, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertTrue(summary.get("boundedExit").getAsBoolean());
        assertTrue(!summary.get("relationallyComplete").getAsBoolean());
        assertEquals(1,
                summary.getAsJsonObject("outputExpressions").size());
        JsonObject diagnostic = ArtifactIO.readJsonl(
                imported.diagnostics).get(0);
        assertEquals("INCOMPLETE_RELATION",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString()
                .contains("OUTPUT_CAPTURE_COUNT:"
                        + "REGION.BOUNDARY.out.1:0"));
    }

    @Test
    public void resourceCapWithoutAnyDemandedOutputRemainsAGap()
            throws Exception {
        PathImport imported = importOutputPath("empty-resource-output",
                outputBoundaryTask(2), resourceCapOutputResult(0));

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals(1, imported.result.diagnosticCount);
        JsonObject diagnostic = ArtifactIO.readJsonl(
                imported.diagnostics).get(0);
        assertEquals("REPLAY_LOOP_RESOURCE_CAP",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString()
                .contains("no demanded output relation was captured "
                        + "before cut"));
    }

    private static JsonObject resourceCapResult(boolean alsoUnrollBound) {
        JsonObject raw = pathResult(false, true);
        raw.addProperty("exitKind", "CUT");
        JsonObject cap = new JsonObject();
        cap.addProperty("kind", "REPLAY_LOOP_RESOURCE_CAP");
        cap.addProperty("loopId", "<L: void offerService()>#loop:u38");
        cap.addProperty("maxLoopBodies", 32);
        cap.addProperty("attemptedBody", 33);
        cap.addProperty("reason", "REPLAY_LOOP_RESOURCE_CAP");
        raw.add("replayResourceCut", cap);
        if (alsoUnrollBound) {
            JsonObject pathCut = new JsonObject();
            pathCut.addProperty("kind", "LOOP_BOUND");
            pathCut.addProperty("backedgeId", "<L: void run()>#backedge:u4->u1");
            raw.add("pathCut", pathCut);
        }
        return raw;
    }

    private static JsonObject resourceCapOutputResult(int capturedCount) {
        JsonObject raw = outputBoundaryResult(capturedCount);
        raw.addProperty("exitKind", "BOUNDED");
        JsonObject cap = new JsonObject();
        cap.addProperty("kind", "REPLAY_LOOP_RESOURCE_CAP");
        cap.addProperty("loopId", "<L: void offerService()>#loop:u38");
        cap.addProperty("maxLoopBodies", 32);
        cap.addProperty("attemptedBody", 33);
        cap.addProperty("reason", "REPLAY_LOOP_RESOURCE_CAP");
        raw.add("replayResourceCut", cap);
        return raw;
    }

    @Test
    public void exactOutputBoundaryImportsAsNormalBoundedPrefix()
            throws Exception {
        Path directory = folder.newFolder("output-boundary-import").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject task = outputBoundaryTask(2);
        JsonObject raw = outputBoundaryResult(2);
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(task));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.rawResultCount);
        assertEquals(1, imported.validSummaryCount);
        assertEquals(0, imported.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(output).get(0);
        assertTrue(summary.get("normalExit").getAsBoolean());
        assertTrue(summary.get("boundedExit").getAsBoolean());
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        assertEquals(2, summary.getAsJsonObject("outputExpressions").size());
    }

    @Test
    public void producerSeedKeepsItsBoundaryPathGuard()
            throws Exception {
        JsonObject task = outputBoundaryTask(1);
        task.addProperty("pathSeedKey", "PATH.SEED.RELATION");
        task.add("branches", pathTask(false).get("branches").deepCopy());
        JsonObject raw = outputBoundaryResult(1);
        raw.getAsJsonObject("engineSummary").getAsJsonArray("pathCondition")
                .add(branchPredicate(true));

        PathImport imported = importOutputPath("relation-boundary-guard",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        assertEquals(branchPredicate(true),
                summary.getAsJsonArray("pathCondition").get(0));
        assertEquals(0, summary.getAsJsonArray("branchMappings").size());
    }

    @Test
    public void explicitFaultProducerKeepsReplayableBranchWitness()
            throws Exception {
        String fault = "REGION.BOUNDARY.in.rpcFails";
        JsonObject task = outputBoundaryTask(1);
        task.add("branches", pathTask(false).get("branches").deepCopy());
        JsonObject action = new JsonObject();
        action.addProperty("portId", fault);
        action.addProperty("symbol", fault);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("javaType", "boolean");
        action.addProperty("authority",
                "EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1");
        JsonArray actions = new JsonArray();
        actions.add(action);
        task.add("inputActions", actions);

        JsonObject predicate = branchPredicate(true);
        predicate.getAsJsonObject("_left").addProperty("_exp", fault);
        JsonObject raw = outputBoundaryResult(1);
        raw.getAsJsonObject("engineSummary").getAsJsonArray("pathCondition")
                .add(predicate);
        raw.getAsJsonArray("symbolizedInputs").add(fault);
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 1L);
        event.addProperty("contextId", 1L);
        event.addProperty("predicateNormalization", "IDENTITY");
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", seedSite());
        mapping.addProperty("method", seedMethod());
        mapping.addProperty("unitIndex", 3);
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("rawPathConditionBaseline", 0);
        mapping.addProperty("rawPathConditionSize", 1);
        mapping.add("witness", BranchWitness.vmPc(seedSite(), seedMethod(),
                3, 1, true, predicate, 0, event).toJson());
        raw.getAsJsonArray("branchMappings").add(mapping);

        PathImport imported = importOutputPath("explicit-fault-guard",
                task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(imported.output).get(0);
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        assertEquals(1, summary.getAsJsonArray("branchMappings").size());
    }

    @Test
    public void composedFieldInputDropsOnlyItsReplayMaterialization()
            throws Exception {
        JsonObject task = outputBoundaryTask(1);
        task.addProperty("pathSeedKey", "PATH.SEED.COMPOSED.FIELD");
        JsonObject action = new JsonObject();
        action.addProperty("portId", "REGION.BOUNDARY.in.key");
        action.addProperty("symbol", "REGION.BOUNDARY.in.key");
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("intraRegionSourceOutputPort",
                "REGION.BOUNDARY.out.previous-key");
        action.addProperty("intraRegionReadFromAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        JsonArray actions = new JsonArray();
        actions.add(action);
        task.add("inputActions", actions);

        JsonObject raw = outputBoundaryResult(1);
        JsonArray path = raw.getAsJsonObject("engineSummary")
                .getAsJsonArray("pathCondition");
        JsonObject definition = new JsonObject();
        definition.addProperty("_type", "BinaryExpression");
        definition.addProperty("_op", "==");
        definition.addProperty("_code_position",
                "static void java.lang.System.symbolizeExactField("
                        + "jobject,jobject,jobject,jobject,jobject):-1");
        JsonObject field = new JsonObject();
        field.addProperty("_type", "FieldAccessExpression");
        definition.add("_left", field);
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_exp",
                "M_I_field_REGION.BOUNDARY.in.key_test/Key");
        definition.add("_right", symbol);
        path.add(definition);
        path.add(branchPredicate(true));

        PathImport imported = importOutputPath(
                "composed-field-materialization", task, raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        JsonArray semanticPath = ArtifactIO.readJsonl(imported.output).get(0)
                .getAsJsonArray("pathCondition");
        assertEquals(1, semanticPath.size());
        assertEquals(branchPredicate(true), semanticPath.get(0));
    }

    @Test
    public void anObservationAtAnotherOccurrenceIsImported() throws Exception {
        // The goal states the relation without an invocation ordinal, so a
        // bounded replay that reached the site a different number of times
        // than the recording did has still observed the relation.  A failed
        // earlier occurrence is a guarded observation, not a gap.
        Path directory = folder.newFolder("relaxed-occurrence").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject raw = outputBoundaryResult(1);
        JsonArray captures = raw.getAsJsonArray("outputCaptures");
        JsonObject guarded = new JsonObject();
        guarded.addProperty("captureBindingId", "CAPTURE.0");
        guarded.addProperty("outputSiteId", "<test.Worker: void run()>#u1");
        guarded.addProperty("outputOccurrence", 1);
        guarded.addProperty("replayOccurrence", 1);
        // Twenty-six is far past the CFG loop bound: the per-site ordinal
        // counts nested-call executions too, so a bounded replay can reach
        // the site that often, and the importer must still admit it.
        captures.get(0).getAsJsonObject()
                .addProperty("outputOccurrence", 26);
        JsonArray ordered = new JsonArray();
        ordered.add(guarded);
        ordered.add(captures.get(0));
        raw.add("outputCaptures", ordered);

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(
                outputBoundaryTask(1)));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.validSummaryCount);
        assertEquals(0, imported.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(output).get(0);
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        assertEquals(1, summary.getAsJsonObject("outputExpressions").size());
    }

    @Test
    public void boundedSiteLocalOutputVersionsAreAllExported()
            throws Exception {
        // The bounded replay wrote the captured site eight times inside one
        // activation.  The ordinal is a site-local bounded index, so every
        // version is exported; which one a reader observes is settled by the
        // composed versioned channel, never by collapsing or picking here.
        Path directory = folder.newFolder("bounded-versions").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject raw = outputBoundaryResult(0);
        raw.add("outputCaptures", versionedCaptures(8, false));
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(
                outputBoundaryTask(1)));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.validSummaryCount);
        assertEquals(0, imported.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(output).get(0);
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        JsonObject outputs = summary.getAsJsonObject("outputExpressions");
        assertEquals(1, outputs.size());
        JsonObject versionSet = outputs.getAsJsonObject(
                "REGION.BOUNDARY.out.0");
        assertTrue(BoundedOutputVersions.isVersionSet(versionSet));
        assertEquals("<test.Worker: void run()>#u1",
                BoundedOutputVersions.outputSiteId(versionSet));
        NavigableMap<Integer, JsonElement> versions =
                BoundedOutputVersions.versions(versionSet);
        assertEquals(8, versions.size());
        assertEquals(Integer.valueOf(1), versions.firstKey());
        assertEquals(Integer.valueOf(8), versions.lastKey());
        assertEquals("Y_I_3", versions.get(3).getAsJsonObject()
                .get("_exp").getAsString());
    }

    @Test
    public void collidingOutputVersionOrdinalsFailClosed() throws Exception {
        Path directory = folder.newFolder("version-collision").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject raw = outputBoundaryResult(0);
        raw.add("outputCaptures", versionedCaptures(2, true));
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(
                outputBoundaryTask(1)));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.diagnosticCount);
        JsonObject diagnostic = ArtifactIO.readJsonl(diagnostics).get(0);
        assertEquals("INCOMPLETE_RELATION",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString()
                .contains("OUTPUT_CAPTURE_VERSION_COLLISION:"
                        + "REGION.BOUNDARY.out.0:1"));
    }

    @Test
    public void identicalOutputVersionOrdinalsAreDeduplicated()
            throws Exception {
        Path directory = folder.newFolder("version-duplicate").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");
        JsonObject raw = outputBoundaryResult(0);
        JsonArray captures = versionedCaptures(2, true);
        captures.get(1).getAsJsonObject().add("expression",
                captures.get(0).getAsJsonObject().get("expression")
                        .deepCopy());
        raw.add("outputCaptures", captures);
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(
                outputBoundaryTask(1)));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.validSummaryCount);
        assertEquals(0, imported.diagnosticCount);
    }

    private static JsonArray versionedCaptures(int count,
                                               boolean collide) {
        JsonArray captures = new JsonArray();
        for (int version = 1; version <= count; version++) {
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId", "CAPTURE.0");
            capture.addProperty("outputSiteId",
                    "<test.Worker: void run()>#u1");
            // Every capture is the first selected mutation of its own
            // definition invocation, so outputOccurrence is 1 throughout.
            // replayOccurrence is the request provenance and also stays 1;
            // only the boundary-wide version ordinal tells them apart.
            capture.addProperty("outputOccurrence", 1);
            capture.addProperty("outputVersionOrdinal",
                    collide ? 1 : version);
            capture.addProperty("replayOccurrence", 1);
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("_exp", "Y_I_" + version);
            capture.add("expression", expression);
            captures.add(capture);
        }
        return captures;
    }

    @Test
    public void aReferenceOutputIsKeptAsAnIdentityRelation() throws Exception {
        // The VM has no expression for a reference; the write still related
        // an exact object, and that alias is kept apart from the values so a
        // composition cannot read a scalar out of it.
        Path directory = folder.newFolder("reference-identity").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject raw = outputBoundaryResult(1);
        JsonObject capture = raw.getAsJsonArray("outputCaptures").get(0)
                .getAsJsonObject();
        capture.remove("expression");
        JsonObject identity = new JsonObject();
        identity.addProperty("authority", ConcolicSummaryImporter
                .CONCRETE_REFERENCE_IDENTITY_AUTHORITY);
        identity.addProperty("fieldSignature", "<test.State: int value0>");
        identity.addProperty("javaType", "test.Held");
        identity.addProperty("objectId", 74965L);
        capture.add("referenceIdentity", identity);

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(
                outputBoundaryTask(1)));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.validSummaryCount);
        assertEquals(0, imported.diagnosticCount);
        JsonObject summary = ArtifactIO.readJsonl(output).get(0);
        assertTrue(summary.get("relationallyComplete").getAsBoolean());
        assertEquals(0, summary.getAsJsonObject("outputExpressions").size());
        assertEquals(1, summary.getAsJsonObject(
                "outputReferenceIdentities").size());
    }

    @Test
    public void anObservationAtAnotherSiteIsRejectedFailClosed()
            throws Exception {
        Path directory = folder.newFolder("wrong-site").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject raw = outputBoundaryResult(1);
        raw.getAsJsonArray("outputCaptures").get(0).getAsJsonObject()
                .addProperty("outputSiteId",
                        "<test.Worker: void run()>#u99");
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(
                outputBoundaryTask(1)));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(0, imported.validSummaryCount);
        assertTrue(imported.diagnosticCount > 0);
    }

    @Test
    public void incompleteOutputBoundaryIsRejectedFailClosed()
            throws Exception {
        Path directory = folder.newFolder("incomplete-boundary").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.BOUNDARY");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(
                outputBoundaryTask(2)));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(
                outputBoundaryResult(1)));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(0, imported.validSummaryCount);
        assertEquals(1, imported.diagnosticCount);
        assertEquals("INCOMPLETE_OUTPUT_BOUNDARY",
                ArtifactIO.readJsonl(diagnostics).get(0)
                        .get("code").getAsString());
    }

    @Test
    public void matchingStableSeedBranchIdentityIsImported()
            throws Exception {
        PathImport imported = importPath("matching-seed",
                pathTask(false), pathResult(true, true));

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
        assertEquals(1, ArtifactIO.readJsonl(imported.output).size());
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
        assertEquals("PATH_SEED_MISMATCH",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString()
                .contains("wrong outcome"));
    }

    @Test
    public void replaySourceMustReachRequestedOppositeOutcome()
            throws Exception {
        PathImport imported = importPath("wrong-replay-source",
                pathTask(true), pathResult(true, true));

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals(1, imported.result.diagnosticCount);
        assertEquals("PATH_SEED_MISMATCH", ArtifactIO.readJsonl(
                imported.diagnostics).get(0).get("code").getAsString());
    }

    @Test
    public void matchingReplaySourceIsImported()
            throws Exception {
        PathImport imported = importPath("matching-replay-source",
                pathTask(true), pathResult(true, false));

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    @Test
    public void unreachedSeedBranchSiteIsRejectedFailClosed()
            throws Exception {
        // Neither a symbolic mapping nor a concrete execution witness: the
        // replay never reached the recorded site at all.
        PathImport imported = importPath("missing-seed-event",
                pathTask(false), pathResult(false, true));

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals("PATH_SEED_MISMATCH", ArtifactIO.readJsonl(
                imported.diagnostics).get(0).get("code").getAsString());
        assertTrue(ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString().contains("missing"));
    }

    @Test
    public void abortedSymbolicExecutionIsChargedToItselfNotToTheSeed()
            throws Exception {
        // The engine gave up mid-region, so it stopped recording branch
        // events and the activation ran on concretely to a NORMAL exit.
        // Coverage of the recorded sites necessarily fails, but the gap is
        // the abort, not a seed mismatch.  Naming the wrong one sends the
        // reader after a semantics defect that does not exist.
        JsonObject raw = pathResult(false, true);
        raw.getAsJsonObject("engineSummary")
                .addProperty("aborted", true);
        raw.getAsJsonObject("engineSummary")
                .addProperty("abortReason", "ASSOCIATIVE_OPERATION_UNSUPPORTED");

        PathImport imported = importPath("aborted-seed", pathTask(false), raw);

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals(1, imported.result.diagnosticCount);
        JsonObject diagnostic = ArtifactIO.readJsonl(
                imported.diagnostics).get(0);
        assertEquals("SYMBOLIC_EXECUTION_ABORTED",
                diagnostic.get("code").getAsString());
        assertEquals("ASSOCIATIVE_OPERATION_UNSUPPORTED",
                diagnostic.get("detail").getAsString());
    }

    @Test
    public void abortedSymbolicExecutionIsRefusedEvenWhenCoverageHolds()
            throws Exception {
        // A truncated path condition cannot be a region summary even when the
        // sites that did execute happen to attest the whole seed: the
        // constraints after the abort are missing, not merely unproven.
        JsonObject raw = pathResult(true, true);
        raw.getAsJsonObject("engineSummary")
                .addProperty("aborted", true);
        raw.getAsJsonObject("engineSummary")
                .addProperty("abortReason", "ASSOCIATIVE_MUTATOR_UNSUPPORTED");

        PathImport imported = importPath("aborted-covered",
                pathTask(false), raw);

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals(0, ArtifactIO.readJsonl(imported.output).size());
        assertEquals("SYMBOLIC_EXECUTION_ABORTED", ArtifactIO.readJsonl(
                imported.diagnostics).get(0).get("code").getAsString());
    }

    @Test
    public void anUnabortedTruncationIsStillASeedMismatch() throws Exception {
        // The converse guard: without an abort, a replay that never reached a
        // recorded site is still refused, and still as a seed mismatch.
        PathImport imported = importPath("unaborted-truncation",
                pathTask(false), pathResult(false, true));

        assertEquals(0, imported.result.validSummaryCount);
        assertEquals("PATH_SEED_MISMATCH", ArtifactIO.readJsonl(
                imported.diagnostics).get(0).get("code").getAsString());
    }

    @Test
    public void concretelyExecutedSeedBranchSiteAttestsCoverage()
            throws Exception {
        // The branch ran before the symbolic gate opened, so it has no VM
        // event. Execution still attests the recorded site.
        JsonObject raw = pathResult(false, true);
        raw.add("concreteBranchWitnesses", concreteWitnesses(true));

        PathImport imported = importPath("concrete-seed-event",
                pathTask(false), raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    @Test
    public void concreteWitnessStillFailsClosedOnTheOppositeOutcome()
            throws Exception {
        JsonObject raw = pathResult(false, true);
        raw.add("concreteBranchWitnesses", concreteWitnesses(false));

        PathImport imported = importPath("concrete-wrong-outcome",
                pathTask(false), raw);

        assertEquals(0, imported.result.validSummaryCount);
        assertTrue(ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString().contains("wrong outcome"));
    }

    @Test
    public void concreteWitnessNeverMakesASiteUnexpected() throws Exception {
        // A concrete prefix decides branches the demanded slice never
        // planned; that is ordinary execution, not a path divergence.
        JsonObject raw = pathResult(true, true);
        JsonArray witnesses = concreteWitnesses(true);
        JsonObject unplanned = witnesses.get(0).getAsJsonObject().deepCopy();
        unplanned.addProperty("siteId", "<test.Other: void run()>#u7");
        unplanned.addProperty("method", "<test.Other: void run()>");
        unplanned.addProperty("unitIndex", 7);
        witnesses.add(unplanned);
        raw.add("concreteBranchWitnesses", witnesses);

        PathImport imported = importPath("concrete-unplanned",
                pathTask(false), raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    @Test
    public void earlyStopExitDoesNotDemandCoverageOfTheRecordedTail()
            throws Exception {
        // A target-reach activation stops at its target; the recorded tail of
        // the region is never executed and cannot be witnessed.
        JsonObject raw = pathResult(false, true);
        raw.addProperty("exitKind", "TARGET_REACHED");

        PathImport imported = importPath("early-stop-tail",
                pathTask(false), raw);

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    @Test
    public void earlyStopExitStillFailsClosedOnAContradiction()
            throws Exception {
        JsonObject raw = pathResult(true, false);
        raw.addProperty("exitKind", "TARGET_REACHED");

        PathImport imported = importPath("early-stop-contradiction",
                pathTask(false), raw);

        assertEquals(0, imported.result.validSummaryCount);
        assertTrue(ArtifactIO.readJsonl(imported.diagnostics).get(0)
                .get("detail").getAsString().contains("wrong outcome"));
    }

    private static JsonArray concreteWitnesses(boolean outcome) {
        JsonObject witness = new JsonObject();
        witness.addProperty("kind", "CONCRETE_BRANCH_EXECUTION_WITNESS_V1");
        witness.addProperty("schemaVersion", 1);
        witness.addProperty("siteId", seedSite());
        witness.addProperty("method", seedMethod());
        witness.addProperty("unitIndex", 3);
        witness.addProperty("sourceTakenOutcome", outcome);
        JsonArray witnesses = new JsonArray();
        witnesses.add(witness);
        return witnesses;
    }

    @Test
    public void narrowerEnvironmentWidthKeepsTheSameSeedWitness()
            throws Exception {
        PathImport imported = importPath("narrower-width",
                widthTask(2), widthResult(1));

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    @Test
    public void widerEnvironmentWidthKeepsTheSameSeedWitness()
            throws Exception {
        PathImport imported = importPath("wider-width",
                widthTask(1), widthResult(3));

        assertEquals(1, imported.result.validSummaryCount);
        assertEquals(0, imported.result.diagnosticCount);
    }

    /**
     * The seed campaign witnessed an outcome at a site the recording only ever
     * witnessed the other way, and the flip's replay prefix carries that
     * event.  The planner may refuse such a contract before spending a solve
     * and a replay on it, but only if it refuses exactly what admission
     * refuses -- so both verdicts are pinned against each other here, in the
     * refusing direction and in the admitting one.
     */
    @Test
    public void contractSeedConflictIsTheSameVerdictEarlyAndLate()
            throws Exception {
        BranchReplayContract conflicting = BranchReplayContract.flip(
                Collections.singletonList(BranchWitness.vmPc(seedSite(),
                        seedMethod(), 3, 1, false, branchPredicate(false), 0,
                        new JsonObject())),
                BranchWitness.vmPc(seedSite(), seedMethod(), 3, 2, true,
                        branchPredicate(true), 1, new JsonObject()));
        JsonObject conflicted = pathTask(true);
        conflicted.add("replayContract", conflicting.toJson());

        String early = ConcolicSummaryImporter.plannedReplaySeedConflict(
                conflicted, conflicting);
        assertEquals("replay event conflicts with task seed at "
                + seedSite() + "#1", early);
        PathImport refused = importPath("contract-seed-conflict", conflicted,
                pathResult(true, true));
        assertEquals(0, refused.result.validSummaryCount);
        JsonObject diagnostic = ArtifactIO.readJsonl(
                refused.diagnostics).get(0);
        assertEquals("PATH_SEED_MISMATCH",
                diagnostic.get("code").getAsString());
        assertTrue(diagnostic.get("detail").getAsString().endsWith(early));

        JsonObject consistent = pathTask(true);
        assertEquals("", ConcolicSummaryImporter.plannedReplaySeedConflict(
                consistent, BranchReplayContract.fromJson(
                        consistent.getAsJsonObject("replayContract"))));
        assertEquals(1, importPath("contract-seed-agreement", consistent,
                pathResult(true, false)).result.validSummaryCount);

        // Incomplete information is not a verdict.  A source task stating no
        // seed is admitted early and still fails closed late, which is the
        // only direction the two answers are allowed to differ in.
        JsonObject seedless = pathTask(true);
        seedless.add("branches", new JsonArray());
        assertEquals("", ConcolicSummaryImporter.plannedReplaySeedConflict(
                seedless, conflicting));
        seedless.add("replayContract", conflicting.toJson());
        assertEquals(0, importPath("contract-seed-unstated", seedless,
                pathResult(true, true)).result.validSummaryCount);
    }

    private PathImport importPath(String name, JsonObject task,
                                  JsonObject raw) throws Exception {
        Path directory = folder.newFolder(name).toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");
        raw.addProperty("taskId", task.get("taskId").getAsString());
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.SEED");
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(task));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));
        return new PathImport(ConcolicSummaryImporter.importSummaries(
                results, tasks, regions, output, diagnostics), output,
                diagnostics);
    }

    private PathImport importOutputPath(String name, JsonObject task,
                                        JsonObject raw) throws Exception {
        Path directory = folder.newFolder(name).toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");
        raw.addProperty("taskId", task.get("taskId").getAsString());
        JsonObject region = new JsonObject();
        region.addProperty("regionId", task.get("regionId").getAsString());
        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(task));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));
        return new PathImport(ConcolicSummaryImporter.importSummaries(
                results, tasks, regions, output, diagnostics), output,
                diagnostics);
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
        task.addProperty("relationContractHash", "CONTRACT.SEED");
        task.addProperty("pathSeedKey", "PATH.SEED.STABLE");
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
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        if (replay) {
            task.add("replayContract", BranchReplayContract.flip(
                    Collections.<BranchWitness>emptyList(),
                    branchWitness(true)).toJson());
        }
        return task;
    }

    private static JsonObject widthTask(int occurrenceCount) {
        JsonObject task = pathTask(false);
        JsonArray occurrences = task.getAsJsonArray("branches").get(0)
                .getAsJsonObject().getAsJsonArray("occurrences");
        while (occurrences.size() < occurrenceCount) {
            JsonObject occurrence = new JsonObject();
            occurrence.addProperty("occurrence", occurrences.size() + 1);
            occurrence.addProperty("outcome", true);
            occurrences.add(occurrence);
        }
        return task;
    }

    private static JsonObject widthResult(int occurrenceCount) {
        JsonObject raw = pathResult(true, true);
        JsonArray path = raw.getAsJsonObject("engineSummary")
                .getAsJsonArray("pathCondition");
        JsonArray mappings = raw.getAsJsonArray("branchMappings");
        for (int occurrence = 2; occurrence <= occurrenceCount;
             occurrence++) {
            int pcIndex = path.size();
            path.add(branchPredicate(true));
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", seedSite());
            mapping.addProperty("method", seedMethod());
            mapping.addProperty("unitIndex", 3);
            mapping.addProperty("occurrence", occurrence);
            mapping.addProperty("rawPathConditionBaseline", pcIndex);
            mapping.addProperty("rawPathConditionSize", pcIndex + 1);
            mapping.add("witness", BranchWitness.vmPc(seedSite(),
                    seedMethod(), 3, occurrence, true,
                    branchPredicate(true), pcIndex,
                    new JsonObject()).toJson());
            mappings.add(mapping);
        }
        return raw;
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
        return raw;
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

        private PathImport(ConcolicSummaryImporter.ImportResult result,
                           Path output, Path diagnostics) {
            this.result = result;
            this.output = output;
            this.diagnostics = diagnostics;
        }
    }

    private static JsonObject outputBoundaryTask(int outputCount) {
        String region = "REGION.BOUNDARY";
        String instance = region + "@test#call1";
        String method = "<test.Worker: void run()>";
        List<OutputClosureContract> members = new ArrayList<>();
        for (int index = 0; index < outputCount; index++) {
            String port = region + ".out." + index;
            String cell = "<test.State: int value" + index + ">";
            String site = method + "#u" + (index + 1);
            JsonObject binding = new JsonObject();
            binding.addProperty("captureBindingId", "CAPTURE." + index);
            binding.addProperty("captureKind",
                    OutputCaptureSpec.FIELD_WRITE_STATE);
            binding.addProperty("outputPort", port);
            binding.addProperty("outputCell", cell);
            binding.addProperty("fieldSignature", cell);
            binding.addProperty("javaType", "int");
            binding.addProperty("definitionMethod", method);
            binding.addProperty("definitionUnitIndex", index + 1);
            binding.addProperty("outputSiteId", site);
            binding.addProperty("outputOccurrence", 1);
            binding.addProperty("replayOccurrence", 1);

            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            JsonObject slice = new JsonObject();
            slice.addProperty("outputPort", port);
            slice.addProperty("outputCell", cell);
            slice.add("inputPorts", new JsonArray());
            slice.add("sites", strings(site));
            slice.add("staticSites", strings(site));
            slice.add("methods", strings(method));
            slice.add("causalEdgeIds", new JsonArray());
            slice.add("captureBindings", bindings);
            slice.add("captureBindingIssues", new JsonArray());
            members.add(OutputClosureCodec.singleton("REL." + region, region,
                    "CONTRACT.TEST",
                    port, cell, "HEAP_STATE", "int", slice));
        }

        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.BOUNDARY");
        task.addProperty("goalId", "GOAL.BOUNDARY");
        task.addProperty("regionId", region);
        task.addProperty("sourceKey", "test/source#epoch0");
        task.addProperty("occurrenceId", instance);
        task.addProperty("relationKey", "REL." + region);
        task.addProperty("relationContractHash", "CONTRACT.TEST");
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        OutputClosureCodec.writeTo(task, OutputClosureCodec.merge(members));
        return task;
    }

    private static JsonObject outputBoundaryResult(int capturedCount) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("taskId", "TASK.BOUNDARY");
        raw.addProperty("exitKind", "OUTPUT_BOUNDARY");
        raw.addProperty("exceptionType", "");
        JsonObject engine = new JsonObject();
        engine.addProperty("complete", true);
        engine.addProperty("aborted", false);
        engine.add("pathCondition", new JsonArray());
        raw.add("engineSummary", engine);
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", new JsonArray());
        raw.add("branchMappings", new JsonArray());
        JsonArray captures = new JsonArray();
        for (int index = 0; index < capturedCount; index++) {
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId", "CAPTURE." + index);
            capture.addProperty("outputSiteId",
                    "<test.Worker: void run()>#u" + (index + 1));
            capture.addProperty("outputOccurrence", 1);
            capture.addProperty("replayOccurrence", 1);
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("_exp", "Y_I_" + index);
            capture.add("expression", expression);
            captures.add(capture);
        }
        raw.add("outputCaptures", captures);
        return raw;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }
}
