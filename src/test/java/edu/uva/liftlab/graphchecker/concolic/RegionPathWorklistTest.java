package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

public class RegionPathWorklistTest {
    @Test
    public void targetCaptureDoesNotEnumerateEveryRegionPath() {
        JsonObject summary = summary("ACT.TARGET",
                RegionCaptureGoal.targetBranch());
        JsonObject activation = activation("ACT.TARGET",
                RegionCaptureGoal.targetBranch());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(8, result.manifest.size());
        assertEquals("REGION.3",
                result.manifest.get("regionId").getAsString());
        assertEquals(RegionPathWorklist.State.NOT_STARTED.name(),
                result.manifest.get("state").getAsString());
        assertEquals(0, result.manifest.get(
                "observedPathCount").getAsInt());
        assertEquals(0, result.manifest.get(
                "pendingTaskCount").getAsInt());
        assertEquals("NO_OBSERVED_PATH_SEED", result.manifest
                .getAsJsonArray("gaps").get(0).getAsJsonObject()
                .get("kind").getAsString());
        assertFalse(result.manifest.has("complete"));
        assertFalse(result.manifest.has("status"));
    }

    @Test
    public void outputCaptureFlipsLatestBranchAndDropsOldSuffix() {
        JsonObject summary = summary("ACT.NEW",
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation("ACT.NEW",
                RegionCaptureGoal.outputClosure());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(2, result.tasks.size());
        JsonObject latest = result.tasks.get(0);
        BranchReplayContract replay = replayContract(latest);
        assertEquals("SITE.1", replay.source().siteId());
        assertEquals(1, replay.orderedPrefix().size());
        assertEquals(2, replay.requiredPathPredicates().size());
        assertEquals(">=", replay.requiredSatisfiedPredicate()
                .getAsJsonObject().get("_op").getAsString());
        assertEquals(BranchReplayContract.DROP_SOURCE_SUFFIX,
                latest.getAsJsonObject("replayContract")
                        .get("suffixPolicy").getAsString());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
    }

    @Test
    public void replayAdmitsNewlyObservedStaticSliceAlternative() {
        JsonObject summary = summary("ACT.NEW.ALTERNATIVE",
                RegionCaptureGoal.outputClosure());
        JsonObject slice = new JsonObject();
        JsonArray seedPathSites = new JsonArray();
        seedPathSites.add("SITE.0");
        slice.add("sites", seedPathSites);
        JsonArray staticSites = new JsonArray();
        staticSites.add("SITE.0");
        staticSites.add("SITE.1");
        slice.add("staticSites", staticSites);
        JsonArray excluded = new JsonArray();
        excluded.add("SITE.1");
        slice.add("excludedPathAlternativeSites", excluded);
        summary.add("requestedOutputSlice", slice);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation(
                        "ACT.NEW.ALTERNATIVE",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 2, result.tasks.size());
        assertEquals("SITE.1", sourceSite(result.tasks.get(0)));
        assertEquals("SITE.0", sourceSite(result.tasks.get(1)));
    }

    @Test
    public void witnessSummaryEmitsOneAuthoritativeReplayContract() {
        JsonObject summary = summary("ACT.WITNESS",
                RegionCaptureGoal.outputClosure());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.WITNESS",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        JsonObject latest = result.tasks.get(0);
        assertEquals(3, latest.get("schemaVersion").getAsInt());
        BranchReplayContract contract = BranchReplayContract.fromJson(
                latest.getAsJsonObject("replayContract"));
        assertEquals("SITE.1", contract.source().siteId());
        assertEquals(1, contract.orderedPrefix().size());
        assertEquals(">=", contract.requiredSatisfiedPredicate()
                .getAsJsonObject().get("_op").getAsString());
        assertFalse(latest.has("constraints"));
        assertFalse(latest.has("flipSite"));
        assertFalse(latest.has("desiredOutcome"));
        assertFalse(latest.has("negatedCondition"));
    }

    @Test
    public void arrayLoadContextIsSeparatedFromTheBranchContract() {
        JsonObject summary = summary("ACT.ARRAY.CONTEXT",
                RegionCaptureGoal.outputClosure());
        JsonObject arrayLoad = new JsonObject();
        arrayLoad.addProperty("_type", "_array_expr");
        arrayLoad.addProperty("_arr_str", "AL_1");
        arrayLoad.addProperty("_is_load", true);
        JsonObject index = new JsonObject();
        index.addProperty("_type", "ConstExpr");
        index.addProperty("_java_type", "I");
        index.addProperty("_exp", "Y_I_1");
        arrayLoad.add("_index_exp", index);
        JsonObject value = new JsonObject();
        value.addProperty("_type", "SymbolExpression");
        value.addProperty("_java_type", "Lexample/State;");
        value.addProperty("_exp", "EL_1-0-1");
        arrayLoad.add("_value_exp", value);
        JsonArray conditions = new JsonArray();
        conditions.add(arrayLoad);
        conditions.add(binary("<", 5));
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping("SITE.1", 1));
        summary.add("branchMappings", mappings);
        authorizeVmPcMappings(summary);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation(
                        "ACT.ARRAY.CONTEXT",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 1, result.tasks.size());
        JsonObject task = result.tasks.get(0);
        BranchReplayContract replay = replayContract(task);
        assertTrue(replay.orderedPrefix().isEmpty());
        SolverPathContext context = SolverPathContext.fromJson(
                task.getAsJsonObject("solverPathContext"));
        assertEquals(1, context.size());
        assertEquals(arrayLoad, context.expressions().get(0));
        assertFalse(task.has("constraints"));
    }

    @Test
    public void summaryWithoutBranchPolicyFailsClosed() {
        JsonObject summary = summary("ACT.LEGACY",
                RegionCaptureGoal.outputClosure());
        summary.getAsJsonArray("branchMappings").get(0).getAsJsonObject()
                .remove("policy");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.LEGACY",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                result.manifest.get("state").getAsString());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString(),
                result.manifest.getAsJsonArray("gaps").toString()
                        .contains("INVALID_BRANCH_MAPPING_SCHEMA"));
    }

    @Test
    public void policyAwareSummaryEnumeratesOnlyExploreMappings() {
        JsonObject summary = summary("ACT.POLICY",
                RegionCaptureGoal.outputClosure());
        JsonArray mappings = summary.getAsJsonArray("branchMappings");
        mappings.get(0).getAsJsonObject().addProperty("policy",
                "PATH_ASSUMPTION");
        mappings.get(1).getAsJsonObject().addProperty("policy", "EXPLORE");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.POLICY",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(1, result.tasks.size());
        assertEquals("SITE.1", sourceSite(result.tasks.get(0)));
    }

    @Test
    public void policyAwareSummaryFailsClosedForUnknownPolicy() {
        JsonObject summary = summary("ACT.FAIL.CLOSED",
                RegionCaptureGoal.outputClosure());
        summary.getAsJsonArray("branchMappings").get(1).getAsJsonObject()
                .addProperty("policy", "UNKNOWN");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.FAIL.CLOSED",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                result.manifest.get("state").getAsString());
        assertEquals(1, result.manifest.getAsJsonArray("gaps").size());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("unsupported branch policy: UNKNOWN"));
    }

    @Test
    public void stableFlipIdentityExcludesActivationIdsAndUnsatClosesIt() {
        JsonObject first = summary("ACT.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.2",
                RegionCaptureGoal.outputClosure());
        JsonObject activation1 = activation("ACT.1",
                RegionCaptureGoal.outputClosure());
        JsonObject activation2 = activation("ACT.2",
                RegionCaptureGoal.outputClosure());

        RegionPathWorklist.Result initial = RegionPathWorklist.plan(
                Arrays.asList(first, second), Arrays.asList(activation1,
                        activation2), Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(2, initial.tasks.size());

        List<JsonObject> records = new ArrayList<>();
        for (JsonObject task : initial.tasks) {
            JsonObject record = new JsonObject();
            record.addProperty("queryKey", task.get("queryKey").getAsString());
            record.addProperty("status", "UNSAT");
            records.add(record);
        }
        RegionPathWorklist.Result closed = RegionPathWorklist.plan(
                Arrays.asList(first, second), Arrays.asList(activation1,
                        activation2), records,
                RegionPathWorklist.Bounds.defaults());

        assertTrue(closed.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                closed.manifest.get("state").getAsString());
        assertEquals(1, closed.manifest.get(
                "observedPathCount").getAsInt());
        assertEquals(0, closed.manifest.get(
                "pendingTaskCount").getAsInt());
    }

    @Test
    public void oppositeObservedFrontiersCloseWithoutReverseReplay() {
        JsonObject taken = oneBranchSummary("ACT.TAKEN", ">", true, -1);
        JsonObject notTaken = oneBranchSummary("ACT.NOT.TAKEN", "<=",
                false, 1);
        assertNotEquals(RegionPathWorklist.stablePathKey(taken),
                RegionPathWorklist.stablePathKey(notTaken));

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Arrays.asList(taken, notTaken), Arrays.asList(
                        activation("ACT.TAKEN",
                                RegionCaptureGoal.outputClosure()),
                        activation("ACT.NOT.TAKEN",
                                RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.toString(), result.tasks.isEmpty());
        assertEquals(result.manifest.toString(),
                RegionPathWorklist.State.CLOSED.name(),
                result.manifest.get("state").getAsString());
        assertEquals(2, result.manifest.get(
                "observedPathCount").getAsInt());
        assertTrue(result.manifest.getAsJsonArray("gaps").isEmpty());
    }

    @Test
    public void observedOutcomeUnderDifferentPrefixDoesNotCloseFlip() {
        JsonObject first = summary("ACT.PREFIX.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.PREFIX.2",
                RegionCaptureGoal.outputClosure());
        second.getAsJsonArray("pathCondition").set(0, binary("<=", 0));
        second.getAsJsonArray("pathCondition").set(1, binary(">=", 5));
        replaceWitnessOutcomes(second, false);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Arrays.asList(first, second), Arrays.asList(
                        activation("ACT.PREFIX.1",
                                RegionCaptureGoal.outputClosure()),
                        activation("ACT.PREFIX.2",
                                RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 2, result.tasks.size());
        assertTrue(result.tasks.stream().allMatch(task -> "SITE.1".equals(
                sourceSite(task))));
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
    }

    @Test
    public void materializationGapIsTerminalAndSurfacesExplorationGap() {
        JsonObject summary = summary("ACT.GAP",
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation("ACT.GAP",
                RegionCaptureGoal.outputClosure());
        RegionPathWorklist.Result initial = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        List<JsonObject> records = new ArrayList<>();
        for (JsonObject task : initial.tasks) {
            JsonObject record = new JsonObject();
            record.addProperty("queryKey",
                    task.get("queryKey").getAsString());
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT");
            records.add(record);
        }

        RegionPathWorklist.Result replanned = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation), records,
                RegionPathWorklist.Bounds.defaults());

        assertTrue(replanned.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                replanned.manifest.get("state").getAsString());
        assertEquals(0, replanned.manifest.get(
                "pendingTaskCount").getAsInt());
        assertTrue(replanned.manifest.getAsJsonArray("gaps").toString()
                .contains("EXPLORATION_GAP"));
        assertTrue(replanned.manifest.getAsJsonArray("gaps").toString()
                .contains("OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT"));
    }

    @Test
    public void incompleteRegionSummaryIsAGapAndIsNeverFlipped() {
        JsonObject summary = summary("ACT.INCOMPLETE",
                RegionCaptureGoal.outputClosure());
        summary.addProperty("relationallyComplete", false);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.INCOMPLETE",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                result.manifest.get("state").getAsString());
        assertEquals("INCOMPLETE_REGION_SUMMARY", result.manifest
                .getAsJsonArray("gaps").get(0).getAsJsonObject()
                .get("kind").getAsString());
    }

    @Test
    public void quarantinedDiscoverySeedMayFlipOnlyItsReachabilityGuard() {
        JsonObject summary = summary("ACT.DISCOVERY",
                RegionCaptureGoal.transitionDiscovery());
        summary.addProperty("relationallyComplete", false);
        summary.addProperty("normalExit", true);
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        JsonArray sites = new JsonArray();
        sites.add("SITE.1");
        slice.add("sites", sites);
        slice.add("inputPorts", new JsonArray());
        summary.add("requestedOutputSlice", slice);
        JsonObject discovery = new JsonObject();
        discovery.addProperty("candidateEdgeId", "EDGE.P.C");
        discovery.addProperty("guardSiteId", "SITE.1");
        discovery.addProperty("guardOccurrence", 1);
        discovery.addProperty("desiredOutcome", false);
        discovery.addProperty("seedExecutionId", "EXEC.1");
        summary.add("transitionDiscovery", discovery);
        JsonObject activation = activation("ACT.DISCOVERY",
                RegionCaptureGoal.transitionDiscovery());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 1, result.tasks.size());
        JsonObject task = result.tasks.get(0);
        assertEquals("SITE.1", sourceSite(task));
        assertTrue(task.get("discoveryOnly").getAsBoolean());
        assertTrue(RegionCaptureGoal.from(task).isTransitionDiscovery());
        assertEquals("QUARANTINED", task.get(
                "summaryCacheAdmission").getAsString());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());

        JsonObject anotherExecution = summary.deepCopy();
        anotherExecution.getAsJsonObject("transitionDiscovery").addProperty(
                "seedExecutionId", "EXEC.99");
        RegionPathWorklist.Result replanned = RegionPathWorklist.plan(
                Collections.singletonList(anotherExecution),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(task.get("queryKey").getAsString(), replanned.tasks
                .get(0).get("queryKey").getAsString());

        JsonObject legacyTopLevel = summary.deepCopy();
        legacyTopLevel.addProperty("requestedOutputSliceComplete", true);
        legacyTopLevel.getAsJsonObject("requestedOutputSlice")
                .addProperty("complete", false);
        RegionPathWorklist.Result nestedFalse = RegionPathWorklist.plan(
                Collections.singletonList(legacyTopLevel),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertTrue(nestedFalse.tasks.isEmpty());

        legacyTopLevel.remove("requestedOutputSlice");
        RegionPathWorklist.Result nestedMissing = RegionPathWorklist.plan(
                Collections.singletonList(legacyTopLevel),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertTrue(nestedMissing.tasks.isEmpty());
    }

    @Test
    public void stablePathIdentityAlphaNormalizesOnlyExecutionLocals() {
        JsonObject first = summary("ACT.ALPHA.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.ALPHA.2",
                RegionCaptureGoal.outputClosure());
        replaceConditionSymbol(first, "M_I_1");
        replaceConditionSymbol(second, "M_I_97");
        first.getAsJsonObject("outputExpressions").add(
                "REGION.3.out.0", localSymbol("M_I_1"));
        second.getAsJsonObject("outputExpressions").add(
                "REGION.3.out.0", localSymbol("M_I_97"));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentAlias = second.deepCopy();
        differentAlias.getAsJsonArray("pathCondition").get(1)
                .getAsJsonObject().getAsJsonObject("_left")
                .addProperty("_exp", "M_I_98");
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentAlias));
    }

    @Test
    public void stablePathIdentityPreservesCanonicalActivationPorts() {
        JsonObject first = summary("ACT.PORT.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.PORT.2",
                RegionCaptureGoal.outputClosure());
        first.add("symbolicInputs", strings("REGION.3.in.0"));
        second.add("symbolicInputs", strings("REGION.3.in.1"));
        replaceConditionSymbol(first,
                "M_I_field_REGION.3.in.0_java/lang/Integer");
        replaceConditionSymbol(second,
                "M_I_field_REGION.3.in.1_java/lang/Integer");

        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));
    }

    @Test
    public void dynamicSelectorIsStableAcrossObjectTokensButKeepsOccurrence()
            throws Exception {
        JsonObject first = summary("ACT.DYNAMIC.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.DYNAMIC.2",
                RegionCaptureGoal.outputClosure());
        first.add("dynamicFieldBindings", dynamicBindings("OBJECT.1", 2,
                "key-two"));
        second.add("dynamicFieldBindings", dynamicBindings("OBJECT.99", 2,
                "key-two"));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentOccurrence = second.deepCopy();
        differentOccurrence.getAsJsonArray("dynamicFieldBindings").get(0)
                .getAsJsonObject().addProperty("materializationOccurrence",
                1);
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentOccurrence));

        RegionPathWorklist.Result planned = RegionPathWorklist.plan(
                Collections.singletonList(first),
                Collections.singletonList(activation("ACT.DYNAMIC.1",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(2, planned.tasks.get(0).getAsJsonArray(
                "dynamicFieldBindings").get(0).getAsJsonObject().get(
                "materializationOccurrence").getAsInt());
    }

    @Test
    public void mapProjectionStableKeyErasesTokensButKeepsIndexAndOperation() {
        JsonObject first = summary("ACT.MAP.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.MAP.2",
                RegionCaptureGoal.outputClosure());
        first.add("dynamicFieldBindings", mapProjectionBindings(
                "ACT.MAP.1", 10L, 20L, 30L, 0,
                "MAP_VALUES_VIEW"));
        second.add("dynamicFieldBindings", mapProjectionBindings(
                "ACT.MAP.2", 100L, 200L, 300L, 0,
                "MAP_VALUES_VIEW"));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentIndex = second.deepCopy();
        differentIndex.add("dynamicFieldBindings", mapProjectionBindings(
                "ACT.MAP.2", 100L, 200L, 300L, 1,
                "MAP_VALUES_VIEW"));
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentIndex));

        JsonObject differentOperation = second.deepCopy();
        differentOperation.add("dynamicFieldBindings",
                mapProjectionBindings("ACT.MAP.2", 100L, 200L, 300L, 0,
                        "MAP_KEY_SET_VIEW"));
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentOperation));
    }

    @Test
    public void engineArrayBridgeAlphaNormalizesIdsButPreservesPortJoin() {
        JsonObject first = summary("ACT.ARRAY.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.ARRAY.2",
                RegionCaptureGoal.outputClosure());
        first.getAsJsonArray("pathCondition").set(0,
                arrayLoad("VM_ARRAY_1"));
        second.getAsJsonArray("pathCondition").set(0,
                arrayLoad("VM_ARRAY_99"));
        first.add("engineArrayInputBindings", engineArrayBindings(
                "REGION.3.in.0", "VM_ARRAY_1", 7));
        second.add("engineArrayInputBindings", engineArrayBindings(
                "REGION.3.in.0", "VM_ARRAY_99", 700));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentPort = second.deepCopy();
        differentPort.add("engineArrayInputBindings", engineArrayBindings(
                "REGION.3.in.1", "VM_ARRAY_99", 700));
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentPort));
    }

    @Test
    public void pathFlipTaskCarriesExactEngineArrayBridgeCatalog() {
        JsonObject summary = summary("ACT.ARRAY.TASK",
                RegionCaptureGoal.outputClosure());
        JsonArray bindings = engineArrayBindings("REGION.3.in.0",
                "VM_ARRAY_TASK", 17);
        summary.add("engineArrayInputBindings", bindings);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.ARRAY.TASK",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertFalse(result.tasks.isEmpty());
        assertEquals(bindings, result.tasks.get(0).getAsJsonArray(
                "engineArrayInputBindings"));
    }

    @Test
    public void boundedNumericLoopKeepsEveryOccurrenceAndFailsClosedWhenUnmapped() {
        JsonObject summary = summary("ACT.NUMERIC.LOOP",
                RegionCaptureGoal.outputClosure());
        JsonArray conditions = new JsonArray();
        conditions.add(typedBinary(">=", "J", 7));
        conditions.add(typedBinary("<", "D", 3));
        conditions.add(typedBinary("<", "I", 3));
        conditions.add(typedBinary("<", "I", 3));
        conditions.add(typedBinary(">=", "I", 3));
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping("NUMERIC.LONG", 0, 1));
        mappings.add(mapping("NUMERIC.DOUBLE", 1, 1));
        mappings.add(mapping("NUMERIC.LOOP.GUARD", 2, 1));
        mappings.add(mapping("NUMERIC.LOOP.GUARD", 3, 2));
        mappings.add(mapping("NUMERIC.LOOP.GUARD", 4, 3));
        summary.add("branchMappings", mappings);
        authorizeVmPcMappings(summary);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.NUMERIC.LOOP",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 5, result.tasks.size());
        assertEquals("NUMERIC.LOOP.GUARD", sourceSite(result.tasks.get(0)));
        assertEquals(3, replayContract(result.tasks.get(0)).source()
                .occurrence());
        assertEquals(2, replayContract(result.tasks.get(1)).source()
                .occurrence());
        assertEquals(1, replayContract(result.tasks.get(2)).source()
                .occurrence());
        assertEquals("D", replayContract(result.tasks.get(3))
                .requiredSatisfiedPredicate().getAsJsonObject()
                .getAsJsonObject("_left")
                .get("_java_type").getAsString());
        assertEquals("J", replayContract(result.tasks.get(4))
                .requiredSatisfiedPredicate().getAsJsonObject()
                .getAsJsonObject("_left")
                .get("_java_type").getAsString());
        assertEquals(5, result.tasks.stream().map(task -> task.get(
                "queryKey").getAsString()).distinct().count());

        JsonObject unmodeled = summary.deepCopy();
        JsonArray onlyUnmapped = new JsonArray();
        onlyUnmapped.add(SummaryBranchMapping.concrete(
                ExactConcreteBranchObservation.attested(
                        "NUMERIC.LOOP.GUARD",
                        "<test.Region: void run()>", 4, 3, true),
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        unmodeled.add("branchMappings", onlyUnmapped);
        RegionPathWorklist.Result rejected = RegionPathWorklist.plan(
                Collections.singletonList(unmodeled),
                Collections.singletonList(activation("ACT.NUMERIC.LOOP",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertTrue(rejected.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                rejected.manifest.get("state").getAsString());
        JsonObject gap = rejected.manifest.getAsJsonArray("gaps").get(0)
                .getAsJsonObject();
        assertEquals("UNMAPPED_BRANCH", gap.get("kind").getAsString());
        assertEquals("NO_NORMALIZED_CONDITION", gap.get("reason")
                .getAsString());
        assertEquals(3, gap.get("occurrence").getAsInt());
    }

    @Test
    public void concreteBranchCoveredAtSamePositionNeedsNoBorrowedPredicate() {
        JsonObject modeled = exactBranchTemplateSummary("ACT.MODELED",
                false);
        JsonObject concrete = exactBranchTemplateSummary("ACT.CONCRETE",
                true);
        List<JsonObject> summaries = Arrays.asList(modeled, concrete);
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.MODELED", RegionCaptureGoal.outputClosure()),
                activation("ACT.CONCRETE", RegionCaptureGoal.outputClosure()));

        RegionPathWorklist.Result initial = RegionPathWorklist.plan(
                summaries, activations, Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(initial.tasks.toString(), initial.tasks.isEmpty());
        assertEquals(initial.manifest.toString(),
                RegionPathWorklist.State.CLOSED.name(),
                initial.manifest.get("state").getAsString());
        assertTrue(initial.manifest.getAsJsonArray("gaps").isEmpty());
    }

    @Test
    public void exactConcreteSwitchDoesNotBorrowBinaryIfPredicate() {
        JsonObject modeled = exactBranchTemplateSummary("ACT.SWITCH.MODELED",
                false);
        JsonObject concrete = exactBranchTemplateSummary(
                "ACT.SWITCH.CONCRETE", true);
        JsonObject mapping = concrete.getAsJsonArray("branchMappings").get(1)
                .getAsJsonObject();
        mapping.remove("concreteObservation");
        mapping.addProperty("branchKind", "TABLE_SWITCH");
        mapping.addProperty("observedSuccessorIndex", 2);
        JsonArray keys = new JsonArray();
        keys.add(0);
        keys.add(1);
        mapping.add("switchCaseKeys", keys);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Arrays.asList(modeled, concrete), Arrays.asList(
                        activation("ACT.SWITCH.MODELED",
                                RegionCaptureGoal.outputClosure()),
                        activation("ACT.SWITCH.CONCRETE",
                                RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                result.manifest.get("state").getAsString());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("INVALID_BRANCH_MAPPING_SCHEMA"));
    }

    private static JsonObject exactBranchTemplateSummary(
            String activationId, boolean concreteUpperGuard) {
        JsonObject result = summary(activationId,
                RegionCaptureGoal.outputClosure());
        result.add("symbolicInputs", strings("REGION.3.in.0"));
        JsonArray conditions = new JsonArray();
        conditions.add(binary("<", 0));
        if (!concreteUpperGuard) conditions.add(binary("<=", 4));
        result.add("pathCondition", conditions);

        JsonArray mappings = new JsonArray();
        JsonObject lower = mapping("SITE.CLAMP.LOWER", 0);
        lower.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(lower);
        JsonObject upper = exactVmIfMapping("SITE.CLAMP.UPPER",
                concreteUpperGuard ? -1 : 1, true,
                concreteUpperGuard ? 0 : 1);
        upper.addProperty("policy", concreteUpperGuard
                ? "EXPLORE" : "PATH_ASSUMPTION");
        upper.addProperty("pathConditionBaseline", 1);
        if (!concreteUpperGuard) {
            upper.add("condition", conditions.get(1).deepCopy());
        }
        mappings.add(upper);
        result.add("branchMappings", mappings);
        authorizeVmPcMappings(result);
        return result;
    }

    private static JsonObject exactVmIfMapping(String site,
                                               int conditionIndex,
                                               boolean outcome,
                                               int conditionCount) {
        JsonObject mapping = mapping(site, conditionIndex);
        mapping.addProperty("branchKind", "IF");
        mapping.addProperty("method", "<example.Producer: int compute(int)>");
        mapping.addProperty("unitIndex", 6);
        mapping.addProperty("expression", "i3 <= 4");
        mapping.addProperty("outcome", outcome);
        mapping.addProperty("observedOutcome", outcome);
        mapping.addProperty("effectiveOutcome", outcome);
        mapping.addProperty("overrideApplied", false);
        mapping.addProperty("overrideMode", "NONE");
        mapping.addProperty("mappingPolicy",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX");
        mapping.addProperty("vmBranchEventExpected", true);
        mapping.addProperty("vmBranchEventId", 17);
        mapping.addProperty("vmOccurrence", 1);
        mapping.addProperty("vmBranchEventValidated", true);
        mapping.addProperty("vmBranchEventAuthority",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
        mapping.addProperty("vmThreadContextId", 7L);
        mapping.addProperty("vmOwnerJavaThreadId", 11L);
        mapping.addProperty("vmOwnerOsThreadId", 13L);
        JsonArray indices = new JsonArray();
        if (conditionCount == 1) indices.add(1);
        mapping.add("vmConditionIndices", indices);
        mapping.addProperty("conditionAuthority", conditionCount == 0
                ? "VM_THREAD_CONTEXT_EXACT_CONCRETE_BRANCH_EVENT"
                : "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX");
        return mapping;
    }

    private static void replaceConditionSymbol(JsonObject summary,
                                               String symbol) {
        for (com.google.gson.JsonElement element : summary.getAsJsonArray(
                "pathCondition")) {
            element.getAsJsonObject().getAsJsonObject("_left")
                    .addProperty("_exp", symbol);
        }
    }

    private static JsonObject localSymbol(String raw) {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", raw);
        return symbol;
    }

    private static JsonArray strings(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray dynamicBindings(String objectToken,
                                             int occurrence, String key) {
        JsonArray result = new JsonArray();
        JsonObject binding = new JsonObject();
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("baseInputSymbol", "REGION.3.in.0");
        binding.addProperty("dynamicFieldSymbol",
                "REGION.3.in.0.field.stable.occ." + occurrence);
        binding.addProperty("materializationSiteId", "SITE.FIELD");
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("leafOwnerObjectToken", objectToken);
        JsonObject selector = new JsonObject();
        selector.addProperty("_type", "ConstExpr");
        selector.addProperty("_exp", key);
        binding.add("keyExpression", selector);
        binding.addProperty("keyExpressionAuthority", "RUNTIME_KEY");
        binding.addProperty("complete", true);
        result.add(binding);
        return result;
    }

    private static JsonArray mapProjectionBindings(
            String scope, long mapToken, long elementToken,
            long outputToken, int index, String operation) {
        JsonObject binding = new JsonObject();
        binding.addProperty("kind",
                "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
        binding.addProperty("baseInputSymbol", "REGION.3.in.0");
        binding.addProperty("dynamicFieldSymbol",
                "REGION.3.in.0.field.mapstable.occ." + (index + 1));
        binding.addProperty("materializationSiteId", "SITE.MAP");
        binding.addProperty("materializationOccurrence", index + 1);
        binding.addProperty("fieldSignature", "<example.Value: long expiry>");
        binding.add("fieldPath", strings("expiry"));
        binding.addProperty("leafOwnerObjectToken", elementToken);
        binding.addProperty("objectTokenScope", scope);
        binding.addProperty("entrySnapshotElementCount", 2);
        binding.addProperty("outputElementCount", 2);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.MAP");
        selector.addProperty("mapInputPort", "REGION.3.in.0");
        selector.addProperty("mapInputCell", "<Producer: Map values>");
        selector.addProperty("outputPort", "REGION.3.out.1");
        selector.addProperty("outputCell", "<Payload: Value[] values>");
        selector.addProperty("mapProjectionOperation", operation);
        selector.addProperty("outputIndex", index);
        selector.addProperty("elementOccurrence", index + 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Value");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature",
                "<example.Value: long expiry>");
        selector.addProperty("mapObjectToken", mapToken);
        selector.addProperty("elementObjectToken", elementToken);
        selector.addProperty("outputArrayObjectToken", outputToken);
        selector.addProperty("objectTokenScope", scope);
        selector.addProperty("complete", true);
        binding.add("mapProjectionSelector", selector);
        binding.addProperty("complete", true);
        JsonArray result = new JsonArray();
        result.add(binding);
        return result;
    }

    private static JsonObject arrayLoad(String arrayId) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "_array_expr");
        result.addProperty("_is_load", true);
        result.addProperty("_arr_str", arrayId);
        result.add("_index_exp", localSymbol("M_I_INDEX"));
        result.add("_value_exp", localSymbol("M_I_VALUE"));
        return result;
    }

    private static JsonArray engineArrayBindings(String port, String id,
                                                 long token) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        binding.addProperty("inputPort", port);
        binding.addProperty("inputCell",
                "<example.Handler: void run(java.lang.Object[])>"
                        + ".param0:java.lang.Object[]");
        binding.addProperty("inputJavaType", "java.lang.Object[]");
        binding.addProperty("inputJavaTypeDescriptor",
                "[Ljava/lang/Object;");
        binding.addProperty("symbolizationPrefix", port);
        binding.addProperty("symbolizationMode",
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
        binding.addProperty("engineArrayId", id);
        binding.addProperty("engineArrayIdAuthority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        binding.addProperty("arrayObjectToken", token);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("symbolizationIdentityAuthority",
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE");
        binding.addProperty("sameArrayObjectTokenVerified", true);
        binding.addProperty("captureAuthority",
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION");
        binding.addProperty("complete", true);
        JsonArray result = new JsonArray();
        result.add(binding);
        return result;
    }

    private static JsonObject activation(String id, RegionCaptureGoal goal) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", id);
        activation.addProperty("regionId", "REGION.3");
        activation.add("captureGoal", goal.toJson());
        return activation;
    }

    private static JsonObject summary(String activationId,
                                      RegionCaptureGoal goal) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + activationId);
        summary.addProperty("activationId", activationId);
        summary.addProperty("regionId", "REGION.3");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", goal.toJson());
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.3.out.0");
        summary.add("requestedOutput", output);

        JsonArray conditions = new JsonArray();
        conditions.add(binary(">", 0));
        conditions.add(binary("<", 5));
        summary.add("pathCondition", conditions);

        JsonArray mappings = new JsonArray();
        mappings.add(mapping("SITE.0", 0));
        mappings.add(mapping("SITE.1", 1));
        summary.add("branchMappings", mappings);
        summary.add("outputExpressions", new JsonObject());
        summary.add("heapEffects", new JsonArray());
        authorizeVmPcMappings(summary);
        return summary;
    }

    private static JsonObject oneBranchSummary(String activationId,
                                               String operator,
                                               boolean outcome,
                                               int outputValue) {
        JsonObject result = summary(activationId,
                RegionCaptureGoal.outputClosure());
        JsonArray conditions = new JsonArray();
        conditions.add(binary(operator, 0));
        result.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        JsonObject mapping = mapping("SITE.0", 0);
        mapping.addProperty("outcome", outcome);
        mappings.add(mapping);
        result.add("branchMappings", mappings);
        authorizeVmPcMappings(result);
        JsonObject outputs = new JsonObject();
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConstExpr");
        value.addProperty("_java_type", "I");
        value.addProperty("_exp", "Y_I_" + outputValue);
        outputs.add("REGION.3.out.0", value);
        result.add("outputExpressions", outputs);
        return result;
    }

    private static void authorizeVmPcMappings(JsonObject summary) {
        JsonArray conditions = summary.getAsJsonArray("pathCondition");
        JsonArray canonical = new JsonArray();
        for (com.google.gson.JsonElement element
                : summary.getAsJsonArray("branchMappings")) {
            JsonObject mapping = element.getAsJsonObject();
            int conditionIndex = mapping.get("conditionIndex").getAsInt();
            SummaryBranchMapping.Policy policy =
                    SummaryBranchMapping.Policy.fromWire(
                            mapping.has("policy")
                                    ? mapping.get("policy").getAsString()
                                    : "EXPLORE");
            if (conditionIndex < 0 || conditionIndex >= conditions.size()) {
                canonical.add(SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                mapping.get("siteId").getAsString(),
                                "<test.Region: void run()>", 0,
                                mapping.get("occurrence").getAsInt(),
                                mapping.get("outcome").getAsBoolean()),
                        policy).toJson());
                continue;
            }
            JsonObject event = new JsonObject();
            event.addProperty("eventId", conditionIndex + 1L);
            event.addProperty("contextId", 7L);
            event.addProperty("predicateNormalization", "IDENTITY");
            BranchWitness witness = BranchWitness.vmPc(
                    mapping.get("siteId").getAsString(),
                    "<test.Region: void run()>", conditionIndex,
                    mapping.get("occurrence").getAsInt(),
                    mapping.get("outcome").getAsBoolean(),
                    conditions.get(conditionIndex), conditionIndex, event);
            canonical.add(SummaryBranchMapping.witnessed(witness,
                    conditionIndex, policy).toJson());
        }
        summary.add("branchMappings", canonical);
    }

    private static void replaceWitnessOutcomes(
            JsonObject summary, boolean outcome) {
        JsonArray replacements = new JsonArray();
        for (com.google.gson.JsonElement element
                : summary.getAsJsonArray("branchMappings")) {
            SummaryBranchMapping mapping = SummaryBranchMapping.fromJson(
                    element.getAsJsonObject());
            BranchWitness source = mapping.witness();
            JsonObject metadata = new JsonObject();
            metadata.addProperty("predicateNormalization",
                    source.predicateNormalization());
            BranchWitness replacement = BranchWitness.vmPc(
                    source.siteId(), source.method(), source.unitIndex(),
                    source.occurrence(), outcome,
                    summary.getAsJsonArray("pathCondition")
                            .get(mapping.summaryPcIndex()),
                    source.vmPcIndex(), metadata);
            replacements.add(SummaryBranchMapping.witnessed(replacement,
                    mapping.summaryPcIndex(), mapping.policy()).toJson());
        }
        summary.add("branchMappings", replacements);
    }

    private static BranchReplayContract replayContract(JsonObject task) {
        return BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract"));
    }

    private static String sourceSite(JsonObject task) {
        return replayContract(task).source().siteId();
    }

    private static JsonObject mapping(String site, int condition) {
        return mapping(site, condition, 1);
    }

    private static JsonObject mapping(String site, int condition,
                                      int occurrence) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("conditionIndex", condition);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", true);
        return mapping;
    }

    private static JsonObject typedBinary(String operator, String javaType,
                                          int constant) {
        JsonObject expression = binary(operator, constant);
        expression.getAsJsonObject("_left").addProperty("_java_type",
                javaType);
        expression.getAsJsonObject("_left").addProperty("_exp",
                "M_" + javaType + "_field_REGION.3.in.0");
        expression.getAsJsonObject("_right").addProperty("_java_type",
                javaType);
        expression.getAsJsonObject("_right").addProperty("_exp",
                "Y_" + javaType + "_" + constant);
        return expression;
    }

    private static JsonObject binary(String operator, int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp",
                "M_I_field_REGION.3.in.0_java/lang/Integer");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }
}
