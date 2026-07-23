package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class CausynthModuleSupportTest {
    @Rule
    public final TemporaryFolder temporaryFolder = new TemporaryFolder();

    @Test
    public void jsonSerializationRemainsOrderedAndEscaped() {
        Map<String, Object> value = new LinkedHashMap<>();
        value.put("text", "a\n\"b\\c");
        value.put("values", Arrays.asList(1, true, null));

        assertEquals("{\"text\":\"a\\n\\\"b\\\\c\","
                        + "\"values\":[1,true,null]}",
                CausynthJson.write(value));
    }

    @Test
    public void artifactWriterWritesOnlyConsumedStaticArtifacts()
            throws Exception {
        Path output = temporaryFolder.newFolder("artifacts").toPath();
        CausynthAnalysisResult result = new CausynthAnalysisResult();
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("id", "DF.0");
        result.edges.add(edge);

        new CausynthArtifactWriter(output, result).writeAll();

        assertEquals("{}",
                read(output.resolve("target_resolved.json")));
        assertEquals("{\"id\":\"DF.0\"}\n",
                read(output.resolve("static_dataflow_edges.jsonl")));
        assertEquals("", read(output.resolve("symbolic_regions.jsonl")));
        assertEquals("", read(output.resolve("symbolic_region_edges.jsonl")));
        try (Stream<Path> artifacts = Files.list(output)) {
            assertEquals(4, artifacts.count());
        }
        assertFalse(Files.exists(output.resolve("seeds.json")));
        assertFalse(Files.exists(output.resolve("static_slices.json")));
    }

    @Test
    public void automaticStaticSemanticsRequireTheCurrentSchema() {
        Map<String, Object> oldTuple = new LinkedHashMap<>();
        oldTuple.put("mappingOnly", false);
        oldTuple.put("semanticAssertionsAllowed", true);
        oldTuple.put("eligibleForAutomaticDerivation", true);
        oldTuple.put("eligibleForAutomaticSmt", true);
        oldTuple.put("direction",
                StaticDataflowEdgeSchema.DEFAULT_DIRECTION);

        assertFalse(StaticDataflowEdgeSchema.automaticSemantics(oldTuple));
        oldTuple.put("schemaVersion", StaticDataflowEdgeSchema.VERSION);
        assertTrue(StaticDataflowEdgeSchema.automaticSemantics(oldTuple));
        oldTuple.put("schemaVersion", 2);
        assertFalse(StaticDataflowEdgeSchema.automaticSemantics(oldTuple));
    }

    @Test
    public void artifactWriterPersistsCanonicalRegionEdgeReferences()
            throws Exception {
        Path output = temporaryFolder.newFolder("compact-regions").toPath();
        CausynthAnalysisResult result = new CausynthAnalysisResult();
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("id", "DF.7");
        edge.put("kind", "local_def_use");
        edge.put("method", "<example.Owner: int compute()>");
        edge.put("siteId", "<example.Owner: int compute()>#u1");
        edge.put("fromCell", "input");
        edge.put("toCell", "output");
        edge.put("transferKind", "COMPUTE");
        result.edges.add(edge);

        Map<String, Object> reference = new LinkedHashMap<>();
        reference.put("edgeId", "DF.7");
        reference.put("kind", "local_def_use");
        Map<String, Object> slice = new LinkedHashMap<>();
        slice.put("outputPort", "REGION.0.out.0");
        slice.put("causalEdgeIds", Collections.singletonList("DF.7"));
        slice.put("causalEdges", Collections.singletonList(reference));
        slice.put("causalEdgeCount", 1);
        slice.put("causalCellCount", 1);
        slice.put("causalCellLimit", 20000);
        slice.put("derivedInputs", Collections.singletonList("input"));
        slice.put("inputPortCountBeforeSlice", 1);
        slice.put("inputPortPromotionLimit", 128);
        slice.put("methods", Collections.singletonList(
                "<example.Owner: int compute()>"));
        slice.put("methodCount", 1);
        slice.put("promotionAuthority", "RETIRED_ALIAS");

        Map<String, Object> region = new LinkedHashMap<>();
        region.put("regionId", "REGION.0");
        region.put("rootMethod", "<example.Owner: int compute()>");
        region.put("staticRootCandidate",
                "<example.Owner: int compute()>");
        region.put("rootValidation", "RUNTIME_REQUIRED");
        region.put("methods", Collections.singletonList(
                "<example.Owner: int compute()>"));
        region.put("methodCount", 1);
        region.put("broadInputPortCount", 1);
        region.put("broadInputPortLimit", 128);
        region.put("pathAssumptionSites",
                Collections.singletonList("<example.Owner: int compute()>#u1"));
        Map<String, Object> branch = new LinkedHashMap<>();
        branch.put("siteId", "<example.Owner: int compute()>#u1");
        branch.put("policy", "EXPLORE");
        branch.put("sourceEdgeId", "DF.7");
        branch.put("sourceEdgeIds", Collections.singletonList("DF.7"));
        branch.put("policyAuthority", "RETIRED_SELF_CLAIM");
        branch.put("explorationReason", "RETIRED_SELF_CLAIM");
        branch.put("role", "REACHABILITY");
        region.put("branchPolicies", Collections.singletonList(branch));
        region.put("outputSlices", Collections.singletonList(slice));
        result.symbolicRegions.add(region);

        Map<String, Object> regionEdge = new LinkedHashMap<>();
        regionEdge.put("edgeId", "REGION_EDGE.0");
        regionEdge.put("fromRegion", "REGION.0");
        regionEdge.put("toRegion", "REGION.1");
        regionEdge.put("rootValidation", "RUNTIME_REQUIRED");
        result.symbolicRegionEdges.add(regionEdge);

        new CausynthArtifactWriter(output, result).writeAll();

        String persistedRegion = read(output.resolve(
                "symbolic_regions.jsonl"));
        assertTrue(persistedRegion.contains("\"schemaVersion\":1"));
        assertTrue(persistedRegion.contains(
                "\"causalEdgeIds\":[\"DF.7\"]"));
        assertFalse(persistedRegion.contains("\"causalEdges\""));
        assertFalse(persistedRegion.contains("\"causalEdgeCount\""));
        assertFalse(persistedRegion.contains("\"methodCount\""));
        assertFalse(persistedRegion.contains("\"broadInputPortCount\""));
        assertFalse(persistedRegion.contains("\"broadInputPortLimit\""));
        assertFalse(persistedRegion.contains("\"pathAssumptionSites\""));
        assertFalse(persistedRegion.contains("\"sourceEdgeId\""));
        assertTrue(persistedRegion.contains(
                "\"sourceEdgeIds\":[\"DF.7\"]"));
        assertFalse(persistedRegion.contains("\"policyAuthority\""));
        assertFalse(persistedRegion.contains("\"explorationReason\""));
        assertFalse(persistedRegion.contains("\"role\""));
        assertFalse(persistedRegion.contains("\"causalCellCount\""));
        assertFalse(persistedRegion.contains("\"causalCellLimit\""));
        assertFalse(persistedRegion.contains("\"derivedInputs\""));
        assertFalse(persistedRegion.contains("\"inputPortCountBeforeSlice\""));
        assertFalse(persistedRegion.contains("\"inputPortPromotionLimit\""));
        assertFalse(persistedRegion.contains("\"staticRootCandidate\""));
        assertFalse(persistedRegion.contains("\"rootValidation\""));
        assertFalse(persistedRegion.contains("\"promotionAuthority\""));
        assertTrue(read(output.resolve("symbolic_region_edges.jsonl"))
                .contains("\"schemaVersion\":1"));
        assertFalse(read(output.resolve("symbolic_region_edges.jsonl"))
                .contains("\"rootValidation\""));

        // Persistence is a projection; planner-owned rows remain available to
        // in-memory validation and diagnostics.
        assertTrue(slice.containsKey("causalEdges"));
        assertTrue(region.containsKey("staticRootCandidate"));
    }

    @Test(expected = IllegalStateException.class)
    public void compactRegionSchemaRejectsUnknownCausalEdgeIds() {
        Map<String, Object> slice = new LinkedHashMap<>();
        slice.put("causalEdgeIds", Collections.singletonList("DF.missing"));
        slice.put("causalEdges", Collections.singletonList(
                Collections.<String, Object>singletonMap(
                        "edgeId", "DF.missing")));
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("outputSlices", Collections.singletonList(slice));

        StaticRegionArtifactSchema.regions(
                Collections.singletonList(region),
                Collections.<Map<String, Object>>emptyList());
    }

    @Test
    public void controlDependenceMetadataRetainsExactSchema() {
        String method = "<example.Owner: int compute(int)>";
        assertTrue(ControlDependenceEdgeSupport.permitsSameCellEdge(
                "path_guard_dependency", "value", "value", true));
        assertFalse(ControlDependenceEdgeSupport.permitsSameCellEdge(
                "local_def_use", "value", "value", true));
        assertFalse(ControlDependenceEdgeSupport.permitsSameCellEdge(
                "path_guard_dependency", "value", "value", false));

        Map<String, Object> path = new LinkedHashMap<>();
        ControlDependenceEdgeSupport.annotatePathGuard(path, method, 1, 2,
                "value = 10", false, "value", "value");
        assertEquals(method + "#u1", path.get("guardSiteId"));
        assertEquals(method + "#u2",
                path.get("controlledDefinitionSiteId"));
        assertEquals(Boolean.TRUE, path.get("sameCellRedefinition"));
        assertEquals("SOOT_CFG_REQUIRED_OUTCOME_TO_EXACT_RELEVANT_"
                        + "DEFINITION_V1",
                path.get("controlDependenceAuthority"));

        Map<String, Object> multiway = new LinkedHashMap<>();
        ControlDependenceEdgeSupport.annotatePathGuard(multiway, method, 4,
                8, "result = 1", null, Arrays.asList(0, 2), "selector",
                "result");
        assertFalse(multiway.containsKey("requiredOutcome"));
        assertEquals(Arrays.asList(0, 2),
                multiway.get("reachingSuccessorIndices"));
        assertEquals("SOOT_CFG_REQUIRED_SUCCESSORS_TO_EXACT_RELEVANT_"
                        + "DEFINITION_V1",
                multiway.get("controlDependenceAuthority"));

        Map<String, Object> independent = new LinkedHashMap<>();
        assertFalse(ControlDependenceEdgeSupport
                .hasAuditableOutputIndependenceProof(independent));
        ControlDependenceEdgeSupport.annotateOutputIndependentGuard(
                independent, Arrays.asList("out.0", "out.1"),
                "both CFG successors preserve both outputs");
        assertTrue(ControlDependenceEdgeSupport
                .hasAuditableOutputIndependenceProof(independent));

        Map<String, Object> mutation = new LinkedHashMap<>();
        assertTrue(ControlDependenceEdgeSupport.annotateGuardedMutation(
                mutation, method, 1, 3, true));
        assertFalse(ControlDependenceEdgeSupport.annotateGuardedMutation(
                mutation, method, 1, 3, true));
        assertTrue(ControlDependenceEdgeSupport.annotateGuardedMutation(
                mutation, method, 1, 4, false));
        assertEquals(2, mutation.get("guardedMutationCount"));
        assertFalse(mutation.containsKey("guardedMutationSiteId"));
        assertFalse(mutation.containsKey("requiredOutcome"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> rows =
                (List<Map<String, Object>>) mutation.get("guardedMutations");
        assertEquals(method + "#u3",
                rows.get(0).get("guardedMutationSiteId"));
        assertEquals(method + "#u4",
                rows.get(1).get("guardedMutationSiteId"));
    }

    @Test
    public void symbolicPlanBuilderPreservesClassificationAndLiveIns() {
        String method = "<example.Owner: int compute(int)>";
        SymbolicExecutionPlanBuilder builder =
                new SymbolicExecutionPlanBuilder(method);
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("fromCell", method + ".param0:int");
        edge.put("toCell", method + "::value");
        edge.put("unit", "if value >= 10 goto return");
        builder.observe(edge, "GUARD", method + "#u1");

        Map<String, Object> row = builder.toRow("SP.0");

        assertEquals(method, builder.method());
        assertEquals("SYMBOLIC_EXECUTION", row.get("classification"));
        assertEquals(Boolean.TRUE, row.get("requiresSymbolicExecution"));
        assertEquals("relevant branch guard", row.get("reason"));
        @SuppressWarnings("unchecked")
        List<String> inputs = (List<String>) row.get("symbolicInputs");
        assertEquals(Arrays.asList(method + ".param0:int"), inputs);
        assertEquals("graph_directed_static_slice", row.get("precision"));
    }

    @Test
    public void targetResolverPreservesConfigPriorityAndTargetIdParsing()
            throws Exception {
        Path root = temporaryFolder.newFolder("target-resolver").toPath();
        Path target = root.resolve("target.yaml");
        Path config = root.resolve("workflow.properties");
        Files.write(target, Collections.singletonList(
                "exception_target_id: request-failure"),
                StandardCharsets.UTF_8);
        Files.write(config, Arrays.asList(
                "causynth_target_spec=" + target,
                "causynth_output_dir=" + root.resolve("output"),
                "causynth_analysis_scope=fixture-scope",
                "value_with_equals=left=right"), StandardCharsets.UTF_8);
        CausynthTargetContext context =
                CausynthTargetResolver.resolve(config.toString());

        assertEquals(root.resolve("output").toAbsolutePath().normalize(),
                context.outputDir);
        assertNull(context.seedException);
        assertEquals("request-failure", context.exceptionTargetId);
        assertEquals("fixture-scope", context.analysisScope);
        assertEquals("left=right", CausynthTargetResolver.readConfig(
                config.toString()).get("value_with_equals"));
    }

    @Test
    public void symbolicPlanningStagePreservesOrderingAndTransferSchema() {
        String methodA = "<example.A: int compute(int)>";
        String methodB = "<example.B: int compute(int)>";
        CausynthAnalysisResult result = new CausynthAnalysisResult();
        Map<String, Object> compute = new LinkedHashMap<>();
        compute.put("kind", "local_def_use");
        compute.put("method", methodB);
        compute.put("fromCell", methodB + "::input");
        compute.put("toCell", methodB + "::output");
        compute.put("unit", "output = input + 1");
        compute.put("unitIndex", 2);
        result.edges.add(compute);
        Map<String, Object> guard = new LinkedHashMap<>();
        guard.put("kind", "path_guard_dependency");
        guard.put("method", methodA);
        guard.put("fromCell", methodA + "::input");
        guard.put("toCell", methodA + "::output");
        guard.put("unit", "if input == 0 goto return");
        guard.put("unitIndex", 1);
        result.edges.add(guard);

        SymbolicPlanningStage.build(result);

        assertEquals("COMPUTE", compute.get("transferKind"));
        assertEquals(methodB + "#u2", compute.get("siteId"));
        assertEquals("GUARD", guard.get("transferKind"));
        assertEquals(methodA + "#u1", guard.get("siteId"));
        assertEquals(methodA, result.symbolicPlan.get(0).get("method"));
        assertEquals(methodB, result.symbolicPlan.get(1).get("method"));
        assertEquals(2, result.slices.get("symbolicPlanMethodCount"));
        @SuppressWarnings("unchecked")
        Map<String, Object> classifications =
                (Map<String, Object>) result.slices.get(
                        "symbolicPlanClassifications");
        assertEquals(2, classifications.get("SYMBOLIC_EXECUTION"));
        assertEquals("HEAP_READ", SymbolicPlanningStage.transferKind(
                "accessor_field", "", "",
                "<example.Owner: int value>", "value"));
        assertEquals("HEAP_LOOKUP", SymbolicPlanningStage.transferKind(
                "invoke", "x = interfaceinvoke cache.get(key)", "",
                "key", "x"));
    }

    @Test
    public void regionAssemblyMetadataJoinPreservesCompactEdgeSchema() {
        Map<String, Object> mutation = new LinkedHashMap<>();
        mutation.put("id", "DF.7");
        mutation.put("kind", "heap_mutation_path_guard");
        mutation.put("guardSiteId", "method#u1");
        mutation.put("guardedMutationCount", 2);
        mutation.put("guardedMutationsAuthority",
                "STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE");
        mutation.put("guardedMutations", Arrays.asList(
                new LinkedHashMap<String, Object>(),
                new LinkedHashMap<String, Object>()));
        Map<String, Object> reference = new LinkedHashMap<>();
        reference.put("edgeId", "DF.7");
        Map<String, Object> slice = new LinkedHashMap<>();
        slice.put("causalEdges", Arrays.asList(reference));
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("outputSlices", Arrays.asList(slice));

        SymbolicRegionAssemblyStage.enrichHeapMutationGuardMetadata(
                Arrays.asList(region), Arrays.asList(mutation));

        assertEquals("method#u1", reference.get("guardSiteId"));
        assertEquals(2, reference.get("guardedMutationCount"));
        assertEquals(mutation.get("guardedMutations"),
                reference.get("guardedMutations"));
        assertFalse(reference.containsKey("requiredOutcome"));
    }

    @Test
    public void activationSelectionParsersPreserveFilteringAndOrder()
            throws Exception {
        Path plan = temporaryFolder.newFile("activation-plan.jsonl").toPath();
        String first = "{\"activationId\":\"ACT.0\","
                + "\"rootMethod\":\"<example.First: void run()>\","
                + "\"replayable\":true,\"schedulerReady\":true}";
        String second = "{\"activationId\":\"ACT.1\","
                + "\"rootMethod\":\"<example.Second: void run()>\","
                + "\"replayable\":true,\"schedulerReady\":true,"
                + "\"requestedOutputCapture\":["
                + "{\"captureBindingId\":\"CAP.0\","
                + "\"outputPort\":\"REGION.1.out.0\","
                + "\"outputCell\":\"value\","
                + "\"callerMethod\":\"<example.Second: void run()>\","
                + "\"unitIndex\":4,"
                + "\"siteId\":\"<example.Second: void run()>#u4\","
                + "\"calleeMethod\":\"<example.Sink: void take(int)>\","
                + "\"argumentIndex\":0,\"occurrence\":1},"
                + "{\"captureBindingId\":\"CAP.INVALID\"}]}";
        String retired = "{\"activationId\":\"ACT.OLD\","
                + "\"rootMethod\":\"<example.Retired: void run()>\","
                + "\"replayable\":true,\"symbolicReady\":true}";
        Files.write(plan, Arrays.asList(first, second, retired),
                StandardCharsets.UTF_8);

        assertEquals(Arrays.asList("<example.First: void run()>",
                        "<example.Second: void run()>"),
                new ArrayList<>(ConcolicInstrumentationSelections
                        .readRuntimeSelectedRoots(plan, "")));
        assertEquals(Arrays.asList("<example.Second: void run()>"),
                new ArrayList<>(ConcolicInstrumentationSelections
                        .readRuntimeSelectedRoots(plan, "ACT.1")));

        ConcolicInstrumentationSelections
                .ConcolicOutputCaptureSelection captures =
                ConcolicInstrumentationSelections
                        .ConcolicOutputCaptureSelection.from(plan, "ACT.1");
        assertEquals(1, captures.targets().size());
        assertEquals("CAP.0", captures.targets().iterator().next()
                .captureBindingId);
    }

    @Test
    public void branchSelectionDeduplicatesUnitsInInsertionOrder() {
        Map<String, Object> first = new LinkedHashMap<>();
        first.put("method", "<example.First: void run()>");
        first.put("unitIndex", 7);
        Map<String, Object> duplicate = new LinkedHashMap<>(first);
        Map<String, Object> second = new LinkedHashMap<>();
        second.put("method", "<example.First: void run()>");
        second.put("unitIndex", 2);
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("branchPolicies", Arrays.asList(first, duplicate, second));

        ConcolicInstrumentationSelections.ConcolicBranchSelection selection =
                ConcolicInstrumentationSelections.ConcolicBranchSelection
                        .from(Arrays.asList(region));

        assertEquals(Arrays.asList(7, 2),
                new ArrayList<>(selection.units(
                        "<example.First: void run()>")));
    }

    private static String read(Path path) throws Exception {
        return new String(Files.readAllBytes(path), StandardCharsets.UTF_8);
    }

}
