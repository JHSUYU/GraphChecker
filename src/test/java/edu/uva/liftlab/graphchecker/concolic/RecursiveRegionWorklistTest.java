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

public class RecursiveRegionWorklistTest {
    @Test
    public void recursivelyDiscoversNeutralUpstreamChainWithStableKeys() {
        List<JsonObject> regions = Arrays.asList(
                region("REGION.CONSUMER"),
                regionWithSlice("REGION.MIDDLE", "middle.out", true,
                        "middle.in"),
                regionWithSlice("REGION.SOURCE", "source.out", true));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.C", "REGION.CONSUMER"),
                activation("ACT.M", "REGION.MIDDLE"),
                activation("ACT.S", "REGION.SOURCE"));
        List<JsonObject> edges = Arrays.asList(
                edge("EDGE.MC", "REGION.MIDDLE", "middle.out",
                        "REGION.CONSUMER", "consumer.in", "EQUALITY"),
                edge("EDGE.SM", "REGION.SOURCE", "source.out",
                        "REGION.MIDDLE", "middle.in", "EQUALITY"));
        JsonObject cachedSource = new JsonObject();
        cachedSource.addProperty("summaryId", "SUMMARY.SOURCE");
        cachedSource.addProperty("regionId", "REGION.SOURCE");
        cachedSource.addProperty("valid", true);
        cachedSource.addProperty("relationallyComplete", true);
        cachedSource.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject cachedOutput = new JsonObject();
        cachedOutput.addProperty("portId", "source.out");
        cachedSource.add("requestedOutput", cachedOutput);
        JsonObject cachedSlice = outputSlice("source.out", true);
        cachedSource.add("requestedOutputSlice", cachedSlice);
        JsonObject cachedRelation = new JsonObject();
        cachedRelation.addProperty("kind", "GUARDED_PATH_MERGE");
        cachedRelation.addProperty("complete", true);
        cachedSource.add("regionRelation", cachedRelation);
        List<JsonObject> summaries = Arrays.asList(
                completeSummary("SUMMARY.MIDDLE", "REGION.MIDDLE",
                        "middle.out", "middle.in"),
                cachedSource);

        RecursiveRegionWorklist.Result first =
                RecursiveRegionWorklist.explore(regions, activations,
                        edges, summaries,
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertTrue(first.manifest.get("complete").getAsBoolean());
        assertEquals("COMPLETE_BOUNDED_REGION_CLOSURE",
                first.manifest.get("status").getAsString());
        assertEquals(2, first.workItems.size());
        assertEquals(2, first.upstreamRequests.size());
        assertEquals(0, first.workItems.get(0).get("depth").getAsInt());
        assertEquals(1, first.workItems.get(1).get("depth").getAsInt());
        assertEquals("REGION.SOURCE", first.upstreamRequests.get(1)
                .get("upstreamRegion").getAsString());
        assertTrue(first.upstreamRequests.get(1)
                .get("terminalUpstreamRegion").getAsBoolean());
        assertEquals("HIT_COMPLETE", first.upstreamRequests.get(1)
                .getAsJsonObject("summaryCache").get("status").getAsString());
        assertFalse(first.upstreamRequests.get(1)
                .get("captureRequired").getAsBoolean());

        List<JsonObject> reversedEdges = new ArrayList<>(edges);
        List<JsonObject> reversedActivations = new ArrayList<>(activations);
        Collections.reverse(reversedEdges);
        Collections.reverse(reversedActivations);
        RecursiveRegionWorklist.Result second =
                RecursiveRegionWorklist.explore(regions,
                        reversedActivations, reversedEdges,
                        summaries,
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertEquals(first.workItems.get(0).get("queryKey").getAsString(),
                second.workItems.get(0).get("queryKey").getAsString());
        assertEquals(first.workItems.get(1).get("queryKey").getAsString(),
                second.workItems.get(1).get("queryKey").getAsString());
        JsonObject differentRuntimeRoot = activation("ACT.RUNTIME.999",
                "REGION.CONSUMER");
        differentRuntimeRoot.addProperty("regionInstanceId",
                "REGION.CONSUMER@test#differentCallId");
        RecursiveRegionWorklist.Result third =
                RecursiveRegionWorklist.explore(regions, activations, edges,
                        summaries,
                        Collections.singletonList(differentRuntimeRoot),
                        RecursiveRegionWorklist.Bounds.defaults());
        assertEquals(first.workItems.get(0).get("queryKey").getAsString(),
                third.workItems.get(0).get("queryKey").getAsString());
    }

    @Test
    public void matchesOutputSlicePortIdToValidatedEdgeInputCell() {
        String inputPort = "REGION.MIDDLE.in.44";
        String inputCell = "<example.State: int currentKey>";
        JsonObject middle = regionWithSlice("REGION.MIDDLE", "middle.out",
                true, inputPort);
        JsonObject input = new JsonObject();
        input.addProperty("portId", inputPort);
        input.addProperty("cell", inputCell);
        middle.getAsJsonArray("symbolicInputs").add(input);
        List<JsonObject> regions = Arrays.asList(
                region("REGION.CONSUMER"), middle,
                regionWithSlice("REGION.SOURCE", "source.out", true));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.C", "REGION.CONSUMER"),
                activation("ACT.M", "REGION.MIDDLE"),
                activation("ACT.S", "REGION.SOURCE"));
        List<JsonObject> edges = Arrays.asList(
                edge("EDGE.MC", "REGION.MIDDLE", "middle.out",
                        "REGION.CONSUMER", "consumer.in", "EQUALITY"),
                edge("EDGE.SM", "REGION.SOURCE", "source.out",
                        "REGION.MIDDLE", inputCell, "READ_FROM"));

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(regions, activations, edges,
                        Collections.singletonList(completeSummary(
                                "SUMMARY.MIDDLE", "REGION.MIDDLE",
                                "middle.out", inputPort)),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertEquals(2, result.workItems.size());
        assertEquals(2, result.upstreamRequests.size());
        assertEquals("REGION.SOURCE", result.upstreamRequests.get(1)
                .get("upstreamRegion").getAsString());
        assertEquals(0, result.upstreamRequests.get(0)
                .getAsJsonArray("recursiveBoundaryInputPorts").size());
    }

    @Test
    public void exactCanonicalAliasSelectsSliceBackedProducerOutput() {
        String canonicalPort = "REGION.PRODUCER.out.16";
        String canonicalCell = "<example.Keys: int[] allKeys>";
        JsonObject producer = regionWithOutputAndSlice(
                "REGION.PRODUCER", canonicalPort, canonicalCell, true);
        JsonObject consumer = region("REGION.CONSUMER");
        JsonObject producerActivation = activation("ACT.P",
                "REGION.PRODUCER");
        JsonObject consumerActivation = activation("ACT.C",
                "REGION.CONSUMER");
        JsonObject edge = edge("EDGE.CANONICAL", "REGION.PRODUCER",
                "<example.NameNode: void publish()>::r5#field:allKeys",
                "REGION.CONSUMER", "consumer.in", "EQUALITY");
        addCanonicalAlias(edge, canonicalPort, canonicalCell);

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(
                        Arrays.asList(consumer, producer),
                        Arrays.asList(consumerActivation,
                                producerActivation),
                        Collections.singletonList(edge),
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(consumerActivation),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertEquals(1, result.upstreamRequests.size());
        JsonObject request = result.upstreamRequests.get(0);
        assertEquals(canonicalPort, request.get("upstreamOutputPort")
                .getAsString());
        assertEquals(canonicalCell, request.get("upstreamOutputCell")
                .getAsString());
        assertEquals("<example.NameNode: void publish()>::r5"
                        + "#field:allKeys",
                request.get("edgeOutputEndpoint").getAsString());
    }

    @Test
    public void partialCanonicalAliasNeverFallsBackToRawOutput() {
        String rawPort = "REGION.PRODUCER.out.raw";
        String canonicalPort = "REGION.PRODUCER.out.16";
        String canonicalCell = "<example.Keys: int[] allKeys>";
        JsonObject producer = regionWithSlices("REGION.PRODUCER",
                outputSlice(rawPort, true),
                outputSlice(canonicalPort, true));
        JsonObject rawOutput = new JsonObject();
        rawOutput.addProperty("portId", rawPort);
        rawOutput.addProperty("cell", "producer.raw.cell");
        producer.getAsJsonArray("outputs").add(rawOutput);
        JsonObject canonicalOutput = new JsonObject();
        canonicalOutput.addProperty("portId", canonicalPort);
        canonicalOutput.addProperty("cell", canonicalCell);
        producer.getAsJsonArray("outputs").add(canonicalOutput);
        JsonObject consumer = region("REGION.CONSUMER");
        JsonObject producerActivation = activation("ACT.P",
                "REGION.PRODUCER");
        JsonObject consumerActivation = activation("ACT.C",
                "REGION.CONSUMER");
        JsonObject edge = edge("EDGE.PARTIAL", "REGION.PRODUCER",
                rawPort, "REGION.CONSUMER", "consumer.in", "EQUALITY");
        edge.addProperty("fromOutputPort", canonicalPort);
        edge.addProperty("fromOutputCell", canonicalCell);
        edge.addProperty("aliasProofAuthority",
                "STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                        + "AND_DECLARED_RETURN_FIELD");
        // aliasProofComplete and proof IDs are intentionally absent.  The raw
        // endpoint is nevertheless a valid output, proving no fallback occurs.

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(
                        Arrays.asList(consumer, producer),
                        Arrays.asList(consumerActivation,
                                producerActivation),
                        Collections.singletonList(edge),
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(consumerActivation),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertEquals(0, result.upstreamRequests.size());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("MISSING_ENDPOINT"));
    }

    @Test
    public void recordsCycleAndBoundTruncationAsExplicitGaps() {
        List<JsonObject> regions = Arrays.asList(
                regionWithSlice("REGION.A", "a.out", true, "a.in"),
                regionWithSlice("REGION.B", "b.out", true, "b.in"));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.A", "REGION.A"),
                activation("ACT.B", "REGION.B"));
        List<JsonObject> cycleEdges = Arrays.asList(
                edge("EDGE.BA", "REGION.B", "b.out",
                        "REGION.A", "a.in", "READ_FROM"),
                edge("EDGE.AB", "REGION.A", "a.out",
                        "REGION.B", "b.in", "READ_FROM"));

        RecursiveRegionWorklist.Result cycle =
                RecursiveRegionWorklist.explore(regions, activations,
                        cycleEdges, Collections.<JsonObject>emptyList(),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertFalse(cycle.manifest.get("complete").getAsBoolean());
        assertEquals(1, cycle.manifest.get("cycleCount").getAsInt());
        assertTrue(cycle.manifest.getAsJsonArray("gaps").toString()
                .contains("CYCLE_DETECTED"));

        List<JsonObject> chain = Arrays.asList(
                edge("EDGE.BA", "REGION.B", "b.out",
                        "REGION.A", "a.in", "EQUALITY"),
                edge("EDGE.CB", "REGION.C", "c.out",
                        "REGION.B", "b.in", "EQUALITY"));
        List<JsonObject> boundedRegions = Arrays.asList(
                region("REGION.A"),
                regionWithSlice("REGION.B", "b.out", true, "b.in"),
                regionWithSlice("REGION.C", "c.out", true));
        List<JsonObject> boundedActivations = Arrays.asList(
                activation("ACT.A", "REGION.A"),
                activation("ACT.B", "REGION.B"),
                activation("ACT.C", "REGION.C"));
        RecursiveRegionWorklist.Bounds depthZero =
                new RecursiveRegionWorklist.Bounds(
                        0, 8, 4, 4, 16, 16, 10_000);
        RecursiveRegionWorklist.Result bounded =
                RecursiveRegionWorklist.explore(boundedRegions,
                        boundedActivations, chain,
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(boundedActivations.get(0)),
                        depthZero);

        assertFalse(bounded.manifest.get("complete").getAsBoolean());
        assertEquals(1, bounded.workItems.size());
        assertTrue(bounded.manifest.getAsJsonArray("gaps").toString()
                .contains("MAX_DEPTH"));
    }

    @Test
    public void groupsAlternativeWritersUnderStableExclusiveGuards() {
        List<JsonObject> regions = Arrays.asList(
                region("REGION.READER"),
                regionWithSlice("REGION.LEFT", "left.out", true),
                regionWithSlice("REGION.RIGHT", "right.out", true));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.R", "REGION.READER"),
                activation("ACT.L", "REGION.LEFT"),
                activation("ACT.W", "REGION.RIGHT"));
        List<JsonObject> edges = Arrays.asList(
                edge("EDGE.LEFT", "REGION.LEFT", "left.out",
                        "REGION.READER", "reader.state", "READ_FROM"),
                edge("EDGE.RIGHT", "REGION.RIGHT", "right.out",
                        "REGION.READER", "reader.state", "READ_FROM"));

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(regions, activations,
                        edges, Arrays.asList(
                                completeSummary("SUMMARY.LEFT",
                                        "REGION.LEFT", "left.out"),
                                completeSummary("SUMMARY.RIGHT",
                                        "REGION.RIGHT", "right.out")),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertTrue(result.manifest.get("complete").getAsBoolean());
        assertEquals(1, result.workItems.size());
        assertEquals(2, result.upstreamRequests.size());
        assertEquals(1, result.alternativeWriterGroups.size());
        JsonObject group = result.alternativeWriterGroups.get(0);
        assertEquals("EXACTLY_ONE_GUARDED",
                group.get("selectionSemantics").getAsString());
        JsonArray alternatives = group.getAsJsonArray("alternatives");
        assertEquals(2, alternatives.size());
        assertNotEquals(alternatives.get(0).getAsJsonObject()
                        .get("guardSymbol").getAsString(),
                alternatives.get(1).getAsJsonObject()
                        .get("guardSymbol").getAsString());
    }

    @Test
    public void cacheIsOutputSpecificAndUnprovenMappingIsNeverExecuted() {
        List<JsonObject> regions = Arrays.asList(
                region("REGION.TARGET"), region("REGION.UPSTREAM"),
                region("REGION.BEHIND_MAPPING"));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.T", "REGION.TARGET"),
                activation("ACT.U", "REGION.UPSTREAM"),
                activation("ACT.B", "REGION.BEHIND_MAPPING"));

        JsonObject mappingOnly = edge("EDGE.MAPPING", "REGION.UPSTREAM",
                "wanted.out", "REGION.TARGET", "target.in", "EQUALITY");
        mappingOnly.addProperty("composable", false);
        mappingOnly.addProperty("eligibleForAutomaticDerivation", false);
        mappingOnly.addProperty("eligibleForAutomaticSmt", false);
        mappingOnly.addProperty("eligibleForRecursiveDiscovery", true);
        mappingOnly.addProperty("endpointPairCount", 1);
        mappingOnly.addProperty("status",
                "PORT_MAPPING_OBSERVED_VALUE_EQUALITY_UNPROVEN");
        mappingOnly.addProperty("valueEqualityObserved", false);

        JsonObject behind = edge("EDGE.BEHIND", "REGION.BEHIND_MAPPING",
                "behind.out", "REGION.UPSTREAM", "upstream.in", "EQUALITY");

        JsonObject wrongOutputSummary = new JsonObject();
        wrongOutputSummary.addProperty("summaryId", "SUMMARY.WRONG.OUTPUT");
        wrongOutputSummary.addProperty("regionId", "REGION.UPSTREAM");
        wrongOutputSummary.addProperty("valid", true);
        wrongOutputSummary.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject wrongOutput = new JsonObject();
        wrongOutput.addProperty("portId", "other.out");
        wrongOutputSummary.add("requestedOutput", wrongOutput);
        JsonObject relation = new JsonObject();
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.addProperty("complete", true);
        wrongOutputSummary.add("regionRelation", relation);

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(regions, activations,
                        Arrays.asList(mappingOnly, behind),
                        Collections.singletonList(wrongOutputSummary),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertEquals(1, result.workItems.size());
        assertEquals(1, result.upstreamRequests.size());
        JsonObject request = result.upstreamRequests.get(0);
        assertEquals("MISS", request.getAsJsonObject("summaryCache")
                .get("status").getAsString());
        assertFalse(request.get("captureRequired").getAsBoolean());
        assertTrue(request.get("captureDeferredUntilEdgeValidation")
                .getAsBoolean());
        assertFalse(request.get("recursiveExpansionAllowed").getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("UNPROVEN_REGION_EDGE"));
    }

    @Test
    public void usesCompleteValidatedBindingsAndCarriesExactConsumerInstance() {
        JsonObject target = activation("ACT.T", "REGION.TARGET");
        target.addProperty("regionInstanceId", "REGION.TARGET#call7004");
        JsonObject wrong = activation("ACT.U.OLD", "REGION.UPSTREAM");
        wrong.addProperty("regionInstanceId", "REGION.UPSTREAM#call3468");
        JsonObject aligned = activation("ACT.U.ALIGNED", "REGION.UPSTREAM");
        aligned.addProperty("regionInstanceId", "REGION.UPSTREAM#call3545");
        JsonObject edge = edge("EDGE.TARGET", "REGION.UPSTREAM",
                "REGION.UPSTREAM.out.4", "REGION.TARGET",
                "REGION.TARGET.in.25", "READ_FROM");
        JsonArray diagnosticEvidence = new JsonArray();
        JsonObject oldBinding = new JsonObject();
        oldBinding.addProperty("fromRegionInstance",
                "REGION.UPSTREAM#call3468");
        oldBinding.addProperty("toRegionInstance",
                "REGION.TARGET#other");
        diagnosticEvidence.add(oldBinding);
        edge.add("evidence", diagnosticEvidence);
        JsonArray validated = new JsonArray();
        JsonObject exactBinding = concreteBinding("EDGE.TARGET",
                "REGION.UPSTREAM#call3545", "REGION.TARGET#call7004",
                "REGION.UPSTREAM.out.4", "REGION.UPSTREAM.out.4",
                "REGION.TARGET.in.25", 10, 20);
        validated.add(exactBinding);
        edge.add("validatedBindings", validated);

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(
                        Arrays.asList(region("REGION.TARGET"),
                                regionWithSlice("REGION.UPSTREAM",
                                        "REGION.UPSTREAM.out.4", true)),
                        Arrays.asList(target, wrong, aligned),
                        Collections.singletonList(edge),
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(target),
                        RecursiveRegionWorklist.Bounds.defaults());

        JsonObject request = result.upstreamRequests.get(0);
        assertEquals("REGION.TARGET#call7004", request.get(
                "downstreamRegionInstance").getAsString());
        assertEquals(1, request.getAsJsonArray("upstreamActivations").size());
        assertEquals("ACT.U.ALIGNED", request.getAsJsonArray(
                "upstreamActivations").get(0).getAsJsonObject().get(
                "activationId").getAsString());
        assertEquals("REGION.TARGET#call7004", request.getAsJsonArray(
                "runtimeEvidence").get(0).getAsJsonObject().get(
                "toRegionInstance").getAsString());
    }

    @Test
    public void filtersExactBindingBeforeActivationBoundAndResolvesOutputCell() {
        String outputCell = "<example.Store: java.util.Map state>";
        JsonObject target = activation("ACT.T", "REGION.TARGET");
        target.addProperty("regionInstanceId", "REGION.TARGET#call7004");

        JsonObject old = activation("ACT.U.OLD", "REGION.UPSTREAM");
        old.addProperty("regionInstanceId", "REGION.UPSTREAM#call3468");
        JsonObject base = activation("ACT.U.BASE", "REGION.UPSTREAM");
        base.addProperty("regionInstanceId", "REGION.UPSTREAM#call3545");
        JsonObject exact = base.deepCopy();
        exact.addProperty("activationId", "ACT.U.EXACT");
        exact.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.UPSTREAM.out.4");
        requested.addProperty("cell", outputCell);
        exact.add("requestedOutput", requested);
        exact.add("requestedOutputSlice", outputSlice(
                "REGION.UPSTREAM.out.4", true));

        JsonObject edge = edge("EDGE.TARGET", "REGION.UPSTREAM",
                outputCell, "REGION.TARGET", "REGION.TARGET.in.25",
                "READ_FROM");
        JsonObject alignedBinding = concreteBinding("EDGE.TARGET",
                "REGION.UPSTREAM#call3545", "REGION.TARGET#call7004",
                "REGION.UPSTREAM.out.4", outputCell,
                "REGION.TARGET.in.25", 10, 20);
        JsonObject unrelatedBinding = concreteBinding("EDGE.TARGET",
                "REGION.UPSTREAM#call3468", "REGION.TARGET#other",
                "REGION.UPSTREAM.out.4", outputCell,
                "REGION.TARGET.in.25", 1, 2);
        JsonArray validated = new JsonArray();
        validated.add(unrelatedBinding.deepCopy());
        validated.add(alignedBinding.deepCopy());
        edge.add("validatedBindings", validated);
        JsonArray activationBindings = new JsonArray();
        JsonObject activationBinding = alignedBinding.deepCopy();
        activationBinding.addProperty("writerEventSeq",
                activationBinding.remove("writeSeq").getAsLong());
        activationBinding.addProperty("readerEventSeq",
                activationBinding.remove("readSeq").getAsLong());
        activationBindings.add(activationBinding);
        exact.add("edgeBindings", activationBindings);

        RecursiveRegionWorklist.Bounds oneActivation =
                new RecursiveRegionWorklist.Bounds(
                        8, 64, 1, 8, 256, 512, 30_000L);
        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(
                        Arrays.asList(region("REGION.TARGET"),
                                regionWithOutputAndSlice("REGION.UPSTREAM",
                                        "REGION.UPSTREAM.out.4", outputCell,
                                        true)),
                        Arrays.asList(target, old, base, exact),
                        Collections.singletonList(edge),
                        Collections.singletonList(completeSummary(
                                "SUMMARY.UPSTREAM", "REGION.UPSTREAM",
                                "REGION.UPSTREAM.out.4")),
                        Collections.singletonList(target), oneActivation);

        JsonObject request = result.upstreamRequests.get(0);
        assertEquals("REGION.UPSTREAM.out.4", request.get(
                "upstreamOutputPort").getAsString());
        assertEquals(outputCell, request.get("upstreamOutputCell")
                .getAsString());
        assertEquals(1, request.getAsJsonArray("runtimeEvidence").size());
        assertEquals("REGION.TARGET#call7004", request.getAsJsonArray(
                "runtimeEvidence").get(0).getAsJsonObject().get(
                "toRegionInstance").getAsString());
        assertEquals(1, request.getAsJsonArray("upstreamActivations").size());
        assertEquals("ACT.U.EXACT", request.getAsJsonArray(
                "upstreamActivations").get(0).getAsJsonObject().get(
                "activationId").getAsString());
        assertFalse(result.manifest.getAsJsonArray("gaps").toString()
                .contains("MAX_ACTIVATIONS_PER_REGION"));
    }

    @Test
    public void doesNotFallbackToUnrelatedActivationsWhenTargetBindingIsAbsent() {
        JsonObject target = activation("ACT.T", "REGION.TARGET");
        target.addProperty("regionInstanceId", "REGION.TARGET#call7004");
        JsonObject upstream = activation("ACT.U", "REGION.UPSTREAM");
        upstream.addProperty("regionInstanceId", "REGION.UPSTREAM#call10");
        JsonObject edge = edge("EDGE.TARGET", "REGION.UPSTREAM", "u.out",
                "REGION.TARGET", "t.in", "READ_FROM");
        JsonArray bindings = new JsonArray();
        bindings.add(concreteBinding("EDGE.TARGET",
                "REGION.UPSTREAM#call10", "REGION.TARGET#other",
                "u.out", "u.cell", "t.in", 1, 2));
        edge.add("validatedBindings", bindings);

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(
                        Arrays.asList(region("REGION.TARGET"),
                                regionWithSlice("REGION.UPSTREAM", "u.out",
                                        true)),
                        Arrays.asList(target, upstream),
                        Collections.singletonList(edge),
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(target),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertEquals(0, result.upstreamRequests.get(0).getAsJsonArray(
                "upstreamActivations").size());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("MISSING_UPSTREAM_ACTIVATION"));
    }

    @Test
    public void deduplicatesOverlappingRegionsByExactWriterAnchorOwner() {
        String outputCell = "<example.Store: java.util.Map state>";
        String writer = "<example.Store: void addKeys(example.Keys)>";
        JsonObject target = activation("ACT.T", "REGION.TARGET");
        target.addProperty("regionInstanceId", "REGION.TARGET#call7004");

        JsonObject broad = ownerRegion("REGION.BROAD", "broad.out",
                outputCell, "<example.Store: void initialize()>", 5);
        JsonObject precise = ownerRegion("REGION.PRECISE", "precise.out",
                outputCell, writer, 3);
        JsonObject unrelated = ownerRegion("REGION.UNRELATED", "other.out",
                outputCell, "<example.Key: void initialize()>", 7);

        JsonObject broadEdge = ownedEdge("EDGE.BROAD", "REGION.BROAD",
                "broad.out", outputCell, writer);
        JsonObject preciseEdge = ownedEdge("EDGE.PRECISE", "REGION.PRECISE",
                "precise.out", outputCell, writer);
        JsonObject unrelatedEdge = ownedEdge("EDGE.UNRELATED",
                "REGION.UNRELATED", "other.out", outputCell, writer);

        JsonObject broadActivation = ownedActivation("ACT.BROAD",
                "REGION.BROAD", "broad.out", outputCell, broadEdge, false);
        JsonObject preciseActivation = ownedActivation("ACT.PRECISE",
                "REGION.PRECISE", "precise.out", outputCell, preciseEdge,
                true);
        JsonObject unrelatedActivation = ownedActivation("ACT.UNRELATED",
                "REGION.UNRELATED", "other.out", outputCell, unrelatedEdge,
                false);

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(
                        Arrays.asList(region("REGION.TARGET"), broad,
                                precise, unrelated),
                        Arrays.asList(target, broadActivation,
                                preciseActivation, unrelatedActivation),
                        Arrays.asList(broadEdge, preciseEdge, unrelatedEdge),
                        Arrays.asList(
                                completeSummary("SUMMARY.BROAD",
                                        "REGION.BROAD", "broad.out"),
                                completeSummary("SUMMARY.PRECISE",
                                        "REGION.PRECISE", "precise.out"),
                                completeSummary("SUMMARY.UNRELATED",
                                        "REGION.UNRELATED", "other.out")),
                        Collections.singletonList(target),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertEquals(1, result.upstreamRequests.size());
        JsonObject request = result.upstreamRequests.get(0);
        assertEquals("REGION.PRECISE", request.get("upstreamRegion")
                .getAsString());
        assertEquals("precise.out", request.get("upstreamOutputPort")
                .getAsString());
        assertEquals("ACT.PRECISE", request.getAsJsonArray(
                "upstreamActivations").get(0).getAsJsonObject().get(
                "activationId").getAsString());
        JsonObject selection = request.getAsJsonObject(
                "dynamicOwnerSelection");
        assertEquals("EXACT_BINDING_WRITER_METHOD_MATCHES_REGION_ANCHOR",
                selection.get("authority").getAsString());
        assertEquals(2, selection.getAsJsonArray(
                "deduplicatedOverlappingRegions").size());
        assertEquals(2, result.manifest.get(
                "deduplicatedConcreteBindingAlternativeCount").getAsInt());
        assertEquals(0, result.alternativeWriterGroups.size());
    }

    @Test
    public void recursivelyFollowsOnlyRequestedOutputDependenciesAcrossBothPaths() {
        List<JsonObject> regions = Arrays.asList(
                region("REGION.CONSUMER"),
                regionWithSlice("REGION.MIDDLE", "middle.out", true,
                        "middle.relevant.in"),
                regionWithSlices("REGION.SOURCE",
                        outputSlice("source.via.out", true),
                        outputSlice("source.direct.out", true)),
                regionWithSlice("REGION.NOISE", "noise.out", true));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.C", "REGION.CONSUMER"),
                activation("ACT.M", "REGION.MIDDLE"),
                activation("ACT.S", "REGION.SOURCE"),
                activation("ACT.N", "REGION.NOISE"));
        List<JsonObject> edges = Arrays.asList(
                edge("EDGE.MIDDLE.CONSUMER", "REGION.MIDDLE", "middle.out",
                        "REGION.CONSUMER", "consumer.via.in", "EQUALITY"),
                edge("EDGE.DIRECT", "REGION.SOURCE", "source.direct.out",
                        "REGION.CONSUMER", "consumer.direct.in", "EQUALITY"),
                edge("EDGE.SOURCE.MIDDLE", "REGION.SOURCE", "source.via.out",
                        "REGION.MIDDLE", "middle.relevant.in", "EQUALITY"),
                edge("EDGE.UNRELATED", "REGION.NOISE", "noise.out",
                        "REGION.MIDDLE", "middle.unrelated.in", "EQUALITY"));

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(regions, activations, edges,
                        Arrays.asList(
                                completeSummary("SUMMARY.MIDDLE",
                                        "REGION.MIDDLE", "middle.out",
                                        "middle.relevant.in"),
                                completeSummary("SUMMARY.SOURCE.VIA",
                                        "REGION.SOURCE", "source.via.out"),
                                completeSummary("SUMMARY.SOURCE.DIRECT",
                                        "REGION.SOURCE",
                                        "source.direct.out")),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertTrue(result.manifest.get("complete").getAsBoolean());
        assertEquals(3, result.workItems.size());
        assertEquals(3, result.upstreamRequests.size());
        assertTrue(result.upstreamRequests.toString()
                .contains("source.direct.out"));
        assertTrue(result.upstreamRequests.toString()
                .contains("source.via.out"));
        assertFalse(result.upstreamRequests.toString()
                .contains("REGION.NOISE"));
        assertFalse(result.workItems.toString()
                .contains("middle.unrelated.in"));
        JsonObject middleRequest = requestForOutput(result, "middle.out");
        assertEquals("COMPLETE_RUNTIME_REGION_RELATION_OUTPUT_SLICE",
                middleRequest.get("outputDependencyClosureAuthority")
                        .getAsString());
        assertEquals("[\"middle.relevant.in\"]", middleRequest
                .getAsJsonArray("outputDependencyInputPorts").toString());
    }

    @Test
    public void completeRuntimeRelationCanProvideOutputSpecificDependencies() {
        List<JsonObject> regions = Arrays.asList(
                region("REGION.CONSUMER"), region("REGION.MIDDLE"),
                regionWithSlice("REGION.SOURCE", "source.out", true));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.C", "REGION.CONSUMER"),
                activation("ACT.M", "REGION.MIDDLE"),
                activation("ACT.S", "REGION.SOURCE"));
        List<JsonObject> edges = Arrays.asList(
                edge("EDGE.MC", "REGION.MIDDLE", "middle.out",
                        "REGION.CONSUMER", "consumer.in", "EQUALITY"),
                edge("EDGE.SM", "REGION.SOURCE", "source.out",
                        "REGION.MIDDLE", "middle.in", "EQUALITY"),
                edge("EDGE.UNRELATED", "REGION.SOURCE", "source.out",
                        "REGION.MIDDLE", "middle.unrelated.in", "EQUALITY"));
        JsonObject summary = completeSummary("SUMMARY.MIDDLE",
                "REGION.MIDDLE", "middle.out", "middle.in");

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(regions, activations, edges,
                        Arrays.asList(summary,
                                completeSummary("SUMMARY.SOURCE",
                                        "REGION.SOURCE", "source.out")),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertTrue(result.manifest.get("complete").getAsBoolean());
        assertEquals(2, result.workItems.size());
        JsonObject request = requestForOutput(result, "middle.out");
        assertEquals("HIT_COMPLETE", request.getAsJsonObject("summaryCache")
                .get("status").getAsString());
        assertEquals("COMPLETE_RUNTIME_REGION_RELATION_OUTPUT_SLICE",
                request.get("outputDependencyClosureAuthority").getAsString());
        assertFalse(result.workItems.toString()
                .contains("middle.unrelated.in"));
    }

    @Test
    public void staticOutputSliceDrivesRecursiveCaptureBeforeSummaryExists() {
        List<JsonObject> regions = Arrays.asList(
                region("REGION.CONSUMER"),
                regionWithSlice("REGION.MIDDLE", "middle.out", true,
                        "middle.in"),
                regionWithSlice("REGION.SOURCE", "source.out", true),
                regionWithSlice("REGION.NOISE", "noise.out", true));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.C", "REGION.CONSUMER"),
                activation("ACT.M", "REGION.MIDDLE"),
                activation("ACT.S", "REGION.SOURCE"),
                activation("ACT.N", "REGION.NOISE"));
        List<JsonObject> edges = Arrays.asList(
                edge("EDGE.MC", "REGION.MIDDLE", "middle.out",
                        "REGION.CONSUMER", "consumer.in", "EQUALITY"),
                edge("EDGE.SM", "REGION.SOURCE", "source.out",
                        "REGION.MIDDLE", "middle.in", "EQUALITY"),
                edge("EDGE.NOISE", "REGION.NOISE", "noise.out",
                        "REGION.MIDDLE", "middle.unrelated.in", "EQUALITY"));

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(regions, activations, edges,
                        Collections.singletonList(completeSummary(
                                "SUMMARY.SOURCE", "REGION.SOURCE",
                                "source.out")),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertEquals(2, result.upstreamRequests.size());
        JsonObject middle = requestForOutput(result, "middle.out");
        assertEquals("STATIC_REQUESTED_OUTPUT_BACKWARD_SLICE", middle.get(
                "outputDependencyClosureAuthority").getAsString());
        assertTrue(middle.get("captureRequired").getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("INCOMPLETE_UPSTREAM_REGION_RELATION"));
        assertFalse(result.upstreamRequests.toString()
                .contains("REGION.NOISE"));
    }

    @Test
    public void missingOutputSpecificSliceIsAnExplicitFailClosedGap() {
        List<JsonObject> regions = Arrays.asList(
                region("REGION.CONSUMER"), region("REGION.UPSTREAM"),
                regionWithSlice("REGION.SOURCE", "source.out", true));
        List<JsonObject> activations = Arrays.asList(
                activation("ACT.C", "REGION.CONSUMER"),
                activation("ACT.U", "REGION.UPSTREAM"),
                activation("ACT.S", "REGION.SOURCE"));
        List<JsonObject> edges = Arrays.asList(
                edge("EDGE.UC", "REGION.UPSTREAM", "upstream.out",
                        "REGION.CONSUMER", "consumer.in", "EQUALITY"),
                edge("EDGE.SU", "REGION.SOURCE", "source.out",
                        "REGION.UPSTREAM", "upstream.in", "EQUALITY"));

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(regions, activations, edges,
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertEquals(1, result.workItems.size());
        assertEquals(1, result.upstreamRequests.size());
        JsonObject request = result.upstreamRequests.get(0);
        assertFalse(request.get("recursiveExpansionAllowed").getAsBoolean());
        assertFalse(request.get("outputDependencyClosureComplete")
                .getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("MISSING_OUTPUT_DEPENDENCY_CLOSURE"));
        assertFalse(result.upstreamRequests.toString()
                .contains("source.out"));

        JsonObject incomplete = activations.get(1).deepCopy();
        incomplete.add("captureGoal", RegionCaptureGoal.outputClosure()
                .toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "upstream.out");
        incomplete.add("requestedOutput", requested);
        JsonObject partialSlice = outputSlice("upstream.out", false,
                "upstream.in");
        incomplete.add("requestedOutputSlice", partialSlice);
        incomplete.addProperty("requestedOutputSliceComplete", true);

        RecursiveRegionWorklist.Result rejected =
                RecursiveRegionWorklist.explore(regions,
                        Arrays.asList(activations.get(0), incomplete,
                                activations.get(2)), edges,
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());
        JsonObject rejectedRequest = requestForOutput(rejected,
                "upstream.out");
        assertFalse(rejectedRequest.get("recursiveExpansionAllowed")
                .getAsBoolean());
        assertFalse(rejectedRequest.get("outputDependencyClosureComplete")
                .getAsBoolean());
        assertTrue(rejected.manifest.getAsJsonArray("gaps").toString()
                .contains("MISSING_OUTPUT_DEPENDENCY_CLOSURE"));
        assertFalse(rejected.upstreamRequests.toString()
                .contains("source.out"));

        incomplete.remove("requestedOutputSlice");
        RecursiveRegionWorklist.Result missingNested =
                RecursiveRegionWorklist.explore(regions,
                        Arrays.asList(activations.get(0), incomplete,
                                activations.get(2)), edges,
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(activations.get(0)),
                        RecursiveRegionWorklist.Bounds.defaults());
        JsonObject missingNestedRequest = requestForOutput(missingNested,
                "upstream.out");
        assertFalse(missingNestedRequest.get("recursiveExpansionAllowed")
                .getAsBoolean());
        assertFalse(missingNestedRequest.get(
                "outputDependencyClosureComplete").getAsBoolean());
    }

    @Test
    public void validatedTransportEndpointCanPassThroughOneSymbolicInput() {
        JsonObject consumer = region("REGION.CONSUMER");
        JsonObject sender = region("REGION.SENDER");
        JsonObject input = new JsonObject();
        input.addProperty("portId", "sender.in.username");
        input.addProperty("cell", "<example.SaslClient: void send(java.lang.String)>.param0:java.lang.String");
        sender.getAsJsonArray("symbolicInputs").add(input);
        JsonObject transport = edge("EDGE.SASL", "REGION.SENDER",
                input.get("cell").getAsString(), "REGION.CONSUMER",
                "consumer.in.username", "EQUALITY");
        transport.addProperty("kind", "SASL_TRANSFER");

        RecursiveRegionWorklist.Result result =
                RecursiveRegionWorklist.explore(
                        Arrays.asList(consumer, sender),
                        Arrays.asList(activation("ACT.C", "REGION.CONSUMER"),
                                activation("ACT.S", "REGION.SENDER")),
                        Collections.singletonList(transport),
                        Collections.<JsonObject>emptyList(),
                        Collections.singletonList(
                                activation("ACT.C", "REGION.CONSUMER")),
                        RecursiveRegionWorklist.Bounds.defaults());

        assertEquals(1, result.upstreamRequests.size());
        JsonObject request = result.upstreamRequests.get(0);
        assertTrue(request.get("outputDependencyClosureComplete")
                .getAsBoolean());
        assertEquals("STATIC_TRANSPORT_ENDPOINT_IDENTITY", request.get(
                "outputDependencyClosureAuthority").getAsString());
        assertEquals("[\"sender.in.username\"]", request.getAsJsonArray(
                "outputDependencyInputPorts").toString());
        assertFalse(result.manifest.getAsJsonArray("gaps").toString()
                .contains("MISSING_OUTPUT_DEPENDENCY_CLOSURE"));
    }

    private static JsonObject region(String id) {
        JsonObject value = new JsonObject();
        value.addProperty("regionId", id);
        value.add("symbolicInputs", new JsonArray());
        value.add("outputs", new JsonArray());
        value.add("outputSlices", new JsonArray());
        return value;
    }

    private static JsonObject regionWithSlice(String id, String outputPort,
                                              boolean complete,
                                              String... inputPorts) {
        return regionWithSlices(id, outputSlice(outputPort, complete,
                inputPorts));
    }

    private static JsonObject regionWithOutputAndSlice(String id,
                                                       String outputPort,
                                                       String outputCell,
                                                       boolean complete,
                                                       String... inputs) {
        JsonObject value = regionWithSlice(id, outputPort, complete, inputs);
        JsonObject output = new JsonObject();
        output.addProperty("portId", outputPort);
        output.addProperty("cell", outputCell);
        value.getAsJsonArray("outputs").add(output);
        return value;
    }

    private static JsonObject ownerRegion(String id, String outputPort,
                                          String outputCell,
                                          String anchorMethod,
                                          int methodCount) {
        JsonObject value = regionWithOutputAndSlice(id, outputPort,
                outputCell, true);
        value.addProperty("anchorMethod", anchorMethod);
        JsonArray methods = new JsonArray();
        for (int index = 0; index < methodCount; index++) {
            methods.add("<example.Owner" + index + ": void run()>");
        }
        value.add("methods", methods);
        return value;
    }

    private static JsonObject concreteBinding(String edgeId,
                                              String fromInstance,
                                              String toInstance,
                                              String fromPort,
                                              String fromCell,
                                              String toPort,
                                              long writeSeq,
                                              long readSeq) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("fromOutputCell", fromCell);
        binding.addProperty("toInputPort", toPort);
        binding.addProperty("writeSeq", writeSeq);
        binding.addProperty("readSeq", readSeq);
        binding.addProperty("writerCallId", 99);
        binding.addProperty("writerOccurrence", 1);
        binding.addProperty("receiverObjectId", 1234);
        binding.addProperty("valueObjectId", 5678);
        binding.addProperty("field", fromCell);
        binding.addProperty("writeEvidenceKind", "FIELD_ASSIGNMENT");
        binding.addProperty("writeEvidenceAuthority",
                "RUNTIME_EXACT_FIELD_WRITE_EVENT_V1");
        binding.addProperty("orderAuthority",
                "GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1");
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("fieldReceiverIdentityConfirmed", true);
        return binding;
    }

    private static JsonObject ownedEdge(String edgeId, String fromRegion,
                                        String fromPort, String outputCell,
                                        String writerMethod) {
        JsonObject edge = edge(edgeId, fromRegion, outputCell,
                "REGION.TARGET", "target.in", "READ_FROM");
        JsonObject binding = concreteBinding(edgeId,
                fromRegion + "#call100", "REGION.TARGET#call7004",
                fromPort, outputCell, "target.in", 4016, 8361);
        binding.addProperty("writerSiteId", writerMethod + "#u17");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        edge.add("validatedBindings", bindings);
        return edge;
    }

    private static JsonObject ownedActivation(String activationId,
                                              String region,
                                              String outputPort,
                                              String outputCell,
                                              JsonObject edge,
                                              boolean anchorObserved) {
        JsonObject activation = activation(activationId, region);
        activation.addProperty("regionInstanceId", region + "#call100");
        activation.addProperty("anchorObserved", anchorObserved);
        activation.addProperty("replayable", true);
        activation.add("requestedOutputSlice", outputSlice(outputPort, true));
        activation.add("captureGoal", RegionCaptureGoal.outputClosure()
                .toJson());
        JsonObject output = new JsonObject();
        output.addProperty("portId", outputPort);
        output.addProperty("cell", outputCell);
        activation.add("requestedOutput", output);
        JsonArray bindings = new JsonArray();
        bindings.add(edge.getAsJsonArray("validatedBindings").get(0)
                .deepCopy());
        activation.add("edgeBindings", bindings);
        return activation;
    }

    private static JsonObject regionWithSlices(String id,
                                               JsonObject... slices) {
        JsonObject value = region(id);
        JsonArray outputSlices = value.getAsJsonArray("outputSlices");
        for (JsonObject slice : slices) outputSlices.add(slice);
        return value;
    }

    private static JsonObject outputSlice(String outputPort,
                                          boolean complete,
                                          String... inputPorts) {
        JsonObject value = new JsonObject();
        value.addProperty("outputPort", outputPort);
        value.addProperty("complete", complete);
        JsonArray inputs = new JsonArray();
        for (String input : inputPorts) inputs.add(input);
        value.add("inputPorts", inputs);
        return value;
    }

    private static JsonObject completeSummary(String id, String region,
                                              String outputPort,
                                              String... inputPorts) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", id);
        summary.addProperty("regionId", region);
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", outputPort);
        summary.add("requestedOutput", requested);
        summary.add("requestedOutputSlice", outputSlice(outputPort, true,
                inputPorts));
        JsonObject relation = new JsonObject();
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.addProperty("complete", true);
        summary.add("regionRelation", relation);
        return summary;
    }

    private static JsonObject requestForOutput(
            RecursiveRegionWorklist.Result result, String outputPort) {
        for (JsonObject request : result.upstreamRequests) {
            if (outputPort.equals(request.get("upstreamOutputPort")
                    .getAsString())) return request;
        }
        throw new AssertionError("no request for " + outputPort);
    }

    private static JsonObject activation(String id, String region) {
        JsonObject value = new JsonObject();
        value.addProperty("activationId", id);
        value.addProperty("regionInstanceId", region + "@test#runtime");
        value.addProperty("regionId", region);
        value.addProperty("test", "neutralUnitTest");
        value.addProperty("rootMethod", "<example.Neutral: void run()>");
        value.addProperty("invocationOrdinal", 1);
        value.add("branches", new JsonArray());
        value.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        return value;
    }

    private static JsonObject edge(String id, String fromRegion,
                                   String fromPort, String toRegion,
                                   String toPort, String relation) {
        JsonObject value = new JsonObject();
        value.addProperty("edgeId", id);
        value.addProperty("fromRegion", fromRegion);
        value.addProperty("fromPort", fromPort);
        value.addProperty("toRegion", toRegion);
        value.addProperty("toPort", toPort);
        value.addProperty("validatedRelation", relation);
        value.addProperty("composable", true);
        value.addProperty("eligibleForAutomaticDerivation", true);
        value.addProperty("eligibleForAutomaticSmt", true);
        if ("READ_FROM".equals(relation)) {
            value.addProperty("status", "CONFIRMED_READ_FROM");
            value.addProperty("confirmedReadFromPairCount", 1);
            JsonArray bindings = new JsonArray();
            bindings.add(concreteBinding(id,
                    fromRegion + "@test#runtime",
                    toRegion + "@test#runtime", fromPort, fromPort,
                    toPort, 1, 2));
            value.add("validatedBindings", bindings);
        } else {
            value.addProperty("status",
                    "CONFIRMED_RUNTIME_VALUE_EQUALITY");
            value.addProperty("valueEqualityObserved", true);
            value.addProperty("confirmedValueEqualityPairCount", 1);
            value.addProperty("valueEqualityAuthority",
                    "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
            JsonObject binding = new JsonObject();
            binding.addProperty("fromRegionInstance",
                    fromRegion + "@test#runtime");
            binding.addProperty("toRegionInstance",
                    toRegion + "@test#runtime");
            binding.addProperty("valueEqualityObserved", true);
            binding.addProperty("valueEqualityAuthority",
                    "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
            binding.addProperty("valueFingerprint", "sha256:" + id);
            binding.addProperty("endpointOrderAuthority",
                    "GLOBAL_TRACE_ENDPOINT_SEQUENCE");
            binding.addProperty("fromEndpointSeq", 1);
            binding.addProperty("toEndpointSeq", 2);
            binding.addProperty("orderConfirmed", true);
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            value.add("validatedBindings", bindings);
        }
        value.add("evidence", new JsonArray());
        return value;
    }

    private static void addCanonicalAlias(JsonObject edge, String port,
                                          String cell) {
        edge.addProperty("fromOutputPort", port);
        edge.addProperty("fromOutputCell", cell);
        JsonArray proofs = new JsonArray();
        proofs.add("DF.PROOF.1");
        proofs.add("DF.PROOF.2");
        edge.add("aliasProofEdgeIds", proofs);
        edge.addProperty("aliasProofAuthority",
                "CONFIGURED_RPC_PRODUCER_RETURN_AND_STATIC_EXACT_"
                        + "PUBLISH_VALUE_FLOW_V1");
        edge.addProperty("aliasProofComplete", true);
    }
}
