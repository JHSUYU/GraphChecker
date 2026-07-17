package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicComposedModelProjectorTest {
    @Test
    public void mergedSelectorModelChoosesExactlyOneSourceSummary()
            throws Exception {
        JsonObject composition = compositionManifest(
                minimalCase("CASE.REMOVE", "selector_remove",
                        "SUMMARY.REMOVE"),
                minimalCase("CASE.NO_REMOVE", "selector_no_remove",
                        "SUMMARY.NO_REMOVE"));
        Map<String, String> remove = new LinkedHashMap<>();
        remove.put("selector_remove", "true");
        remove.put("selector_no_remove", "false");
        Map<String, String> noRemove = new LinkedHashMap<>();
        noRemove.put("selector_remove", "false");
        noRemove.put("selector_no_remove", "true");

        assertEquals("SUMMARY.REMOVE",
                ConcolicComposedModelProjector.selectedCaseProjection(
                        composition, "REGION.10", remove).get(
                        "sourceSummaryId").getAsString());
        assertEquals("SUMMARY.NO_REMOVE",
                ConcolicComposedModelProjector.selectedCaseProjection(
                        composition, "REGION.10", noRemove).get(
                        "sourceSummaryId").getAsString());

        remove.put("selector_no_remove", "true");
        try {
            ConcolicComposedModelProjector.selectedCaseProjection(
                    composition, "REGION.10", remove);
            fail("two true selectors must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "MORE_THAN_ONE_TRUE_CASE_SELECTOR"));
        }
    }

    @Test
    public void selectedRemoveCaseProjectsExpiryWithoutMapClear()
            throws Exception {
        ProjectionFixture fixture = projectionFixture(false, true);

        ConcolicComposedModelProjector.Result result =
                ConcolicComposedModelProjector.project(fixture.arguments);

        assertTrue(result.manifest.get("projectionComplete").getAsBoolean());
        assertEquals("SUMMARY.REMOVE", result.manifest.get(
                "selectedCaseSourceSummaryId").getAsString());
        assertTrue(result.manifest.get(
                "selectedCaseContainsMapRemove").getAsBoolean());
        assertEquals("7", result.manifest.get(
                "targetDynamicEntryKey").getAsString());
        JsonArray assignments = result.manifest.getAsJsonArray(
                "upstreamModelAssignments");
        assertFalse(assignments.toString().contains("MAP_CLEAR"));
        assertTrue(assignments.toString().contains("expiry_remove"));
        assertTrue(assignments.toString().contains(
                "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM"));
        JsonObject expiry = assignmentBySolver(assignments,
                "expiry_remove");
        assertEquals("7", constantValue(expiry.getAsJsonObject(
                "expectedEntryKey")));
        assertEquals(0, result.manifest.get(
                "downstreamModelAssignmentCount").getAsInt());
        assertEquals(0, result.manifest.get(
                "downstreamReplayMaterializationCount").getAsInt());
        assertEquals(0, result.manifest.get(
                "downstreamBranchOverrideCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "finalModelSolverInvocationCount").getAsInt());
        assertEquals("ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL",
                result.manifest.get("modelScope").getAsString());
        for (JsonObject activation : result.activations) {
            if (activation.has("observationOnlyReplay")) continue;
            assertEquals(result.manifest.get("solverInputSha256").getAsString(),
                    activation.get("modelProjectionSolverInputSha256")
                            .getAsString());
            assertEquals(1, activation.get(
                    "modelProjectionManifestSchemaVersion").getAsInt());
        }
    }

    @Test
    public void missingExistingPreMapProducerRelationFailsClosed()
            throws Exception {
        ProjectionFixture fixture = projectionFixture(false, false);
        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("an existing pre-map must have runtime producer evidence");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "PRE_MAP_PRODUCER_PROJECTION_GAP"));
        }
    }

    @Test
    public void derivesExistingPreMapProducerFromExactRuntimeEdgeBinding()
            throws Exception {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.CONSUMER");
        summary.addProperty("activationId", "ACT.CONSUMER");
        summary.addProperty("regionId", "REGION.11");
        summary.addProperty("regionInstanceId", "INSTANCE.CONSUMER");
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "REGION_EDGE.STATE");
        edge.addProperty("relation", "READ_FROM");
        edge.addProperty("fromRegion", "REGION.12");
        edge.addProperty("fromRegionInstance", "INSTANCE.PRODUCER");
        edge.addProperty("fromOutputPort", "REGION.12.out.20");
        edge.addProperty("toRegion", "REGION.11");
        edge.addProperty("toRegionInstance", "INSTANCE.CONSUMER");
        edge.addProperty("toInputPort", "REGION.11.in.5");
        edge.addProperty("writerEventSeq", 100);
        edge.addProperty("readerEventSeq", 120);
        edge.addProperty("receiverObjectId", 77);
        edge.addProperty("orderConfirmed", true);
        edge.addProperty("objectIdentityConfirmed", true);
        edge.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_READ_FROM");
        JsonArray bindings = new JsonArray();
        bindings.add(edge);
        summary.add("edgeBindings", bindings);
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.CONSUMER");
        activation.addProperty("regionInstanceId", "INSTANCE.CONSUMER");

        JsonObject evidence = ConcolicComposedModelProjector
                .preMapProducerEvidence(summary, activation,
                        "REGION.11.in.5");

        assertEquals("REGION.12.out.20", evidence
                .get("producerStatePort").getAsString());
        assertEquals("INSTANCE.PRODUCER", evidence
                .get("producerRegionInstanceId").getAsString());
        assertEquals("EXACT_RUNTIME_EDGE_BINDING_READ_FROM_WITNESS",
                evidence.get("derivationAuthority").getAsString());
        assertTrue(evidence.get("complete").getAsBoolean());
    }

    @Test
    public void ambiguousRuntimePreMapWritersFailClosed() throws Exception {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.CONSUMER");
        summary.addProperty("activationId", "ACT.CONSUMER");
        summary.addProperty("regionId", "REGION.11");
        summary.addProperty("regionInstanceId", "INSTANCE.CONSUMER");
        JsonArray bindings = new JsonArray();
        for (int index = 0; index < 2; index++) {
            JsonObject edge = new JsonObject();
            edge.addProperty("edgeId", "EDGE." + index);
            edge.addProperty("relation", "READ_FROM");
            edge.addProperty("fromRegion", "REGION." + (12 + index));
            edge.addProperty("fromRegionInstance", "INSTANCE.P." + index);
            edge.addProperty("fromOutputPort", "REGION." + (12 + index)
                    + ".out.0");
            edge.addProperty("toRegion", "REGION.11");
            edge.addProperty("toRegionInstance", "INSTANCE.CONSUMER");
            edge.addProperty("toInputPort", "REGION.11.in.5");
            edge.addProperty("writerEventSeq", 100 + index);
            edge.addProperty("readerEventSeq", 120);
            edge.addProperty("receiverObjectId", 77);
            edge.addProperty("orderConfirmed", true);
            edge.addProperty("objectIdentityConfirmed", true);
            edge.addProperty("selectionAuthority",
                    "RUNTIME_CONFIRMED_READ_FROM");
            bindings.add(edge);
        }
        summary.add("edgeBindings", bindings);
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.CONSUMER");
        activation.addProperty("regionInstanceId", "INSTANCE.CONSUMER");

        try {
            ConcolicComposedModelProjector.preMapProducerEvidence(summary,
                    activation, "REGION.11.in.5");
            fail("two exact read-from writers must not be guessed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("found 2"));
        }
    }

    @Test
    public void receivedTargetKeyMakesMaterializableModelUnsat()
            throws Exception {
        ProjectionFixture fixture = projectionFixture(true, true);
        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("a received target key must contradict target absence");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "Materializable composed model is unsat"));
        }
    }
    @Test
    public void selectsCompletePreTargetProducerOrdinalBound()
            throws Exception {
        JsonObject source = source();
        JsonObject target = new JsonObject();
        target.addProperty("rootCallId", 7000);
        JsonObject first = candidate("ACT.UPSTREAM.2", "instance-3428",
                3428, 1);
        JsonObject second = candidate("ACT.UPSTREAM.3", "instance-3565",
                3565, 2);
        JsonObject afterTarget = candidate("ACT.UPSTREAM.4",
                "instance-90423", 90423, 3);
        JsonObject unconfirmedDuplicate = candidate("ACT.212",
                "instance-3428", 3428, 1);
        unconfirmedDuplicate.remove("upstreamEventObserved");
        unconfirmedDuplicate.remove("selectedUpstreamEvent");

        List<JsonObject> selected =
                ConcolicComposedModelProjector.selectBroadcastCandidates(
                        Arrays.asList(afterTarget, second,
                                unconfirmedDuplicate, first),
                        source, target, "REGION.10", 2);

        assertEquals(2, selected.size());
        assertEquals("ACT.UPSTREAM.2",
                selected.get(0).get("activationId").getAsString());
        assertEquals("ACT.UPSTREAM.3",
                selected.get(1).get("activationId").getAsString());
    }

    @Test
    public void rejectsChangedBoundInsteadOfTruncatingCandidates()
            throws Exception {
        JsonObject target = new JsonObject();
        target.addProperty("rootCallId", 7000);
        try {
            ConcolicComposedModelProjector.selectBroadcastCandidates(
                    Arrays.asList(
                            candidate("ACT.UPSTREAM.2", "instance-3428",
                                    3428, 1),
                            candidate("ACT.UPSTREAM.3", "instance-3565",
                                    3565, 2)),
                    source(), target, "REGION.10", 1);
            fail("a changed producer bound must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "expected 1 but selected 2"));
        }
    }

    @Test
    public void rejectsBoundThatOmitsCapturedSourceInstance()
            throws Exception {
        JsonObject target = new JsonObject();
        target.addProperty("rootCallId", 7000);
        try {
            ConcolicComposedModelProjector.selectBroadcastCandidates(
                    Arrays.asList(
                            candidate("ACT.UPSTREAM.2", "instance-3428",
                                    3428, 1),
                            candidate("ACT.UPSTREAM.X", "instance-other",
                                    3565, 2)),
                    source(), target, "REGION.10", 2);
            fail("the exact captured source must belong to the bound");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "does not contain captured source"));
        }
    }

    @Test
    public void exactDynamicProjectionRetainsOccurrenceTwoSelector()
            throws Exception {
        JsonObject summary = new JsonObject();
        JsonObject first = binding("REGION.10.in.6", "SITE.EXPIRY", 1,
                "key-one");
        JsonObject second = binding("REGION.10.in.6", "SITE.EXPIRY", 2,
                "key-two");
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        summary.add("dynamicFieldBindings", bindings);
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol",
                second.get("dynamicFieldSymbol").getAsString());
        assignment.addProperty("inputSymbol", "REGION.10.in.6");

        JsonObject retained =
                ConcolicComposedModelProjector.retainDynamicSelector(
                        summary, source(), assignment);

        assertEquals(2, retained.get("materializationOccurrence")
                .getAsInt());
        assertEquals(second.get("keyExpression"),
                retained.get("expectedEntryKey"));
    }

    @Test
    public void exactContainerProjectionRetainsArraySelectorWithoutMapKey()
            throws Exception {
        JsonObject summary = new JsonObject();
        JsonObject binding = containerBinding("REGION.10.in.0",
                "SITE.ID", 2, 3);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        summary.add("dynamicFieldBindings", bindings);
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol",
                binding.get("dynamicFieldSymbol").getAsString());
        assignment.addProperty("inputSymbol", "REGION.10.in.0");

        JsonObject retained =
                ConcolicComposedModelProjector.retainDynamicSelector(
                        summary, source(), assignment);

        assertFalse(retained.has("expectedEntryKey"));
        JsonObject selector = retained.getAsJsonObject("containerSelector");
        assertEquals("BIND.ARRAY.3",
                selector.get("bindingId").getAsString());
        assertEquals(2, selector.get("elementIndex").getAsInt());
        assertEquals(3, selector.get("elementOccurrence").getAsInt());
        assertEquals("EXACT_ARRAY_INDEX",
                selector.get("selectorAuthority").getAsString());

        JsonObject crossed = assignment.deepCopy();
        JsonObject wrong = selector.deepCopy();
        wrong.addProperty("elementIndex", 1);
        crossed.add("containerSelector", wrong);
        try {
            ConcolicComposedModelProjector.retainDynamicSelector(summary,
                    source(), crossed);
            fail("wrong array index must not project");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "CROSS_BINDING_CONTAINER_SELECTOR"));
        }
    }

    @Test
    public void exactMapProjectionRetainsRuntimeSelectorAndRejectsBadEvidence()
            throws Exception {
        JsonObject binding = mapProjectionBinding("REGION.10.in.0",
                "SITE.MAP", 0);
        JsonObject summary = new JsonObject();
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        summary.add("dynamicFieldBindings", bindings);
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol",
                binding.get("dynamicFieldSymbol").getAsString());
        assignment.addProperty("inputSymbol", "REGION.10.in.0");

        JsonObject retained =
                ConcolicComposedModelProjector.retainDynamicSelector(
                        summary, source(), assignment);

        assertFalse(retained.has("expectedEntryKey"));
        assertFalse(retained.has("containerSelector"));
        JsonObject selector = retained.getAsJsonObject(
                "mapProjectionSelector");
        assertEquals("MAP_OUTPUT_ARRAY_INDEX",
                selector.get("kind").getAsString());
        assertEquals(0, selector.get("outputIndex").getAsInt());
        assertEquals(901L, selector.get("mapObjectToken").getAsLong());
        assertEquals("NONE", selector.get(
                "crossExecutionOrdinalAuthority").getAsString());
        assertEquals("Y_I_11", selector.getAsJsonObject(
                "expectedMapKey").get("_exp").getAsString());

        JsonObject duplicateTokens = binding.deepCopy();
        duplicateTokens.getAsJsonArray(
                "entrySnapshotElementObjectTokens").set(1,
                duplicateTokens.getAsJsonArray(
                        "entrySnapshotElementObjectTokens").get(0));
        JsonObject invalid = new JsonObject();
        JsonArray invalidBindings = new JsonArray();
        invalidBindings.add(duplicateTokens);
        invalid.add("dynamicFieldBindings", invalidBindings);
        try {
            ConcolicComposedModelProjector.retainDynamicSelector(invalid,
                    source(), assignment);
            fail("duplicate activation-local element tokens must fail");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "INCOMPLETE_DYNAMIC_BINDING"));
        }

        JsonObject floatKey = binding.deepCopy();
        JsonObject negativeZero = new JsonObject();
        negativeZero.addProperty("_type", "ConstExpr");
        negativeZero.addProperty("_java_type", "java/lang/Float");
        negativeZero.addProperty("_exp", "Y_F_-0.0");
        floatKey.getAsJsonObject("mapProjectionSelector").add(
                "expectedMapKey", negativeZero.deepCopy());
        floatKey.getAsJsonArray("entrySnapshotMapKeyExpressions").set(0,
                negativeZero.deepCopy());
        JsonObject floatSummary = new JsonObject();
        JsonArray floatBindings = new JsonArray();
        floatBindings.add(floatKey);
        floatSummary.add("dynamicFieldBindings", floatBindings);
        try {
            ConcolicComposedModelProjector.retainDynamicSelector(
                    floatSummary, source(), assignment);
            fail("Float -0.0 key must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "INCOMPLETE_DYNAMIC_BINDING"));
        }

        JsonObject missingScope = binding.deepCopy();
        missingScope.remove("objectTokenScope");
        JsonObject missing = new JsonObject();
        JsonArray missingBindings = new JsonArray();
        missingBindings.add(missingScope);
        missing.add("dynamicFieldBindings", missingBindings);
        try {
            ConcolicComposedModelProjector.retainDynamicSelector(missing,
                    source(), assignment);
            fail("missing source activation scope must fail");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "INCOMPLETE_DYNAMIC_BINDING"));
        }
    }

    @Test
    public void vmWrappedDynamicProjectionRetainsExactSelector()
            throws Exception {
        JsonObject summary = new JsonObject();
        JsonObject first = binding("REGION.10.in.6", "SITE.EXPIRY", 1,
                "key-one");
        JsonObject second = binding("REGION.10.in.6", "SITE.EXPIRY", 2,
                "key-two");
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        summary.add("dynamicFieldBindings", bindings);
        String dynamic = second.get("dynamicFieldSymbol").getAsString();
        String engine = "M_J_field_" + dynamic
                + "_org/apache/hadoop/hdfs/security/token/block/BlockKey";
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", engine);
        assignment.addProperty("inputSymbol", "REGION.10.in.6");

        JsonObject retained =
                ConcolicComposedModelProjector.retainDynamicSelector(
                        summary, source(), assignment);

        assertEquals(engine, retained.get("engineSymbol").getAsString());
        assertEquals(dynamic,
                retained.get("dynamicFieldSymbol").getAsString());
        assertEquals(2, retained.get("materializationOccurrence")
                .getAsInt());
    }

    @Test
    public void uniqueBaseOnlyProjectionIsAlsoAnExplicitGap()
            throws Exception {
        JsonObject summary = new JsonObject();
        JsonArray bindings = new JsonArray();
        bindings.add(binding("REGION.10.in.6", "SITE.EXPIRY", 1,
                "key-one"));
        summary.add("dynamicFieldBindings", bindings);
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "REGION.10.in.6");
        assignment.addProperty("inputSymbol", "REGION.10.in.6");

        try {
            ConcolicComposedModelProjector.retainDynamicSelector(summary,
                    source(), assignment);
            fail("base-only projection must name the exact dynamic entry");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "BASE_ONLY_DYNAMIC_INPUT_PROHIBITED"));
        }
    }

    @Test
    public void malformedVmSuffixAndCrossBindingMetadataAreRejected()
            throws Exception {
        JsonObject summary = new JsonObject();
        JsonObject first = binding("REGION.10.in.6", "SITE.EXPIRY", 1,
                "key-one");
        JsonObject second = binding("REGION.10.in.6", "SITE.EXPIRY", 2,
                "key-two");
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        summary.add("dynamicFieldBindings", bindings);
        String dynamic = second.get("dynamicFieldSymbol").getAsString();

        JsonObject malformed = new JsonObject();
        malformed.addProperty("engineSymbol", "M_J_field_" + dynamic
                + "_java.lang.Long");
        malformed.addProperty("inputSymbol", "REGION.10.in.6");
        try {
            ConcolicComposedModelProjector.retainDynamicSelector(summary,
                    source(), malformed);
            fail("a non-VM owner suffix must not select a binding");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "ENGINE_SYMBOL_NOT_EXACT_DYNAMIC_BINDING"));
        }

        JsonObject crossed = new JsonObject();
        crossed.addProperty("engineSymbol", "M_J_field_" + dynamic
                + "_java/lang/Long");
        crossed.addProperty("inputSymbol", "REGION.10.in.6");
        crossed.addProperty("dynamicBindingId",
                first.get("dynamicBindingId").getAsString());
        try {
            ConcolicComposedModelProjector.retainDynamicSelector(summary,
                    source(), crossed);
            fail("engine and selector metadata must name the same binding");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "CROSS_BINDING_SELECTOR:dynamicBindingId"));
        }
    }

    @Test
    public void ambiguousBaseOnlyProjectionIsAnExplicitGap()
            throws Exception {
        JsonObject summary = new JsonObject();
        JsonArray bindings = new JsonArray();
        bindings.add(binding("REGION.10.in.6", "SITE.EXPIRY", 1,
                "key-one"));
        bindings.add(binding("REGION.10.in.6", "SITE.EXPIRY", 2,
                "key-two"));
        summary.add("dynamicFieldBindings", bindings);
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "REGION.10.in.6");
        assignment.addProperty("inputSymbol", "REGION.10.in.6");

        try {
            ConcolicComposedModelProjector.retainDynamicSelector(summary,
                    source(), assignment);
            fail("base-only projection must not broadcast to two entries");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "DYNAMIC_BINDING_PROJECTION_GAP"));
            assertTrue(expected.getMessage().contains(
                    "AMBIGUOUS_DYNAMIC_BASE_INPUT"));
        }
    }

    @Test
    public void projectsTwoProducerGroupsFromOneFinalSmtModel()
            throws Exception {
        ProjectionFixture fixture = multiGroupProjectionFixture();

        ConcolicComposedModelProjector.Result result =
                ConcolicComposedModelProjector.project(fixture.arguments);

        assertEquals(2, result.manifest.get("schemaVersion").getAsInt());
        assertEquals(1, result.manifest.get(
                "finalModelSolverInvocationCount").getAsInt());
        assertEquals("ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL",
                result.manifest.get("modelScope").getAsString());
        JsonArray groups = result.manifest.getAsJsonArray("producerGroups");
        assertEquals(2, groups.size());
        assertEquals(3, groups.get(0).getAsJsonObject().get(
                "upstreamModelAssignmentCount").getAsInt());
        assertEquals(4, groups.get(1).getAsJsonObject().get(
                "upstreamModelAssignmentCount").getAsInt());
        assertEquals("TARGET_MAP_STATE", groups.get(0).getAsJsonObject().get(
                "projectionRole").getAsString());
        assertEquals(2, groups.get(0).getAsJsonObject().get(
                "verifiedCaseWitnessCount").getAsInt());
        assertEquals("LOOKUP_KEY_PRODUCER",
                groups.get(1).getAsJsonObject().get("projectionRole")
                        .getAsString());
        assertEquals("key_g2_a", groups.get(1).getAsJsonObject().get(
                "lookupKeyProducerSolverTerm").getAsString());
        assertEquals("EFFECT.PUT.G2.A", groups.get(1).getAsJsonObject().get(
                "lookupKeyProducerSummaryEffectId").getAsString());
        assertEquals(2, result.manifest.get(
                "upstreamReplayActivationCount").getAsInt());
        assertEquals("<org.apache.hadoop.hdfs.security.token.block."
                        + "BlockTokenSecretManager: java.util.Map allKeys>",
                result.manifest.get("targetMapCell").getAsString());
        assertTrue(result.manifest.getAsJsonObject("modelValues").has(
                "key_g1_a"));
        assertTrue(result.manifest.getAsJsonObject("modelValues").has(
                "key_g2_b"));
        int targetCount = 0;
        java.util.Set<String> activationIds = new java.util.LinkedHashSet<>();
        for (JsonObject activation : result.activations) {
            assertTrue(activationIds.add(activation.get("activationId")
                    .getAsString()));
            if (!activation.has("observationOnlyReplay")) {
                assertEquals(result.manifest.get(
                                "solverInputSha256").getAsString(),
                        activation.get(
                                "modelProjectionSolverInputSha256")
                                .getAsString());
                assertEquals("ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL",
                        activation.get("modelProjectionModelScope")
                                .getAsString());
                assertEquals(2, activation.get(
                        "modelProjectionManifestSchemaVersion").getAsInt());
                continue;
            }
            targetCount++;
            assertEquals(0, activation.getAsJsonArray(
                    "modelAssignments").size());
            assertEquals(0, activation.getAsJsonArray(
                    "replayMaterializations").size());
            assertEquals(0, activation.getAsJsonArray(
                    "forcedBranches").size());
        }
        assertEquals(1, targetCount);
        assertEquals("TARGET_MAP_STATE", groups.get(0).getAsJsonObject()
                .get("projectionRole").getAsString());
        assertEquals("LOOKUP_KEY_PRODUCER", groups.get(1).getAsJsonObject()
                .get("projectionRole").getAsString());
    }

    @Test
    public void exactFatalReceiverIgnoresOtherTargetBindings()
            throws Exception {
        ProjectionFixture fixture = projectionFixture(false, true);
        Path summaries = fixture.summaries;
        JsonObject summary = new com.google.gson.JsonParser().parse(
                new String(Files.readAllBytes(summaries),
                        StandardCharsets.UTF_8).trim()).getAsJsonObject();
        JsonObject unrelated = new JsonObject();
        unrelated.addProperty("toRegionInstance", "INSTANCE.TARGET");
        unrelated.addProperty("toInputPort", "REGION.0.in.99");
        unrelated.addProperty("toInputCell", "<example.Other: int value>");
        summary.getAsJsonArray("edgeBindings").add(unrelated);
        writeJsonl(summaries, summary);

        ConcolicComposedModelProjector.Result result =
                ConcolicComposedModelProjector.project(fixture.arguments);

        assertEquals("REGION.0.in.0",
                result.manifest.get("targetMapInput").getAsString());

        JsonObject exactEdge = summary.getAsJsonArray("edgeBindings").get(0)
                .getAsJsonObject();
        String exactCell = exactEdge.get("toInputCell").getAsString();
        exactEdge.addProperty("toInputCell",
                "<example.OtherOwner: java.util.Map allKeys>");
        writeJsonl(summaries, summary);
        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("same field name on another owner must not match");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "found=0"));
        }
        exactEdge.addProperty("toInputCell", exactCell);

        JsonObject duplicate = summary.getAsJsonArray("edgeBindings").get(0)
                .getAsJsonObject().deepCopy();
        duplicate.addProperty("edgeId", "DUPLICATE.EXACT");
        summary.getAsJsonArray("edgeBindings").add(duplicate);
        writeJsonl(summaries, summary);
        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("two exact target receiver bindings must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "EXPECTED_ONE_EXACT_TARGET_ALL_KEYS_EDGE_BINDING"));
        }

        JsonArray edges = summary.getAsJsonArray("edgeBindings");
        edges.remove(0);
        edges.remove(1);
        writeJsonl(summaries, summary);
        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("missing exact target receiver binding must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "found=0"));
        }
    }

    @Test
    public void rejectsInvalidProducerRoleCardinalityAndMissingAuthority()
            throws Exception {
        ProjectionFixture fixture = multiGroupProjectionFixture();
        Path catalogPath = fixture.summaries.getParent().resolve(
                "producer-groups.json");
        JsonObject catalog = new com.google.gson.JsonParser().parse(
                new String(Files.readAllBytes(catalogPath),
                        StandardCharsets.UTF_8)).getAsJsonObject();
        JsonObject lookup = catalog.getAsJsonArray("producerGroups").get(1)
                .getAsJsonObject();
        lookup.remove("projectionRoleAuthority");
        write(catalogPath, catalog.toString());
        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("lookup role without runtime authority must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "DERIVED_ROLE_AUTHORITY_MISMATCH"));
        }

        fixture = multiGroupProjectionFixture();
        catalogPath = fixture.summaries.getParent().resolve(
                "producer-groups.json");
        catalog = new com.google.gson.JsonParser().parse(new String(
                Files.readAllBytes(catalogPath), StandardCharsets.UTF_8))
                .getAsJsonObject();
        lookup = catalog.getAsJsonArray("producerGroups").get(1)
                .getAsJsonObject();
        lookup.addProperty("projectionRole", "TARGET_MAP_STATE");
        lookup.addProperty("projectionRoleAuthority",
                ConcolicProducerGroupPlanner.TARGET_AUTHORITY);
        write(catalogPath, catalog.toString());
        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("two target-state roles must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "GROUP_WITNESS_ROLE_OR_REGION_MISMATCH"));
        }
    }

    @Test
    public void rejectsAmbiguousRuntimeConfirmedLookupKeyMapPut()
            throws Exception {
        ProjectionFixture fixture = multiGroupProjectionFixture();
        List<String> lines = Files.readAllLines(fixture.summaries,
                StandardCharsets.UTF_8);
        JsonObject first = new com.google.gson.JsonParser().parse(
                lines.get(0)).getAsJsonObject();
        JsonObject second = new com.google.gson.JsonParser().parse(
                lines.get(1)).getAsJsonObject();
        JsonObject secondPut = second.getAsJsonArray("heapEffects").get(1)
                .getAsJsonObject();
        secondPut.add("keyExpression", symbol("I", "KEY_G2_A_RAW"));
        write(fixture.summaries, first + "\n" + second + "\n");

        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("mutating a witnessed summary must invalidate its hash");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "ENRICHED_SUMMARIES_HASH_MISMATCH"));
        }
    }

    @Test
    public void rejectsCrossAttemptBindingsWithSameTestSeqAndFingerprint()
            throws Exception {
        JsonObject target = new JsonObject();
        target.addProperty("postDiscoveryTargetExecutionId", "EXEC.A");
        target.addProperty("regionInstanceId", "EXEC.A::INSTANCE.TARGET");
        JsonObject first = discoveredEqualityEdge("EDGE.A", "EXEC.A");
        JsonObject second = discoveredEqualityEdge("EDGE.B", "EXEC.B");
        try {
            ConcolicProducerGroupPlanner.validateExecutionBindingsForTests(
                    target, Arrays.asList(first, second), "artifact-sha");
            fail("same test/seq/fingerprint must not join campaign attempts");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "CROSS_OR_MISSING_DISCOVERED_EXECUTION"));
        }
    }

    @Test
    public void producerPlannerRefusesExistingOrAliasedOutputs()
            throws Exception {
        ProjectionFixture fixture = multiGroupProjectionFixture();
        JsonObject catalog = readObject(fixture.producerGroups);
        ConcolicProducerGroupPlanner.Arguments rerun = plannerArguments(
                catalog, fixture.producerGroups, fixture.targetActivationId);
        try {
            ConcolicProducerGroupPlanner.plan(rerun);
            fail("planner must not overwrite immutable outputs");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "OUTPUT_ALREADY_EXISTS"));
        }
    }

    @Test
    public void projectorRejectsComposerBindingHashPastedOntoOtherEdge()
            throws Exception {
        ProjectionFixture fixture = multiGroupProjectionFixture();
        Path catalogPath = fixture.producerGroups;
        JsonObject catalog = readObject(catalogPath);
        Path sidecarPath = java.nio.file.Paths.get(catalog.getAsJsonObject(
                "witnessSidecar").get("path").getAsString());
        JsonObject sidecar = readObject(sidecarPath);
        JsonObject targetWitness = witnessOfKind(sidecar,
                ConcolicProducerGroupPlanner.TARGET_WITNESS_KIND);
        JsonObject edge = targetWitness.getAsJsonArray(
                "runtimeProvenancePath").get(0).getAsJsonObject();
        JsonObject admission = edge.getAsJsonArray("composerAdmissions")
                .get(0).getAsJsonObject();
        JsonObject summary = summaryById(fixture.summaries, "SUMMARY.G1");
        JsonObject decoy = edgeBindingById(summary, "EDGE.DECOY.G1");
        admission.addProperty("selectedBindingObjectSha256",
                sha256(decoy.toString()));
        write(sidecarPath, sidecar.toString());
        catalog.getAsJsonObject("witnessSidecar").addProperty("sha256",
                sha256File(sidecarPath));
        write(catalogPath, catalog.toString());

        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("a legal selected binding hash cannot authenticate another "
                    + "runtime edge");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "COMPOSER_SELECTED_BINDING_DOES_NOT_DESCRIBE_RUNTIME_"
                            + "EDGE"));
        }
    }

    @Test
    public void projectorRejectsStaticMappingEvenWithRefreshedArtifactHashes()
            throws Exception {
        ProjectionFixture fixture = multiGroupProjectionFixture();
        Path catalogPath = fixture.producerGroups;
        JsonObject catalog = readObject(catalogPath);
        Path sidecarPath = java.nio.file.Paths.get(catalog.getAsJsonObject(
                "witnessSidecar").get("path").getAsString());
        JsonObject sidecar = readObject(sidecarPath);
        Path runtime = artifactPath(catalog, "RUNTIME_EDGE_VALIDATION");
        List<String> lines = Files.readAllLines(runtime,
                StandardCharsets.UTF_8);
        JsonObject first = new com.google.gson.JsonParser().parse(lines.get(0))
                .getAsJsonObject();
        first.addProperty("mappingOnly", true);
        lines.set(0, first.toString());
        Files.write(runtime, lines, StandardCharsets.UTF_8);
        String runtimeSha = sha256File(runtime);
        updateArtifactSha(catalog, "RUNTIME_EDGE_VALIDATION", runtimeSha);
        updateArtifactSha(sidecar, "RUNTIME_EDGE_VALIDATION", runtimeSha);
        write(sidecarPath, sidecar.toString());
        catalog.getAsJsonObject("witnessSidecar").addProperty("sha256",
                sha256File(sidecarPath));
        write(catalogPath, catalog.toString());

        try {
            ConcolicComposedModelProjector.project(fixture.arguments);
            fail("mapping-only evidence must never enter projection");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "RUNTIME_EDGE_METADATA_MISMATCH"));
        }
    }

    @Test
    public void producerPlannerRejectsAmbiguousRuntimePath()
            throws Exception {
        ProjectionFixture fixture = multiGroupProjectionFixture();
        Path catalogPath = fixture.producerGroups;
        JsonObject catalog = readObject(catalogPath);
        Path originalFatal = artifactPath(catalog, "FATAL_QUERIES");
        Path runtime = artifactPath(catalog, "RUNTIME_EDGE_VALIDATION");
        JsonObject fatal = readObject(originalFatal);
        JsonObject relation = fatal.getAsJsonObject("symbolicContext")
                .getAsJsonArray("equalityRelations").get(0)
                .getAsJsonObject().deepCopy();
        relation.addProperty("edgeId", "EDGE.LOOKUP.G2.ALT");
        relation.addProperty("toEndpoint", "REGION.0.in.10");
        relation.addProperty("toCell", "<example.Transport: int keyInAlt>");
        JsonObject selected = relation.getAsJsonArray("selectedBindings")
                .get(0).getAsJsonObject();
        selected.addProperty("fromEndpointSeq", 21);
        selected.addProperty("toEndpointSeq", 31);
        fatal.getAsJsonObject("symbolicContext").getAsJsonArray(
                "equalityRelations").add(relation);
        writeJsonl(originalFatal, fatal);
        JsonObject alternate = lookupRuntimeEdge();
        alternate.addProperty("edgeId", "EDGE.LOOKUP.G2.ALT");
        alternate.addProperty("toPort", "<example.Transport: int keyInAlt>");
        JsonObject raw = alternate.getAsJsonArray("validatedBindings").get(0)
                .getAsJsonObject();
        raw.addProperty("fromEndpointSeq", 21);
        raw.addProperty("toEndpointSeq", 31);
        Files.write(runtime, (alternate + "\n").getBytes(
                StandardCharsets.UTF_8), java.nio.file.StandardOpenOption.APPEND);

        Path sidecar = java.nio.file.Paths.get(catalog.getAsJsonObject(
                "witnessSidecar").get("path").getAsString());
        Path enriched = fixture.summaries;
        Files.delete(catalogPath);
        Files.delete(sidecar);
        Files.delete(enriched);
        ConcolicProducerGroupPlanner.Arguments rerun = plannerArguments(
                catalog, catalogPath, fixture.targetActivationId);
        try {
            ConcolicProducerGroupPlanner.plan(rerun);
            fail("two runtime paths to the same fatal instance are ambiguous");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "LOOKUP_RUNTIME_PATH_COUNT"));
        }
    }

    private static ProjectionFixture projectionFixture(
            boolean receivedContainsTarget, boolean includePreMapEvidence)
            throws Exception {
        Path root = Files.createTempDirectory("projector-selected-case-");
        Path smt = root.resolve("composition.smt2");
        Path composition = root.resolve("composition.json");
        Path summaries = root.resolve("summaries.jsonl");
        Path graph = root.resolve("graph.jsonl");
        Path upstreamActivations = root.resolve("upstream.jsonl");
        Path broadcastActivations = root.resolve("broadcast.jsonl");
        Path targetActivations = root.resolve("target.jsonl");
        Path fatal = root.resolve("fatal.jsonl");

        String site = "SITE.EXPIRY";
        String dynamic = "REGION.10.in.6.field."
                + sha256(site).substring(0, 12) + ".occ.1";
        String dynamicRaw = "M_J_field_" + dynamic + "_example/Key";
        JsonObject runtimeBinding = projectionRuntimeBinding(dynamic, site);
        JsonObject removeCase = projectionCase("CASE.REMOVE",
                "selector_remove", "SUMMARY.REMOVE", runtimeBinding,
                dynamicRaw);
        JsonObject noRemoveCase = minimalCase("CASE.NO_REMOVE",
                "selector_no_remove", "SUMMARY.NO_REMOVE");
        write(composition, compositionManifest(removeCase, noRemoveCase)
                .toString());

        write(smt, projectionSmt(receivedContainsTarget));
        JsonObject summary = projectionSummary(runtimeBinding);
        writeJsonl(summaries, summary);
        JsonObject activation = projectionActivation(summary,
                includePreMapEvidence);
        writeJsonl(upstreamActivations, activation);
        writeJsonl(broadcastActivations, activation);
        writeJsonl(targetActivations, targetActivation());
        writeJsonl(fatal, fatalQuery());
        writeJsonl(graph, staticAccessorEdge());

        ConcolicComposedModelProjector.Arguments arguments =
                ConcolicComposedModelProjector.Arguments.parse(new String[]{
                        "--smt", smt.toString(),
                        "--composition-manifest", composition.toString(),
                        "--upstream-summaries", summaries.toString(),
                        "--static-graph", graph.toString(),
                        "--upstream-activations",
                        upstreamActivations.toString(),
                        "--broadcast-activations",
                        broadcastActivations.toString(),
                        "--expected-broadcast-candidates", "1",
                        "--target-activations", targetActivations.toString(),
                        "--fatal-query", fatal.toString(),
                        "--upstream-region", "REGION.10",
                        "--target-activation-id", "ACT.TARGET",
                        "--output", root.resolve("plan.jsonl").toString(),
                        "--manifest", root.resolve("projection.json").toString()
                });
        return new ProjectionFixture(arguments, summaries);
    }

    private static ProjectionFixture multiGroupProjectionFixture()
            throws Exception {
        Path root = Files.createTempDirectory("projector-multi-group-");
        Path smt = root.resolve("composition.smt2");
        Path composition = root.resolve("composition.json");
        Path summaries = root.resolve("summaries.jsonl");
        Path graph = root.resolve("graph.jsonl");
        Path allActivations = root.resolve("producer-activations.jsonl");
        Path targetActivations = root.resolve("target.jsonl");
        Path fatal = root.resolve("fatal.jsonl");
        Path runtimeEdges = root.resolve("runtime-edges.jsonl");
        Path producerGroups = root.resolve("producer-groups.json");
        Path producerWitnesses = root.resolve("producer-witnesses.json");
        Path enrichedSummaries = root.resolve("enriched-summaries.jsonl");

        JsonObject bindingOne = multiRuntimeBinding("REGION.10", "G1");
        JsonObject bindingTwo = multiRuntimeBinding("REGION.20", "G2");
        JsonObject caseOne = multiProjectionCase("REGION.10", "G1",
                bindingOne, false);
        JsonObject caseOneAlternative = caseOne.deepCopy();
        caseOneAlternative.addProperty("caseId", "CASE.G1.ALT");
        caseOneAlternative.addProperty("pathKey", "PATH.CASE.G1.ALT");
        caseOneAlternative.addProperty("symbolScope",
                "region:REGION.10/case:CASE.G1.ALT");
        caseOneAlternative.addProperty("sourceSummaryId", "SUMMARY.G1.ALT");
        caseOneAlternative.addProperty("selectorSolverSymbol",
                "selector_g1_alt");
        JsonObject caseTwo = multiProjectionCase("REGION.20", "G2",
                bindingTwo, true);
        JsonObject compositionObject = compositionManifest(caseOne,
                caseOneAlternative, caseTwo);
        compositionObject.getAsJsonArray("boundedUpstreamRegions").add(
                "REGION.20");
        compositionObject.addProperty("fatalActivation", "ACT.TARGET");
        write(composition, compositionObject.toString());
        write(smt, multiProjectionSmt());

        JsonObject summaryOne = multiProjectionSummary("REGION.10", "G1",
                bindingOne, false);
        JsonObject summaryOneAlternative = summaryOne.deepCopy();
        summaryOneAlternative.addProperty("summaryId", "SUMMARY.G1.ALT");
        JsonObject summaryTwo = multiProjectionSummary("REGION.20", "G2",
                bindingTwo, true);
        write(summaries, summaryOne + "\n" + summaryOneAlternative + "\n"
                + summaryTwo + "\n");
        JsonObject activationOne = multiProjectionActivation("REGION.10",
                "G1", summaryOne, 10);
        JsonObject activationTwo = multiProjectionActivation("REGION.20",
                "G2", summaryTwo, 20);
        write(allActivations, activationOne + "\n" + activationTwo + "\n");
        JsonObject target = targetActivation();
        target.addProperty("test", "ExampleTest#test");
        writeJsonl(targetActivations, target);
        JsonObject fatalObject = fatalQuery();
        addLookupRuntimeContext(fatalObject);
        writeJsonl(fatal, fatalObject);
        write(runtimeEdges, targetStateRuntimeEdge() + "\n"
                + lookupRuntimeEdge() + "\n" + decoyRuntimeEdge() + "\n");
        writeJsonl(graph, staticAccessorEdge());

        ConcolicProducerGroupPlanner.Arguments plannerArguments =
                ConcolicProducerGroupPlanner.Arguments.parse(new String[]{
                        "--composition-manifest", composition.toString(),
                        "--smt", smt.toString(),
                        "--summaries", summaries.toString(),
                        "--activations", allActivations.toString(),
                        "--target-activations", targetActivations.toString(),
                        "--fatal-query", fatal.toString(),
                        "--runtime-edges", runtimeEdges.toString(),
                        "--z3", "/usr/local/bin/z3",
                        "--target-activation-id", "ACT.TARGET",
                        "--output-catalog", producerGroups.toString(),
                        "--output-witnesses", producerWitnesses.toString(),
                        "--output-summaries", enrichedSummaries.toString()
                });
        ConcolicProducerGroupPlanner.plan(plannerArguments);

        ConcolicComposedModelProjector.Arguments arguments =
                ConcolicComposedModelProjector.Arguments.parse(new String[]{
                        "--smt", smt.toString(),
                        "--composition-manifest", composition.toString(),
                        "--upstream-summaries", enrichedSummaries.toString(),
                        "--static-graph", graph.toString(),
                        "--producer-groups", producerGroups.toString(),
                        "--runtime-edges", runtimeEdges.toString(),
                        "--target-activations", targetActivations.toString(),
                        "--fatal-query", fatal.toString(),
                        "--target-activation-id", "ACT.TARGET",
                        "--output", root.resolve("plan.jsonl").toString(),
                        "--manifest", root.resolve("projection.json").toString()
                });
        return new ProjectionFixture(arguments, enrichedSummaries,
                producerGroups, "ACT.TARGET");
    }

    private static JsonObject producerGroupSpec(String id, String region,
                                                String activationFile,
                                                int expected, String role,
                                                String lookupRaw,
                                                JsonObject lookupWitness) {
        JsonObject result = new JsonObject();
        result.addProperty("producerGroupId", id);
        result.addProperty("upstreamRegion", region);
        result.addProperty("upstreamActivations", activationFile);
        result.addProperty("broadcastActivations", activationFile);
        result.addProperty("expectedBroadcastCandidates", expected);
        result.addProperty("projectionRole", role);
        if ("LOOKUP_KEY_PRODUCER".equals(role)) {
            result.addProperty("lookupKeyProducerRawEngineSymbol", lookupRaw);
            result.addProperty("lookupKeyProducerAuthority",
                    "RUNTIME_CONFIRMED_VALUE_EQUALITY_TO_LOOKUP_KEY_SOURCE");
            result.add("lookupKeyProducerWitness", lookupWitness);
        }
        return result;
    }

    private static JsonObject lookupKeyWitness(String region, String instance,
                                               String raw, String effectId) {
        JsonObject witness = new JsonObject();
        witness.addProperty("schemaVersion", 1);
        witness.addProperty("kind", "RUNTIME_CONFIRMED_LOOKUP_KEY_PRODUCER");
        witness.addProperty("complete", true);
        witness.addProperty("runtimeConfirmed", true);
        witness.addProperty("valueEqualityConfirmed", true);
        witness.addProperty("producerRegion", region);
        witness.addProperty("producerRegionInstanceId", instance);
        witness.addProperty("rawEngineSymbol", raw);
        witness.addProperty("summaryEffectId", effectId);
        witness.addProperty("sourceSummaryId", "SUMMARY.G2");
        witness.addProperty("producerActivationId", "ACT.UPSTREAM.G2");
        witness.addProperty("writerEventSeq", 20);
        witness.addProperty("readerEventSeq", 30);
        return witness;
    }

    private static JsonObject multiRuntimeBinding(String region,
                                                  String suffix)
            throws Exception {
        String site = "SITE.EXPIRY." + suffix;
        String base = region + ".in.6";
        String dynamic = base + ".field."
                + sha256(site).substring(0, 12) + ".occ.1";
        JsonObject result = projectionRuntimeBinding(dynamic, site);
        result.addProperty("baseInputSymbol", base);
        result.addProperty("dynamicFieldSymbol", dynamic);
        result.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        result.addProperty("materializationSiteId", site);
        if ("G2".equals(suffix)) {
            result.add("keyExpression", constant("I", "Y_I_99"));
        }
        return result;
    }

    private static JsonObject multiProjectionCase(String region,
                                                  String suffix,
                                                  JsonObject runtimeBinding,
                                                  boolean twoEffects) {
        String lower = suffix.toLowerCase();
        String dynamic = runtimeBinding.get("dynamicFieldSymbol").getAsString();
        String dynamicRaw = "M_J_field_" + dynamic + "_example/Key";
        JsonObject result = minimalCase("CASE." + suffix,
                "selector_" + lower, "SUMMARY." + suffix);
        result.addProperty("regionId", region);
        result.addProperty("symbolScope", "region:" + region + "/case:CASE."
                + suffix);
        result.addProperty("selectorGuardFormula", "(< expiry_" + lower
                + " 0)");
        JsonArray mappings = new JsonArray();
        mappings.add(termMapping("KEY_" + suffix + "_A_RAW",
                "key_" + lower + "_a", "Int", "SCOPED_ENGINE_SYMBOL"));
        mappings.add(termMapping("VALUE_" + suffix + "_A_RAW",
                "value_" + lower + "_a", "Ref",
                "SCOPED_ENGINE_SYMBOL"));
        if (twoEffects) {
            mappings.add(termMapping("KEY_" + suffix + "_B_RAW",
                    "key_" + lower + "_b", "Int",
                    "SCOPED_ENGINE_SYMBOL"));
            mappings.add(termMapping("VALUE_" + suffix + "_B_RAW",
                    "value_" + lower + "_b", "Ref",
                    "SCOPED_ENGINE_SYMBOL"));
        }
        mappings.add(termMapping("ARRAY_" + suffix + "_RAW",
                "array_" + lower, "(Array Int Value)",
                "SCOPED_ENGINE_ARRAY"));
        mappings.add(termMapping(dynamicRaw, "expiry_" + lower, "Int",
                "SCOPED_DYNAMIC_FIELD"));
        result.add("rawEngineSymbolMappings", mappings);
        result.addProperty("rawEngineSymbolMappingCount", mappings.size());
        JsonObject dynamicCatalog = runtimeBinding.deepCopy();
        dynamicCatalog.add("runtimeBinding", runtimeBinding.deepCopy());
        dynamicCatalog.add("fieldExpression", symbol("J", dynamicRaw));
        dynamicCatalog.addProperty("fieldExpressionRawEngineSymbol",
                dynamicRaw);
        dynamicCatalog.addProperty("fieldJavaType", "long");
        dynamicCatalog.addProperty("heapObservationId", "OBS." + suffix);
        dynamicCatalog.addProperty("observationMatched", true);
        dynamicCatalog.addProperty("solverTerm", "expiry_" + lower);
        dynamicCatalog.addProperty("sort", "INT");
        dynamicCatalog.addProperty("solverSort", "Int");
        dynamicCatalog.addProperty("termBindingAuthority",
                "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM");
        JsonArray dynamics = new JsonArray();
        dynamics.add(dynamicCatalog);
        result.add("dynamicFieldBindings", dynamics);
        result.addProperty("dynamicFieldBindingCount", 1);
        return result;
    }

    private static JsonObject multiProjectionSummary(String region,
                                                     String suffix,
                                                     JsonObject binding,
                                                     boolean twoEffects) {
        JsonObject result = new JsonObject();
        result.addProperty("summaryId", "SUMMARY." + suffix);
        result.addProperty("activationId", "ACT.UPSTREAM." + suffix);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", "INSTANCE." + suffix);
        result.addProperty("valid", true);
        result.addProperty("relationallyComplete", true);
        JsonArray effects = new JsonArray();
        effects.add(multiPutEffect(region, suffix, "A", true));
        if (twoEffects) effects.add(multiPutEffect(region, suffix, "B",
                false));
        JsonObject remove = new JsonObject();
        remove.addProperty("effectId", "EFFECT.REMOVE." + suffix);
        remove.addProperty("kind", "MAP_REMOVE");
        remove.addProperty("stateFamily", "MAP.STATE." + suffix);
        remove.addProperty("inputPort", region + ".in.0");
        effects.add(remove);
        result.add("heapEffects", effects);
        JsonArray path = new JsonArray();
        path.add(multiArrayLoad(suffix, "A", 0));
        if (twoEffects) path.add(multiArrayLoad(suffix, "B", 1));
        result.add("pathCondition", path);
        JsonArray dynamics = new JsonArray();
        dynamics.add(binding.deepCopy());
        result.add("dynamicFieldBindings", dynamics);
        JsonObject targetEdge = new JsonObject();
        targetEdge.addProperty("edgeId", "EDGE.TARGET." + suffix);
        targetEdge.addProperty("relation", "READ_FROM");
        targetEdge.addProperty("fromRegion", region);
        targetEdge.addProperty("toRegion", "REGION.0");
        targetEdge.addProperty("fromRegionInstance", "INSTANCE." + suffix);
        targetEdge.addProperty("toRegionInstance", "INSTANCE.TARGET");
        targetEdge.addProperty("fromOutputPort", region + ".out.0");
        targetEdge.addProperty("fromOutputCell",
                "<example.Manager: java.util.Map allKeys>" + suffix);
        targetEdge.addProperty("toInputPort", "REGION.0.in.0");
        targetEdge.addProperty("toInputCell",
                "<org.apache.hadoop.hdfs.security.token.block."
                        + "BlockTokenSecretManager: java.util.Map allKeys>");
        targetEdge.addProperty("writerEventSeq", 10);
        targetEdge.addProperty("readerEventSeq", 40);
        targetEdge.addProperty("receiverObjectId", 101);
        targetEdge.addProperty("valueObjectId", 202);
        targetEdge.addProperty("orderConfirmed", true);
        targetEdge.addProperty("objectIdentityConfirmed", true);
        targetEdge.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_READ_FROM");
        JsonArray edges = new JsonArray();
        if ("G1".equals(suffix)) {
            edges.add(targetEdge);
            edges.add(decoySummaryEdge());
        }
        result.add("edgeBindings", edges);
        return result;
    }

    private static JsonObject decoySummaryEdge() {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.DECOY.G1");
        edge.addProperty("relation", "READ_FROM");
        edge.addProperty("fromRegion", "REGION.10");
        edge.addProperty("toRegion", "REGION.99");
        edge.addProperty("fromRegionInstance", "INSTANCE.G1");
        edge.addProperty("toRegionInstance", "INSTANCE.DECOY");
        edge.addProperty("fromOutputPort", "REGION.10.out.99");
        edge.addProperty("fromOutputCell", "<example.Manager: int decoyOut>");
        edge.addProperty("toInputPort", "REGION.99.in.0");
        edge.addProperty("toInputCell", "<example.Manager: int decoyIn>");
        edge.addProperty("writerEventSeq", 11);
        edge.addProperty("readerEventSeq", 12);
        edge.addProperty("receiverObjectId", 303);
        edge.addProperty("valueObjectId", 404);
        edge.addProperty("orderConfirmed", true);
        edge.addProperty("objectIdentityConfirmed", true);
        edge.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_READ_FROM");
        return edge;
    }

    private static JsonObject multiPutEffect(String region, String suffix,
                                             String element,
                                             boolean bindsInput) {
        JsonObject put = new JsonObject();
        put.addProperty("effectId", "EFFECT.PUT." + suffix + "." + element);
        put.addProperty("kind", "MAP_PUT");
        put.addProperty("stateFamily", "MAP.STATE." + suffix);
        if (bindsInput) put.addProperty("inputBinding",
                "ACTIVATION_SYMBOL");
        put.addProperty("inputPort", region + ".in.0");
        put.add("keyExpression", symbol("I", "KEY_" + suffix + "_"
                + element + "_RAW"));
        put.add("valueExpression", symbol("example/Key", "VALUE_" + suffix
                + "_" + element + "_RAW"));
        put.addProperty("codePosition",
                "virtual int example.Key.getId():42");
        return put;
    }

    private static JsonObject multiArrayLoad(String suffix, String element,
                                             int index) {
        JsonObject load = new JsonObject();
        load.addProperty("_type", "_array_expr");
        load.addProperty("_is_load", true);
        load.addProperty("_arr_str", "ARRAY_" + suffix + "_RAW");
        load.add("_index_exp", constant("I", "Y_I_" + index));
        load.add("_value_exp", symbol("example/Key", "VALUE_" + suffix
                + "_" + element + "_RAW"));
        return load;
    }

    private static JsonObject multiProjectionActivation(String region,
                                                        String suffix,
                                                        JsonObject summary,
                                                        int call) {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", "ACT.UPSTREAM." + suffix);
        result.addProperty("selectedUpstreamActivationId",
                "ACT.UPSTREAM." + suffix);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", "INSTANCE." + suffix);
        result.addProperty("test", "ExampleTest#test");
        result.addProperty("rootMethod", "<example.Manager: void addKeys"
                + suffix + "()>");
        result.addProperty("rootCallId", call);
        result.addProperty("invocationOrdinal", 1);
        result.addProperty("upstreamEventObserved", true);
        JsonObject event = new JsonObject();
        event.addProperty("rootCallId", call);
        event.addProperty("writerCallId", call);
        result.add("selectedUpstreamEvent", event);
        JsonObject output = new JsonObject();
        output.addProperty("portId", region + ".out.0");
        output.addProperty("cell", "<example.Manager: java.util.Map allKeys>"
                + suffix);
        result.add("requestedOutput", output);
        JsonArray actions = new JsonArray();
        actions.add(projectionAction(region + ".in.0",
                "<example.Manager: java.util.Map allKeys>", "allKeys"));
        actions.add(projectionAction(region + ".in.1",
                "<example.Keys: example.Key[] allKeys>", "allKeys"));
        actions.add(projectionAction(region + ".in.6",
                "<example.Key: long expiry>", "expiry"));
        result.add("materializations", actions);
        JsonObject evidence = new JsonObject();
        evidence.addProperty("schemaVersion", 1);
        evidence.addProperty("kind",
                "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_RELATION");
        evidence.addProperty("authority",
                "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_RELATION");
        evidence.addProperty("complete", true);
        evidence.addProperty("runtimeConfirmed", true);
        evidence.addProperty("existingStateObserved", true);
        evidence.addProperty("inputPort", region + ".in.0");
        evidence.addProperty("producerStatePort", region + ".upstream.out.0");
        evidence.addProperty("producerRegionInstanceId",
                "INSTANCE.PRODUCER." + suffix);
        evidence.addProperty("sourceSummaryId",
                summary.get("summaryId").getAsString());
        evidence.addProperty("consumerActivationId",
                "ACT.UPSTREAM." + suffix);
        JsonArray relations = new JsonArray();
        relations.add(evidence);
        result.add("preMapProducerRelations", relations);
        return result;
    }

    private static String multiProjectionSmt() {
        return "(set-logic ALL)\n"
                + "(declare-sort Ref 0)\n"
                + "(declare-const nullRef Ref)\n"
                + "(declare-sort Value 0)\n"
                + "(declare-fun VInt (Int) Value)\n"
                + "(declare-sort MapState 0)\n"
                + "(declare-fun map_has (MapState Value) Bool)\n"
                + "(declare-const port__REGION_0_in_0 MapState)\n"
                + "(declare-const selector_g1 Bool)\n"
                + "(declare-const selector_g1_alt Bool)\n"
                + "(declare-const selector_g2 Bool)\n"
                + "(declare-const target_key Int)\n"
                + "(declare-const key_g1_a Int)\n"
                + "(declare-const value_g1_a Ref)\n"
                + "(declare-const array_g1 (Array Int Value))\n"
                + "(declare-const expiry_g1 Int)\n"
                + "(declare-const key_g2_a Int)\n"
                + "(declare-const value_g2_a Ref)\n"
                + "(declare-const key_g2_b Int)\n"
                + "(declare-const value_g2_b Ref)\n"
                + "(declare-const array_g2 (Array Int Value))\n"
                + "(declare-const expiry_g2 Int)\n"
                + "(assert selector_g1)\n"
                + "(assert (not selector_g1_alt))\n"
                + "(assert selector_g2)\n"
                + "(assert (= target_key 7))\n"
                + "(assert (= key_g1_a 8))\n"
                + "(assert (= key_g2_a 7))\n"
                + "(assert (= key_g2_b 10))\n"
                + "(assert (= expiry_g1 (- 5)))\n"
                + "(assert (= expiry_g2 (- 6)))\n"
                + "(assert (not (map_has port__REGION_0_in_0 "
                + "(VInt target_key))))\n";
    }

    private static JsonObject compositionManifest(JsonObject... cases) {
        JsonObject result = new JsonObject();
        result.addProperty("complete", true);
        result.addProperty("boundedComposition", true);
        result.addProperty("fatalReplayValidated", true);
        result.addProperty("fatalRegion", "REGION.0");
        JsonArray bounded = new JsonArray();
        bounded.add("REGION.10");
        result.add("boundedUpstreamRegions", bounded);
        JsonArray catalog = new JsonArray();
        for (JsonObject pathCase : cases) catalog.add(pathCase);
        result.add("caseProjectionCatalog", catalog);
        result.addProperty("caseProjectionCatalogComplete", true);
        result.addProperty("caseProjectionCatalogCount", catalog.size());
        return result;
    }

    private static JsonObject minimalCase(String caseId, String selector,
                                          String sourceSummary) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "GUARDED_CASE_PROJECTION_CATALOG");
        result.addProperty("regionId", "REGION.10");
        result.addProperty("caseId", caseId);
        result.addProperty("pathKey", "PATH." + caseId);
        result.addProperty("symbolScope", "region:REGION.10/case:" + caseId);
        result.addProperty("sourceSummaryId", sourceSummary);
        result.addProperty("sourceActivationId",
                "SUMMARY.REMOVE".equals(sourceSummary)
                        ? "ACT.UPSTREAM.REMOVE" : "ACT." + sourceSummary);
        result.addProperty("selectorSolverSymbol", selector);
        result.addProperty("selectorGuardFormula", "true");
        result.addProperty("selectorAuthority",
                "DECLARED_BOOL_EQ_EXACT_CASE_GUARD");
        result.addProperty("rawEngineSymbolMappingAuthority",
                "EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE");
        result.add("rawEngineSymbolMappings", new JsonArray());
        result.addProperty("rawEngineSymbolMappingCount", 0);
        result.add("dynamicFieldBindings", new JsonArray());
        result.addProperty("dynamicFieldBindingCount", 0);
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject projectionCase(String caseId, String selector,
                                             String sourceSummary,
                                             JsonObject runtimeBinding,
                                             String dynamicRaw) {
        JsonObject result = minimalCase(caseId, selector, sourceSummary);
        result.addProperty("selectorGuardFormula", "(< expiry_remove 0)");
        JsonArray mappings = new JsonArray();
        mappings.add(termMapping("KEY_REMOVE_RAW", "key_remove", "Int",
                "SCOPED_ENGINE_SYMBOL"));
        mappings.add(termMapping("VALUE_REMOVE_RAW", "value_remove", "Ref",
                "SCOPED_ENGINE_SYMBOL"));
        mappings.add(termMapping("ARRAY_REMOVE_RAW", "array_remove",
                "(Array Int Value)", "SCOPED_ENGINE_ARRAY"));
        mappings.add(termMapping(dynamicRaw, "expiry_remove", "Int",
                "SCOPED_DYNAMIC_FIELD"));
        result.add("rawEngineSymbolMappings", mappings);
        result.addProperty("rawEngineSymbolMappingCount", mappings.size());

        JsonObject dynamic = runtimeBinding.deepCopy();
        dynamic.add("runtimeBinding", runtimeBinding.deepCopy());
        dynamic.add("fieldExpression", symbol("J", dynamicRaw));
        dynamic.addProperty("fieldExpressionRawEngineSymbol", dynamicRaw);
        dynamic.addProperty("fieldJavaType", "long");
        dynamic.addProperty("heapObservationId", "OBS.EXPIRY");
        dynamic.addProperty("observationMatched", true);
        dynamic.addProperty("solverTerm", "expiry_remove");
        dynamic.addProperty("sort", "INT");
        dynamic.addProperty("solverSort", "Int");
        dynamic.addProperty("termBindingAuthority",
                "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM");
        JsonArray dynamics = new JsonArray();
        dynamics.add(dynamic);
        result.add("dynamicFieldBindings", dynamics);
        result.addProperty("dynamicFieldBindingCount", 1);
        return result;
    }

    private static JsonObject termMapping(String raw, String solver,
                                          String sort, String kind) {
        JsonObject result = new JsonObject();
        result.addProperty("rawEngineSymbol", raw);
        result.addProperty("solverTerm", solver);
        result.addProperty("solverSort", sort);
        result.addProperty("sort", "Int".equals(sort) ? "INT" : sort);
        result.addProperty("termKind", kind);
        result.addProperty("authority", "EMITTER_ACTUAL_TERM");
        return result;
    }

    private static JsonObject projectionRuntimeBinding(String dynamic,
                                                       String site) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        result.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        result.addProperty("baseInputSymbol", "REGION.10.in.6");
        result.addProperty("dynamicFieldSymbol", dynamic);
        result.addProperty("materializationSiteId", site);
        result.addProperty("materializationOccurrence", 1);
        result.addProperty("fieldSignature", "<example.Key: long expiry>");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        result.add("fieldPath", fieldPath);
        result.addProperty("entryReadObservationId", "OBS.EXPIRY");
        result.add("keyExpression", constant("I", "Y_I_7"));
        result.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        result.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject projectionSummary(JsonObject dynamicBinding) {
        JsonObject result = new JsonObject();
        result.addProperty("summaryId", "SUMMARY.REMOVE");
        result.addProperty("activationId", "ACT.UPSTREAM.REMOVE");
        result.addProperty("regionId", "REGION.10");
        result.addProperty("regionInstanceId", "INSTANCE.REMOVE");
        result.addProperty("valid", true);
        result.addProperty("relationallyComplete", true);

        JsonObject put = new JsonObject();
        put.addProperty("effectId", "EFFECT.PUT");
        put.addProperty("kind", "MAP_PUT");
        put.addProperty("stateFamily", "MAP.STATE.0");
        put.addProperty("inputBinding", "ACTIVATION_SYMBOL");
        put.addProperty("inputPort", "REGION.10.in.0");
        put.add("keyExpression", symbol("I", "KEY_REMOVE_RAW"));
        put.add("valueExpression", symbol("example/Key",
                "VALUE_REMOVE_RAW"));
        put.addProperty("codePosition",
                "virtual int example.Key.getId():42");
        JsonObject remove = new JsonObject();
        remove.addProperty("effectId", "EFFECT.REMOVE");
        remove.addProperty("kind", "MAP_REMOVE");
        remove.addProperty("stateFamily", "MAP.STATE.0");
        remove.addProperty("inputPort", "REGION.10.in.0");
        JsonArray effects = new JsonArray();
        effects.add(put);
        effects.add(remove);
        result.add("heapEffects", effects);

        JsonObject load = new JsonObject();
        load.addProperty("_type", "_array_expr");
        load.addProperty("_is_load", true);
        load.addProperty("_arr_str", "ARRAY_REMOVE_RAW");
        load.add("_index_exp", constant("I", "Y_I_0"));
        load.add("_value_exp", symbol("example/Key", "VALUE_REMOVE_RAW"));
        JsonArray path = new JsonArray();
        path.add(load);
        result.add("pathCondition", path);

        JsonArray dynamics = new JsonArray();
        dynamics.add(dynamicBinding.deepCopy());
        result.add("dynamicFieldBindings", dynamics);
        JsonObject edge = new JsonObject();
        edge.addProperty("toRegionInstance", "INSTANCE.TARGET");
        edge.addProperty("toInputPort", "REGION.0.in.0");
        edge.addProperty("toInputCell",
                "<org.apache.hadoop.hdfs.security.token.block."
                        + "BlockTokenSecretManager: java.util.Map allKeys>");
        JsonArray edges = new JsonArray();
        edges.add(edge);
        result.add("edgeBindings", edges);
        return result;
    }

    private static JsonObject projectionActivation(JsonObject summary,
                                                   boolean includeEvidence) {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", "ACT.UPSTREAM.REMOVE");
        result.addProperty("selectedUpstreamActivationId",
                "ACT.UPSTREAM.REMOVE");
        result.addProperty("regionId", "REGION.10");
        result.addProperty("regionInstanceId", "INSTANCE.REMOVE");
        result.addProperty("test", "ExampleTest#test");
        result.addProperty("rootMethod", "<example.Manager: void addKeys()>");
        result.addProperty("rootCallId", 10);
        result.addProperty("invocationOrdinal", 1);
        result.addProperty("upstreamEventObserved", true);
        JsonObject event = new JsonObject();
        event.addProperty("rootCallId", 10);
        event.addProperty("writerCallId", 10);
        result.add("selectedUpstreamEvent", event);
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.10.out.0");
        output.addProperty("cell", "<example.Manager: java.util.Map allKeys>");
        result.add("requestedOutput", output);

        JsonArray actions = new JsonArray();
        actions.add(projectionAction("REGION.10.in.0",
                "<example.Manager: java.util.Map allKeys>", "allKeys"));
        actions.add(projectionAction("REGION.10.in.1",
                "<example.Keys: example.Key[] allKeys>", "allKeys"));
        actions.add(projectionAction("REGION.10.in.6",
                "<example.Key: long expiry>", "expiry"));
        result.add("materializations", actions);
        if (includeEvidence) {
            JsonObject evidence = new JsonObject();
            evidence.addProperty("schemaVersion", 1);
            evidence.addProperty("kind",
                    "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_"
                            + "RELATION");
            evidence.addProperty("authority",
                    "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_"
                            + "RELATION");
            evidence.addProperty("complete", true);
            evidence.addProperty("runtimeConfirmed", true);
            evidence.addProperty("existingStateObserved", true);
            evidence.addProperty("inputPort", "REGION.10.in.0");
            evidence.addProperty("producerStatePort", "REGION.9.out.0");
            evidence.addProperty("producerRegionInstanceId",
                    "INSTANCE.PRODUCER");
            evidence.addProperty("sourceSummaryId",
                    summary.get("summaryId").getAsString());
            evidence.addProperty("consumerActivationId",
                    "ACT.UPSTREAM.REMOVE");
            JsonArray relations = new JsonArray();
            relations.add(evidence);
            result.add("preMapProducerRelations", relations);
        }
        return result;
    }

    private static JsonObject projectionAction(String symbol, String cell,
                                               String path) {
        JsonObject result = action(symbol, cell);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add(path);
        result.add("fieldPath", fieldPath);
        result.addProperty("bindingMode", "FIELD_ACCESS");
        return result;
    }

    private static JsonObject targetActivation() {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", "ACT.TARGET");
        result.addProperty("regionId", "REGION.0");
        result.addProperty("regionInstanceId", "INSTANCE.TARGET");
        result.addProperty("rootCallId", 100);
        JsonArray materializations = new JsonArray();
        materializations.add(projectionAction("REGION.0.in.0",
                "<org.apache.hadoop.hdfs.security.token.block."
                        + "BlockTokenSecretManager: java.util.Map allKeys>",
                "allKeys"));
        result.add("materializations", materializations);
        return result;
    }

    private static void addLookupRuntimeContext(JsonObject fatal) {
        JsonObject context = new JsonObject();
        context.addProperty("regionInstanceId", "INSTANCE.TARGET");
        JsonObject relation = new JsonObject();
        relation.addProperty("edgeId", "EDGE.LOOKUP.G2");
        relation.addProperty("fromEndpoint", "REGION.20.out.0");
        relation.addProperty("toEndpoint", "REGION.0.in.9");
        relation.addProperty("fromCell", "<example.Transport: int keyOut>");
        relation.addProperty("toCell", "<example.Transport: int keyIn>");
        relation.addProperty("runtimeStatus",
                "CONFIRMED_RUNTIME_VALUE_EQUALITY");
        JsonObject binding = lookupEqualityBinding();
        JsonArray selected = new JsonArray();
        selected.add(binding);
        relation.add("selectedBindings", selected);
        JsonArray equalities = new JsonArray();
        equalities.add(relation);
        context.add("equalityRelations", equalities);
        context.add("versionedStateMerges", new JsonArray());
        context.add("alternativeWriterGroups", new JsonArray());
        fatal.add("symbolicContext", context);
    }

    private static JsonObject targetStateRuntimeEdge() {
        JsonObject edge = runtimeEdgeBase("EDGE.TARGET.G1", "REGION.10",
                "REGION.0", "READ_FROM",
                "<example.Manager: java.util.Map allKeys>G1",
                "<org.apache.hadoop.hdfs.security.token.block."
                        + "BlockTokenSecretManager: java.util.Map allKeys>");
        JsonObject binding = new JsonObject();
        binding.addProperty("fromRegionInstance", "INSTANCE.G1");
        binding.addProperty("toRegionInstance", "INSTANCE.TARGET");
        binding.addProperty("test", "ExampleTest#test");
        binding.addProperty("writeSeq", 10);
        binding.addProperty("readSeq", 40);
        binding.addProperty("receiverObjectId", 101);
        binding.addProperty("valueObjectId", 202);
        binding.addProperty("orderConfirmed", true);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        edge.add("validatedBindings", bindings);
        edge.addProperty("validatedBindingCount", 1);
        return edge;
    }

    private static JsonObject lookupRuntimeEdge() {
        JsonObject edge = runtimeEdgeBase("EDGE.LOOKUP.G2", "REGION.20",
                "REGION.0", "EQUALITY",
                "<example.Transport: int keyOut>",
                "<example.Transport: int keyIn>");
        JsonArray bindings = new JsonArray();
        bindings.add(lookupEqualityBinding());
        edge.add("validatedBindings", bindings);
        edge.addProperty("validatedBindingCount", 1);
        return edge;
    }

    private static JsonObject decoyRuntimeEdge() {
        JsonObject edge = runtimeEdgeBase("EDGE.DECOY.G1", "REGION.10",
                "REGION.99", "READ_FROM",
                "<example.Manager: int decoyOut>",
                "<example.Manager: int decoyIn>");
        JsonObject binding = new JsonObject();
        binding.addProperty("fromRegionInstance", "INSTANCE.G1");
        binding.addProperty("toRegionInstance", "INSTANCE.DECOY");
        binding.addProperty("test", "ExampleTest#test");
        binding.addProperty("writeSeq", 11);
        binding.addProperty("readSeq", 12);
        binding.addProperty("receiverObjectId", 303);
        binding.addProperty("valueObjectId", 404);
        binding.addProperty("orderConfirmed", true);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        edge.add("validatedBindings", bindings);
        edge.addProperty("validatedBindingCount", 1);
        return edge;
    }

    private static JsonObject runtimeEdgeBase(String id, String from,
                                              String to, String relation,
                                              String fromCell,
                                              String toCell) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", id);
        edge.addProperty("fromRegion", from);
        edge.addProperty("toRegion", to);
        edge.addProperty("fromPort", fromCell);
        edge.addProperty("toPort", toCell);
        edge.addProperty("validatedRelation", relation);
        edge.addProperty("mappingOnly", false);
        edge.addProperty("composable", true);
        edge.addProperty("eligibleForAutomaticSmt", true);
        return edge;
    }

    private static JsonObject lookupEqualityBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("fromRegionInstance", "INSTANCE.G2");
        binding.addProperty("toRegionInstance", "INSTANCE.TARGET");
        binding.addProperty("test", "ExampleTest#test");
        binding.addProperty("fromEndpointSeq", 20);
        binding.addProperty("toEndpointSeq", 30);
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("valueEqualityObserved", true);
        binding.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        binding.addProperty("valueFingerprint", "sha256:fixture-key");
        binding.addProperty("fromFingerprintSource", "METHOD_RETURN");
        binding.addProperty("toFingerprintSource", "METHOD_ARGUMENT");
        return binding;
    }

    private static JsonObject fatalQuery() {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", "ACT.TARGET");
        result.addProperty("regionId", "REGION.0");
        result.addProperty("regionInstanceId", "INSTANCE.TARGET");
        result.addProperty("readyForSolver", true);
        JsonObject get = new JsonObject();
        get.addProperty("_type", "MethodExpression");
        get.addProperty("_name", "java/util/HashMap get");
        JsonArray parameters = new JsonArray();
        parameters.add(symbol("java/util/Map",
                "M_L_field_REGION.0.in.0_example/Manager"));
        parameters.add(symbol("I", "TARGET_KEY_RAW"));
        get.add("_param_list", parameters);
        get.add("_res_exp", symbol("example/Key", "TARGET_RESULT_RAW"));
        JsonArray constraints = new JsonArray();
        constraints.add(get);
        result.add("constraints", constraints);
        return result;
    }

    private static JsonObject staticAccessorEdge() {
        JsonObject result = new JsonObject();
        result.addProperty("id", "EDGE.GET_ID");
        result.addProperty("kind", "accessor_field_return");
        result.addProperty("line", 42);
        result.addProperty("method", "<example.Key: int getId()>");
        result.addProperty("fieldPath", "<example.Key: int id>#field:id");
        return result;
    }

    private static String projectionSmt(boolean receivedContainsTarget) {
        return "(set-logic ALL)\n"
                + "(declare-sort Ref 0)\n"
                + "(declare-const nullRef Ref)\n"
                + "(declare-sort Value 0)\n"
                + "(declare-fun VInt (Int) Value)\n"
                + "(declare-sort MapState 0)\n"
                + "(declare-fun map_has (MapState Value) Bool)\n"
                + "(declare-const port__REGION_0_in_0 MapState)\n"
                + "(declare-const selector_remove Bool)\n"
                + "(declare-const selector_no_remove Bool)\n"
                + "(declare-const target_key Int)\n"
                + "(declare-const key_remove Int)\n"
                + "(declare-const value_remove Ref)\n"
                + "(declare-const array_remove (Array Int Value))\n"
                + "(declare-const expiry_remove Int)\n"
                + "(assert selector_remove)\n"
                + "(assert (not selector_no_remove))\n"
                + "(assert (or selector_remove selector_no_remove))\n"
                + "(assert (not (and selector_remove selector_no_remove)))\n"
                + "(assert (= target_key 7))\n"
                + "(assert (= key_remove "
                + (receivedContainsTarget ? "7" : "8") + "))\n"
                + "(assert (= expiry_remove (- 5)))\n"
                + "(assert (not (map_has port__REGION_0_in_0 "
                + "(VInt target_key))))\n";
    }

    private static JsonObject symbol(String type, String raw) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", type);
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject constant(String type, String raw) {
        JsonObject result = symbol(type, raw);
        result.addProperty("_type", "ConstExpr");
        return result;
    }

    private static String constantValue(JsonObject expression) {
        String raw = expression.get("_exp").getAsString();
        int split = raw.lastIndexOf('_');
        return split < 0 ? raw : raw.substring(split + 1);
    }

    private static JsonObject assignmentBySolver(JsonArray assignments,
                                                 String solver) {
        for (com.google.gson.JsonElement element : assignments) {
            JsonObject assignment = element.getAsJsonObject();
            if (solver.equals(assignment.get("solverSymbol").getAsString())) {
                return assignment;
            }
        }
        throw new AssertionError("missing assignment for " + solver);
    }

    private static JsonObject discoveredEqualityEdge(String edgeId,
                                                     String execution) {
        JsonObject edge = runtimeEdgeBase(edgeId, "REGION.20", "REGION.0",
                "EQUALITY", "<example.Transport: int keyOut>",
                "<example.Transport: int keyIn>");
        edge.addProperty("discoveredExecutionId", execution);
        JsonArray executions = new JsonArray();
        executions.add(execution);
        edge.add("discoveredExecutionIds", executions);
        JsonObject binding = lookupEqualityBinding();
        binding.addProperty("fromRegionInstance", execution
                + "::INSTANCE.G2");
        binding.addProperty("toRegionInstance", execution
                + "::INSTANCE.TARGET");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        edge.add("validatedBindings", bindings);
        edge.addProperty("validatedBindingCount", 1);
        return edge;
    }

    private static ConcolicProducerGroupPlanner.Arguments plannerArguments(
            JsonObject catalog, Path catalogPath, String targetActivation) {
        return ConcolicProducerGroupPlanner.Arguments.parse(new String[]{
                "--composition-manifest", artifactPath(catalog,
                "COMPOSITION_MANIFEST").toString(),
                "--smt", artifactPath(catalog, "COMPOSED_SMT").toString(),
                "--summaries", artifactPath(catalog,
                "ORIGINAL_SUMMARIES").toString(),
                "--activations", artifactPath(catalog,
                "PRODUCER_ACTIVATIONS").toString(),
                "--target-activations", artifactPath(catalog,
                "TARGET_ACTIVATIONS").toString(),
                "--fatal-query", artifactPath(catalog,
                "FATAL_QUERIES").toString(),
                "--runtime-edges", artifactPath(catalog,
                "RUNTIME_EDGE_VALIDATION").toString(),
                "--z3", "/usr/local/bin/z3",
                "--target-activation-id", targetActivation,
                "--output-catalog", catalogPath.toString(),
                "--output-witnesses", catalog.getAsJsonObject(
                "witnessSidecar").get("path").getAsString(),
                "--output-summaries", catalog.getAsJsonObject(
                "enrichedSummaries").get("path").getAsString()
        });
    }

    private static Path artifactPath(JsonObject catalog, String role) {
        for (com.google.gson.JsonElement element : catalog.getAsJsonArray(
                "sourceArtifacts")) {
            JsonObject artifact = element.getAsJsonObject();
            if (role.equals(artifact.get("role").getAsString())) {
                return java.nio.file.Paths.get(artifact.get("path")
                        .getAsString());
            }
        }
        throw new AssertionError("missing artifact " + role);
    }

    private static void updateArtifactSha(JsonObject root, String role,
                                          String sha) {
        for (com.google.gson.JsonElement element : root.getAsJsonArray(
                "sourceArtifacts")) {
            JsonObject artifact = element.getAsJsonObject();
            if (role.equals(artifact.get("role").getAsString())) {
                artifact.addProperty("sha256", sha);
                return;
            }
        }
        throw new AssertionError("missing artifact " + role);
    }

    private static JsonObject witnessOfKind(JsonObject sidecar, String kind) {
        for (com.google.gson.JsonElement element : sidecar.getAsJsonArray(
                "witnesses")) {
            JsonObject witness = element.getAsJsonObject();
            if (kind.equals(witness.get("kind").getAsString())) return witness;
        }
        throw new AssertionError("missing witness " + kind);
    }

    private static JsonObject summaryById(Path summaries, String id)
            throws Exception {
        for (String line : Files.readAllLines(summaries,
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject summary = new com.google.gson.JsonParser().parse(line)
                    .getAsJsonObject();
            if (id.equals(summary.get("summaryId").getAsString())) {
                return summary;
            }
        }
        throw new AssertionError("missing summary " + id);
    }

    private static JsonObject edgeBindingById(JsonObject summary, String id) {
        for (com.google.gson.JsonElement element : summary.getAsJsonArray(
                "edgeBindings")) {
            JsonObject edge = element.getAsJsonObject();
            if (id.equals(edge.get("edgeId").getAsString())) return edge;
        }
        throw new AssertionError("missing edge binding " + id);
    }

    private static JsonObject readObject(Path path) throws Exception {
        return new com.google.gson.JsonParser().parse(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8))
                .getAsJsonObject();
    }

    private static String sha256File(Path path) throws Exception {
        byte[] digest = MessageDigest.getInstance("SHA-256").digest(
                Files.readAllBytes(path));
        StringBuilder result = new StringBuilder();
        for (byte value : digest) result.append(String.format("%02x",
                value & 0xff));
        return result.toString();
    }

    private static void writeJsonl(Path path, JsonObject value)
            throws Exception {
        write(path, value.toString() + "\n");
    }

    private static void write(Path path, String value) throws Exception {
        Files.write(path, value.getBytes(StandardCharsets.UTF_8));
    }

    private static final class ProjectionFixture {
        private final ConcolicComposedModelProjector.Arguments arguments;
        private final Path summaries;
        private final Path producerGroups;
        private final String targetActivationId;

        private ProjectionFixture(
                ConcolicComposedModelProjector.Arguments arguments,
                Path summaries) {
            this(arguments, summaries, null, "ACT.TARGET");
        }

        private ProjectionFixture(
                ConcolicComposedModelProjector.Arguments arguments,
                Path summaries, Path producerGroups,
                String targetActivationId) {
            this.arguments = arguments;
            this.summaries = summaries;
            this.producerGroups = producerGroups;
            this.targetActivationId = targetActivationId;
        }
    }

    private static JsonObject source() {
        JsonObject source = candidate("ACT.OUTPUT.capture",
                "instance-3565", 3565, 2);
        source.addProperty("selectedUpstreamActivationId",
                "ACT.UPSTREAM.3");
        JsonArray materializations = source.remove("symbolize")
                .getAsJsonArray();
        for (int index = 0; index < materializations.size(); index++) {
            JsonObject action = materializations.get(index)
                    .getAsJsonObject();
            action.addProperty("bindingMode", "FIELD_ACCESS");
            JsonArray fieldPath = new JsonArray();
            fieldPath.add("allKeys");
            action.add("fieldPath", fieldPath);
        }
        source.add("materializations", materializations);
        return source;
    }

    private static JsonObject candidate(String id, String instance,
                                        int call, int ordinal) {
        JsonObject candidate = new JsonObject();
        candidate.addProperty("activationId", id);
        candidate.addProperty("regionId", "REGION.10");
        candidate.addProperty("regionInstanceId", instance);
        candidate.addProperty("test", "ExampleTest#test");
        candidate.addProperty("rootMethod", "<Manager: void addKeys(Keys)>");
        candidate.addProperty("rootCallId", call);
        candidate.addProperty("invocationOrdinal", ordinal);
        candidate.addProperty("upstreamEventObserved", true);
        JsonObject event = new JsonObject();
        event.addProperty("rootCallId", call);
        event.addProperty("writerCallId", call);
        candidate.add("selectedUpstreamEvent", event);
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.10.out.4");
        output.addProperty("cell", "<Manager: java.util.Map allKeys>");
        candidate.add("requestedOutput", output);
        JsonArray actions = new JsonArray();
        actions.add(action("REGION.10.in.0",
                "<Manager: java.util.Map allKeys>"));
        actions.add(action("REGION.10.in.6",
                "<Keys: Key[] allKeys>"));
        candidate.add("symbolize", actions);
        return candidate;
    }

    private static JsonObject action(String symbol, String cell) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("sourceKind", "SHARED_HEAP");
        action.addProperty("projection", "value");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        return action;
    }

    private static JsonObject binding(String base, String site,
                                      int occurrence, String key)
            throws Exception {
        String dynamic = base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        JsonArray path = new JsonArray();
        path.add("expiry");
        binding.add("fieldPath", path);
        JsonObject keyExpression = new JsonObject();
        keyExpression.addProperty("_type", "ConstExpr");
        keyExpression.addProperty("_exp", key);
        binding.add("keyExpression", keyExpression);
        binding.addProperty("keyExpressionAuthority", "RUNTIME_KEY");
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject containerBinding(String base, String site,
                                               int index, int occurrence)
            throws Exception {
        String dynamic = base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 2);
        binding.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("leafOwnerObjectToken", 302L);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.UPSTREAM.3");
        binding.addProperty("containerBindingId", "BIND.ARRAY.3");
        binding.addProperty("containerInputPort", "REGION.10.in.6");
        binding.addProperty("containerInputCell", "<Keys: Key[] allKeys>");
        binding.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        binding.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        binding.addProperty("elementIndex", index);
        binding.addProperty("elementOccurrence", occurrence);
        binding.addProperty("declaredFieldOwnerClass", "example.Key");
        binding.addProperty("declaredFieldType", "int");
        JsonArray path = new JsonArray();
        path.add("id");
        binding.add("fieldPath", path);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.ARRAY.3");
        selector.addProperty("containerInputPort", "REGION.10.in.6");
        selector.addProperty("containerInputCell", "<Keys: Key[] allKeys>");
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", index);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "int");
        selector.addProperty("containerObjectToken", 301L);
        selector.addProperty("elementObjectToken", 302L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.UPSTREAM.3");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);
        binding.add("containerSelector", selector);
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject mapProjectionBinding(
            String base, String site, int index) throws Exception {
        int occurrence = index + 1;
        String dynamic = base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("kind",
                "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
        binding.addProperty("authority",
                "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_EXACT_"
                        + "OUTPUT_IDENTITY");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("fieldSignature",
                "<example.Key: long expiry>");
        JsonArray path = new JsonArray();
        path.add("expiry");
        binding.add("fieldPath", path);
        binding.addProperty("leafOwnerObjectToken", 911L + index);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.UPSTREAM.3");
        binding.addProperty("fieldJavaType", "long");
        binding.addProperty("entrySnapshotElementCount", 2);
        binding.addProperty("outputElementCount", 2);
        JsonArray tokens = new JsonArray();
        tokens.add(911L);
        tokens.add(912L);
        binding.add("entrySnapshotElementObjectTokens", tokens);
        JsonArray keys = new JsonArray();
        keys.add(immutableIntKey(11));
        keys.add(immutableIntKey(22));
        binding.add("entrySnapshotMapKeyExpressions", keys);
        binding.addProperty("entryKeyExpressionAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
        binding.addProperty("entrySetViewOrderAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                        + "REFERENCE_EQUALITY");
        binding.addProperty("runtimeSymbolizationAuthority",
                "EXACT_SYMBOLIZE_FIELD_OBSERVATION_AND_SYMBOLIZED_INPUT");
        binding.addProperty("projectionEvidenceAuthority",
                "UNIQUE_ENTRYSET_KEYED_SNAPSHOT_AND_OUTPUT_IDENTITY_"
                        + "VALIDATION");
        binding.addProperty("outputValidationMode",
                "ROOT_RETURN_PROJECTED_FIELD");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.MAP.EXPIRY");
        selector.addProperty("mapInputPort", base);
        selector.addProperty("mapInputCell",
                "<Manager: java.util.Map allKeys>");
        selector.addProperty("outputPort", "REGION.10.out.5");
        selector.addProperty("outputCell", "<Payload: Key[] keys>");
        selector.addProperty("mapProjectionOperation", "MAP_VALUES_VIEW");
        selector.addProperty("outputIndex", index);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature",
                "<example.Key: long expiry>");
        selector.addProperty("mapObjectToken", 901L);
        selector.addProperty("elementObjectToken", 911L + index);
        selector.addProperty("outputArrayObjectToken", 921L);
        selector.addProperty("outputIdentityVerified", true);
        selector.addProperty("outputVerificationAuthority",
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.UPSTREAM.3");
        selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
        selector.add("expectedMapKey", keys.get(index).deepCopy());
        selector.addProperty("expectedMapKeyAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
        selector.addProperty("sourceOutputIndexAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                        + "REFERENCE_EQUALITY");
        selector.addProperty("replaySelectionAuthority",
                "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_EXACT_"
                        + "OUTPUT_IDENTITY");
        selector.addProperty("authority",
                "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_EXACT_"
                        + "OUTPUT_IDENTITY");
        selector.addProperty("complete", true);
        binding.add("mapProjectionSelector", selector);
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject immutableIntKey(int value) {
        JsonObject key = new JsonObject();
        key.addProperty("_type", "ConstExpr");
        key.addProperty("_java_type", "java/lang/Integer");
        key.addProperty("_exp", "Y_I_" + value);
        return key;
    }

    private static String sha256(String value) throws Exception {
        byte[] bytes = MessageDigest.getInstance("SHA-256").digest(
                value.getBytes(StandardCharsets.UTF_8));
        StringBuilder result = new StringBuilder();
        for (byte current : bytes) {
            result.append(String.format("%02x", current & 0xff));
        }
        return result.toString();
    }
}
