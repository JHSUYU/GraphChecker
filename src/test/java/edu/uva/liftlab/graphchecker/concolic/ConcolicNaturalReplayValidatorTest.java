package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicNaturalReplayValidatorTest {
    @Test
    public void validatesEveryMemberOfBoundedConcreteProducerSet()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true,
                    false);
            JsonObject report = ConcolicNaturalReplayValidator.validate(
                    arguments(fixture));

            assertTrue(report.get("valid").getAsBoolean());
            assertEquals(2, report.get(
                    "boundedProducerInstanceCount").getAsInt());
            assertEquals(2, report.get(
                    "upstreamAppliedModelAssignmentCount").getAsInt());
            assertTrue(report.get(
                    "naturalPropagationEstablished").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsReplayMissingOneBoundedProducerResult()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false,
                    false);
            JsonObject report = ConcolicNaturalReplayValidator.validate(
                    arguments(fixture));

            assertFalse(report.get("valid").getAsBoolean());
            assertTrue(report.getAsJsonArray("failures").toString()
                    .contains("UPSTREAM_REPLAY_RESULT_MISSING:U2"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void validatesTwoProducerGroupsWithDifferentAssignmentCounts()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = multiGroupFixture(folder.getRoot().toPath(),
                    false, false, false, false);
            JsonObject report = ConcolicNaturalReplayValidator.validate(
                    arguments(fixture));

            assertTrue(report.toString(), report.get("valid").getAsBoolean());
            assertEquals(2, report.get("producerGroupCount").getAsInt());
            assertEquals(3, report.get(
                    "boundedProducerInstanceCount").getAsInt());
            assertEquals(4, report.get(
                    "upstreamAppliedModelAssignmentCount").getAsInt());
            JsonArray groups = report.getAsJsonArray("producerGroups");
            assertEquals(1, groups.get(0).getAsJsonObject().get(
                    "modelAssignmentCount").getAsInt());
            assertEquals(2, groups.get(1).getAsJsonObject().get(
                    "modelAssignmentCount").getAsInt());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsCrossGroupPlanAndUndeclaredDownstreamInjection()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = multiGroupFixture(folder.getRoot().toPath(),
                    true, true, false, false);
            JsonObject report = ConcolicNaturalReplayValidator.validate(
                    arguments(fixture));

            assertFalse(report.get("valid").getAsBoolean());
            String failures = report.getAsJsonArray("failures").toString();
            assertTrue(failures, failures.contains(
                    "UPSTREAM_PLAN_CROSSES_GROUP_BOUNDARY:G2U1"));
            assertTrue(failures, failures.contains(
                    "DOWNSTREAM_OR_UNDECLARED_INJECTION_PRESENT"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void keyedMapReplayRequiresPostApplicationOutputIdentity()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture exact = keyedFixture(folder.getRoot().toPath()
                    .resolve("exact"), false);
            JsonObject valid = ConcolicNaturalReplayValidator.validate(
                    arguments(exact));
            assertTrue(valid.toString(), valid.get("valid").getAsBoolean());

            Fixture mismatch = keyedFixture(folder.getRoot().toPath()
                    .resolve("mismatch"), true);
            JsonObject rejected = ConcolicNaturalReplayValidator.validate(
                    arguments(mismatch));
            assertFalse(rejected.get("valid").getAsBoolean());
            assertTrue(rejected.getAsJsonArray("failures").toString(),
                    rejected.getAsJsonArray("failures").toString().contains(
                            "UPSTREAM_MAP_PROJECTION_OUTPUT_IDENTITY_NOT_"
                                    + "VALIDATED:U2"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void schemaTwoRejectsSameCountManifestPlanValueTampering()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = multiGroupFixture(folder.getRoot().toPath(),
                    false, false, true, false);
            JsonObject report = ConcolicNaturalReplayValidator.validate(
                    arguments(fixture));

            assertFalse(report.get("valid").getAsBoolean());
            assertTrue(report.getAsJsonArray("failures").toString(),
                    report.getAsJsonArray("failures").toString().contains(
                            "UPSTREAM_MANIFEST_PLAN_ASSIGNMENT_MISMATCH"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void schemaOneRejectsUndeclaredAppliedAssignment()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true,
                    true);
            JsonObject report = ConcolicNaturalReplayValidator.validate(
                    arguments(fixture));

            assertFalse(report.get("valid").getAsBoolean());
            assertTrue(report.getAsJsonArray("failures").toString(),
                    report.getAsJsonArray("failures").toString().contains(
                            "UNDECLARED_MODEL_ASSIGNMENT_PRESENT"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void schemaTwoRejectsTopLevelModelProvenanceTampering()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = multiGroupFixture(folder.getRoot().toPath(),
                    false, false, false, true);
            JsonObject report = ConcolicNaturalReplayValidator.validate(
                    arguments(fixture));

            assertFalse(report.get("valid").getAsBoolean());
            assertTrue(report.getAsJsonArray("failures").toString(),
                    report.getAsJsonArray("failures").toString().contains(
                            "UPSTREAM_MODEL_PROVENANCE_MISMATCH:G1U1"));
        } finally {
            folder.delete();
        }
    }

    private static Fixture fixture(Path directory,
                                   boolean includeSecondResult,
                                   boolean extraAppliedAssignment)
            throws Exception {
        Path manifest = directory.resolve("manifest.json");
        Path plan = directory.resolve("plan.jsonl");
        Path results = directory.resolve("results.jsonl");
        Path output = directory.resolve("validation.json");
        write(manifest, manifest().toString() + "\n");
        writeJsonl(plan, Arrays.asList(upstreamPlan("U1", 1),
                upstreamPlan("U2", 2), targetPlan()));
        List<JsonObject> resultRows = new java.util.ArrayList<>(
                includeSecondResult
                ? Arrays.asList(upstreamResult("U1"),
                upstreamResult("U2"), targetResult())
                : Arrays.asList(upstreamResult("U1"), targetResult()));
        if (extraAppliedAssignment) {
            resultRows.add(upstreamResult("UNDECLARED"));
        }
        writeJsonl(results, resultRows);
        return new Fixture(manifest, plan, results, output);
    }

    private static Fixture multiGroupFixture(Path directory,
                                             boolean crossBoundary,
                                             boolean downstreamInjection,
                                             boolean tamperPlanValue,
                                             boolean tamperProvenance)
            throws Exception {
        Path manifest = directory.resolve("manifest-v2.json");
        Path plan = directory.resolve("plan-v2.jsonl");
        Path results = directory.resolve("results-v2.jsonl");
        Path output = directory.resolve("validation-v2.json");
        write(manifest, multiGroupManifest().toString() + "\n");
        JsonObject secondGroupPlan = multiUpstreamPlan("G2U1", "GROUP.2",
                "SET.2", 2);
        if (crossBoundary) secondGroupPlan.addProperty("producerGroupId",
                "GROUP.1");
        JsonObject target = multiTargetPlan();
        List<JsonObject> plans = new java.util.ArrayList<>(Arrays.asList(
                multiUpstreamPlan("G1U1", "GROUP.1", "SET.1", 1),
                multiUpstreamPlan("G1U2", "GROUP.1", "SET.1", 1),
                secondGroupPlan, target));
        if (tamperPlanValue) {
            plans.get(0).getAsJsonArray("modelAssignments").get(0)
                    .getAsJsonObject().addProperty("value", "999999");
        }
        if (tamperProvenance) {
            plans.get(0).addProperty("modelProjectionSolverInputSha256",
                    "wrong-model-hash");
        }
        if (downstreamInjection) {
            JsonObject extra = new JsonObject();
            extra.addProperty("activationId", "DOWNSTREAM.EXTRA");
            JsonArray assignments = new JsonArray();
            assignments.add(new JsonObject());
            extra.add("modelAssignments", assignments);
            extra.add("replayMaterializations", new JsonArray());
            extra.add("forcedBranches", new JsonArray());
            plans.add(extra);
        }
        writeJsonl(plan, plans);
        List<JsonObject> resultRows = new java.util.ArrayList<>(Arrays.asList(
                multiUpstreamResult("G1U1", 1),
                multiUpstreamResult("G1U2", 1),
                multiUpstreamResult("G2U1", 2), multiTargetResult()));
        if (downstreamInjection) {
            JsonObject extra = multiUpstreamResult("DOWNSTREAM.EXTRA", 1);
            resultRows.add(extra);
        }
        writeJsonl(results, resultRows);
        return new Fixture(manifest, plan, results, output);
    }

    private static Fixture keyedFixture(Path directory,
                                        boolean secondOutputMismatch)
            throws Exception {
        Files.createDirectories(directory);
        Path manifest = directory.resolve("manifest.json");
        Path plan = directory.resolve("plan.jsonl");
        Path results = directory.resolve("results.jsonl");
        Path output = directory.resolve("validation.json");
        write(manifest, keyedManifest().toString() + "\n");
        writeJsonl(plan, Arrays.asList(keyedUpstreamPlan("U1", 1),
                keyedUpstreamPlan("U2", 2), targetPlan()));
        writeJsonl(results, Arrays.asList(keyedUpstreamResult("U1", false),
                keyedUpstreamResult("U2", secondOutputMismatch),
                targetResult()));
        return new Fixture(manifest, plan, results, output);
    }

    private static ConcolicNaturalReplayValidator.Arguments arguments(
            Fixture fixture) {
        return ConcolicNaturalReplayValidator.Arguments.parse(new String[]{
                "--plan", fixture.plan.toString(),
                "--results", fixture.results.toString(),
                "--projection-manifest", fixture.manifest.toString(),
                "--output", fixture.output.toString()
        });
    }

    private static JsonObject manifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("projectionComplete", true);
        manifest.addProperty("downstreamInjectionForbidden", true);
        manifest.addProperty("boundedProducerInstanceSetComplete", true);
        manifest.addProperty("expectedBoundedProducerInstanceCount", 2);
        manifest.addProperty("boundedProducerInstanceCount", 2);
        manifest.addProperty("upstreamReplayActivationCount", 2);
        manifest.addProperty("boundedProducerInstanceSetId", "SET");
        JsonArray upstream = new JsonArray();
        upstream.add("U1");
        upstream.add("U2");
        manifest.add("upstreamReplayActivations", upstream);
        JsonArray members = new JsonArray();
        JsonObject first = new JsonObject();
        first.addProperty("capturedSourceInstance", false);
        first.addProperty("capturedSourceActivation", false);
        members.add(first);
        JsonObject second = new JsonObject();
        second.addProperty("capturedSourceInstance", true);
        second.addProperty("capturedSourceActivation", true);
        members.add(second);
        manifest.add("boundedProducerInstances", members);
        manifest.addProperty("targetObservationActivation", "T");
        manifest.addProperty("upstreamModelAssignmentCount", 1);
        manifest.add("upstreamModelAssignments",
                simpleAssignments("SINGLE", 1));
        manifest.addProperty("finalModelSolverInvocationCount", 1);
        manifest.addProperty("modelScope",
                "ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL");
        manifest.addProperty("solverInputSha256", "single-model-hash");
        return manifest;
    }

    private static JsonObject keyedManifest() {
        JsonObject manifest = manifest();
        JsonArray assignments = new JsonArray();
        assignments.add(mapProjectionAssignment("ACT.SOURCE"));
        manifest.add("upstreamModelAssignments", assignments);
        return manifest;
    }

    private static JsonObject multiGroupManifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("projectionComplete", true);
        manifest.addProperty("downstreamInjectionForbidden", true);
        manifest.addProperty("boundedProducerInstanceSetComplete", true);
        manifest.addProperty("allProducerGroupsComplete", true);
        manifest.addProperty("producerGroupCount", 2);
        manifest.addProperty("finalModelSolverInvocationCount", 1);
        manifest.addProperty("modelScope",
                "ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL");
        manifest.addProperty("solverInputSha256", "shared-model-hash");
        JsonArray groups = new JsonArray();
        groups.add(producerGroup("GROUP.1", "REGION.12", "SET.1",
                new String[]{"G1U1", "G1U2"}, 1));
        groups.add(producerGroup("GROUP.2", "REGION.9", "SET.2",
                new String[]{"G2U1"}, 2));
        manifest.add("producerGroups", groups);
        JsonArray flattened = new JsonArray();
        flattened.add("G1U1");
        flattened.add("G1U2");
        flattened.add("G2U1");
        manifest.add("upstreamReplayActivations", flattened);
        manifest.addProperty("upstreamReplayActivationCount", 3);
        manifest.addProperty("upstreamModelAssignmentDefinitionCount", 3);
        manifest.addProperty("expectedTotalUpstreamModelAssignmentCount", 4);
        manifest.addProperty("targetObservationActivation", "T2");
        return manifest;
    }

    private static JsonObject producerGroup(String id, String region,
                                            String setId, String[] replayIds,
                                            int assignmentCount) {
        JsonObject group = new JsonObject();
        group.addProperty("complete", true);
        group.addProperty("producerGroupId", id);
        group.addProperty("upstreamRegion", region);
        boolean targetState = "GROUP.1".equals(id);
        group.addProperty("projectionRole", targetState
                ? "TARGET_MAP_STATE" : "LOOKUP_KEY_PRODUCER");
        group.addProperty("selectedCaseId", "CASE." + id);
        group.addProperty("selectedCaseSourceSummaryId", "SUMMARY." + id);
        group.addProperty("upstreamRegionInstance", "INSTANCE." + id);
        group.addProperty("upstreamSourceActivation", "SOURCE." + id);
        group.addProperty("upstreamReplayActivation",
                replayIds[replayIds.length - 1]);
        group.addProperty("boundedProducerInstanceSetId", setId);
        group.addProperty("expectedBoundedProducerInstanceCount",
                replayIds.length);
        group.addProperty("boundedProducerInstanceCount", replayIds.length);
        group.addProperty("upstreamReplayActivationCount", replayIds.length);
        group.addProperty("upstreamModelAssignmentCount", assignmentCount);
        group.add("upstreamModelAssignments",
                simpleAssignments(id, assignmentCount));
        JsonObject evidence = new JsonObject();
        evidence.addProperty("complete", true);
        group.add("upstreamPreMapProducerEvidence", evidence);
        if (targetState) {
            group.addProperty("targetDynamicBindingId", "DYNAMIC.TARGET");
            group.addProperty("targetDynamicEntryKey", "7");
        } else {
            group.addProperty("lookupKeyProducerRawEngineSymbol", "KEY.RAW");
            group.addProperty("lookupKeyProducerSolverTerm", "key_solver");
            group.addProperty("lookupKeyProducerSummaryEffectId",
                    "EFFECT.KEY");
            group.addProperty("lookupKeyProducerAuthority",
                    "RUNTIME_CONFIRMED_VALUE_EQUALITY_TO_LOOKUP_KEY_SOURCE");
            JsonObject witness = new JsonObject();
            witness.addProperty("complete", true);
            group.add("lookupKeyProducerWitness", witness);
        }
        JsonArray replay = new JsonArray();
        JsonArray members = new JsonArray();
        for (int index = 0; index < replayIds.length; index++) {
            replay.add(replayIds[index]);
            JsonObject member = new JsonObject();
            member.addProperty("replayActivationId", replayIds[index]);
            member.addProperty("regionInstanceId", "INSTANCE." + id + "."
                    + index);
            member.addProperty("capturedSourceInstance",
                    index == replayIds.length - 1);
            member.addProperty("capturedSourceActivation",
                    index == replayIds.length - 1);
            members.add(member);
        }
        group.add("upstreamReplayActivations", replay);
        group.add("boundedProducerInstances", members);
        return group;
    }

    private static JsonObject upstreamPlan(String id, int ordinal) {
        JsonObject plan = new JsonObject();
        plan.addProperty("activationId", id);
        plan.addProperty("invocationOrdinal", ordinal);
        plan.addProperty("concreteReplayOnly", true);
        plan.addProperty("boundedProducerBroadcast", true);
        plan.addProperty("boundedProducerInstanceSetId", "SET");
        plan.add("modelAssignments", simpleAssignments("SINGLE", 1));
        addPlanProvenance(plan, 1, "single-model-hash");
        plan.add("replayMaterializations", new JsonArray());
        plan.add("forcedBranches", new JsonArray());
        return plan;
    }

    private static JsonObject keyedUpstreamPlan(String id, int ordinal) {
        JsonObject plan = upstreamPlan(id, ordinal);
        JsonArray assignments = new JsonArray();
        assignments.add(mapProjectionAssignment(id));
        plan.add("modelAssignments", assignments);
        return plan;
    }

    private static JsonObject targetPlan() {
        JsonObject plan = new JsonObject();
        plan.addProperty("activationId", "T");
        plan.addProperty("concreteReplayOnly", true);
        plan.addProperty("observationOnlyReplay", true);
        plan.addProperty("boundedProducerInstanceSetId", "SET");
        plan.add("modelAssignments", new JsonArray());
        plan.add("replayMaterializations", new JsonArray());
        plan.add("forcedBranches", new JsonArray());
        return plan;
    }

    private static JsonObject multiUpstreamPlan(String id, String group,
                                                String set,
                                                int assignmentCount) {
        JsonObject plan = upstreamPlan(id, 1);
        plan.addProperty("producerGroupId", group);
        plan.addProperty("boundedProducerInstanceSetId", set);
        plan.add("modelAssignments", simpleAssignments(group,
                assignmentCount));
        addPlanProvenance(plan, 2, "shared-model-hash");
        return plan;
    }

    private static JsonObject multiTargetPlan() {
        JsonObject plan = targetPlan();
        plan.addProperty("activationId", "T2");
        plan.remove("boundedProducerInstanceSetId");
        JsonArray sets = new JsonArray();
        sets.add("SET.1");
        sets.add("SET.2");
        plan.add("boundedProducerInstanceSetIds", sets);
        return plan;
    }

    private static JsonObject upstreamResult(String id) {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        result.addProperty("activationId", id);
        result.addProperty("executionMode", "CONCRETE_REPLAY_ONLY");
        result.addProperty("allModelAssignmentsApplied", true);
        result.add("modelAssignmentsApplied",
                runtimeAssignments(simpleAssignments("SINGLE", 1)));
        result.add("replayMaterializationsApplied", new JsonArray());
        result.addProperty("branchOverrideUsed", false);
        return result;
    }

    private static JsonObject keyedUpstreamResult(
            String id, boolean outputMismatch) {
        JsonObject result = upstreamResult(id);
        JsonArray applied = new JsonArray();
        applied.add(mapProjectionAssignment(id));
        result.add("modelAssignmentsApplied", runtimeAssignments(applied));
        result.add("unresolvedInputs", new JsonArray());
        JsonArray observations = new JsonArray();
        JsonObject entry = mapProjectionObservation(id,
                "ENTRY_SNAPSHOT");
        entry.addProperty("entrySnapshotComplete", true);
        entry.addProperty("expectedMapKeyAndSourceIndexValidated", true);
        entry.addProperty("expectedMapKeyAssignmentCount", 1);
        entry.addProperty("expectedMapKeyValidatedCount", 1);
        observations.add(entry);
        JsonObject output = mapProjectionObservation(id,
                "OUTPUT_IDENTITY_VALIDATION");
        output.addProperty("outputIdentityVerified", !outputMismatch);
        output.addProperty("outputArrayObjectToken", 701L);
        output.addProperty("outputVerificationAuthority",
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
        output.addProperty("complete", !outputMismatch);
        observations.add(output);
        result.add("mapValueElementProjectionObservations", observations);
        return result;
    }

    private static JsonObject mapProjectionObservation(String activation,
                                                        String phase) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "MAP_VALUE_OUTPUT_ARRAY_PROJECTION");
        row.addProperty("phase", phase);
        row.addProperty("groupId", "REGION.MAP.in.0\nREGION.MAP.out.0\n"
                + "<Payload: Key[] keys>\nMAP_VALUES_VIEW");
        row.addProperty("objectTokenScope", activation);
        row.addProperty("entrySetViewOrderVerified", true);
        row.addProperty("entrySetViewOrderAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                        + "REFERENCE_EQUALITY");
        row.addProperty("complete", true);
        return row;
    }

    private static JsonObject mapProjectionAssignment(String activation) {
        String dynamic = "REGION.MAP.in.0.field.keyed.occ.1";
        JsonObject assignment = new JsonObject();
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        assignment.addProperty("baseInputSymbol", "REGION.MAP.in.0");
        assignment.addProperty("dynamicFieldSymbol", dynamic);
        assignment.addProperty("engineSymbol", dynamic);
        assignment.addProperty("solverSymbol", "solver_map_expiry");
        assignment.addProperty("inputSymbol", "REGION.MAP.in.0");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "123456");
        assignment.addProperty("authority",
                "Z3_BOUNDED_COMPOSED_MODEL_PROJECTION");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.addProperty("materializationSiteId", "SITE.MAP");
        assignment.addProperty("materializationOccurrence", 1);
        assignment.addProperty("dynamicFieldBindingKind",
                "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.MAP.EXPIRY");
        selector.addProperty("mapInputPort", "REGION.MAP.in.0");
        selector.addProperty("mapInputCell", "<Manager: Map allKeys>");
        selector.addProperty("outputPort", "REGION.MAP.out.0");
        selector.addProperty("outputCell", "<Payload: Key[] keys>");
        selector.addProperty("mapProjectionOperation", "MAP_VALUES_VIEW");
        selector.addProperty("outputIndex", 0);
        selector.addProperty("elementOccurrence", 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature",
                "<example.Key: long expiry>");
        selector.addProperty("mapObjectToken", 501L);
        selector.addProperty("elementObjectToken", 601L);
        selector.addProperty("outputArrayObjectToken", 701L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", activation);
        selector.addProperty("sourceObjectTokenScope", "ACT.SOURCE");
        selector.addProperty("replayScopeRebindingAuthority",
                "SOURCE_CASE_SELECTOR_VALIDATED_THEN_REPLAY_ACTIVATION_"
                        + "SCOPE_REBOUND_TOKENS_NOT_COMPARED_ACROSS_"
                        + "EXECUTIONS");
        selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
        JsonObject key = new JsonObject();
        key.addProperty("_type", "ConstExpr");
        key.addProperty("_java_type", "java/lang/Integer");
        key.addProperty("_exp", "Y_I_11");
        selector.add("expectedMapKey", key);
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
        selector.addProperty("outputIdentityVerified", true);
        selector.addProperty("outputVerificationAuthority",
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
        selector.addProperty("complete", true);
        assignment.add("mapProjectionSelector", selector);
        return assignment;
    }

    private static JsonArray simpleAssignments(String group, int count) {
        JsonArray result = new JsonArray();
        for (int index = 0; index < count; index++) {
            JsonObject assignment = new JsonObject();
            String suffix = group.replace('.', '_') + "_" + index;
            assignment.addProperty("engineSymbol", "ENGINE_" + suffix);
            assignment.addProperty("solverSymbol", "solver_" + suffix);
            assignment.addProperty("inputSymbol", "INPUT_" + suffix);
            assignment.addProperty("valueType", "INT");
            assignment.addProperty("value", String.valueOf(100 + index));
            assignment.addProperty("authority",
                    "Z3_BOUNDED_COMPOSED_MODEL_PROJECTION");
            assignment.addProperty("materializeAtRealDefinition", true);
            result.add(assignment);
        }
        return result;
    }

    private static JsonArray runtimeAssignments(JsonArray planned) {
        JsonArray result = planned.deepCopy();
        for (int index = 0; index < result.size(); index++) {
            result.get(index).getAsJsonObject().remove("solverSymbol");
        }
        return result;
    }

    private static void addPlanProvenance(JsonObject plan, int schema,
                                          String solverHash) {
        plan.addProperty("modelProjectionAuthority",
                "Z3_BOUNDED_COMPOSITION_WITH_MATERIALIZABILITY_REFINEMENT");
        plan.addProperty("modelProjectionSolverInputSha256", solverHash);
        plan.addProperty("modelProjectionModelScope",
                "ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL");
        plan.addProperty("modelProjectionManifestSchemaVersion", schema);
    }

    private static JsonObject multiUpstreamResult(String id,
                                                  int assignmentCount) {
        JsonObject result = upstreamResult(id);
        String group = id.startsWith("G1") ? "GROUP.1" : "GROUP.2";
        result.add("modelAssignmentsApplied", runtimeAssignments(
                simpleAssignments(group, assignmentCount)));
        return result;
    }

    private static JsonObject targetResult() {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        result.addProperty("activationId", "T");
        result.addProperty("executionMode", "CONCRETE_REPLAY_ONLY");
        result.add("modelAssignmentsApplied", new JsonArray());
        result.add("replayMaterializationsApplied", new JsonArray());
        result.addProperty("branchOverrideUsed", false);
        JsonObject mapping = new JsonObject();
        mapping.addProperty("scheduledTarget", true);
        mapping.addProperty("scheduledOutcomeMatched", true);
        mapping.addProperty("replayValidation", "PASS");
        mapping.addProperty("overrideApplied", false);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        result.add("branchMappings", mappings);
        result.addProperty("exitKind", "THROW");
        JsonObject exception = new JsonObject();
        exception.addProperty("type", "ExampleException");
        JsonArray exceptions = new JsonArray();
        exceptions.add(exception);
        result.add("exceptionChain", exceptions);
        return result;
    }

    private static JsonObject multiTargetResult() {
        JsonObject result = targetResult();
        result.addProperty("activationId", "T2");
        return result;
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws Exception {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(row).append('\n');
        write(path, value.toString());
    }

    private static void write(Path path, String value) throws Exception {
        Files.write(path, value.getBytes(StandardCharsets.UTF_8));
    }

    private static final class Fixture {
        private final Path manifest;
        private final Path plan;
        private final Path results;
        private final Path output;

        private Fixture(Path manifest, Path plan, Path results, Path output) {
            this.manifest = manifest;
            this.plan = plan;
            this.results = results;
            this.output = output;
        }
    }
}
