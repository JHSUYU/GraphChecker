package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Assume;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicPrimitiveBootstrapProjectorTest {
    @Test
    public void z3SelectsProducerCasesAndBuildsAllTargetBundle()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        assertTrue(result.manifest.toString(), result.manifest.get(
                "complete").getAsBoolean());
        assertEquals("SAT_UPSTREAM_BOOLEAN_MODEL_READY",
                result.manifest.get("status").getAsString());
        JsonObject solverIdentity = result.manifest.getAsJsonObject(
                "solverIdentity");
        assertTrue(solverIdentity.get("version").getAsString().contains(
                "Z3"));
        assertTrue(Paths.get(solverIdentity.get("resolvedPath").getAsString())
                .isAbsolute());
        if (solverIdentity.get("regularFile").getAsBoolean()) {
            assertEquals(64, solverIdentity.get("binarySha256")
                    .getAsString().length());
        }
        assertEquals(sha256(fixture.summaries), result.manifest
                .getAsJsonObject("summaryLedgerArtifact").get("sha256")
                .getAsString());
        assertEquals(sha256(fixture.activations), result.manifest
                .getAsJsonObject("producerActivationLedgerArtifact")
                .get("sha256").getAsString());
        assertEquals(sha256(fixture.target), result.manifest
                .getAsJsonObject("targetActivationPlanArtifact")
                .get("sha256").getAsString());
        assertEquals(sha256(fixture.fatal), result.manifest
                .getAsJsonObject("fatalQueryArtifact").get("sha256")
                .getAsString());
        assertFalse(result.manifest.get(
                "reportableFinalReachCondition").getAsBoolean());
        assertEquals(3, result.activations.size());
        assertEquals("REACHABILITY_SUPPORT", result.activations.get(0)
                .get("activationBundleMemberRole").getAsString());
        assertEquals("REACHABILITY_SUPPORT", result.activations.get(1)
                .get("activationBundleMemberRole").getAsString());
        for (int index = 0; index < 2; index++) {
            JsonObject producer = result.activations.get(index);
            assertEquals("ALL", producer.get(
                    "activationSelectionRequired").getAsString());
            assertTrue(producer.get("receiverRuntimeClass").getAsString()
                    .startsWith("fixture.REGION."));
            assertEquals(1, producer.get(
                    "invocationOrdinalWithinContext").getAsInt());
            assertFalse(producer.get("threadIdSelectionUsed")
                    .getAsBoolean());
            assertTrue(producer.get("concreteReplayOnly").getAsBoolean());
            JsonArray assignments = producer.getAsJsonArray(
                    "modelAssignments");
            assertEquals(1, assignments.size());
            assertEquals("true", assignments.get(0).getAsJsonObject()
                    .get("value").getAsString());
            assertEquals("Z3_PATH_FLIP_MODEL", assignments.get(0)
                    .getAsJsonObject().get("authority").getAsString());
            assertEquals(64, assignments.get(0).getAsJsonObject()
                    .get("targetActionIdentitySha256").getAsString()
                    .length());
        }
        JsonObject target = result.activations.get(2);
        assertEquals("PRIMARY", target.get(
                "activationBundleMemberRole").getAsString());
        assertTrue(target.get("targetReplayRequired").getAsBoolean());
        assertTrue(target.get("observationOnlyReplay").getAsBoolean());
        assertFalse(target.get("concreteReplayOnly").getAsBoolean());
        assertEquals(0, target.getAsJsonArray("modelAssignments").size());
        assertFalse(target.has("forcedBranches"));
        assertEquals(0, target.getAsJsonArray(
                "replayMaterializations").size());
        assertEquals("fixture.ConsumerThread", target.get(
                "receiverRuntimeClass").getAsString());
        assertEquals("rpc-consumer", target.get("threadName")
                .getAsString());
        assertEquals(1, target.get("invocationOrdinalWithinContext")
                .getAsInt());
        assertFalse(target.get("threadIdSelectionUsed").getAsBoolean());
        assertEquals("TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1",
                target.get("rootContextSelectionAuthority").getAsString());
        assertTrue(target.has("replayContract"));
        assertFalse(target.has("directedTargetQuery"));
        assertFalse(target.has("targetBranch"));
        assertFalse(target.has("branchCaptureSelector"));
    }

    @Test
    public void selectedProducerProjectsSupplementalStaticIntIntoSameReplay()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installSupplementalStaticInt(fixture);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject producerA = null;
        for (JsonObject activation : result.activations) {
            if ("REGION.A".equals(activation.get("regionId").getAsString())) {
                producerA = activation;
                break;
            }
        }
        assertTrue("missing REGION.A producer replay", producerA != null);
        JsonArray assignments = producerA.getAsJsonArray(
                "modelAssignments");
        assertEquals(2, assignments.size());
        JsonObject supplemental = assignments.get(1).getAsJsonObject();
        assertEquals("REGION.A.in.1", supplemental.get(
                "inputSymbol").getAsString());
        assertEquals("INT", supplemental.get("valueType").getAsString());
        assertEquals("37", supplemental.get("value").getAsString());
        assertEquals("FIELD_ACCESS", supplemental.getAsJsonObject("target")
                .get("bindingMode").getAsString());
        assertEquals("<fixture.Globals: int t>", supplemental
                .getAsJsonObject("target").get("accessFieldSignature")
                .getAsString());
        assertEquals(3, result.manifest.get(
                "totalProjectedPrimitiveInputCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "supplementalPrimitiveAssignmentCount").getAsInt());
        assertEquals(3, result.manifest.get(
                "upstreamModelAssignmentCount").getAsInt());
        assertEquals(2, result.manifest.get(
                "producerReplayActivationCount").getAsInt());
        JsonArray projected = result.manifest.getAsJsonArray(
                "supplementalPrimitiveAssignments");
        assertEquals(1, projected.size());
        assertEquals("SUPPLEMENTAL_PRIMITIVE", projected.get(0)
                .getAsJsonObject().get("projectionRole").getAsString());
    }

    @Test
    public void selectedProducerProjectsMixedSupplementalScalarInputs()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installSupplementalStaticScalars(fixture);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject producerA = producer(result, "REGION.A");
        JsonArray assignments = producerA.getAsJsonArray(
                "modelAssignments");
        assertEquals(5, assignments.size());
        assertSupplemental(assignments, "REGION.A.in.1", "INT", "37");
        assertSupplemental(assignments, "REGION.A.in.2", "INT",
                "5000000000");
        assertEquals("D", assertSupplemental(assignments,
                "REGION.A.in.3", "REAL", "2.5")
                .get("floatingPointFormat").getAsString());
        assertSupplemental(assignments, "REGION.A.in.4", "STRING",
                "\"needle\"");
        assertEquals(6, result.manifest.get(
                "totalProjectedPrimitiveInputCount").getAsInt());
        assertEquals(4, result.manifest.get(
                "supplementalPrimitiveAssignmentCount").getAsInt());
        assertEquals(4, result.manifest.getAsJsonArray(
                "supplementalPrimitiveAssignments").size());
        assertTrue(result.manifest.get("projectionComplete").getAsBoolean());
    }

    @Test
    public void exactDoubleRootCatalogProjectsIeeeModelForReplay()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installSupplementalStaticScalars(fixture);
        JsonArray roots = new JsonArray();
        roots.add(scalarRoot("REGION.A", "REGION.A.in.3", "td",
                "double", "D", "(_ FloatingPoint 11 53)", 0));
        fixture.reach.addProperty("existentialNonBooleanRootInputCount", 1);
        fixture.reach.add("existentialNonBooleanRootInputs", roots);
        fixture.reach.addProperty(
                "existentialNonBooleanRootInputDiscoveryAuthority",
                "STATIC_JAVA_SCALAR_PORT_TYPE_PLUS_COMPOSER_CANONICAL_"
                        + "TERM_AND_RUNTIME_RELATIONSHIP_DIRECTION_V1");
        refreshBootstrapArtifacts(fixture);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject assignment = assertSupplemental(producer(result,
                "REGION.A").getAsJsonArray("modelAssignments"),
                "REGION.A.in.3", "REAL", "2.5");
        assertEquals("D", assignment.get("floatingPointFormat")
                .getAsString());
        assertEquals(1, result.manifest.get(
                "existentialNonBooleanRootAssignmentCount").getAsInt());
    }

    @Test
    public void booleanAndStringOnlyProducersUseExactRootCatalog()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        // This legacy-looking scalar is intentionally not in the new root
        // catalog and therefore must not leak into REGION.A's replay.
        installSupplementalStaticInt(fixture);
        installScalarOnlyProducerCatalog(fixture, false);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        assertEquals(1, producer(result, "REGION.A").getAsJsonArray(
                "modelAssignments").size());
        JsonArray stringAssignments = producer(result, "REGION.B")
                .getAsJsonArray("modelAssignments");
        assertEquals(1, stringAssignments.size());
        assertSupplemental(stringAssignments, "REGION.B.in.0", "STRING",
                "\"needle\"");
        assertEquals(1, result.manifest.get("rootBooleanInputCount")
                .getAsInt());
        assertEquals(1, result.manifest.get(
                "existentialNonBooleanRootInputCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "existentialNonBooleanRootAssignmentCount").getAsInt());
        JsonArray roots = result.manifest.getAsJsonArray(
                "existentialNonBooleanRootAssignments");
        assertEquals(1, roots.size());
        assertEquals("EXISTENTIAL_NON_BOOLEAN_ROOT", roots.get(0)
                .getAsJsonObject().get("projectionRole").getAsString());
        assertEquals("REGION.B.in.0", roots.get(0).getAsJsonObject()
                .get("inputPort").getAsString());
        assertFalse(result.manifest.getAsJsonArray(
                "supplementalPrimitiveAssignments").toString().contains(
                "REGION.A.in.1"));
    }

    @Test
    public void nullableStringRootProjectsNullWithoutMaterializingContent()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installScalarOnlyProducerCatalog(fixture, false);
        String smt = new String(Files.readAllBytes(fixture.smt),
                StandardCharsets.UTF_8).replace(
                "(assert (= scalar_b_is_null false))",
                "(assert (= scalar_b_is_null true))");
        Files.write(fixture.smt, smt.getBytes(StandardCharsets.UTF_8));
        refreshBootstrapArtifacts(fixture);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject assignment = assertSupplemental(producer(result,
                "REGION.B").getAsJsonArray("modelAssignments"),
                "REGION.B.in.0", "NULL", "null");
        assertEquals("scalar_b_is_null", assignment.get(
                "nullnessSolverTerm").getAsString());
        assertEquals("true", assignment.get(
                "nullnessModelValue").getAsString());
        assertEquals("scalar_b", assignment.get(
                "contentSolverTerm").getAsString());
        assertEquals(1, result.manifest.get(
                "nullableStringAssignmentCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "nullStringAssignmentCount").getAsInt());
    }

    @Test
    public void stringRootWithoutExplicitNullnessCompanionFailsClosed()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installScalarOnlyProducerCatalog(fixture, false);
        JsonObject reach = fixture.reach;
        JsonObject stringRoot = reach.getAsJsonArray(
                "existentialNonBooleanRootInputs").get(0)
                .getAsJsonObject();
        stringRoot.remove("nullnessSolverTerm");
        Files.write(fixture.reachPath, reach.toString().getBytes(
                StandardCharsets.UTF_8));
        refreshBootstrapArtifacts(fixture);

        expectFailure(fixture.arguments(),
                "INVALID_EXISTENTIAL_NON_BOOLEAN_ROOT:REGION.B.in.0");
    }

    @Test
    public void pureScalarCatalogAllowsEmptyBooleanValuation()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installScalarOnlyProducerCatalog(fixture, true);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        assertEquals(0, result.manifest.get("rootBooleanInputCount")
                .getAsInt());
        assertEquals(2, result.manifest.get(
                "existentialNonBooleanRootInputCount").getAsInt());
        assertEquals(2, result.manifest.get(
                "existentialNonBooleanRootAssignmentCount").getAsInt());
        assertEquals(2, result.manifest.get(
                "producerReplayActivationCount").getAsInt());
        assertSupplemental(producer(result, "REGION.A").getAsJsonArray(
                "modelAssignments"), "REGION.A.in.0", "INT", "37");
        assertSupplemental(producer(result, "REGION.B").getAsJsonArray(
                "modelAssignments"), "REGION.B.in.0", "STRING",
                "\"needle\"");
    }

    @Test
    public void supplementalScalarSortTypeMismatchFailsClosed()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installSupplementalStaticScalars(fixture);
        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        for (com.google.gson.JsonElement caseElement : composition
                .getAsJsonArray("caseProjectionCatalog")) {
            for (com.google.gson.JsonElement mappingElement : caseElement
                    .getAsJsonObject().getAsJsonArray(
                            "rawEngineSymbolMappings")) {
                JsonObject mapping = mappingElement.getAsJsonObject();
                if (mapping.has("canonicalPort")
                        && "REGION.A.in.3".equals(mapping.get(
                        "canonicalPort").getAsString())) {
                    mapping.addProperty("sort", "INT");
                    mapping.addProperty("solverSort", "Int");
                }
            }
        }
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));
        refreshBootstrapArtifacts(fixture);

        expectFailure(fixture.arguments(),
                "SUPPLEMENTAL_PRIMITIVE_SORT_TYPE_MISMATCH:REGION.A.in.3");
    }

    @Test
    public void selectedArrayElementBooleanRetainsExactContainerSelector()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject binding = installDynamicLeaf(fixture, true);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject assignment = producerAssignment(result, "REGION.A");
        assertEquals("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING",
                assignment.get("dynamicFieldBindingKind").getAsString());
        assertEquals(binding.get("dynamicBindingId"),
                assignment.get("dynamicBindingId"));
        assertEquals(binding.get("dynamicFieldSymbol"),
                assignment.get("engineSymbol"));
        JsonObject selector = assignment.getAsJsonObject(
                "containerSelector");
        assertEquals("BIND.ARRAY.0", selector.get("bindingId").getAsString());
        assertEquals(0, selector.get("elementIndex").getAsInt());
        assertFalse(selector.has("containerObjectToken"));
        assertFalse(selector.has("elementObjectToken"));
        assertFalse(selector.has("objectTokenAuthority"));
        assertFalse(selector.has("objectTokenScope"));
        assertFalse(selector.has("resolvedFromSelectorAuthority"));
        assertEquals(selector, assignment.getAsJsonObject("dynamicSelector")
                .get("containerSelector"));
        assertEquals("EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1",
                assignment.get("containerReplayRebindingAuthority")
                        .getAsString());
        assertFalse(assignment.get("sourceContainerObjectTokensRetained")
                .getAsBoolean());
        assertEquals(JsonParser.parseString(
                "[\"state\",\"guard\",\"enabled\"]"),
                binding.get("fieldPath"));
        assertEquals(binding.get("fieldPath"),
                assignment.get("materializationPath"));
        assertEquals(binding.get("fieldPath"), assignment
                .getAsJsonObject("target").get("fieldPath"));
        assertEquals("FIELD_ACCESS", assignment.getAsJsonObject("target")
                .get("bindingMode").getAsString());
        assertFalse(assignment.has("expectedEntryKey"));
        assertFalse(assignment.has("dynamicReplayRebindingAuthority"));
    }

    @Test
    public void selectedDirectArrayElementBooleanUsesDeclaredLeafAction()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject binding = installDynamicLeaf(fixture, true, true);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject assignment = producerAssignment(result, "REGION.A");
        assertEquals(JsonParser.parseString("[\"enabled\"]"),
                binding.get("fieldPath"));
        assertEquals(binding.get("fieldPath"),
                assignment.get("materializationPath"));
        assertEquals(binding.get("fieldSignature"), assignment
                .getAsJsonObject("target").get("accessFieldSignature"));
        assertFalse(assignment.getAsJsonObject("containerSelector")
                .has("elementObjectToken"));
    }

    @Test
    public void selectedMapEntryBooleanUsesFreshEntryRebindingWithoutSeedKey()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject binding = installDynamicLeaf(fixture, false);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject assignment = producerAssignment(result, "REGION.A");
        String authority = "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                + "FRESH_ENTRY_REBIND_V1";
        assertEquals("DYNAMIC_MAP_ENTRY_FIELD_BINDING",
                assignment.get("dynamicFieldBindingKind").getAsString());
        assertEquals(binding.get("dynamicBindingId"),
                assignment.get("dynamicBindingId"));
        assertEquals(binding.get("dynamicFieldSymbol"),
                assignment.get("engineSymbol"));
        assertEquals(authority, assignment.get(
                "dynamicReplayRebindingAuthority").getAsString());
        assertFalse(assignment.get("sourceEntrySelectorRetained")
                .getAsBoolean());
        assertEquals(authority, assignment.getAsJsonObject(
                "dynamicSelector").get("replayRebindingAuthority")
                .getAsString());
        assertFalse(assignment.has("entryReadObservationId"));
        assertFalse(assignment.has("keyExpression"));
        assertFalse(assignment.has("keyExpressionAuthority"));
        assertFalse(assignment.has("expectedEntryKey"));
        assertFalse(assignment.has("expectedEntryKeyAuthority"));
        assertFalse(assignment.has("containerSelector"));
        assertFalse(assignment.toString().contains("OBS.ENTRY.SEED"));
        assertFalse(assignment.toString().contains("Y_I_7"));
    }

    @Test
    public void selectedDynamicLeafRejectsSourceSummaryFieldPathMismatch()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installDynamicLeaf(fixture, true);

        JsonObject summary = jsonlRow(fixture.summaries, "summaryId",
                "SUMMARY.A.1");
        JsonObject sourceBinding = summary.getAsJsonArray(
                "dynamicFieldBindings").get(0).getAsJsonObject();
        sourceBinding.add("fieldPath", JsonParser.parseString(
                "[\"state\",\"otherGuard\",\"enabled\"]"));
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        expectFailure(fixture.arguments(),
                "SELECTED_CASE_SOURCE_DYNAMIC_BINDING_MISMATCH");
    }

    @Test
    public void selectedDynamicLeafUsesAttestedCanonicalBridge()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        installDynamicCanonicalBridge(fixture, false);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        JsonObject assignment = producerAssignment(result, "REGION.A");
        assertEquals("sym__port__REGION_A_in_0__int", assignment.get(
                "solverSymbol").getAsString());
        assertEquals("actual_dynamic_a", assignment.get(
                "actualCaseSolverTerm").getAsString());
        JsonObject bridge = assignment.getAsJsonObject(
                "canonicalDynamicRootBridge");
        assertEquals("REGION.A.in.0", bridge.get(
                "canonicalPort").getAsString());
        assertEquals("CASE_UNIQUE_DYNAMIC_BASE_TO_CANONICAL_PORT_"
                        + "GUARDED_EQUALITY_V1",
                bridge.get("canonicalBridgeAuthority").getAsString());
        assertEquals(1, bridge.getAsJsonArray(
                "dynamicBindingIds").size());
    }

    @Test
    public void dynamicStringBridgeAttestsContentAndNullnessTogether()
            throws Exception {
        String port = "REGION.A.in.4";
        String actual = "actual_string";
        String actualNullness = "actual_string_is_null";
        String canonical = "sym__port__REGION_A_in_4__string";
        String canonicalNullness = canonical + "_is_null";
        String guard = "case_a";
        String expression = "(and (= " + actual + " " + canonical
                + ") (= " + actualNullness + " " + canonicalNullness
                + "))";
        String formula = "(=> " + guard + " " + expression + ")";
        String assertionName = "bridge_nullable_string";
        String assertion = "(assert (! " + formula + " :named "
                + assertionName + "))";

        JsonObject mapping = new JsonObject();
        mapping.addProperty("rawEngineSymbol", "dynamic.string.field");
        mapping.addProperty("solverTerm", actual);
        mapping.addProperty("nullnessSolverTerm", actualNullness);
        mapping.addProperty("sort", "STRING");
        mapping.addProperty("solverSort", "String");
        mapping.addProperty("canonicalPort", port);
        mapping.addProperty("canonicalSolverTerm", canonical);
        mapping.addProperty("canonicalNullnessSolverTerm",
                canonicalNullness);
        mapping.addProperty("canonicalBridgeGuard", guard);
        mapping.addProperty("canonicalBridgeExpression", expression);
        mapping.addProperty("canonicalBridgeFormula", formula);
        mapping.addProperty("canonicalBridgeAssertionName", assertionName);
        mapping.addProperty("canonicalBridgeAssertion", assertion);
        mapping.addProperty("canonicalBridgeAssertionSha256",
                sha256(assertion));
        mapping.addProperty("canonicalBridgeAuthority",
                "CASE_UNIQUE_DYNAMIC_BASE_TO_CANONICAL_PORT_"
                        + "GUARDED_EQUALITY_V1");
        mapping.addProperty("nullableStringEncodingAuthority",
                "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
        mapping.addProperty("termKind", "SCOPED_DYNAMIC_FIELD");
        JsonArray ids = new JsonArray();
        ids.add("BIND.STRING");
        mapping.add("dynamicBindingIds", ids);

        JsonObject binding = new JsonObject();
        binding.addProperty("dynamicBindingId", "BIND.STRING");
        binding.addProperty("baseInputSymbol", port);
        binding.addProperty("solverTerm", actual);
        binding.addProperty("nullnessSolverTerm", actualNullness);
        binding.addProperty("fieldExpressionRawEngineSymbol",
                "dynamic.string.field");
        binding.addProperty("complete", true);
        binding.addProperty("observationMatched", true);
        binding.addProperty("termBindingAuthority",
                "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM");
        binding.addProperty("nullableStringEncodingAuthority",
                "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
        JsonObject pathCase = new JsonObject();
        pathCase.addProperty("regionId", "REGION.A");
        pathCase.addProperty("selectorSolverSymbol", guard);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        pathCase.add("dynamicFieldBindings", bindings);

        assertTrue(ConcolicPrimitiveBootstrapProjector
                .exactDynamicCanonicalBridge(pathCase, mapping, port,
                        canonical, assertion + "\n"));
        mapping.remove("canonicalNullnessSolverTerm");
        assertFalse(ConcolicPrimitiveBootstrapProjector
                .exactDynamicCanonicalBridge(pathCase, mapping, port,
                        canonical, assertion + "\n"));
    }

    @Test
    public void duplicatedCanonicalBridgeAssertionFailsClosed()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        String assertion = installDynamicCanonicalBridge(fixture, false);
        String smt = new String(Files.readAllBytes(fixture.smt),
                StandardCharsets.UTF_8).replace("(check-sat)\n",
                "#|\n" + assertion + "\n|#\n(check-sat)\n");
        Files.write(fixture.smt, smt.getBytes(StandardCharsets.UTF_8));
        refreshBootstrapArtifacts(fixture);

        expectFailure(fixture.arguments(),
                "CASE_DYNAMIC_CANONICAL_BRIDGE_NOT_EXACT");
    }

    @Test
    public void finalReportCannotBeReusedAsBootstrapAuthority()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject report = fixture.reach.deepCopy();
        report.addProperty("extractionMode", "FINAL_REPORT");
        report.addProperty("replayBootstrapOnly", false);
        report.addProperty("reportableFinalReachCondition", true);
        Files.write(fixture.reachPath, report.toString().getBytes(
                StandardCharsets.UTF_8));

        try {
            ConcolicPrimitiveBootstrapProjector.project(fixture.arguments());
            fail("final reach report must not authorize bootstrap replay");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "BOOLEAN_REPORT_IS_NOT_AN_EXACT_BOOTSTRAP_MODEL"));
        }
    }

    @Test
    public void tamperedDefinitionIdentityCannotJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        activation.getAsJsonArray("materializations").get(0)
                .getAsJsonObject().getAsJsonArray("definitionSites").get(0)
                .getAsJsonObject().addProperty("local", "$z9");
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "LOCAL_DEFINITION_ACTION_SITE_MISMATCH");
    }

    @Test
    public void resolvedCallReturnDefinitionCanJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        assertTrue(result.manifest.toString(), result.manifest.get(
                "complete").getAsBoolean());
    }

    @Test
    public void callReturnWithoutSourceBindingModeCannotJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        action.remove("sourceBindingMode");
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "LOCAL_DEFINITION_ACTION_IDENTITY_INCOMPLETE");
    }

    @Test
    public void deferredCallReturnCannotJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        action.addProperty("deferredResolution", true);
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "ROOT_INPUT_HAS_NO_REAL_MATERIALIZATION");
    }

    @Test
    public void mislabeledLocalCellCannotJoinAsCallReturnDefinition()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        action.addProperty("cell", "<fixture.REGION.A: boolean input()>"
                + "::$z0");
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "LOCAL_DEFINITION_ACTION_IDENTITY_INCOMPLETE");
    }

    @Test
    public void mainWritesOneCompactJsonObjectPerActivationLine()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();

        ConcolicPrimitiveBootstrapProjector.main(
                fixture.commandLine(Paths.get("z3")));

        List<String> lines = Files.readAllLines(fixture.output,
                StandardCharsets.UTF_8);
        assertEquals(3, lines.size());
        for (String line : lines) {
            assertTrue(JsonParser.parseString(line).isJsonObject());
        }
    }

    @Test
    public void summaryAdmissionMustOwnSelectedMaterialization()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject summary = jsonlRow(fixture.summaries, "summaryId",
                "SUMMARY.A.1");
        summary.getAsJsonObject("inputMaterializationAdmission")
                .add("observedSymbolizedInputs", new JsonArray());
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        expectFailure(fixture.arguments(),
                "SELECTED_SUMMARY_INPUT_ADMISSION_NOT_EXACT");

        fixture = fixture();
        summary = jsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1");
        JsonObject requirement = new JsonObject();
        requirement.addProperty("inputPort", "REGION.A.in.0");
        JsonArray requirements = new JsonArray();
        requirements.add(requirement);
        summary.getAsJsonObject("inputMaterializationAdmission")
                .add("unforcedEnvironmentValidationRequirements",
                        requirements);
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        expectFailure(fixture.arguments(),
                "SELECTED_SUMMARY_INPUT_ADMISSION_NOT_EXACT");

        fixture = fixture();
        summary = jsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1");
        JsonArray fallbacks = new JsonArray();
        fallbacks.add("REGION.A.in.0");
        summary.getAsJsonObject("inputMaterializationAdmission")
                .add("admittedConcreteFallbackInputs", fallbacks);
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        expectFailure(fixture.arguments(),
                "SELECTED_SUMMARY_INPUT_ADMISSION_NOT_EXACT");
    }

    @Test
    public void selectedCaseMustBelongToIncludedCompositionInput()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        composition.getAsJsonArray("caseProjectionCatalog").get(1)
                .getAsJsonObject().addProperty("compositionInputSummaryId",
                "SUMMARY.A.NOT_INCLUDED");
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));
        JsonObject report = fixture.reach.deepCopy();
        report.add("compositionManifestArtifact",
                artifact(fixture.composition));
        Files.write(fixture.reachPath, report.toString().getBytes(
                StandardCharsets.UTF_8));

        expectFailure(fixture.arguments(),
                "SELECTED_SOURCE_SUMMARY_NOT_IN_COMPOSITION_INPUT");
    }

    @Test
    public void targetActivationMustMatchFatalBranchIdentity()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject target = jsonlRow(fixture.target, "activationId", "ACT.T");
        target.add("branchCaptureSelector", BranchCaptureSelector.of(
                "<fixture.T: void run()>#u4", 2, true).toJson());
        replaceJsonlRow(fixture.target, "activationId", "ACT.T", target);

        expectFailure(fixture.arguments(),
                "TARGET_ACTIVATION_EXACT_BINDING_MISMATCH");
    }

    @Test
    public void reachSolverLiteralCannotInjectSmt()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject report = fixture.reach.deepCopy();
        report.getAsJsonArray("truthTable").get(0).getAsJsonObject()
                .getAsJsonArray("assignments").get(0).getAsJsonObject()
                .addProperty("solverLiteral",
                        "(= xa 1)) (assert false) (assert (= xa 1)");
        Files.write(fixture.reachPath, report.toString().getBytes(
                StandardCharsets.UTF_8));

        expectFailure(fixture.arguments(),
                "INVALID_BOOTSTRAP_VALUATION_ASSIGNMENT");
    }

    @Test
    public void nonzeroSolverExitAlwaysFailsProjection() throws Exception {
        Fixture fixture = fixture();
        Path solver = fixture.output.getParent().resolve("fake-z3");
        Files.write(solver, ("#!/bin/sh\n"
                + "if [ \"$1\" = \"-version\" ]; then\n"
                + "  echo 'Z3 version fixture'\n"
                + "  exit 0\n"
                + "fi\n"
                + "exit 7\n").getBytes(StandardCharsets.UTF_8));
        assertTrue(solver.toFile().setExecutable(true));

        expectFailure(fixture.arguments(solver),
                "Bootstrap model projection solver failed");
    }

    @Test
    public void solverVersionMustAttestZ3Identity() throws Exception {
        Fixture fixture = fixture();
        Path solver = fixture.output.getParent().resolve("not-z3");
        Files.write(solver, ("#!/bin/sh\n"
                + "echo 'generic solver version fixture'\n"
                + "exit 0\n").getBytes(StandardCharsets.UTF_8));
        assertTrue(solver.toFile().setExecutable(true));

        expectFailure(fixture.arguments(solver),
                "Solver identity is not Z3");
    }

    private static JsonObject producerAssignment(
            ConcolicPrimitiveBootstrapProjector.Result result,
            String region) {
        JsonArray assignments = producer(result, region).getAsJsonArray(
                "modelAssignments");
        assertEquals(1, assignments.size());
        return assignments.get(0).getAsJsonObject();
    }

    private static JsonObject producer(
            ConcolicPrimitiveBootstrapProjector.Result result,
            String region) {
        for (JsonObject activation : result.activations) {
            if (region.equals(activation.get("regionId").getAsString())) {
                return activation;
            }
        }
        throw new AssertionError("missing producer activation " + region);
    }

    private static JsonObject assertSupplemental(JsonArray assignments,
                                                 String port,
                                                 String valueType,
                                                 String value) {
        for (com.google.gson.JsonElement element : assignments) {
            JsonObject assignment = element.getAsJsonObject();
            if (!port.equals(assignment.get("inputSymbol").getAsString())) {
                continue;
            }
            assertEquals(valueType, assignment.get("valueType")
                    .getAsString());
            assertEquals(value, assignment.get("value").getAsString());
            assertEquals("FIELD_ACCESS", assignment.getAsJsonObject(
                    "target").get("bindingMode").getAsString());
            return assignment;
        }
        fail("missing supplemental assignment " + port);
        return null;
    }

    private static void installSupplementalStaticInt(Fixture fixture)
            throws Exception {
        String smt = new String(Files.readAllBytes(fixture.smt),
                StandardCharsets.UTF_8).replace("(check-sat)\n",
                "(declare-const ti Int)\n"
                        + "(assert (= ti 37))\n(check-sat)\n");
        Files.write(fixture.smt, smt.getBytes(StandardCharsets.UTF_8));

        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        for (com.google.gson.JsonElement element : composition
                .getAsJsonArray("caseProjectionCatalog")) {
            JsonObject pathCase = element.getAsJsonObject();
            if (!"CASE.A.1".equals(pathCase.get("caseId").getAsString())) {
                continue;
            }
            JsonObject mapping = new JsonObject();
            mapping.addProperty("rawEngineSymbol",
                    "M_I_field_REGION.A.in.1_java/lang/Integer");
            mapping.addProperty("solverTerm", "ti");
            mapping.addProperty("sort", "INT");
            mapping.addProperty("solverSort", "Int");
            mapping.addProperty("termKind", "CANONICAL_PORT_TERM");
            mapping.addProperty("canonicalPort", "REGION.A.in.1");
            mapping.add("dynamicBindingIds", new JsonArray());
            mapping.addProperty("authority", "EMITTER_ACTUAL_TERM");
            JsonArray mappings = pathCase.getAsJsonArray(
                    "rawEngineSymbolMappings");
            mappings.add(mapping);
            pathCase.addProperty("rawEngineSymbolMappingCount",
                    mappings.size());
        }
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonObject summary = jsonlRow(fixture.summaries, "summaryId",
                "SUMMARY.A.1");
        JsonObject admission = summary.getAsJsonObject(
                "inputMaterializationAdmission");
        for (String member : new String[]{"globalSliceInputs",
                "requiredSliceInputs", "observedSymbolizedInputs"}) {
            admission.getAsJsonArray(member).add("REGION.A.in.1");
        }
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.A.in.1");
        action.addProperty("cell", "<fixture.Globals: int t>");
        action.addProperty("sourceKind", "SHARED_HEAP");
        action.addProperty("projection", "value");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("observed", true);
        action.addProperty("javaType", "int");
        action.addProperty("field", "<fixture.Globals: int t>");
        action.addProperty("accessKind", "FIELD_READ");
        action.addProperty("accessMethod",
                "<fixture.REGION.A: int compute(java.lang.Boolean)>");
        action.addProperty("accessUnitIndex", 7);
        action.addProperty("accessSiteId",
                "<fixture.REGION.A: int compute(java.lang.Boolean)>#u7");
        action.addProperty("accessSiteAuthority",
                "RUNTIME_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1");
        action.addProperty("accessOwnerClass", "fixture.Globals");
        action.addProperty("accessField", "t");
        action.addProperty("accessFieldType", "int");
        action.addProperty("accessFieldSignature",
                "<fixture.Globals: int t>");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("t");
        action.add("fieldPath", fieldPath);
        activation.getAsJsonArray("materializations").add(action);
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        refreshBootstrapArtifacts(fixture);
    }

    private static void installSupplementalStaticScalars(Fixture fixture)
            throws Exception {
        String declarations = "(declare-const ti Int)\n"
                + "(declare-const tl Int)\n"
                + "(declare-const td (_ FloatingPoint 11 53))\n"
                + "(declare-const ts String)\n"
                + "(declare-const ts_is_null Bool)\n"
                + "(assert (= ti 37))\n"
                + "(assert (= tl 5000000000))\n"
                + "(assert (fp.eq td ((_ to_fp 11 53)"
                + " #x4004000000000000)))\n"
                + "(assert (= ts \"needle\"))\n"
                + "(assert (= ts_is_null false))\n";
        String smt = new String(Files.readAllBytes(fixture.smt),
                StandardCharsets.UTF_8).replace("(check-sat)\n",
                declarations + "(check-sat)\n");
        Files.write(fixture.smt, smt.getBytes(StandardCharsets.UTF_8));

        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        for (com.google.gson.JsonElement element : composition
                .getAsJsonArray("caseProjectionCatalog")) {
            JsonObject pathCase = element.getAsJsonObject();
            if (!"CASE.A.1".equals(pathCase.get("caseId").getAsString())) {
                continue;
            }
            JsonArray mappings = pathCase.getAsJsonArray(
                    "rawEngineSymbolMappings");
            mappings.add(scalarMapping("REGION.A.in.1", "ti", "INT",
                    "Int", "M_I_field_REGION.A.in.1_java/lang/Integer"));
            mappings.add(scalarMapping("REGION.A.in.2", "tl", "INT",
                    "Int", "M_J_field_REGION.A.in.2_java/lang/Long"));
            mappings.add(scalarMapping("REGION.A.in.3", "td", "FLOAT64",
                    "(_ FloatingPoint 11 53)",
                    "M_D_field_REGION.A.in.3_java/lang/Double"));
            mappings.add(scalarMapping("REGION.A.in.4", "ts", "STRING",
                    "String",
                    "M_L'String'_field_REGION.A.in.4_java/lang/String"));
            pathCase.addProperty("rawEngineSymbolMappingCount",
                    mappings.size());
        }
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonObject summary = jsonlRow(fixture.summaries, "summaryId",
                "SUMMARY.A.1");
        JsonObject admission = summary.getAsJsonObject(
                "inputMaterializationAdmission");
        for (int index = 1; index <= 4; index++) {
            String port = "REGION.A.in." + index;
            for (String member : new String[]{"globalSliceInputs",
                    "requiredSliceInputs", "observedSymbolizedInputs"}) {
                admission.getAsJsonArray(member).add(port);
            }
        }
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        activation.getAsJsonArray("materializations").add(
                staticScalarAction("REGION.A.in.1", "int", "i", 7));
        activation.getAsJsonArray("materializations").add(
                staticScalarAction("REGION.A.in.2", "long", "l", 8));
        activation.getAsJsonArray("materializations").add(
                staticScalarAction("REGION.A.in.3", "double", "d", 9));
        activation.getAsJsonArray("materializations").add(
                staticScalarAction("REGION.A.in.4", "java.lang.String",
                        "s", 10));
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);
        refreshBootstrapArtifacts(fixture);
    }

    private static void installScalarOnlyProducerCatalog(Fixture fixture,
                                                         boolean pureScalar)
            throws Exception {
        String declarations = "(declare-const scalar_b String)\n"
                + "(declare-const scalar_b_is_null Bool)\n"
                + "(assert (= scalar_b \"needle\"))\n"
                + "(assert (= scalar_b_is_null false))\n";
        if (pureScalar) {
            declarations += "(declare-const scalar_a Int)\n"
                    + "(assert (= scalar_a 37))\n";
        }
        String smt = new String(Files.readAllBytes(fixture.smt),
                StandardCharsets.UTF_8).replace("(check-sat)\n",
                declarations + "(check-sat)\n");
        Files.write(fixture.smt, smt.getBytes(StandardCharsets.UTF_8));

        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        for (com.google.gson.JsonElement element : composition
                .getAsJsonArray("caseProjectionCatalog")) {
            JsonObject pathCase = element.getAsJsonObject();
            String region = pathCase.get("regionId").getAsString();
            if ("REGION.B".equals(region)) {
                JsonArray mappings = new JsonArray();
                mappings.add(scalarMapping("REGION.B.in.0", "scalar_b",
                        "STRING", "String",
                        "M_L'String'_field_REGION.B.in.0_java/lang/String"));
                pathCase.add("rawEngineSymbolMappings", mappings);
                pathCase.addProperty("rawEngineSymbolMappingCount", 1);
            } else if (pureScalar && "REGION.A".equals(region)) {
                JsonArray mappings = new JsonArray();
                mappings.add(scalarMapping("REGION.A.in.0", "scalar_a",
                        "INT", "Int",
                        "M_I_field_REGION.A.in.0_java/lang/Integer"));
                pathCase.add("rawEngineSymbolMappings", mappings);
                pathCase.addProperty("rawEngineSymbolMappingCount", 1);
            }
        }
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonArray booleanRoots = new JsonArray();
        JsonArray valuationAssignments = new JsonArray();
        if (!pureScalar) {
            booleanRoots.add(root("REGION.A", "REGION.A.in.0", "xa"));
            valuationAssignments.add(valuation("REGION.A.in.0", "xa",
                    true));
        }
        fixture.reach.add("rootBooleanInputs", booleanRoots);
        JsonObject valuation = fixture.reach.getAsJsonArray("truthTable")
                .get(0).getAsJsonObject();
        valuation.addProperty("ordinal", pureScalar ? 0 : 1);
        valuation.addProperty("valuationKey", pureScalar ? "" : "1");
        valuation.add("assignments", valuationAssignments);

        JsonArray scalarRoots = new JsonArray();
        int ordinal = 0;
        if (pureScalar) {
            scalarRoots.add(scalarRoot("REGION.A", "REGION.A.in.0",
                    "scalar_a", "int", "I", "Int", ordinal++));
        }
        scalarRoots.add(scalarRoot("REGION.B", "REGION.B.in.0",
                "scalar_b", "java.lang.String", "Ljava/lang/String;",
                "String", ordinal));
        fixture.reach.addProperty("existentialNonBooleanRootInputCount",
                scalarRoots.size());
        fixture.reach.add("existentialNonBooleanRootInputs", scalarRoots);
        fixture.reach.addProperty(
                "existentialNonBooleanRootInputDiscoveryAuthority",
                "STATIC_JAVA_SCALAR_PORT_TYPE_PLUS_COMPOSER_CANONICAL_"
                        + "TERM_AND_RUNTIME_RELATIONSHIP_DIRECTION_V1");

        JsonObject bActivation = jsonlRow(fixture.activations,
                "activationId", "ACT.B.1");
        JsonArray bActions = new JsonArray();
        bActions.add(staticScalarAction("REGION.B", "REGION.B.in.0",
                "java.lang.String", "text", 7));
        bActivation.add("materializations", bActions);
        replaceJsonlRow(fixture.activations, "activationId", "ACT.B.1",
                bActivation);
        if (pureScalar) {
            JsonObject aActivation = jsonlRow(fixture.activations,
                    "activationId", "ACT.A.1");
            JsonArray aActions = new JsonArray();
            aActions.add(staticScalarAction("REGION.A", "REGION.A.in.0",
                    "int", "number", 7));
            aActivation.add("materializations", aActions);
            replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                    aActivation);
        }
        refreshBootstrapArtifacts(fixture);
    }

    private static JsonObject scalarRoot(String region, String port,
                                         String solver, String javaType,
                                         String descriptor, String sort,
                                         int ordinal) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        result.addProperty("regionId", region);
        result.addProperty("cell", "<fixture.Globals: " + javaType
                + " root>");
        result.addProperty("javaType", javaType);
        result.addProperty("javaTypeDescriptor", descriptor);
        result.addProperty("solverTerm", solver);
        result.addProperty("solverSort", sort);
        if ("String".equals(sort)) {
            result.addProperty("nullnessSolverTerm", solver + "_is_null");
            result.addProperty("nullnessSolverSort", "Bool");
            result.addProperty("nullableStringEncodingAuthority",
                    "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
        }
        result.addProperty("root", true);
        result.addProperty("upstreamSupplied", false);
        result.addProperty("projectionRole",
                "EXISTENTIALLY_QUANTIFIED_IN_BOOLEAN_PROJECTION");
        JsonObject evidence = new JsonObject();
        evidence.addProperty("regionId", region);
        evidence.addProperty("caseId", "CASE.EVIDENCE");
        evidence.addProperty("solverTerm", solver);
        JsonArray evidenceRows = new JsonArray();
        evidenceRows.add(evidence);
        result.add("caseProjectionEvidence", evidenceRows);
        result.addProperty("authority",
                "STATIC_JAVA_SCALAR_PORT_PLUS_FINAL_SMT_CANONICAL_"
                        + "BINDING_AND_RUNTIME_RELATIONSHIP_DIRECTION_V1");
        result.addProperty("ordinal", ordinal);
        return result;
    }

    private static JsonObject scalarMapping(String port, String solver,
                                            String sort, String solverSort,
                                            String engine) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("rawEngineSymbol", engine);
        mapping.addProperty("solverTerm", solver);
        mapping.addProperty("sort", sort);
        mapping.addProperty("solverSort", solverSort);
        mapping.addProperty("termKind", "CANONICAL_PORT_TERM");
        mapping.addProperty("canonicalPort", port);
        if ("STRING".equals(sort)) {
            mapping.addProperty("nullnessSolverTerm", solver + "_is_null");
            mapping.addProperty("nullableStringEncodingAuthority",
                    "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
        }
        mapping.add("dynamicBindingIds", new JsonArray());
        mapping.addProperty("authority", "EMITTER_ACTUAL_TERM");
        return mapping;
    }

    private static JsonObject staticScalarAction(String port,
                                                 String javaType,
                                                 String fieldName,
                                                 int unitIndex) {
        return staticScalarAction("REGION.A", port, javaType, fieldName,
                unitIndex);
    }

    private static JsonObject staticScalarAction(String region, String port,
                                                 String javaType,
                                                 String fieldName,
                                                 int unitIndex) {
        String signature = "<fixture.Globals: " + javaType + " "
                + fieldName + ">";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("cell", signature);
        action.addProperty("sourceKind", "SHARED_HEAP");
        action.addProperty("projection", "value");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("observed", true);
        action.addProperty("javaType", javaType);
        action.addProperty("field", signature);
        action.addProperty("accessKind", "FIELD_READ");
        action.addProperty("accessMethod",
                "<fixture." + region + ": int compute()>");
        action.addProperty("accessUnitIndex", unitIndex);
        action.addProperty("accessSiteId",
                "<fixture." + region + ": int compute()>#u" + unitIndex);
        action.addProperty("accessSiteAuthority",
                "RUNTIME_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1");
        action.addProperty("accessOwnerClass", "fixture.Globals");
        action.addProperty("accessField", fieldName);
        action.addProperty("accessFieldType", javaType);
        action.addProperty("accessFieldSignature", signature);
        action.addProperty("bindingMode", "FIELD_ACCESS");
        JsonArray path = new JsonArray();
        path.add(fieldName);
        action.add("fieldPath", path);
        return action;
    }

    private static JsonObject installDynamicLeaf(Fixture fixture,
                                                 boolean container)
            throws Exception {
        return installDynamicLeaf(fixture, container, false);
    }

    private static JsonObject installDynamicLeaf(Fixture fixture,
                                                 boolean container,
                                                 boolean directContainer)
            throws Exception {
        String region = "REGION.A";
        String port = region + ".in.0";
        String site = "<fixture.REGION.A: boolean compute()>#u6";
        String dynamic = port + ".field."
                + sha256(site).substring(0, 12) + ".occ.1";
        JsonObject binding = dynamicLeafBinding(container, directContainer,
                port, dynamic, site);

        JsonObject summary = jsonlRow(fixture.summaries, "summaryId",
                "SUMMARY.A.1");
        JsonArray summaryBindings = new JsonArray();
        summaryBindings.add(binding.deepCopy());
        summary.add("dynamicFieldBindings", summaryBindings);
        JsonArray observed = new JsonArray();
        observed.add(dynamic);
        summary.getAsJsonObject("inputMaterializationAdmission").add(
                "observedSymbolizedInputs", observed);
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject fieldAction = dynamicFieldAction(port, binding,
                container);
        JsonArray actions = new JsonArray();
        if (container) {
            JsonObject containerAction = new JsonObject();
            containerAction.addProperty("symbol", "REGION.A.in.array");
            containerAction.addProperty("cell",
                    "<fixture.ArrayInput: fixture.Flag[] flags>");
            containerAction.addProperty("bindingMode",
                    "CONTAINER_INPUT_OBSERVATION");
            containerAction.addProperty("location", "HEAP_OBJECT_FIELD");
            containerAction.addProperty("arrayFieldObservationOnly", true);
            containerAction.addProperty("modelControllable", false);
            actions.add(containerAction);
            JsonArray declared = new JsonArray();
            declared.add(containerAction.deepCopy());
            declared.add(fieldAction);
            activation.add("symbolize", declared);
        } else {
            actions.add(fieldAction);
        }
        activation.add("materializations", actions);
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        JsonObject selectedCase = null;
        for (com.google.gson.JsonElement element : composition
                .getAsJsonArray("caseProjectionCatalog")) {
            JsonObject candidate = element.getAsJsonObject();
            if ("CASE.A.1".equals(candidate.get("caseId").getAsString())) {
                selectedCase = candidate;
                break;
            }
        }
        if (selectedCase == null) {
            throw new AssertionError("missing selected CASE.A.1");
        }
        JsonObject mapping = selectedCase.getAsJsonArray(
                "rawEngineSymbolMappings").get(0).getAsJsonObject();
        mapping.addProperty("rawEngineSymbol", dynamic);
        mapping.addProperty("termKind", "SCOPED_DYNAMIC_FIELD");
        JsonArray mappingBindingIds = new JsonArray();
        mappingBindingIds.add(binding.get("dynamicBindingId").getAsString());
        mapping.add("dynamicBindingIds", mappingBindingIds);
        JsonObject selectedBinding = binding.deepCopy();
        selectedBinding.add("runtimeBinding", binding.deepCopy());
        selectedBinding.addProperty("fieldExpressionRawEngineSymbol",
                dynamic);
        selectedBinding.addProperty("fieldJavaType", "Z");
        selectedBinding.addProperty("observationMatched", true);
        selectedBinding.addProperty("solverTerm", "xa");
        selectedBinding.addProperty("sort", "INT");
        selectedBinding.addProperty("solverSort", "Int");
        selectedBinding.addProperty("termBindingAuthority",
                "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "Z");
        expression.addProperty("_exp", dynamic);
        selectedBinding.add("fieldExpression", expression);
        JsonArray selectedBindings = new JsonArray();
        selectedBindings.add(selectedBinding);
        selectedCase.add("dynamicFieldBindings", selectedBindings);
        selectedCase.addProperty("dynamicFieldBindingCount", 1);
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonObject reach = fixture.reach.deepCopy();
        reach.add("compositionManifestArtifact",
                artifact(fixture.composition));
        Files.write(fixture.reachPath, reach.toString().getBytes(
                StandardCharsets.UTF_8));
        return binding;
    }

    private static String installDynamicCanonicalBridge(
            Fixture fixture, boolean container) throws Exception {
        installDynamicLeaf(fixture, container);
        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        JsonObject selectedCase = null;
        for (com.google.gson.JsonElement element : composition
                .getAsJsonArray("caseProjectionCatalog")) {
            JsonObject candidate = element.getAsJsonObject();
            if ("CASE.A.1".equals(candidate.get("caseId").getAsString())) {
                selectedCase = candidate;
                break;
            }
        }
        if (selectedCase == null) {
            throw new AssertionError("missing selected CASE.A.1");
        }
        JsonObject mapping = selectedCase.getAsJsonArray(
                "rawEngineSymbolMappings").get(0).getAsJsonObject();
        JsonObject binding = selectedCase.getAsJsonArray(
                "dynamicFieldBindings").get(0).getAsJsonObject();
        String actual = "actual_dynamic_a";
        String canonical = "sym__port__REGION_A_in_0__int";
        String guard = "ca1";
        String expression = "(= " + actual + " " + canonical + ")";
        String formula = "(=> " + guard + " " + expression + ")";
        String assertionName = "bridge_region_a_case_1";
        String assertion = "(assert (! " + formula + " :named "
                + assertionName + "))";
        mapping.addProperty("solverTerm", actual);
        mapping.addProperty("sort", "INT");
        mapping.addProperty("solverSort", "Int");
        mapping.addProperty("canonicalSolverTerm", canonical);
        mapping.addProperty("canonicalBridgeGuard", guard);
        mapping.addProperty("canonicalBridgeExpression", expression);
        mapping.addProperty("canonicalBridgeFormula", formula);
        mapping.addProperty("canonicalBridgeAssertionName", assertionName);
        mapping.addProperty("canonicalBridgeAssertion", assertion);
        mapping.addProperty("canonicalBridgeAssertionSha256",
                sha256(assertion));
        mapping.addProperty("canonicalBridgeAuthority",
                "CASE_UNIQUE_DYNAMIC_BASE_TO_CANONICAL_PORT_"
                        + "GUARDED_EQUALITY_V1");
        binding.addProperty("solverTerm", actual);
        JsonObject root = fixture.reach.getAsJsonArray(
                "rootBooleanInputs").get(0).getAsJsonObject();
        root.addProperty("solverTerm", canonical);
        JsonObject valuation = fixture.reach.getAsJsonArray("truthTable")
                .get(0).getAsJsonObject().getAsJsonArray("assignments")
                .get(0).getAsJsonObject();
        valuation.addProperty("solverTerm", canonical);
        valuation.addProperty("solverLiteral", "(= " + canonical + " 1)");
        String smt = new String(Files.readAllBytes(fixture.smt),
                StandardCharsets.UTF_8).replace("(check-sat)\n",
                "(declare-const " + actual + " Int)\n"
                        + "(declare-const " + canonical + " Int)\n"
                        + assertion
                        + "\n(check-sat)\n");
        Files.write(fixture.smt, smt.getBytes(StandardCharsets.UTF_8));
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));
        refreshBootstrapArtifacts(fixture);
        return assertion;
    }

    private static void refreshBootstrapArtifacts(Fixture fixture)
            throws Exception {
        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        composition.add("composedSmtArtifact", artifact(fixture.smt));
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));
        JsonObject reach = fixture.reach.deepCopy();
        reach.addProperty("composedSmtSha256", sha256(fixture.smt));
        reach.add("composedSmtArtifact", artifact(fixture.smt));
        reach.add("compositionManifestArtifact",
                artifact(fixture.composition));
        Files.write(fixture.reachPath, reach.toString().getBytes(
                StandardCharsets.UTF_8));
    }

    private static JsonObject dynamicFieldAction(String port,
                                                 JsonObject binding,
                                                 boolean container) {
        String field = binding.get("fieldSignature").getAsString();
        JsonArray fieldPath = binding.getAsJsonArray("fieldPath");
        boolean directContainer = container && fieldPath.size() == 1;
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("cell", directContainer ? field : container
                ? "<fixture.State: fixture.Guard state>"
                + "#field:guard#field:enabled" : field);
        action.addProperty("field", field);
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("accessOwnerClass", directContainer
                ? "fixture.BooleanLeaf" : container
                ? "fixture.State" : "fixture.Flag");
        action.addProperty("accessField", fieldPath.get(0).getAsString());
        action.addProperty("accessFieldSignature", directContainer
                ? field : container
                ? "<fixture.State: fixture.Guard state>" : field);
        action.addProperty("fieldPathAuthority",
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        action.addProperty("leafOwnerClass", container
                ? "fixture.BooleanLeaf" : "fixture.Flag");
        action.addProperty("leafField", fieldPath.get(
                fieldPath.size() - 1).getAsString());
        action.addProperty("leafFieldSignature", field);
        action.add("fieldPath", fieldPath.deepCopy());
        return action;
    }

    private static JsonObject dynamicLeafBinding(boolean container,
                                                 boolean directContainer,
                                                 String base,
                                                 String dynamic,
                                                 String site) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", container ? 2 : 1);
        binding.addProperty("kind", container
                ? "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING"
                : "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", 1);
        binding.addProperty("fieldSignature", container
                ? "<fixture.BooleanLeaf: boolean enabled>"
                : "<fixture.Flag: boolean enabled>");
        JsonArray path = new JsonArray();
        if (container && !directContainer) {
            path.add("state");
            path.add("guard");
        }
        path.add("enabled");
        binding.add("fieldPath", path);
        binding.addProperty("leafOwnerObjectToken",
                directContainer ? 202L : 203L);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.A.1");
        if (container) {
            binding.addProperty("authority",
                    "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                            + "AND_STABLE_FIELD_SITE_OCCURRENCE");
            binding.addProperty("containerBindingId", "BIND.ARRAY.0");
            binding.addProperty("containerInputPort", "REGION.A.in.array");
            binding.addProperty("containerInputCell",
                    "<fixture.ArrayInput: fixture.Flag[] flags>");
            binding.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
            binding.addProperty("elementIndex", 0);
            binding.addProperty("elementOccurrence", 1);
            binding.addProperty("declaredFieldOwnerClass",
                    "fixture.BooleanLeaf");
            binding.addProperty("declaredFieldType", "boolean");
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "ARRAY_INDEX");
            selector.addProperty("bindingId", "BIND.ARRAY.0");
            selector.addProperty("containerInputPort",
                    "REGION.A.in.array");
            selector.addProperty("containerInputCell",
                    "<fixture.ArrayInput: fixture.Flag[] flags>");
            selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
            selector.addProperty("resolvedFromSelectorAuthority",
                    "EXACT_ARRAY_INDEX");
            selector.addProperty("elementIndex", 0);
            selector.addProperty("elementOccurrence", 1);
            selector.addProperty("declaredFieldOwnerClass",
                    "fixture.BooleanLeaf");
            selector.addProperty("declaredFieldType", "boolean");
            selector.addProperty("containerObjectToken", 201L);
            selector.addProperty("elementObjectToken", 202L);
            selector.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            selector.addProperty("objectTokenScope", "ACT.A.1");
            selector.addProperty("authority",
                    "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                            + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
            selector.addProperty("complete", true);
            binding.add("containerSelector", selector);
        } else {
            binding.addProperty("authority",
                    "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                            + "FIELD_SITE_OCCURRENCE");
            binding.addProperty("entryReadObservationId", "OBS.ENTRY.SEED");
            JsonObject key = new JsonObject();
            key.addProperty("_type", "ConstExpr");
            key.addProperty("_java_type", "java/lang/Integer");
            key.addProperty("_exp", "Y_I_7");
            binding.add("keyExpression", key);
            binding.addProperty("keyExpressionAuthority",
                    "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        }
        binding.addProperty("complete", true);
        return binding;
    }

    private static void expectFailure(
            ConcolicPrimitiveBootstrapProjector.Arguments arguments,
            String expected) throws Exception {
        try {
            ConcolicPrimitiveBootstrapProjector.project(arguments);
            fail("expected projection failure containing " + expected);
        } catch (java.io.IOException failure) {
            assertTrue(failure.getMessage(), failure.getMessage().contains(
                    expected));
        }
    }

    private static JsonObject jsonlRow(Path path, String field, String id)
            throws Exception {
        for (String line : Files.readAllLines(path,
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject row = JsonParser.parseString(line).getAsJsonObject();
            if (id.equals(row.get(field).getAsString())) return row;
        }
        throw new AssertionError("missing " + field + "=" + id);
    }

    private static void replaceJsonlRow(Path path, String field, String id,
                                        JsonObject replacement)
            throws Exception {
        List<String> lines = Files.readAllLines(path,
                StandardCharsets.UTF_8);
        boolean replaced = false;
        for (int index = 0; index < lines.size(); index++) {
            if (lines.get(index).trim().isEmpty()) continue;
            JsonObject row = JsonParser.parseString(lines.get(index))
                    .getAsJsonObject();
            if (id.equals(row.get(field).getAsString())) {
                lines.set(index, replacement.toString());
                replaced = true;
            }
        }
        if (!replaced) throw new AssertionError("missing " + field + "=" + id);
        Files.write(path, lines, StandardCharsets.UTF_8);
    }

    private static Fixture fixture() throws Exception {
        Path directory = Files.createTempDirectory("primitive-bootstrap-");
        Path smt = directory.resolve("bootstrap.smt2");
        Path composition = directory.resolve("composition.json");
        Path reach = directory.resolve("reach.json");
        Path summaries = directory.resolve("summaries.jsonl");
        Path activations = directory.resolve("activations.jsonl");
        Path target = directory.resolve("target.jsonl");
        Path fatal = directory.resolve("fatal.jsonl");
        Path output = directory.resolve("activation-plan.jsonl");
        Path projection = directory.resolve("projection.json");

        String smtText = "(set-logic ALL)\n"
                + "(declare-const xa Int)\n"
                + "(declare-const xb Int)\n"
                + "(declare-const ca0 Bool)\n"
                + "(declare-const ca1 Bool)\n"
                + "(declare-const cb0 Bool)\n"
                + "(declare-const cb1 Bool)\n"
                + "(assert (= ca0 (= xa 0)))\n"
                + "(assert (= ca1 (= xa 1)))\n"
                + "(assert (= cb0 (= xb 0)))\n"
                + "(assert (= cb1 (= xb 1)))\n"
                + "(assert (= xa 1))\n"
                + "(assert (= xb 1))\n"
                + "(check-sat)\n";
        Files.write(smt, smtText.getBytes(StandardCharsets.UTF_8));

        JsonObject fatalQuery = fatal();
        Files.write(fatal, (fatalQuery + "\n").getBytes(
                StandardCharsets.UTF_8));

        JsonObject compositionJson = new JsonObject();
        compositionJson.addProperty("schemaVersion", 1);
        compositionJson.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        compositionJson.addProperty("compositionStage", "BOOTSTRAP");
        compositionJson.addProperty("structurallyComplete", true);
        compositionJson.addProperty("eligibleForBootstrapModel", true);
        compositionJson.addProperty("fatalReplayValidated", false);
        compositionJson.addProperty("complete", false);
        compositionJson.addProperty(
                "eligibleToReportAutomaticRelationship", false);
        compositionJson.addProperty("caseProjectionCatalogComplete", true);
        compositionJson.addProperty("fatalRegion", "REGION.T");
        compositionJson.addProperty("fatalActivation", "ACT.T");
        compositionJson.addProperty("fatalRegionInstanceId", "INSTANCE.T");
        compositionJson.addProperty("fatalSite",
                "<fixture.T: void run()>#u4");
        compositionJson.addProperty("fatalOccurrence", 1);
        compositionJson.addProperty("fatalDesiredOutcome", true);
        compositionJson.addProperty("fatalConditionCount", 1);
        compositionJson.addProperty("fatalReplayContractId",
                BranchReplayContract.fromJson(fatalQuery.getAsJsonObject(
                        "replayContract")).contractId());
        compositionJson.addProperty("validatedSummaryId", "");
        compositionJson.addProperty("validatedFatalReplaySummary", "");
        compositionJson.add("composedSmtArtifact", artifact(smt));
        compositionJson.add("fatalQueriesArtifact", artifact(fatal));
        JsonArray cases = new JsonArray();
        cases.add(pathCase("REGION.A", "CASE.A.0", "ca0",
                "SUMMARY.A.0", "ACT.A.0", "REGION.A.in.0", "xa",
                "M_Z_field_REGION.A.in.0_java/lang/Boolean"));
        cases.add(pathCase("REGION.A", "CASE.A.1", "ca1",
                "SUMMARY.A.1", "ACT.A.1", "REGION.A.in.0", "xa",
                "M_Z_field_REGION.A.in.0_java/lang/Boolean"));
        cases.add(pathCase("REGION.B", "CASE.B.0", "cb0",
                "SUMMARY.B.0", "ACT.B.0", "REGION.B.in.0", "xb",
                "M_Z_field_REGION.B.in.0_java/lang/Boolean"));
        cases.add(pathCase("REGION.B", "CASE.B.1", "cb1",
                "SUMMARY.B.1", "ACT.B.1", "REGION.B.in.0", "xb",
                "M_Z_field_REGION.B.in.0_java/lang/Boolean"));
        for (com.google.gson.JsonElement element : cases) {
            JsonObject pathCase = element.getAsJsonObject();
            pathCase.addProperty("compositionInputSummaryId",
                    "REGION.A".equals(pathCase.get("regionId").getAsString())
                            ? "SUMMARY.A.MERGED" : "SUMMARY.B.MERGED");
        }
        compositionJson.add("caseProjectionCatalog", cases);
        compositionJson.addProperty("caseProjectionCatalogCount", 4);
        JsonArray included = new JsonArray();
        included.add("SUMMARY.A.MERGED");
        included.add("SUMMARY.B.MERGED");
        compositionJson.add("includedSummaries", included);
        Files.write(composition, compositionJson.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonObject reachJson = new JsonObject();
        reachJson.addProperty("schemaVersion", 1);
        reachJson.addProperty("kind", "BOOLEAN_REACH_CONDITION_REPORT");
        reachJson.addProperty("extractionMode", "BOOTSTRAP_REPLAY_MODEL");
        reachJson.addProperty("replayBootstrapOnly", true);
        reachJson.addProperty("reportableFinalReachCondition", false);
        reachJson.addProperty("complete", true);
        reachJson.addProperty("status",
                "COMPLETE_BOOTSTRAP_BOOLEAN_REPLAY_MODEL");
        reachJson.addProperty("composedSmtSha256", sha256(smt));
        reachJson.add("composedSmtArtifact", artifact(smt));
        reachJson.add("compositionManifestArtifact", artifact(composition));
        JsonArray roots = new JsonArray();
        roots.add(root("REGION.A", "REGION.A.in.0", "xa"));
        roots.add(root("REGION.B", "REGION.B.in.0", "xb"));
        reachJson.add("rootBooleanInputs", roots);
        JsonObject valuation = new JsonObject();
        valuation.addProperty("ordinal", 3);
        valuation.addProperty("valuationKey", "11");
        valuation.addProperty("solverStatus", "sat");
        valuation.addProperty("reachesBug", true);
        JsonArray values = new JsonArray();
        values.add(valuation("REGION.A.in.0", "xa", true));
        values.add(valuation("REGION.B.in.0", "xb", true));
        valuation.add("assignments", values);
        JsonArray truth = new JsonArray();
        truth.add(valuation);
        reachJson.add("truthTable", truth);
        Files.write(reach, reachJson.toString().getBytes(
                StandardCharsets.UTF_8));

        StringBuilder summaryRows = new StringBuilder();
        StringBuilder activationRows = new StringBuilder();
        for (String[] row : new String[][]{
                {"REGION.A", "SUMMARY.A.0", "ACT.A.0"},
                {"REGION.A", "SUMMARY.A.1", "ACT.A.1"},
                {"REGION.B", "SUMMARY.B.0", "ACT.B.0"},
                {"REGION.B", "SUMMARY.B.1", "ACT.B.1"}}) {
            summaryRows.append(summary(row[0], row[1], row[2])).append('\n');
            activationRows.append(activation(row[0], row[2])).append('\n');
        }
        Files.write(summaries, summaryRows.toString().getBytes(
                StandardCharsets.UTF_8));
        Files.write(activations, activationRows.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonObject targetActivation = new JsonObject();
        targetActivation.addProperty("activationId", "ACT.T");
        targetActivation.addProperty("regionId", "REGION.T");
        targetActivation.addProperty("regionInstanceId", "INSTANCE.T");
        targetActivation.addProperty("rootMethod", "<fixture.T: void run()>");
        targetActivation.addProperty("receiverType",
                "fixture.ConsumerThread");
        targetActivation.addProperty("receiverRuntimeClass",
                "fixture.ConsumerThread");
        targetActivation.addProperty("threadName", "rpc-consumer");
        targetActivation.addProperty("threadIdSelectionUsed", false);
        targetActivation.addProperty("invocationOrdinalWithinContext", 1);
        targetActivation.addProperty("rootContextSelectionAuthority",
                "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1");
        targetActivation.addProperty("replayable", true);
        targetActivation.addProperty("symbolicReady", true);
        targetActivation.addProperty("schedulerReady", true);
        targetActivation.addProperty("branchOverrideProhibited", true);
        JsonObject captureGoal = new JsonObject();
        captureGoal.addProperty("kind", "TARGET_BRANCH");
        captureGoal.addProperty("scope", "ONE_DIRECTED_BRANCH");
        targetActivation.add("captureGoal", captureGoal);
        targetActivation.add("branchCaptureSelector",
                BranchCaptureSelector.of("<fixture.T: void run()>#u4", 1,
                        true).toJson());
        Files.write(target, (targetActivation + "\n").getBytes(
                StandardCharsets.UTF_8));
        return new Fixture(smt, composition, reach, summaries, activations,
                target, fatal, output, projection, reachJson);
    }

    private static JsonObject pathCase(String region, String caseId,
                                       String selector, String summary,
                                       String activation, String port,
                                       String solver, String engine) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "GUARDED_CASE_PROJECTION_CATALOG");
        result.addProperty("regionId", region);
        result.addProperty("caseId", caseId);
        result.addProperty("pathKey", "PATH." + caseId);
        result.addProperty("sourceSummaryId", summary);
        result.addProperty("sourceActivationId", activation);
        result.addProperty("selectorSolverSymbol", selector);
        result.addProperty("complete", true);
        result.addProperty("rawEngineSymbolMappingAuthority",
                "EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE");
        JsonObject mapping = new JsonObject();
        mapping.addProperty("canonicalPort", port);
        mapping.addProperty("solverTerm", solver);
        mapping.addProperty("rawEngineSymbol", engine);
        mapping.addProperty("authority", "EMITTER_ACTUAL_TERM");
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        result.add("rawEngineSymbolMappings", mappings);
        result.addProperty("rawEngineSymbolMappingCount", mappings.size());
        return result;
    }

    private static JsonObject root(String region, String port, String solver) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", region);
        result.addProperty("portId", port);
        result.addProperty("javaTypeDescriptor", "Ljava/lang/Boolean;");
        result.addProperty("solverTerm", solver);
        result.addProperty("root", true);
        result.addProperty("upstreamSupplied", false);
        return result;
    }

    private static JsonObject valuation(String port, String solver,
                                        boolean value) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        result.addProperty("solverTerm", solver);
        result.addProperty("value", value);
        result.addProperty("solverLiteral", "(= " + solver + " "
                + (value ? "1" : "0") + ")");
        return result;
    }

    private static JsonObject summary(String region, String summary,
                                      String activation) {
        JsonObject result = new JsonObject();
        result.addProperty("summaryId", summary);
        result.addProperty("activationId", activation);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", "INSTANCE." + region);
        result.addProperty("valid", true);
        result.addProperty("relationallyComplete", true);
        JsonObject admission = new JsonObject();
        admission.addProperty("complete", true);
        JsonArray one = new JsonArray();
        one.add(region + ".in.0");
        admission.add("globalSliceInputs", one.deepCopy());
        admission.add("requiredSliceInputs", one.deepCopy());
        admission.add("observedSymbolizedInputs", one.deepCopy());
        admission.add("pathInactiveSliceInputs", new JsonArray());
        admission.add("admittedObservedInputs", new JsonArray());
        admission.addProperty("admittedObservedInputAuthority",
                "SCHEDULED_OBSERVATION_ONLY_INPUT_PLUS_UNIQUE_COMPLETE_"
                        + "FIRST_CONTAINER_RUNTIME_EVIDENCE_V1");
        admission.add("admittedConcreteFallbackInputs", new JsonArray());
        admission.add("admittedVmIntrinsicPlaceholderInputs",
                new JsonArray());
        admission.add("unforcedEnvironmentValidationRequirements",
                new JsonArray());
        admission.add("failures", new JsonArray());
        admission.addProperty("authority",
                "STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                        + "TRANSFORMER_RUNTIME_PATH_PROOFS_AND_EXPLICIT_"
                        + "CONCRETE_FALLBACKS");
        result.add("inputMaterializationAdmission", admission);
        return result;
    }

    private static JsonObject activation(String region, String activation) {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", activation);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", "INSTANCE." + region);
        result.addProperty("rootMethod", "<fixture." + region
                + ": void run()>");
        result.addProperty("receiverType", "fixture." + region
                + ".Worker");
        result.addProperty("receiverRuntimeClass", "fixture." + region
                + ".Worker");
        result.addProperty("threadName", "rpc-producer-" + region);
        result.addProperty("threadIdSelectionUsed", false);
        result.addProperty("invocationOrdinalWithinContext", 1);
        result.addProperty("rootContextSelectionAuthority",
                "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1");
        result.addProperty("replayable", true);
        result.addProperty("symbolicReady", true);
        JsonObject action = new JsonObject();
        action.addProperty("symbol", region + ".in.0");
        action.addProperty("bindingMode", "LOCAL_DEFINITION");
        action.addProperty("location", "REGION_LIVE_IN");
        String method = "<fixture." + region + ": boolean input()>";
        action.addProperty("method", method);
        action.addProperty("local", "$z0");
        action.addProperty("cell", method + "::$z0");
        action.addProperty("definitionAuthority",
                "STATIC_DATAFLOW_DEF_SITE");
        JsonObject definition = new JsonObject();
        definition.addProperty("method", method);
        definition.addProperty("local", "$z0");
        definition.addProperty("unitIndex", 2);
        definition.addProperty("siteId", method + "#u2");
        JsonArray definitions = new JsonArray();
        definitions.add(definition);
        action.add("definitionSites", definitions);
        JsonArray actions = new JsonArray();
        actions.add(action);
        result.add("materializations", actions);
        return result;
    }

    private static JsonObject fatal() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        result.addProperty("activationId", "ACT.T");
        result.addProperty("regionId", "REGION.T");
        result.addProperty("regionInstanceId", "INSTANCE.T");
        result.addProperty("readyForSolver", true);
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "SymbolExpression");
        condition.addProperty("_java_type", "Z");
        condition.addProperty("_exp", "fatal");
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 1);
        event.addProperty("contextId", 1);
        BranchWitness source = BranchWitness.vmPc(
                "<fixture.T: void run()>#u4",
                "<fixture.T: void run()>", 4, 1, false,
                BranchPredicateAlgebra.complement(condition), 0, event);
        result.add("replayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), source).toJson());
        result.add("solverPathContext", SolverPathContext.empty().toJson());
        JsonObject context = new JsonObject();
        context.addProperty("regionInstanceId", "INSTANCE.T");
        result.add("symbolicContext", context);
        return result;
    }

    private static void makeCallReturn(JsonObject action) {
        action.addProperty("cell",
                "<fixture.Source: boolean read()>.return");
        action.addProperty("sourceKind", "OPAQUE_CALL");
        action.addProperty("projection", "return");
        action.addProperty("location", "CALL_RETURN");
        action.addProperty("sourceBindingMode", "CALL_RETURN_DEFINITION");
    }

    private static JsonObject artifact(Path path) throws Exception {
        JsonObject result = new JsonObject();
        result.addProperty("path", path.toString());
        result.addProperty("sha256", sha256(path));
        result.addProperty("sizeBytes", Files.size(path));
        return result;
    }

    private static String sha256(Path path) throws Exception {
        return sha256(Files.readAllBytes(path));
    }

    private static String sha256(String value) throws Exception {
        return sha256(value.getBytes(StandardCharsets.UTF_8));
    }

    private static String sha256(byte[] bytes) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest(bytes)) {
            result.append(String.format("%02x", value & 0xff));
        }
        return result.toString();
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }

    private static final class Fixture {
        private final Path smt;
        private final Path composition;
        private final Path reachPath;
        private final Path summaries;
        private final Path activations;
        private final Path target;
        private final Path fatal;
        private final Path output;
        private final Path projection;
        private final JsonObject reach;

        private Fixture(Path smt, Path composition, Path reach,
                        Path summaries, Path activations, Path target,
                        Path fatal, Path output, Path projection,
                        JsonObject reachJson) {
            this.smt = smt;
            this.composition = composition;
            this.reachPath = reach;
            this.summaries = summaries;
            this.activations = activations;
            this.target = target;
            this.fatal = fatal;
            this.output = output;
            this.projection = projection;
            this.reach = reachJson;
        }

        private ConcolicPrimitiveBootstrapProjector.Arguments arguments() {
            return arguments(Paths.get("z3"));
        }

        private ConcolicPrimitiveBootstrapProjector.Arguments arguments(
                Path solver) {
            return ConcolicPrimitiveBootstrapProjector.Arguments.parse(
                    commandLine(solver));
        }

        private String[] commandLine(Path solver) {
            return new String[]{
                    "--smt", smt.toString(),
                    "--composition-manifest", composition.toString(),
                    "--reach-report", reachPath.toString(),
                    "--summaries", summaries.toString(),
                    "--activations", activations.toString(),
                    "--target-activations", target.toString(),
                    "--fatal-query", fatal.toString(),
                    "--output", output.toString(),
                    "--manifest", projection.toString(),
                    "--z3", solver.toString(),
                    "--timeout-ms", "10000"
            };
        }
    }
}
