package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Assume;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class ConcolicSmtComposerTest {
    private static void assertFatalQueryRejected(Fixture fixture,
                                                 String message)
            throws Exception {
        try {
            ConcolicSmtComposer.compose(arguments(fixture));
            throw new AssertionError("expected fatal query rejection");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains(message));
        }
    }
    @Test
    public void composesAndSolvesVersionedJavaMapMutationChain()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            writeSummary(fixture, producerSummary(mutationChain(), true));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(),
                    candidateReady(result.manifest));
            assertEquals(0, result.manifest.getAsJsonArray(
                    "gaps").size());
            assertTrue(result.smtLib.contains("(map_put "));
            assertTrue(result.smtLib.contains("(map_remove "));
            assertTrue(result.smtLib.contains("(map_clear "));
            assertTrue(result.smtLib.contains("(map_put_all "));
            assertTrue(result.smtLib.contains(
                    "__REGION_P_out_heapMap0_state3 port__REGION_P_in_1)"));
            assertZ3Status(result.smtLib, "sat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composesGuardedMultiPathRegionRelation() throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject positive = producerSummary(singlePutEffect(), true);
            installTwoEntryContainerEvidence(positive);
            positive.getAsJsonArray("pathCondition").add(
                    integerCondition(">", 0));
            JsonObject nonPositive = producerSummary(singlePutEffect(), true);
            nonPositive.addProperty("summaryId", "SUMMARY.P.SECOND");
            nonPositive.addProperty("activationId", "ACT.P.SECOND");
            installTwoEntryContainerEvidence(nonPositive);
            nonPositive.getAsJsonArray("pathCondition").add(
                    integerCondition("<=", 0));
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(positive, nonPositive),
                    closedPathManifest(positive));
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(),
                    candidateReady(result.manifest));
            assertTrue(result.smtLib.contains(
                    "region_case_selector_partition_REGION_P"));
            assertTrue(result.smtLib.contains("(=>"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    ":named container_element_field_BIND_ARRAY_0"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    ":named container_element_field_BIND_ARRAY_1"));
            for (String line : linesContaining(result.smtLib,
                    ":named container_element_field_BIND_ARRAY_")) {
                assertFalse(line, line.contains(
                        "sym__port__REGION_P_in_3__long"));
            }
            JsonArray catalog = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog");
            assertEquals(2, catalog.size());
            for (com.google.gson.JsonElement element : catalog) {
                JsonObject pathCase = element.getAsJsonObject();
                assertEquals(3, pathCase.size());
                assertFalse(pathCase.get("caseId").getAsString().isEmpty());
                String selector = pathCase.get(
                        "selectorTerm").getAsString();
                assertTrue(result.smtLib.contains(
                        "(declare-const " + selector + " Bool)"));
                assertTrue(result.smtLib.contains("(= " + selector + " "));
                JsonObject mapping = bindingForPort(pathCase,
                        "REGION.P.in.2");
                assertEquals("sym__port__REGION_P_in_2__int",
                        mapping.get("term").getAsString());
            }
            assertZ3Status(result.smtLib, "sat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void recursivelyComposesExactMultiHopSummaryBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String upstreamRegion = "{\"regionId\":\"REGION.U\","
                    + "\"symbolicInputs\":[{\"portId\":\"REGION.U.in.0\","
                    + "\"cell\":\"<example.Upstream: java.util.Map state>\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.U.out.0\","
                    + "\"cell\":\"<example.Upstream: java.util.Map state>\"}]}\n";
            Files.write(fixture.regions, upstreamRegion.getBytes(
                    StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.APPEND);

            JsonObject intermediate = producerSummary(singlePutEffect(), true);

            JsonObject upstream = JsonParser.parseString(
                    producerSummary(singlePutEffect(), true).toString()
                            .replace("REGION.P", "REGION.U")
                            .replace("SUMMARY.P", "SUMMARY.U")
                            .replace("ACT.P", "ACT.U")
                            .replace("fixture#call1", "fixture#call0"))
                    .getAsJsonObject();
            upstream.addProperty("rootCallId", 0);
            upstream.getAsJsonObject(OutputClosureContract.FIELD)
                    .getAsJsonObject("producer")
                    .addProperty("rootCallId", 0);
            JsonArray bindings = new JsonArray();
            JsonObject exactBinding = runtimeEdgeBinding("REGION.U",
                    "REGION.U@fixture#call0", "REGION.U.out.0",
                    "REGION.P", "REGION.P@fixture#call1",
                    "REGION.P.in.0", 5, 8, 91);
            bindings.add(exactBinding);
            upstream.add("edgeBindings", bindings);
            Files.write(fixture.summaries,
                    (canonicalSummary(intermediate) + "\n"
                            + canonicalSummary(upstream) + "\n").getBytes(
                            StandardCharsets.UTF_8));

            ConcolicSmtComposer.Arguments bounded =
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", fixture.fatal.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--regions", fixture.regions.toString(),
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P",
                            "--bounded-upstream-region", "REGION.U"
                    });
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(bounded);

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            JsonArray resolvedEdges = result.manifest.getAsJsonArray(
                    "resolvedEdgeBindings");
            assertEquals(1, resolvedEdges.size());
            assertEquals("EDGE.REGION.U.TO.REGION.P",
                    resolvedEdges.get(0).getAsString());
            assertTrue(result.smtLib.contains(
                    "port__REGION_U_out_0 port__REGION_P_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_P_out_0 port__REGION_F_in_0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void oneExactRegionInstanceSummarySuppliesSixDemandedOutputsOnce()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            java.util.List<String> outputPorts = new java.util.ArrayList<>();
            java.util.List<String> outputCells = new java.util.ArrayList<>();
            JsonArray bindings = new JsonArray();
            for (int index = 0; index < 6; index++) {
                String outputPort = "REGION.P.out." + (index + 3);
                String outputCell = "<example.P: int joint" + index + ">";
                String inputPort = "REGION.F.in." + (index + 8);
                outputPorts.add(outputPort);
                outputCells.add(outputCell);
                addRegionPort(fixture, "REGION.P", "outputs",
                        port(outputPort, outputCell));
                addRegionPort(fixture, "REGION.F", "symbolicInputs",
                        port(inputPort, "<example.F: int joint" + index
                                + ">"));
                bindings.add(runtimeEdgeBinding("REGION.P",
                        "REGION.P@fixture#call1", outputPort,
                        "REGION.F", "REGION.F@fixture#call2", inputPort,
                        10 + index, 30 + index, 100 + index));
            }

            JsonObject summary = producerSummary(new JsonArray(), true);
            explicitPrimitiveOutputClosure(summary, "REGION.P.in.2",
                    outputPorts, outputCells, "JOINT.SIX");
            guardedPrimitiveJointRelation(summary, outputPorts);
            summary.add("edgeBindings", bindings);
            writeSummary(fixture, summary);
            installFatalRelations(fixture, bindings);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonArray constraints = new JsonArray();
            constraints.add(integerCondition("REGION.F.in.8", ">", 0));
            setFatalConstraints(fatal, constraints);
            JsonObject seedReplayContract = fatal.getAsJsonObject(
                    "replayContract").deepCopy();
            JsonObject firstPath = new JsonObject();
            firstPath.add("constraints", constraints.deepCopy());
            JsonObject secondPath = new JsonObject();
            JsonArray secondConstraints = new JsonArray();
            secondConstraints.add(integerCondition(
                    "REGION.F.in.8", "<", 0));
            secondPath.add("constraints", secondConstraints);
            JsonArray reachedPaths = new JsonArray();
            reachedPaths.add(firstPath);
            reachedPaths.add(secondPath);
            fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
            fatal.addProperty("pathClosureState", "CLOSED");
            fatal.addProperty("constraintAuthority",
                    "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1");
            fatal.add("paths", reachedPaths);
            fatal.add("seedReplayContract", seedReplayContract);
            fatal.remove("replayContract");
            fatal.remove("solverPathContext");
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(1, result.manifest.getAsJsonArray(
                    "includedSummaries").size());
            assertEquals("CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1",
                    result.manifest.get("fatalConstraintAuthority")
                            .getAsString());
            assertTrue(result.smtLib.contains(":named fatal_path"));
            assertTrue(result.smtLib.contains("(or "));
            JsonArray catalog = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog");
            assertEquals(2, catalog.size());
            java.util.Set<String> selectors = new java.util.LinkedHashSet<>();
            for (JsonElement element : catalog) {
                selectors.add(element.getAsJsonObject().get(
                        "selectorTerm").getAsString());
            }
            for (String outputPort : outputPorts) {
                assertTrue(result.smtLib.contains(
                        "port__" + outputPort.replace('.', '_')));
                java.util.List<String> outputBindings = linesContaining(
                        result.smtLib, ":named bind_"
                                + outputPort.replace('.', '_'));
                assertEquals(outputBindings.toString(), 2,
                        outputBindings.size());
                for (String binding : outputBindings) {
                    boolean sharesJointSelector = false;
                    for (String selector : selectors) {
                        sharesJointSelector |= binding.contains(
                                "(=> " + selector);
                    }
                    assertTrue(binding, sharesJointSelector);
                }
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void missingOneDemandedOutputPortFailsClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String firstOutput = "REGION.P.out.3";
            String secondOutput = "REGION.P.out.4";
            String firstCell = "<example.P: int firstJoint>";
            String secondCell = "<example.P: int secondJoint>";
            addRegionPort(fixture, "REGION.P", "outputs",
                    port(firstOutput, firstCell));
            addRegionPort(fixture, "REGION.P", "outputs",
                    port(secondOutput, secondCell));
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.8", "<example.F: int firstJoint>"));
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.9", "<example.F: int secondJoint>"));

            JsonObject first = producerSummary(new JsonArray(), true);
            first.getAsJsonObject("outputExpressions").add(
                    firstOutput, symbol("I", "first_joint_output"));
            explicitPrimitiveOutputClosure(first, "REGION.P.in.2",
                    java.util.Collections.singletonList(firstOutput),
                    java.util.Collections.singletonList(firstCell),
                    "SINGLE.FIRST");
            JsonObject firstBinding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", firstOutput,
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.8", 10, 30, 101);
            first.add("edgeBindings", singleton(firstBinding));

            JsonObject second = producerSummary(new JsonArray(), true);
            second.addProperty("summaryId", "SUMMARY.P.SECOND.SINGLETON");
            second.addProperty("activationId",
                    "ACT.P.SECOND.SINGLETON");
            second.getAsJsonObject("outputExpressions").add(
                    secondOutput, symbol("I", "second_joint_output"));
            explicitPrimitiveOutputClosure(second, "REGION.P.in.2",
                    java.util.Collections.singletonList(secondOutput),
                    java.util.Collections.singletonList(secondCell),
                    "SINGLE.SECOND");
            JsonObject secondBinding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", secondOutput,
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.9", 11, 31, 102);
            second.add("edgeBindings", singleton(secondBinding));

            JsonArray bindings = new JsonArray();
            bindings.add(firstBinding);
            bindings.add(secondBinding);
            Files.write(fixture.summaries,
                    (canonicalSummary(first) + "\n"
                            + canonicalSummary(second) + "\n").getBytes(
                            StandardCharsets.UTF_8));
            installFatalRelations(fixture, bindings);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonArray constraints = new JsonArray();
            constraints.add(integerCondition("REGION.F.in.8", ">", 0));
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "gaps").toString().contains(
                    "MissingExactProducerSummary:REGION.P"
                            + "[instance=REGION.P@fixture#call1,"
                            + "outputs=[REGION.P.out.3, REGION.P.out.4]]"));
            assertEquals(0, result.manifest.getAsJsonArray(
                    "includedSummaries").size());
            assertTrue(result.smtLib.contains(
                    "(assert false) ; fail closed: unsupported"));
            assertFalse(result.smtLib.contains("uf__"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsAmbiguousExactProducerSummary() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String output = "REGION.P.out.3";
            String cell = "<example.P: int ambiguous>";
            addRegionPort(fixture, "REGION.P", "outputs",
                    port(output, cell));
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.8", "<example.F: int ambiguous>"));
            JsonObject first = producerSummary(new JsonArray(), true);
            first.getAsJsonObject("outputExpressions").add(
                    output, symbol("I", "ambiguous_output"));
            explicitPrimitiveOutputClosure(first, "REGION.P.in.2",
                    java.util.Collections.singletonList(output),
                    java.util.Collections.singletonList(cell),
                    "AMBIGUOUS.FIRST");
            JsonObject binding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", output,
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.8", 10, 30, 101);
            first.add("edgeBindings", singleton(binding));
            JsonObject second = first.deepCopy();
            second.addProperty("summaryId", "SUMMARY.P.AMBIGUOUS");
            second.getAsJsonObject("outputClosure")
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice")
                    .getAsJsonArray("causalEdgeIds")
                    .set(0, new com.google.gson.JsonPrimitive(
                            "DF.AMBIGUOUS.SECOND"));
            Files.write(fixture.summaries,
                    (canonicalSummary(first) + "\n"
                            + canonicalSummary(second) + "\n").getBytes(
                            StandardCharsets.UTF_8));
            installFatalRelations(fixture, singleton(binding));
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonArray constraints = new JsonArray();
            constraints.add(integerCondition("REGION.F.in.8", ">", 0));
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "gaps").toString().contains(
                    "AmbiguousProducerClosureFingerprint:REGION.P"));
        } finally {
            folder.delete();
        }
    }

    private static JsonObject protocolModel() {
        JsonObject model = new JsonObject();
        model.addProperty("complete", true);
        JsonArray relations = new JsonArray();

        JsonObject codec = protocolRelation("FIXTURE.CODEC",
                "LOSSLESS_CODEC");
        codec.addProperty("codecId", "FIXTURE_INTEGER_CODEC");
        codec.addProperty("lossless", true);
        codec.addProperty("transportEqualityConfirmed", true);
        codec.add("source", protocolPort("REGION.P.in.2", "INT"));
        codec.add("encoded", protocolPort("REGION.P.out.1", "VALUE"));
        codec.add("transport", protocolPort("REGION.F.in.2", "VALUE"));
        JsonObject decoded = new JsonObject();
        decoded.addProperty("kind", "EXPRESSION");
        decoded.addProperty("valueType", "INT");
        decoded.add("expression", symbol("java/lang/Integer",
                "boxed_lookup_key"));
        codec.add("decoded", decoded);
        relations.add(codec);

        JsonObject constant = protocolRelation("FIXTURE.CONSTANT",
                "CONSTANT_BINDING");
        constant.add("target", protocolPort("REGION.F.in.7", "INT"));
        JsonObject value = new JsonObject();
        value.addProperty("kind", "CONSTANT");
        value.addProperty("valueType", "INT");
        value.addProperty("value", 23);
        constant.add("value", value);
        relations.add(constant);

        JsonObject lifecycle = protocolRelation("FIXTURE.LIFECYCLE",
                "EXPIRING_CACHE_MEMBERSHIP");
        lifecycle.addProperty("exactExpiryRemoval", true);
        lifecycle.addProperty("currentValuePresent", true);
        lifecycle.addProperty("retainsCachedValue", true);
        lifecycle.addProperty("uniqueSuccessorValues", true);
        lifecycle.add("cachedValue", protocolPort("REGION.P.in.2", "INT"));
        lifecycle.add("currentValue", protocolPort("REGION.F.in.3", "INT"));
        lifecycle.add("state", protocolPort("REGION.P.out.0", "MAP"));
        lifecycle.add("observationTime",
                protocolPort("REGION.F.in.4", "INT"));
        lifecycle.add("updateInterval",
                protocolPort("REGION.F.in.5", "INT"));
        lifecycle.add("lifetime", protocolPort("REGION.F.in.6", "INT"));
        lifecycle.add("issueTime", protocolSymbol("issue", "INT"));
        lifecycle.add("retirementTime", protocolSymbol("retire", "INT"));
        lifecycle.add("credentialExpiry",
                protocolSymbol("credential_expiry", "INT"));
        lifecycle.add("memberExpiry",
                protocolSymbol("member_expiry", "INT"));
        relations.add(lifecycle);

        model.addProperty("relationCount", relations.size());
        model.add("relations", relations);
        return model;
    }

    private static JsonObject guardedWriter(String guard, String from,
                                            int writeSeq, int readSeq) {
        JsonObject relation = new JsonObject();
        relation.addProperty("edgeId", "EDGE." + guard);
        relation.addProperty("fromEndpoint", from);
        relation.addProperty("toEndpoint", "REGION.F.in.0");
        relation.addProperty("guardSymbol", guard);
        JsonObject binding = new JsonObject();
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("writerEventSeq", writeSeq);
        binding.addProperty("readerEventSeq", readSeq);
        binding.addProperty("receiverObjectId", 41);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        relation.add("selectedBindings", bindings);
        return relation;
    }

    private static JsonObject protocolRelation(String id, String kind) {
        JsonObject relation = new JsonObject();
        relation.addProperty("relationId", id);
        relation.addProperty("kind", kind);
        relation.addProperty("evidenceConfirmed", true);
        return relation;
    }

    private static JsonObject protocolPort(String port, String valueType) {
        JsonObject endpoint = new JsonObject();
        endpoint.addProperty("kind", "PORT");
        endpoint.addProperty("portId", port);
        endpoint.addProperty("valueType", valueType);
        return endpoint;
    }

    private static JsonObject protocolSymbol(String symbol, String valueType) {
        JsonObject endpoint = new JsonObject();
        endpoint.addProperty("kind", "SYMBOL");
        endpoint.addProperty("symbol", symbol);
        endpoint.addProperty("valueType", valueType);
        return endpoint;
    }

    private static JsonArray singlePutEffect() {
        JsonArray effects = new JsonArray();
        effects.add(mapEffect("MAP_PUT", "REGION.P.in.0",
                "REGION.P.out.0", 0));
        return effects;
    }

    private static JsonArray mutationChain() {
        JsonArray effects = new JsonArray();
        effects.add(mapEffect("MAP_PUT", "REGION.P.in.0",
                "REGION.P.out.heapMap0.state1", 0));
        effects.add(mapEffect("MAP_REMOVE",
                "REGION.P.out.heapMap0.state1",
                "REGION.P.out.heapMap0.state2", 1));
        effects.add(mapEffect("MAP_CLEAR",
                "REGION.P.out.heapMap0.state2",
                "REGION.P.out.heapMap0.state3", 2));
        effects.add(mapEffect("MAP_PUT_ALL",
                "REGION.P.out.heapMap0.state3", "REGION.P.out.0", 3));
        return effects;
    }

    private static JsonObject mapEffect(String kind, String input,
                                        String output, int before) {
        JsonObject effect = new JsonObject();
        effect.addProperty("effectId", "HEAP_EFFECT.REGION.P." + before);
        effect.addProperty("kind", kind);
        effect.addProperty("stateFamily", "MAP_STATE.REGION.P.0");
        effect.addProperty("preState", "MAP_STATE.REGION.P.0." + before);
        effect.addProperty("postState",
                "MAP_STATE.REGION.P.0." + (before + 1));
        effect.addProperty("stateOrdinalBefore", before);
        effect.addProperty("stateOrdinalAfter", before + 1);
        effect.addProperty("inputPort", input);
        effect.addProperty("outputPort", output);
        if ("MAP_PUT".equals(kind) || "MAP_REMOVE".equals(kind)) {
            effect.add("keyExpression", constant("I", "Y_I_7"));
        }
        if ("MAP_PUT".equals(kind)) {
            effect.add("valueExpression", symbol("example/Value",
                    "producer_value"));
        }
        if ("MAP_PUT_ALL".equals(kind)) {
            effect.add("sourceExpression", symbol("L",
                    "M_L_field_REGION.P.in.1_example/Source"));
        }
        return effect;
    }

    private static JsonObject producerSummary(JsonArray effects,
                                              boolean complete) {
        return producerSummary(effects, new JsonArray(), complete);
    }

    private static JsonObject producerSummary(JsonArray effects,
                                              JsonArray initializers,
                                              boolean complete) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.P");
        summary.addProperty("activationId", "ACT.P");
        summary.addProperty("regionId", "REGION.P");
        summary.addProperty("regionInstanceId",
                "REGION.P@fixture#call1");
        summary.addProperty("rootCallId", 1);
        summary.addProperty("relationallyComplete", complete);
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        summary.add("pathCondition", new JsonArray());
        summary.add("outputExpressions", new JsonObject());
        summary.add("heapStateInitializers", initializers);
        summary.add("heapEffects", effects);
        explicitSingletonHeapOutputClosure(summary);
        return summary;
    }

    private static void explicitSingletonHeapOutputClosure(
            JsonObject summary) {
        String region = summary.get("regionId").getAsString();
        String instance = summary.get("regionInstanceId").getAsString();
        long rootCallId = summary.get("rootCallId").getAsLong();
        String outputPort = region + ".out.0";
        String outputCell = "<example.Producer: java.util.Map state>";

        JsonObject output = new JsonObject();
        output.addProperty("portId", outputPort);
        output.addProperty("cell", outputCell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "Ljava/util/Map;");
        output.addProperty("selectionAuthority",
                "STATIC_EXACT_OUTPUT_PORT");

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", outputCell);
        slice.add("inputPorts", singletonString(region + ".in.0"));
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.addProperty("captureBindingsRequired", false);
        slice.addProperty("captureBindingsComplete", true);

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);

        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", region);
        producer.addProperty("regionInstanceId", instance);
        producer.addProperty("rootCallId", rootCallId);
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 1);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        summary.add(OutputClosureContract.FIELD, closure);
    }

    private static JsonObject requestedOutput(String port) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        return result;
    }

    private static JsonObject requestedSlice(String... inputs) {
        JsonObject result = new JsonObject();
        JsonArray ports = new JsonArray();
        for (String input : inputs) ports.add(input);
        result.add("inputPorts", ports);
        result.addProperty("complete", true);
        return result;
    }

    private static void explicitPrimitiveOutputClosure(
            JsonObject summary, String inputPort,
            java.util.List<String> outputPorts,
            java.util.List<String> outputCells, String proofSuffix) {
        if (outputPorts.size() != outputCells.size()
                || outputPorts.isEmpty()) {
            throw new IllegalArgumentException(
                    "joint output ports and cells must align");
        }
        String regionId = summary.get("regionId").getAsString();
        String regionInstanceId = summary.get(
                "regionInstanceId").getAsString();
        int call = Integer.parseInt(regionInstanceId.substring(
                regionInstanceId.lastIndexOf("#call") + 5));
        summary.addProperty("rootCallId", call);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", regionId);
        producer.addProperty("regionInstanceId", regionInstanceId);
        producer.addProperty("rootCallId", call);
        envelope.add("producer", producer);
        JsonArray members = new JsonArray();
        String method = "<example.Producer: void produce()>";
        for (int index = 0; index < outputPorts.size(); index++) {
            String outputPort = outputPorts.get(index);
            String outputCell = outputCells.get(index);
            String site = method + "#u" + (20 + index);
            JsonObject output = new JsonObject();
            output.addProperty("portId", outputPort);
            output.addProperty("cell", outputCell);
            output.addProperty("kind", "REGION_OUTPUT");
            output.addProperty("javaTypeDescriptor", "I");
            output.addProperty("selectionAuthority",
                    "STATIC_EXACT_OUTPUT_PORT");

            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId", "CAPTURE."
                    + proofSuffix + "." + index);
            capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
            capture.addProperty("outputPort", outputPort);
            capture.addProperty("outputCell", outputCell);
            capture.addProperty("method", method);
            capture.addProperty("unitIndex", 20 + index);
            capture.addProperty("siteId", site);
            capture.addProperty("fieldSignature", outputCell);
            JsonArray captures = new JsonArray();
            captures.add(capture);

            JsonObject slice = new JsonObject();
            slice.addProperty("outputPort", outputPort);
            slice.addProperty("outputCell", outputCell);
            slice.add("inputPorts", singletonString(inputPort));
            slice.add("sites", singletonString(site));
            slice.add("staticSites", new JsonArray());
            slice.add("methods", singletonString(method));
            slice.add("causalEdgeIds", singletonString(
                    "DF." + proofSuffix + "." + index));
            slice.add("captureBindings", captures);
            slice.addProperty("captureBindingsRequired", true);
            slice.addProperty("captureBindingsComplete", true);

            JsonObject member = new JsonObject();
            member.add("output", output);
            member.add("slice", slice);
            members.add(member);
        }
        envelope.add("members", members);
        summary.add("outputClosure", envelope);
    }

    private static void guardedPrimitiveJointRelation(
            JsonObject summary, java.util.List<String> outputPorts) {
        JsonArray cases = new JsonArray();
        String[] operators = new String[]{">", "<="};
        for (int caseIndex = 0; caseIndex < operators.length; caseIndex++) {
            JsonObject item = new JsonObject();
            item.addProperty("caseId", "CASE.JOINT." + caseIndex);
            JsonObject guard = new JsonObject();
            guard.addProperty("kind", "PATH_CONDITION");
            JsonArray conditions = new JsonArray();
            conditions.add(integerCondition("REGION.P.in.2",
                    operators[caseIndex], 0));
            guard.add("conditions", conditions);
            item.add("guard", guard);
            JsonObject expressions = new JsonObject();
            for (int index = 0; index < outputPorts.size(); index++) {
                expressions.add(outputPorts.get(index), symbol("I",
                        "joint_case_" + caseIndex + "_output_" + index));
            }
            item.add("outputExpressions", expressions);
            item.add("heapStateInitializers", new JsonArray());
            item.add("heapObservations", new JsonArray());
            item.add("finiteMapSnapshots", new JsonArray());
            item.add("dynamicFieldBindings", new JsonArray());
            item.add("engineArrayInputBindings", new JsonArray());
            item.add("vmIntrinsicPlaceholderBindings", new JsonArray());
            item.add("unforcedEnvironmentValidationRequirements",
                    new JsonArray());
            item.add("heapEffects", new JsonArray());
            cases.add(item);
        }
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.add("cases", cases);
        summary.add("regionRelation", relation);
    }

    private static JsonObject runtimeEdgeBinding(
            String fromRegion, String fromInstance, String fromOutput,
            String toRegion, String toInstance, String toInput,
            int writeSeq, int readSeq, int receiver) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", "EDGE." + fromRegion + ".TO."
                + toRegion);
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("fromRegion", fromRegion);
        binding.addProperty("toRegion", toRegion);
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromOutput);
        binding.addProperty("toInputPort", toInput);
        binding.addProperty("writerEventSeq", writeSeq);
        binding.addProperty("readerEventSeq", readSeq);
        binding.addProperty("receiverObjectId", receiver);
        return binding;
    }

    private static JsonObject runtimeValueEqualityBinding(
            String fromRegion, String fromInstance, String fromOutput,
            String toRegion, String toInstance, String toInput,
            int writerSeq, int readerSeq) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", "EDGE." + fromRegion + ".TO."
                + toRegion);
        binding.addProperty("evidenceKind",
                "COMPLETE_VALUE_EQUALITY_V1");
        binding.addProperty("fromRegion", fromRegion);
        binding.addProperty("toRegion", toRegion);
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromOutput);
        binding.addProperty("toInputPort", toInput);
        binding.addProperty("writerEventSeq", writerSeq);
        binding.addProperty("readerEventSeq", readerSeq);
        binding.addProperty("valueFingerprint", "sha256:" + fromInstance
                + ":" + toInstance + ":" + writerSeq + ":" + readerSeq);
        return binding;
    }

    private static JsonObject scalarSummary(String region, String summaryId,
                                            String activationId,
                                            String instanceId,
                                            String symbolName) {
        JsonObject result = producerSummary(new JsonArray(), true);
        result.addProperty("summaryId", summaryId);
        result.addProperty("activationId", activationId);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", instanceId);
        result.add("requestedOutput", requestedOutput(region + ".out.0"));
        result.getAsJsonObject("outputExpressions").add(
                region + ".out.0", symbol("I", symbolName));
        return result;
    }

    private static JsonObject port(String portId, String cell) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", portId);
        result.addProperty("cell", cell);
        result.addProperty("javaType", cellType(cell));
        return result;
    }

    private static String cellType(String cell) {
        String declaration = cell.substring(cell.indexOf(':') + 1,
                cell.lastIndexOf('>')).trim();
        return declaration.substring(0, declaration.lastIndexOf(' '));
    }

    private static String canonicalRegions(String jsonl) {
        StringBuilder result = new StringBuilder();
        for (String line : jsonl.split("\\n")) {
            if (line.isEmpty()) continue;
            JsonObject region = JsonParser.parseString(line)
                    .getAsJsonObject();
            for (String field : new String[]{"symbolicInputs", "outputs"}) {
                for (JsonElement element : region.getAsJsonArray(field)) {
                    JsonObject port = element.getAsJsonObject();
                    port.addProperty("javaType",
                            cellType(port.get("cell").getAsString()));
                }
            }
            result.append(region).append('\n');
        }
        return result.toString();
    }

    private static JsonObject region(String regionId, String javaType,
                                     String cellName) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", regionId);
        JsonArray inputs = new JsonArray();
        inputs.add(port(regionId + ".in.0", "<example." + regionId
                + ": " + javaType + " " + cellName + ">"));
        JsonArray outputs = new JsonArray();
        outputs.add(port(regionId + ".out.0", "<example." + regionId
                + ": " + javaType + " " + cellName + ">"));
        result.add("symbolicInputs", inputs);
        result.add("outputs", outputs);
        return result;
    }

    private static void appendRegion(Fixture fixture, JsonObject region)
            throws Exception {
        Files.write(fixture.regions, (region + "\n").getBytes(
                        StandardCharsets.UTF_8),
                java.nio.file.StandardOpenOption.APPEND);
    }

    private static void addRegionPort(Fixture fixture, String regionId,
                                      String collection, JsonObject port)
            throws Exception {
        java.util.List<String> lines = Files.readAllLines(fixture.regions,
                StandardCharsets.UTF_8);
        java.util.List<String> updated = new java.util.ArrayList<>();
        boolean found = false;
        for (String line : lines) {
            if (line.trim().isEmpty()) continue;
            JsonObject region = JsonParser.parseString(line).getAsJsonObject();
            if (regionId.equals(region.get("regionId").getAsString())) {
                region.getAsJsonArray(collection).add(port.deepCopy());
                found = true;
            }
            updated.add(region.toString());
        }
        if (!found) throw new AssertionError("missing region " + regionId);
        Files.write(fixture.regions,
                (String.join("\n", updated) + "\n").getBytes(
                        StandardCharsets.UTF_8));
    }

    private static void installFatalRelations(Fixture fixture,
                                              JsonArray bindings)
            throws Exception {
        JsonObject fatal = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.fatal), StandardCharsets.UTF_8)
                .trim()).getAsJsonObject();
        JsonObject context = fatal.getAsJsonObject("symbolicContext");
        JsonArray relations = new JsonArray();
        JsonArray classes = new JsonArray();
        for (JsonElement element : bindings) {
            JsonObject binding = element.getAsJsonObject();
            String from = binding.get("fromOutputPort").getAsString();
            String to = binding.get("toInputPort").getAsString();
            JsonObject relation = new JsonObject();
            relation.addProperty("edgeId", binding.get("edgeId")
                    .getAsString());
            relation.addProperty("fromEndpoint", from);
            relation.addProperty("toEndpoint", to);
            JsonArray selected = new JsonArray();
            selected.add(binding.deepCopy());
            relation.add("selectedBindings", selected);
            relations.add(relation);
            JsonObject equality = new JsonObject();
            JsonArray members = new JsonArray();
            members.add(from);
            members.add(to);
            equality.add("members", members);
            classes.add(equality);
        }
        context.add("equalityClasses", classes);
        context.add("equalityRelations", new JsonArray());
        context.add("versionedStateMerges", relations);
        Files.write(fixture.fatal, (fatal + "\n").getBytes(
                StandardCharsets.UTF_8));
    }

    private static JsonObject emptyMapInitializer() {
        JsonObject initializer = new JsonObject();
        initializer.addProperty("initializerId",
                "HEAP_INITIALIZER.REGION.P.0");
        initializer.addProperty("kind", "MAP_EMPTY");
        initializer.addProperty("statePort",
                "REGION.P.state.heapMap0.empty");
        initializer.addProperty("stateFamily", "MAP_STATE.REGION.P.0");
        initializer.addProperty("stateId", "MAP_STATE.REGION.P.0.0");
        initializer.addProperty("requestedOutputPort", "REGION.P.out.0");
        initializer.addProperty("allocatedType", "java.util.HashMap");
        initializer.addProperty("staticInitializerId",
                "STATIC_INIT.REGION.P.0");
        initializer.addProperty("allocationEdgeId", "EDGE.ALLOC.0");
        JsonArray proof = new JsonArray();
        proof.add("EDGE.ALLOC.0");
        initializer.add("proofEdgeIds", proof);
        initializer.addProperty("proofComplete", true);
        initializer.addProperty("bindingAuthority",
                "STATIC_UNIQUE_DEFAULT_ALLOCATION_TO_REQUESTED_OUTPUT_"
                        + "PLUS_RUNTIME_UNIQUE_MAP_RECEIVER");
        initializer.addProperty("emptyStateAuthority",
                "JAVA_PLATFORM_DEFAULT_MAP_CONSTRUCTOR_SEMANTICS");
        return initializer;
    }

    private static JsonObject symbol(String javaType, String expression) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", expression);
        return result;
    }

    private static JsonObject constant(String javaType, String expression) {
        JsonObject result = symbol(javaType, expression);
        result.addProperty("_type", "ConstExpr");
        return result;
    }

    private static JsonObject conString(String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConStringSymbolExp");
        result.addProperty("_java_type", "java/lang/String");
        result.addProperty("_exp", "Y_L'String'_" + value);
        return result;
    }

    private static JsonObject opString(String operation,
                                       JsonElement... params) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "OpStrExpression");
        result.addProperty("_name", operation);
        result.addProperty("_is_not", false);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : params) arguments.add(parameter);
        result.add("_param_list", arguments);
        return result;
    }

    private static JsonObject negatedOpString(String operation,
                                              JsonElement... params) {
        JsonObject result = opString(operation, params);
        result.addProperty("_is_not", true);
        return result;
    }

    private static JsonObject method(String name, JsonElement resultValue,
                                     JsonElement... params) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "MethodExpression");
        result.addProperty("_name", name);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : params) arguments.add(parameter);
        result.add("_param_list", arguments);
        result.add("_res_exp", resultValue);
        return result;
    }

    private static JsonObject cast(JsonElement source, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "TypeCastExpression");
        result.addProperty("_java_type", javaType);
        result.add("_exp", source);
        return result;
    }

    private static JsonObject explicitCast(JsonElement source,
                                           String sourceJavaType,
                                           String targetJavaType) {
        JsonObject result = cast(source, targetJavaType);
        result.addProperty("sourceJavaType", sourceJavaType);
        result.addProperty("targetJavaType", targetJavaType);
        return result;
    }

    private static JsonObject unaryNegation(JsonElement operand) {
        return binaryCondition(JsonNull.INSTANCE, "-", operand);
    }

    private static JsonArray fatalConstraints(JsonObject fatal) {
        BranchReplayContract contract = BranchReplayContract.fromJson(
                fatal.getAsJsonObject("replayContract"));
        SolverPathContext context = SolverPathContext.fromJson(
                fatal.getAsJsonObject("solverPathContext"));
        JsonArray result = context.expressions();
        for (JsonElement predicate : contract.requiredPathPredicates()) {
            result.add(predicate);
        }
        return result;
    }

    /** Rebuilds the immutable test protocol after changing a path formula. */
    private static void setFatalConstraints(JsonObject fatal,
                                            JsonArray constraints) {
        if (constraints == null || constraints.size() == 0) {
            throw new IllegalArgumentException(
                    "fatal test path requires a target predicate");
        }
        int targetPosition = constraints.size() - 1;
        java.util.List<BranchWitness> prefix = new java.util.ArrayList<>();
        java.util.Set<Integer> branchPositions =
                new java.util.LinkedHashSet<>();
        for (int index = 0; index < targetPosition; index++) {
            JsonElement expression = constraints.get(index);
            String type = expression.isJsonObject()
                    && expression.getAsJsonObject().has("_type")
                    ? expression.getAsJsonObject().get("_type").getAsString()
                    : "";
            if ("MethodExpression".equals(type)
                    || "_array_expr".equals(type)) {
                continue;
            }
            branchPositions.add(index);
            prefix.add(testBranchWitness("TEST#u" + (100 + index),
                    100 + index, expression, index));
        }
        JsonElement requiredTarget = constraints.get(targetPosition);
        BranchWitness source = BranchWitness.vmPc("F#u2",
                "<test.Fatal: void run()>", 2, 1, false,
                BranchPredicateAlgebra.complement(requiredTarget),
                targetPosition, testVmEvent(targetPosition));
        BranchReplayContract contract = BranchReplayContract.flip(prefix,
                source);
        SolverPathContext context = SolverPathContext.fromPath(constraints,
                branchPositions, targetPosition);
        fatal.add("replayContract", contract.toJson());
        fatal.add("solverPathContext", context.toJson());
    }

    private static BranchWitness testBranchWitness(String siteId,
                                                   int unitIndex,
                                                   JsonElement predicate,
                                                   int pcIndex) {
        return BranchWitness.vmPc(siteId, "<test.Fatal: void run()>",
                unitIndex, 1, true, predicate, pcIndex,
                testVmEvent(pcIndex));
    }

    private static JsonObject testVmEvent(int pcIndex) {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", pcIndex + 1);
        return event;
    }

    private static void prependFatalConstraints(Fixture fixture,
                                                JsonElement... added)
            throws Exception {
        JsonObject fatal = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.fatal),
                StandardCharsets.UTF_8).trim()).getAsJsonObject();
        JsonArray constraints = new JsonArray();
        for (JsonElement constraint : added) constraints.add(constraint);
        for (JsonElement constraint : fatalConstraints(fatal)) {
            constraints.add(constraint);
        }
        setFatalConstraints(fatal, constraints);
        Files.write(fixture.fatal, (fatal + "\n").getBytes(
                StandardCharsets.UTF_8));
    }

    private static JsonObject codecUsername(JsonElement integer,
                                            String delimiter,
                                            String suffixName) {
        JsonObject prefix = opString("concat",
                opString("toString", integer), conString(delimiter));
        return opString("concat", prefix,
                symbol("java/lang/String", suffixName));
    }

    private static JsonObject codecParse(JsonElement integer,
                                         String delimiter, Integer limit,
                                         int index, Integer radix,
                                         JsonElement resultValue) {
        JsonObject receiver = codecUsername(integer, delimiter,
                "server_suffix");
        JsonObject split;
        if (limit == null) {
            split = method("java/lang/String splitElement",
                    conString("split_result"), receiver,
                    conString(delimiter), constant("I", "Y_I_" + index));
        } else {
            split = method("java/lang/String splitElement",
                    conString("split_result"), receiver,
                    conString(delimiter), constant("I", "Y_I_" + limit),
                    constant("I", "Y_I_" + index));
        }
        if (radix == null) {
            return method("java/lang/Integer parseInt", resultValue, split);
        }
        return method("java/lang/Integer parseInt", resultValue, split,
                constant("I", "Y_I_" + radix));
    }

    private static JsonObject integerCondition(String operator, int value) {
        return integerCondition(
                "M_I_field_REGION.P.in.2_example/Cache", operator, value);
    }

    private static JsonObject integerCondition(String raw, String operator,
                                               int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", symbol("I", raw));
        result.addProperty("_op", operator);
        result.add("_right", constant("I", "Y_I_" + value));
        return result;
    }

    private static JsonObject placeholderCondition(String operator,
                                                   int count) {
        return binaryCondition(placeholderExpression("currentTimeMillis",
                        count), operator,
                constant("I", "Y_I_0"));
    }

    private static JsonObject placeholderExpression(String function,
                                                    int count) {
        JsonObject placeholder = new JsonObject();
        placeholder.addProperty("_type", "PlaceholderExpression");
        placeholder.addProperty("_place_holder_func", function);
        placeholder.addProperty("_count", count);
        return placeholder;
    }

    private static String vmCurrentTimeCell() {
        return "<java.lang.System: long currentTimeMillis()>.return";
    }

    private static String currentTimeMillisCell() {
        return "<java.lang.System: long currentTimeMillis()>.return";
    }

    private static void addVmPlaceholderCertificate(
            JsonObject container, String inputPort, int count) {
        addVmPlaceholderCertificate(container, inputPort, count,
                vmCurrentTimeCell());
    }

    private static void addVmPlaceholderCertificate(
            JsonObject container, String inputPort, int count, String cell) {
        String identity = "currentTimeMills#" + count;
        JsonObject requirement = new JsonObject();
        requirement.addProperty("kind",
                "UNFORCED_ENVIRONMENT_VALIDATION_REQUIREMENT");
        requirement.addProperty("required", true);
        requirement.addProperty("inputPort", inputPort);
        requirement.addProperty("cell", cell);
        requirement.addProperty("sourceKind", "ENVIRONMENT");
        requirement.addProperty("bindingMode",
                "VM_INTRINSIC_PLACEHOLDER");
        requirement.addProperty("placeholderFunction",
                "currentTimeMills");
        requirement.addProperty("captureAuthority",
                "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
        requirement.addProperty("modelControllable", false);
        requirement.addProperty("replayPolicy",
                "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
        requirement.addProperty("evidenceAuthority",
                "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION");
        JsonArray evidence = new JsonArray();
        evidence.add(identity);
        requirement.add("placeholderEvidenceIdentities", evidence);
        JsonArray requirements = new JsonArray();
        requirements.add(requirement);

        container.add("unforcedEnvironmentValidationRequirements",
                requirements);

        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind",
                "VM_INTRINSIC_PLACEHOLDER_PORT_BINDING");
        binding.addProperty("placeholderIdentity", identity);
        binding.addProperty("placeholderFunction", "currentTimeMills");
        binding.addProperty("inputPort", inputPort);
        binding.addProperty("cell", cell);
        binding.addProperty("javaTypeDescriptor", "J");
        binding.addProperty("sourceKind", "ENVIRONMENT");
        binding.addProperty("bindingMode", "VM_INTRINSIC_PLACEHOLDER");
        binding.addProperty("captureAuthority",
                "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
        binding.addProperty("evidenceAuthority",
                "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION");
        binding.addProperty("modelControllable", false);
        binding.addProperty("replayPolicy",
                "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
        binding.addProperty("ownerAuthority",
                "UNIQUE_USED_PLACEHOLDER_IDENTITY_TO_EXACT_SLICE_INPUT");
        binding.addProperty("required", true);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        container.add("vmIntrinsicPlaceholderBindings", bindings);

    }

    private static JsonObject arrayLoad(String array, String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "_array_expr");
        result.addProperty("_is_load", true);
        result.addProperty("_arr_str", array);
        result.add("_index_exp", constant("I", "Y_I_0"));
        result.add("_value_exp", symbol("I", value));
        return result;
    }

    private static JsonObject binaryCondition(com.google.gson.JsonElement left,
                                              String operator,
                                              com.google.gson.JsonElement right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static void prepareOutputCase(JsonObject summary, String operator,
                                          String observationId,
                                          String valueSymbol) {
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.P.out.0");
        summary.add("requestedOutput", requested);
        summary.getAsJsonArray("pathCondition").add(
                integerCondition(operator, 0));
        JsonArray observations = new JsonArray();
        observations.add(heapObservation(observationId, valueSymbol));
        summary.add("heapObservations", observations);
    }

    private static void prepareDynamicOutputCase(JsonObject summary,
                                                 String operator,
                                                 String observationId,
                                                 String valueSymbol,
                                                 String dynamicFieldSymbol) {
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.P.out.0");
        summary.add("requestedOutput", requested);
        summary.getAsJsonArray("pathCondition").add(binaryCondition(
                symbol("J", "M_J_field_" + dynamicFieldSymbol + "_expiry"),
                operator, constant("J", "Y_J_0")));
        JsonArray observations = new JsonArray();
        observations.add(dynamicHeapObservation(observationId, valueSymbol,
                dynamicFieldSymbol));
        summary.add("heapObservations", observations);
        JsonArray dynamicBindings = new JsonArray();
        dynamicBindings.add(runtimeDynamicFieldBinding(observationId,
                dynamicFieldSymbol, summary.get("activationId").getAsString()));
        summary.add("dynamicFieldBindings", dynamicBindings);
    }

    private static JsonObject heapObservation(String id, String valueSymbol) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", "MAP_ENTRY_READ");
        result.addProperty("complete", true);
        result.addProperty("observationId", id);
        result.addProperty("statePort", "REGION.P.in.0");
        result.add("keyExpression", constant("I", "Y_I_7"));
        result.add("valueExpression", symbol("example/Value", valueSymbol));
        result.addProperty("entryBindingAuthority",
                "RUNTIME_BOUND_MAP_ENTRY_READ");
        result.addProperty("entryValueFieldBindingComplete", true);
        JsonObject binding = new JsonObject();
        binding.addProperty("fieldSymbol", "REGION.P.in.3");
        binding.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        binding.addProperty("fieldJavaType", "J");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        binding.add("fieldPath", fieldPath);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        result.add("entryFieldBindings", bindings);
        return result;
    }

    private static JsonObject dynamicHeapObservation(
            String id, String valueSymbol, String dynamicFieldSymbol) {
        JsonObject result = heapObservation(id, valueSymbol);
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicFieldSymbol);
        binding.addProperty("baseInputSymbol", "REGION.P.in.3");
        binding.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
        binding.add("fieldExpression", symbol("J",
                "M_J_field_" + dynamicFieldSymbol + "_expiry"));
        binding.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        binding.addProperty("fieldJavaType", "long");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        binding.add("fieldPath", fieldPath);
        binding.addProperty("materializationSiteId",
                "<example.Store: void prune()>#u4");
        binding.addProperty("materializationOccurrence",
                dynamicFieldSymbol.endsWith(".2") ? 2 : 1);
        binding.addProperty("entryReadObservationId", id);
        binding.add("keyExpression", constant("I", "Y_I_7"));
        binding.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        binding.addProperty("baseInputRole",
                "FIELD_FAMILY_TEMPLATE_ONLY");
        binding.addProperty("authority",
                "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                        + "ENTRY_VALUE_TOKEN_JOIN");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        result.add("entryFieldBindings", bindings);
        return result;
    }

    private static JsonObject nonMutatingDynamicHeapObservation(
            String id, String valueSymbol, String dynamicFieldSymbol) {
        return nonMutatingDynamicHeapObservation(id, valueSymbol,
                dynamicFieldSymbol, "REGION.P.in.3");
    }

    private static JsonObject nonMutatingDynamicHeapObservation(
            String id, String valueSymbol, String dynamicFieldSymbol,
            String baseInputSymbol) {
        JsonObject result = dynamicHeapObservation(id, valueSymbol,
                dynamicFieldSymbol);
        String region = "REGION.P";
        String activationId = "ACT.P";
        String dynamicBindingId = "DYNAMIC_FIELD:" + dynamicFieldSymbol;
        String selectorDigest = ConcolicSmtComposer
                .heapObservationStateSelectorDigestForTests(id,
                        baseInputSymbol, dynamicBindingId);
        String statePort = ConcolicSmtComposer
                .heapObservationStatePortForTests(region, id,
                        baseInputSymbol, dynamicBindingId);
        long mapToken = 101L;
        String mapWitness = "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T"
                + mapToken;
        JsonObject mapExpression = symbol("L", mapWitness);
        result.addProperty("statePort", statePort);
        result.addProperty("stateBindingAuthority",
                "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1");
        result.addProperty("stateBaseComplete", true);
        result.add("mapExpression", mapExpression.deepCopy());
        result.addProperty("expressionAuthority",
                "ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1");
        result.addProperty("backingMapObjectToken", mapToken);
        result.addProperty("objectTokenScope", activationId);
        result.addProperty("mapExpressionWitnessSchemaVersion", 1);
        result.addProperty("mapExpressionWitnessKind",
                "ACTIVATION_LOCAL_MAP_REF_SYMBOL_WITNESS");
        result.addProperty("mapExpressionWitnessObjectToken", mapToken);
        result.addProperty("mapExpressionWitnessObjectTokenScope",
                activationId);
        result.addProperty("mapExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");

        JsonObject binding = result.getAsJsonArray("entryFieldBindings")
                .get(0).getAsJsonObject();
        binding.addProperty("baseInputSymbol", baseInputSymbol);
        if ("REGION.P.in.9".equals(baseInputSymbol)) {
            binding.add("fieldExpression", symbol("Z",
                    "M_Z_field_" + dynamicFieldSymbol + "_enabled"));
            binding.addProperty("fieldSignature",
                    "<example.Value: boolean enabled>");
            binding.addProperty("fieldJavaType", "boolean");
            JsonArray fieldPath = new JsonArray();
            fieldPath.add("enabled");
            binding.add("fieldPath", fieldPath);
        }
        binding.addProperty("fieldExpressionAuthority",
                "EXACT_VM_BRANCH_MAPPING_DYNAMIC_SYMBOL_AND_REQUESTED_"
                        + "SLICE_BASE_V1");
        binding.addProperty("observationStateBindingAuthority",
                "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1");

        JsonObject proof = new JsonObject();
        proof.addProperty("schemaVersion", 1);
        proof.addProperty("kind",
                "NON_MUTATING_MAP_ENTRY_READ_STATE_BASE");
        proof.addProperty("statePort", statePort);
        proof.addProperty("observationId", id);
        proof.addProperty("entryReadObservationId", id);
        proof.addProperty("regionId", region);
        proof.addProperty("activationId", activationId);
        proof.addProperty("baseInputSymbol", baseInputSymbol);
        proof.addProperty("dynamicBindingId", dynamicBindingId);
        proof.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
        proof.add("mapExpression", mapExpression.deepCopy());
        proof.addProperty("expressionAuthority",
                "ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1");
        proof.addProperty("backingMapObjectToken", mapToken);
        proof.addProperty("objectTokenScope", activationId);
        proof.addProperty("mapExpressionWitnessSchemaVersion", 1);
        proof.addProperty("mapExpressionWitnessKind",
                "ACTIVATION_LOCAL_MAP_REF_SYMBOL_WITNESS");
        proof.addProperty("mapExpressionWitnessObjectToken", mapToken);
        proof.addProperty("mapExpressionWitnessObjectTokenScope",
                activationId);
        proof.addProperty("mapExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");
        proof.addProperty("selectorDigest", selectorDigest);
        proof.addProperty("statePortDerivationAuthority",
                "REGION_AND_STATIC_OBSERVATION_SELECTOR_SHA256_V1");
        proof.addProperty("authority",
                "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1");
        proof.addProperty("complete", true);
        result.add("stateBaseProof", proof);
        return result;
    }

    private static JsonObject runtimeDynamicFieldBinding(
            String observationId, String dynamicFieldSymbol,
            String activationId) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        result.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicFieldSymbol);
        result.addProperty("baseInputSymbol", "REGION.P.in.3");
        result.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
        result.addProperty("materializationSiteId",
                "<example.Store: void prune()>#u4");
        result.addProperty("materializationOccurrence",
                dynamicFieldSymbol.endsWith(".2") ? 2 : 1);
        result.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        result.add("fieldPath", fieldPath);
        result.addProperty("leafOwnerObjectToken", 41);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope", activationId);
        result.addProperty("entryReadObservationId", observationId);
        result.add("keyExpression", constant("I", "Y_I_7"));
        result.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        result.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject runtimeContainerFieldBinding(
            String dynamic, int index, String activationId) {
        String bindingId = "BIND_ARRAY_" + index;
        String method = "<example.Store: void update(example.Keys)>";
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 3);
        result.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        result.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        result.addProperty("baseInputSymbol", "REGION.P.in.3");
        result.addProperty("dynamicFieldSymbol", dynamic);
        result.addProperty("materializationSiteId",
                method + "#u" + (14 + 10 * index));
        result.addProperty("materializationOccurrence", 1);
        result.addProperty("fieldSignature",
                "<example.Key: long expiry>");
        JsonArray path = new JsonArray();
        path.add("expiry");
        result.add("fieldPath", path);
        result.addProperty("leafOwnerObjectToken", 302L + index);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope", activationId);
        result.addProperty("containerBindingId", bindingId);
        result.addProperty("containerInputPort", "REGION.P.in.4");
        result.addProperty("containerInputCell",
                "<example.Keys: example.Key[] keys>");
        result.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        result.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        result.addProperty("elementIndex", index);
        result.addProperty("elementOccurrence", 1);
        result.addProperty("declaredFieldOwnerClass", "example.Key");
        result.addProperty("declaredFieldType", "long");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", bindingId);
        selector.addProperty("containerInputPort", "REGION.P.in.4");
        selector.addProperty("containerInputCell",
                "<example.Keys: example.Key[] keys>");
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", index);
        selector.addProperty("elementOccurrence", 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("containerObjectToken", 301L);
        selector.addProperty("elementObjectToken", 302L + index);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", activationId);
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);
        result.add("containerSelector", selector);
        result.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE");
        result.addProperty("complete", true);
        return result;
    }

    private static JsonArray runtimeMapProjectionFieldBindings(
            String operation) {
        JsonArray result = new JsonArray();
        JsonArray tokens = new JsonArray();
        tokens.add(601L);
        tokens.add(602L);
        JsonArray keys = new JsonArray();
        keys.add(constant("java/lang/Integer", "Y_I_11"));
        keys.add(constant("java/lang/Integer", "Y_I_22"));
        for (int index = 0; index < 2; index++) {
            String dynamic = "REGION.P.in.5.field.cccccccccccc.occ."
                    + (index + 1);
            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 3);
            binding.addProperty("kind",
                    "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
            binding.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            binding.addProperty("baseInputSymbol", "REGION.P.in.5");
            binding.addProperty("dynamicFieldSymbol", dynamic);
            binding.addProperty("materializationSiteId",
                    "SITE.MAP#map-element:BIND.MAP.FIELD");
            binding.addProperty("materializationOccurrence", index + 1);
            binding.addProperty("fieldSignature",
                    "<example.Value: long expiry>");
            JsonArray path = new JsonArray();
            path.add("expiry");
            binding.add("fieldPath", path);
            binding.addProperty("leafOwnerObjectToken", 601L + index);
            binding.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            binding.addProperty("objectTokenScope", "ACT.P");
            binding.addProperty("fieldJavaType", "long");
            binding.add("entrySnapshotElementObjectTokens",
                    tokens.deepCopy());
            binding.add("entrySnapshotMapKeyExpressions",
                    keys.deepCopy());
            binding.addProperty("entryKeyExpressionAuthority",
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
            binding.addProperty("entrySetViewOrderAuthority",
                    "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY");
            binding.addProperty("runtimeSymbolizationAuthority",
                    "EXACT_SYMBOLIZE_FIELD_OBSERVATION_AND_SYMBOLIZED_INPUT");
            binding.addProperty("projectionEvidenceAuthority",
                    "UNIQUE_ENTRYSET_KEYED_SNAPSHOT_AND_OUTPUT_IDENTITY_"
                            + "VALIDATION");
            binding.addProperty("outputValidationMode",
                    "ROOT_RETURN_PROJECTED_FIELD");
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
            selector.addProperty("bindingId", "BIND.MAP.FIELD");
            selector.addProperty("mapInputPort", "REGION.P.in.5");
            selector.addProperty("mapInputCell",
                    "<example.Producer: java.util.Map values>");
            selector.addProperty("outputPort", "REGION.P.out.2");
            selector.addProperty("outputCell",
                    "<example.Payload: example.Value[] values>");
            selector.addProperty("mapProjectionOperation", operation);
            selector.addProperty("outputIndex", index);
            selector.addProperty("elementOccurrence", index + 1);
            selector.addProperty("declaredFieldOwnerClass",
                    "example.Value");
            selector.addProperty("declaredFieldType", "long");
            selector.addProperty("declaredFieldSignature",
                    "<example.Value: long expiry>");
            selector.addProperty("mapObjectToken", 501L);
            selector.addProperty("elementObjectToken", 601L + index);
            selector.addProperty("outputArrayObjectToken", 701L);
            selector.addProperty("outputIdentityVerified", true);
            selector.addProperty("outputVerificationAuthority",
                    "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
            selector.addProperty("mapImplementationClass",
                    "java.util.LinkedHashMap");
            selector.addProperty("mapImplementationAuthority",
                    "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_"
                            + "LINKEDHASHMAP_JAVA_EQUALS_HASHCODE_"
                            + "EXTENSIONAL_V1");
            selector.addProperty("entryConcreteFieldValueCaptured", true);
            selector.addProperty("noInterveningFieldWriteVerified", true);
            selector.addProperty("outputFieldValueVerified", true);
            selector.addProperty("fieldValueFlowAuthority",
                    "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                            + "DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_"
                            + "INTERVENING_RUNTIME_FIELD_WRITE_AND_EXACT_"
                            + "OUTPUT_RECHECK");
            selector.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            selector.addProperty("objectTokenScope", "ACT.P");
            selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
            selector.add("expectedMapKey", keys.get(index).deepCopy());
            selector.addProperty("expectedMapKeyAuthority",
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
            selector.addProperty("sourceOutputIndexAuthority",
                    "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY");
            selector.addProperty("replaySelectionAuthority",
                    "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                            + "EXACT_OUTPUT_IDENTITY");
            selector.addProperty("authority",
                    "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                            + "EXACT_OUTPUT_IDENTITY");
            selector.addProperty("complete", true);
            binding.add("mapProjectionSelector", selector);
            binding.addProperty("authority",
                    "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                            + "EXACT_OUTPUT_IDENTITY");
            binding.addProperty("complete", true);
            result.add(binding);
        }
        return result;
    }

    private static JsonArray runtimeMapProjectionFieldBindingsWithKeys(
            JsonArray keys) {
        if (keys == null || keys.size() != 2) {
            throw new IllegalArgumentException("exactly two map keys needed");
        }
        JsonArray result = runtimeMapProjectionFieldBindings(
                "MAP_VALUES_VIEW");
        for (int index = 0; index < result.size(); index++) {
            JsonObject binding = result.get(index).getAsJsonObject();
            binding.add("entrySnapshotMapKeyExpressions", keys.deepCopy());
            binding.getAsJsonObject("mapProjectionSelector").add(
                    "expectedMapKey", keys.get(index).deepCopy());
        }
        return result;
    }

    private static JsonObject closedPathManifest(JsonObject summary) {
        OutputClosureContract contract = OutputClosureCodec.decode(summary);
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "REGION_PATH_WORKLIST");
        result.addProperty("regionId", summary.get(
                "regionId").getAsString());
        result.addProperty("state", RegionPathWorklist.State.CLOSED.name());
        JsonObject bounds = new JsonObject();
        bounds.addProperty("maxPathsPerRegion", 64);
        bounds.addProperty("maxFlipsPerPath", 32);
        bounds.addProperty("maxTasks", 256);
        bounds.addProperty("maxWallClockMillis", 30_000L);
        result.add("bounds", bounds);
        result.add(OutputClosureContract.FIELD, contract.toJson());
        result.add("gaps", new JsonArray());
        return result;
    }

    private static JsonObject bindingForPort(JsonObject projection,
                                             String portId) {
        for (JsonElement element : projection.getAsJsonArray("bindings")) {
            JsonObject binding = element.getAsJsonObject();
            if (portId.equals(binding.get("portId").getAsString())) {
                return binding;
            }
        }
        throw new AssertionError("missing port binding " + portId
                + " in " + projection);
    }

    private static String selectorInLine(JsonArray catalog, String smtLine) {
        for (JsonElement element : catalog) {
            String selector = element.getAsJsonObject().get(
                    "selectorTerm").getAsString();
            if (smtLine.contains(selector)) return selector;
        }
        throw new AssertionError("no case selector in " + smtLine);
    }

    private static int countDeclarationLines(String smt, String... fragments) {
        int count = 0;
        for (String line : smt.split("\\r?\\n")) {
            if (!line.startsWith("(declare-const ")) continue;
            boolean matches = true;
            for (String fragment : fragments) {
                matches &= line.contains(fragment);
            }
            if (matches) count++;
        }
        return count;
    }

    private static int countLines(String text, String... fragments) {
        int count = 0;
        for (String line : text.split("\\r?\\n")) {
            boolean matches = true;
            for (String fragment : fragments) matches &= line.contains(fragment);
            if (matches) count++;
        }
        return count;
    }

    private static java.util.List<String> linesContaining(String text,
                                                          String fragment) {
        java.util.List<String> result = new java.util.ArrayList<>();
        for (String line : text.split("\\r?\\n")) {
            if (line.contains(fragment)) result.add(line);
        }
        return result;
    }

    private static String lineContaining(String text, String fragment) {
        for (String line : text.split("\\r?\\n")) {
            if (line.contains(fragment)) return line;
        }
        return "";
    }

    private static String declaredSymbolContaining(String smt,
                                                   String fragment) {
        for (String line : smt.split("\\r?\\n")) {
            if (!line.startsWith("(declare-const ")
                    || !line.contains(fragment)) continue;
            int start = "(declare-const ".length();
            int end = line.indexOf(' ', start);
            if (end > start) return line.substring(start, end);
        }
        return "";
    }

    private static JsonObject arrayValueExpression(
            String javaType, String componentType, boolean complete,
            JsonElement... values) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ArrayValueExpression");
        result.addProperty("_schema_version", 1);
        result.addProperty("_java_type", javaType);
        result.addProperty("_component_java_type", componentType);
        result.addProperty("_concrete_length", values.length);
        result.add("_length_exp", constant("I", "Y_I_" + values.length));
        result.addProperty("_elements_complete", complete);
        result.addProperty("_authority", "VM_EXACT_FINITE_ARRAY_VALUE_V1");
        JsonArray elements = new JsonArray();
        for (int index = 0; index < values.length; index++) {
            JsonObject element = new JsonObject();
            element.addProperty("index", index);
            JsonObject expression = values[index].getAsJsonObject();
            String type = expression.get("_type").getAsString();
            String raw = expression.has("_exp")
                    ? expression.get("_exp").getAsString() : "";
            element.addProperty("provenance", "N".equals(raw)
                    ? "CONCRETE_NULL" : "ConstExpr".equals(type)
                    ? "CONCRETE_PRIMITIVE" : "SYMBOLIC_ELEMENT");
            element.add("expression", values[index].deepCopy());
            elements.add(element);
        }
        result.add("_elements", elements);
        return result;
    }

    private static JsonObject engineArrayInputBinding(
            String activationId, String inputPort, String inputCell,
            String descriptor, String engineArrayId, long objectToken,
            JsonElement... values) {
        JsonObject expression = arrayValueExpression(descriptor,
                descriptor.substring(1), true, values);
        expression.addProperty("_engine_array_id", engineArrayId);
        expression.addProperty("_engine_array_id_authority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 2);
        result.addProperty("kind", "ENGINE_ARRAY_INPUT_BINDING");
        result.addProperty("sourceActivationId", activationId);
        result.addProperty("inputPort", inputPort);
        result.addProperty("inputCell", inputCell);
        result.addProperty("inputJavaTypeDescriptor", descriptor);
        result.addProperty("engineArrayId", engineArrayId);
        result.addProperty("arrayObjectToken", objectToken);
        result.add("arrayValueExpression", expression);
        return result;
    }

    private static JsonArray singleton(JsonElement value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray singletonString(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static void installArrayProducerFlow(
            Fixture fixture, String producerCell, String consumerCell,
            JsonElement outputExpression) throws Exception {
        addRegionPort(fixture, "REGION.P", "outputs",
                port("REGION.P.out.2", producerCell));
        addRegionPort(fixture, "REGION.F", "symbolicInputs",
                port("REGION.F.in.8", consumerCell));
        JsonObject summary = producerSummary(singlePutEffect(), true);
        summary.getAsJsonObject("outputExpressions").add(
                "REGION.P.out.2", outputExpression.deepCopy());
        JsonArray bindings = new JsonArray();
        bindings.add(runtimeEdgeBinding("REGION.P",
                "REGION.P@fixture#call1", "REGION.P.out.0",
                "REGION.F", "REGION.F@fixture#call2", "REGION.F.in.0",
                10, 30, 101));
        bindings.add(runtimeEdgeBinding("REGION.P",
                "REGION.P@fixture#call1", "REGION.P.out.2",
                "REGION.F", "REGION.F@fixture#call2", "REGION.F.in.8",
                11, 31, 102));
        summary.add("edgeBindings", bindings);
        writeSummary(fixture, summary);
        installFatalRelations(fixture, bindings);
    }

    private static void installTwoEntryContainerEvidence(JsonObject summary) {
        String method = "<example.Store: void update(example.Keys)>";
        String outputCell = "<example.Producer: java.util.Map state>";
        JsonObject slice = summary.getAsJsonObject(
                OutputClosureContract.FIELD).getAsJsonArray("members")
                .get(0).getAsJsonObject().getAsJsonObject("slice");
        slice.getAsJsonArray("inputPorts").add("REGION.P.in.3");
        slice.getAsJsonArray("inputPorts").add("REGION.P.in.4");
        slice.getAsJsonArray("methods").add(method);
        slice.addProperty("requestedStateTransformerContractVersion", 1);
        slice.addProperty("requestedStateTransformerContractApplicable",
                true);
        slice.addProperty("requestedStateTransformerContractOutputPort",
                "REGION.P.out.0");
        slice.addProperty("requestedStateTransformerContractOutputCell",
                outputCell);
        slice.addProperty("requestedStateTransformerContractComplete", true);
        slice.addProperty("requestedStateTransformerContractAuthority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1");
        slice.add("requestedStateTransformerContractIssues",
                new JsonArray());

        JsonArray declarations = new JsonArray();
        JsonArray obligations = new JsonArray();
        JsonArray runtimeBindings = new JsonArray();
        for (int index = 0; index < 2; index++) {
            String bindingId = "BIND_ARRAY_" + index;
            String fieldSite = method + "#u" + (14 + 10 * index);
            String arraySite = method + "#u" + (13 + 10 * index);
            String transformerSite = method + "#u" + (17 + 10 * index);
            JsonArray proof = new JsonArray();
            for (String prefix : new String[]{
                    "CONTAINER_", "LOAD_", "PROJECT_", "READ_",
                    "PUT_KEY_", "PUT_VALUE_"}) {
                String edgeId = prefix + index;
                proof.add(edgeId);
                slice.getAsJsonArray("causalEdgeIds").add(edgeId);
            }
            slice.getAsJsonArray("sites").add(fieldSite);
            slice.getAsJsonArray("sites").add(arraySite);
            slice.getAsJsonArray("sites").add(transformerSite);
            slice.getAsJsonArray("staticSites").add(fieldSite);
            slice.getAsJsonArray("staticSites").add(arraySite);
            slice.getAsJsonArray("staticSites").add(transformerSite);

            JsonObject declaration = new JsonObject();
            declaration.addProperty("schemaVersion", 1);
            declaration.addProperty("kind", "ARRAY_ELEMENT_FIELD");
            declaration.addProperty("bindingId", bindingId);
            declaration.addProperty("baseInputSymbol", "REGION.P.in.3");
            declaration.addProperty("containerInputPort", "REGION.P.in.4");
            declaration.addProperty("containerInputCell",
                    "<example.Keys: example.Key[] keys>");
            declaration.addProperty("selectorAuthority",
                    "EXACT_ARRAY_INDEX");
            declaration.addProperty("elementIndex", index);
            declaration.addProperty("elementOccurrence", 1);
            declaration.add("fieldPath", singletonString("expiry"));
            declaration.addProperty("declaredFieldSignature",
                    "<example.Key: long expiry>");
            declaration.addProperty("declaredFieldOwnerClass",
                    "example.Key");
            declaration.addProperty("declaredFieldType", "long");
            declaration.addProperty("declaredFieldName", "expiry");
            declaration.addProperty("materializationMode",
                    "FIELD_ACCESS_HOOK");
            declaration.addProperty("method", method);
            declaration.addProperty("fieldMaterializationSiteId", fieldSite);
            declaration.addProperty("arrayLoadSiteId", arraySite);
            declaration.addProperty("requestedStateTransformerSiteId",
                    transformerSite);
            declaration.add("proofCausalEdgeIds", proof);
            declaration.addProperty("proofAuthority",
                    "STATIC_EXACT_CONTAINER_ARRAY_FIELD_TO_MAP_PUT_"
                            + "KEY_VALUE_V1");
            declaration.addProperty("complete", true);
            declarations.add(declaration);

            JsonObject obligation = new JsonObject();
            obligation.addProperty("siteId", transformerSite);
            obligation.addProperty("method", method);
            obligation.addProperty("targetCell", outputCell);
            obligation.addProperty("transferKind", "HEAP_WRITE");
            obligation.addProperty("kind", "field_mutation");
            obligation.add("causalEdgeIds",
                    singletonString("PUT_VALUE_" + index));
            obligation.addProperty("authority",
                    "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL");
            obligations.add(obligation);

            String dynamic = "REGION.P.in.3.field.cccccccccccc.occ."
                    + (index + 1);
            JsonObject fieldExpression = symbol("J",
                    "M_J_field_" + dynamic + "_example/Key");
            summary.getAsJsonArray("pathCondition").add(binaryCondition(
                    fieldExpression.deepCopy(), "==",
                    constant("J", "Y_J_" + (11 + 11 * index))));
            JsonObject runtime = runtimeContainerFieldBinding(dynamic, index,
                    summary.get("activationId").getAsString());
            runtime.add("fieldExpression", fieldExpression);
            runtime.addProperty("fieldJavaType", "long");
            runtimeBindings.add(runtime);
        }
        slice.add("containerElementFieldBindings", declarations);
        slice.add("requestedStateTransformerObligations", obligations);
        summary.add("dynamicFieldBindings", runtimeBindings);
    }

    private static void writeSummary(Fixture fixture, JsonObject summary)
            throws Exception {
        Files.write(fixture.summaries,
                (canonicalSummary(summary) + "\n").getBytes(
                        StandardCharsets.UTF_8));
    }

    private static JsonObject canonicalSummary(JsonObject summary) {
        if ("GUARDED_PATH_MERGE".equals(summary.has("regionRelation")
                ? summary.getAsJsonObject("regionRelation").get("kind")
                .getAsString() : "")) {
            return summary;
        }
        RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                java.util.Collections.singletonList(summary),
                closedPathManifest(summary));
        return merged.summaries.get(0);
    }

    private static ConcolicSmtComposer.Arguments arguments(Fixture fixture) {
        java.util.List<String> values = new java.util.ArrayList<>(
                java.util.Arrays.asList(
                "--fatal-query", fixture.fatal.toString(),
                "--summaries", fixture.summaries.toString(),
                "--regions", fixture.regions.toString(),
                "--output", fixture.output.toString(),
                "--manifest", fixture.manifest.toString(),
                "--fatal-region", "REGION.F",
                "--activation-id", "ACT.F"));
        return ConcolicSmtComposer.Arguments.parse(
                values.toArray(new String[0]));
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }

    private static void assertZ3Parses(String smt) throws Exception {
        Process process = new ProcessBuilder("z3", "-in")
                .redirectErrorStream(true).start();
        try (OutputStream input = process.getOutputStream()) {
            input.write(smt.getBytes(StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int count;
        while ((count = process.getInputStream().read(buffer)) >= 0) {
            output.write(buffer, 0, count);
        }
        int exit = process.waitFor();
        String text = new String(output.toByteArray(),
                StandardCharsets.UTF_8);
        assertEquals(text, 0, exit);
        assertFalse(text, text.contains("(error"));
    }

    private static void assertZ3Status(String smt, String expected)
            throws Exception {
        Process process = new ProcessBuilder("z3", "-in")
                .redirectErrorStream(true).start();
        try (OutputStream input = process.getOutputStream()) {
            input.write(smt.getBytes(StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int count;
        while ((count = process.getInputStream().read(buffer)) >= 0) {
            output.write(buffer, 0, count);
        }
        int exit = process.waitFor();
        String text = new String(output.toByteArray(),
                StandardCharsets.UTF_8).trim();
        assertEquals(text, 0, exit);
        assertFalse(text, text.contains("(error"));
        assertTrue(text, text.equals(expected)
                || text.startsWith(expected + "\n"));
    }

    private static Fixture fixture(Path root, boolean includeProducerSummary)
            throws Exception {
        Fixture fixture = new Fixture(root);
        String regions = "{\"regionId\":\"REGION.P\","
                + "\"symbolicInputs\":[{\"portId\":\"REGION.P.in.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.P.in.1\","
                + "\"cell\":\"<example.Source: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.P.in.2\","
                + "\"cell\":\"<example.Cache: int cachedValue>\"},"
                + "{\"portId\":\"REGION.P.in.3\","
                + "\"cell\":\"<example.Value: long expiry>\"},"
                + "{\"portId\":\"REGION.P.in.4\","
                + "\"cell\":\"<example.Keys: example.Key[] keys>\"},"
                + "{\"portId\":\"REGION.P.in.5\","
                + "\"cell\":\"<example.Producer: java.util.Map values>\"}],"
                + "\"outputs\":[{\"portId\":\"REGION.P.out.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.P.out.1\","
                + "\"cell\":\"<example.Codec: java.lang.String encode(int)>"
                + ".return\"},{\"portId\":\"REGION.P.out.2\","
                + "\"cell\":\"<example.Payload: example.Value[] values>\"}]}\n"
                + "{\"regionId\":\"REGION.F\","
                + "\"symbolicInputs\":[{\"portId\":\"REGION.F.in.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.F.in.1\","
                + "\"cell\":\"<example.Request: int key>\"},"
                + "{\"portId\":\"REGION.F.in.2\","
                + "\"cell\":\"<example.Transport: java.lang.String value>\"},"
                + "{\"portId\":\"REGION.F.in.3\","
                + "\"cell\":\"<example.Store: int currentValue>\"},"
                + "{\"portId\":\"REGION.F.in.4\","
                + "\"cell\":\"<example.Clock: long now>\"},"
                + "{\"portId\":\"REGION.F.in.5\","
                + "\"cell\":\"<example.Policy: long updateInterval>\"},"
                + "{\"portId\":\"REGION.F.in.6\","
                + "\"cell\":\"<example.Policy: long lifetime>\"},"
                + "{\"portId\":\"REGION.F.in.7\","
                + "\"cell\":\"<example.Protocol: int constant>\"}],"
                + "\"outputs\":[]}\n";
        regions += "{\"regionId\":\"REGION.D\","
                + "\"symbolicInputs\":[{\"portId\":\"REGION.D.in.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"}],"
                + "\"outputs\":[]}\n";
        Files.write(fixture.regions, canonicalRegions(regions).getBytes(
                StandardCharsets.UTF_8));

        String context = "{\"regionInstanceId\":"
                + "\"REGION.F@fixture#call2\","
                + "\"equalityClasses\":[{\"members\":["
                + "\"REGION.P.out.0\",\"REGION.F.in.0\","
                + "\"REGION.D.in.0\"]}],"
                + "\"equalityRelations\":[],"
                + "\"versionedStateMerges\":[{"
                + "\"edgeId\":\"EDGE.0\","
                + "\"fromEndpoint\":\"REGION.P.out.0\","
                + "\"toEndpoint\":\"REGION.F.in.0\","
                + "\"selectedBindings\":[{"
                + "\"evidenceKind\":\"FIELD_ASSIGNMENT_READ_FROM_V1\","
                + "\"fromRegion\":\"REGION.P\","
                + "\"toRegion\":\"REGION.F\","
                + "\"fromRegionInstance\":"
                + "\"REGION.P@fixture#call1\","
                + "\"toRegionInstance\":"
                + "\"REGION.F@fixture#call2\","
                + "\"fromOutputPort\":\"REGION.P.out.0\","
                + "\"toInputPort\":\"REGION.F.in.0\","
                + "\"writerEventSeq\":10,\"readerEventSeq\":20,"
                + "\"receiverObjectId\":41}]}]}";
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion", 1);
        fatal.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        fatal.addProperty("activationId", "ACT.F");
        fatal.addProperty("regionId", "REGION.F");
        fatal.addProperty("regionInstanceId", "REGION.F@fixture#call2");
        fatal.addProperty("readyForSolver", true);
        JsonArray fatalPath = JsonParser.parseString("[{"
                + "\"_type\":\"MethodExpression\","
                + "\"_name\":\"java/util/HashMap get\","
                + "\"_param_list\":[{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"L\","
                + "\"_exp\":\"M_L_field_REGION.F.in.0_example/Store\"},"
                + "{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"I\","
                + "\"_exp\":\"M_I_field_REGION.F.in.1_example/Request\"}],"
                + "\"_res_exp\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"example/Value\","
                + "\"_exp\":\"map_result\"}},{"
                + "\"_type\":\"BinaryExpression\","
                + "\"_left\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"example/Value\","
                + "\"_exp\":\"map_result\"},\"_op\":\"==\","
                + "\"_right\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"\",\"_exp\":\"N\"}}]")
                .getAsJsonArray();
        setFatalConstraints(fatal, fatalPath);
        fatal.add("symbolicContext", JsonParser.parseString(context));
        Files.write(fixture.fatal, (fatal + "\n").getBytes(
                StandardCharsets.UTF_8));

        if (includeProducerSummary) {
            writeSummary(fixture, producerSummary(singlePutEffect(), true));
        } else {
            Files.write(fixture.summaries, new byte[0]);
        }
        return fixture;
    }

    private static boolean candidateReady(JsonObject manifest) {
        return manifest != null
                && manifest.has("schemaVersion")
                && manifest.get("schemaVersion").getAsInt() == 2
                && "CONCOLIC_COMPOSED_SMT".equals(
                manifest.get("kind").getAsString())
                && "CANDIDATE_ONLY".equals(
                manifest.get("trustState").getAsString())
                && "CANDIDATE_READY".equals(
                manifest.get("state").getAsString());
    }

    private static final class Fixture {
        private final Path fatal;
        private final Path summaries;
        private final Path regions;
        private final Path output;
        private final Path manifest;

        private Fixture(Path root) {
            fatal = root.resolve("fatal.jsonl");
            summaries = root.resolve("summaries.jsonl");
            regions = root.resolve("regions.jsonl");
            output = root.resolve("composed.smt2");
            manifest = root.resolve("manifest.json");
        }
    }
}
