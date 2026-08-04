package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSmtComposerTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void boxedIntegralTagsAcceptPrimitiveAndWrapperTypes() {
        String[] primitives = {"B", "C", "S", "I", "J"};
        String[] wrappers = {"java.lang.Byte", "java/lang/Character",
                "Ljava/lang/Short;", "java.lang.Integer",
                "java/lang/Long"};
        String[] tags = {"Byte", "Char", "Short", "Int", "Long"};
        for (int index = 0; index < tags.length; index++) {
            assertEquals("(V" + tags[index] + " 4)",
                    ContainerSmtCodec.boxIntegral(
                            "4", primitives[index]));
            assertEquals("(V" + tags[index] + " 4)",
                    ContainerSmtCodec.boxIntegral(
                            "4", wrappers[index]));
            assertEquals("(value" + tags[index] + " value)",
                    ContainerSmtCodec.unboxIntegral(
                            "value", wrappers[index]));
        }
    }

    @Test
    public void recursivelySelectsDifferentInstancesOfOneStaticRegion()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        String holderInstance = "REGION.1@Test#call10";
        JsonObject outerToFatal = binding("EDGE.SHARED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject holderToOuter = binding("EDGE.SHARED", holderInstance,
                "REGION.1.out.0", outerInstance, "REGION.1.in.0", 10, 20);
        JsonObject unrelated = binding("EDGE.UNRELATED",
                "REGION.1@Test#call99", "REGION.1.out.0",
                "REGION.0@Test#call99", "REGION.0.in.0", 90, 99);

        RelationSummary outer = summary("OUTER", outerInstance, 20, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(outerToFatal));
        RelationSummary holder = summary("HOLDER", holderInstance, 10, 20,
                Collections.<String>emptyList(),
                Collections.singletonList(holderToOuter));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(outer, holder), outerToFatal, unrelated);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertFalse(result.smtLib,
                result.smtLib.contains("ConflictingProducerRegionInstance"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call20"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call10"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_0_0"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_1_1"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call99"));
        assertEquals(1, result.manifest.getAsJsonArray(
                "resolvedEdgeBindings").size());
        assertEquals("EDGE.SHARED", result.manifest.getAsJsonArray(
                "resolvedEdgeBindings").get(0).getAsString());
    }

    @Test
    public void differentInstancesDoNotShareOneStaticPortSymbol()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        String holderInstance = "REGION.1@Test#call10";
        JsonObject outerToFatal = binding("EDGE.OUTER", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject holderToOuter = binding("EDGE.HOLDER", holderInstance,
                "REGION.1.out.0", outerInstance, "REGION.1.in.0", 10, 20);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(
                        summary("OUTER", outerInstance, 20, 10,
                                Collections.singletonList("REGION.1.in.0"),
                                Collections.singletonList(outerToFatal)),
                        summary("HOLDER", holderInstance, 10, 20,
                                Collections.<String>emptyList(),
                                Collections.singletonList(holderToOuter))),
                outerToFatal);

        String outerPort =
                "port__REGION_1_out_0__instance__REGION_1_Test_call20";
        String holderPort =
                "port__REGION_1_out_0__instance__REGION_1_Test_call10";
        assertTrue(result.smtLib.contains("(declare-const " + outerPort));
        assertTrue(result.smtLib.contains("(declare-const " + holderPort));
        assertTrue(result.smtLib.contains(
                "(= " + outerPort + " (VInt 10))"));
        assertTrue(result.smtLib.contains(
                "(= " + holderPort + " (VInt 20))"));
        assertFalse(result.smtLib.contains(
                "(= " + outerPort + " " + holderPort + ")"));
    }

    @Test
    public void jointClosureMayCoverASingleDemand() throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call10";
        JsonObject toFatal = binding("EDGE.JOINT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 10, 30);
        RelationSummary singleton = summary("JOINT", producerInstance,
                10, 7, Collections.<String>emptyList(),
                Collections.singletonList(toFatal));
        JsonObject row = singleton.toJson();

        JsonObject secondSlice = emptySlice("REGION.1.out.1",
                "<Test: int other>");
        OutputClosureContract second = OutputClosureCodec.singleton(
                "REGION.1", producerInstance, 10, "REGION.1.out.1",
                "<Test: int other>", "REGION_OUTPUT", "int",
                secondSlice);
        OutputClosureContract joint = OutputClosureCodec.merge(Arrays.asList(
                singleton.outputClosure(), second));
        OutputClosureCodec.writeTo(row, joint);
        row.getAsJsonObject("regionRelation").getAsJsonArray("cases")
                .get(0).getAsJsonObject()
                .getAsJsonObject("outputExpressions")
                .add("REGION.1.out.1", integer(9));
        JsonObject producerRegion = region("REGION.1", "", "int");
        producerRegion.getAsJsonArray("outputs").add(
                port("REGION.1.out.1", false));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(RelationSummary.decode(row)),
                Arrays.asList(region("REGION.0", "int", ""),
                        producerRegion),
                toFatal);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib.contains(
                "port__REGION_1_out_0__instance__REGION_1_Test_call10"));
        assertTrue(result.smtLib.contains(
                "port__REGION_1_out_1__instance__REGION_1_Test_call10"));
    }

    @Test
    public void boxedFieldValueUsesPrimitiveCarrierAcrossInvocations()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String consumerInstance = "REGION.1@Test#call20";
        String producerInstance = "REGION.1@Test#call10";
        JsonObject toFatal = binding("EDGE.BOXED.CONSUMER",
                consumerInstance, "REGION.1.out.0", fatalInstance,
                "REGION.0.in.0", 20, 30);
        JsonObject toConsumer = binding("EDGE.BOXED.PRODUCER",
                producerInstance, "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 10, 20);
        JsonObject boxedInput = new JsonObject();
        boxedInput.addProperty("_type", "SymbolExpression");
        boxedInput.addProperty("_java_type", "L");
        boxedInput.addProperty("_exp", "REGION.1.in.0");

        RelationSummary consumer = summary("BOXED_CONSUMER",
                consumerInstance, 20, boxedInput,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(toFatal, toConsumer),
                "java.lang.Integer");
        JsonObject consumerRow = consumer.toJson();
        JsonObject owner = new JsonObject();
        owner.addProperty("_type", "SymbolExpression");
        owner.addProperty("_java_type", "LTest$Box;");
        owner.addProperty("_exp", "BOX_OWNER");
        JsonObject field = new JsonObject();
        field.addProperty("_type", "FieldAccessExpression");
        field.addProperty("_java_type", "L");
        field.addProperty("ownerClass", "Test$Box");
        field.addProperty("fieldOffset", 24);
        field.add("owner", owner);
        JsonObject materialization = binary(field, "==", boxedInput);
        materialization.addProperty("_code_position",
                "static void java.lang.System.symbolizeExactField("
                        + "jobject, jobject, jobject, jobject, jobject):-1");
        consumerRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject()
                .getAsJsonObject("guard").getAsJsonArray("conditions")
                .add(materialization);
        consumer = RelationSummary.decode(consumerRow);
        RelationSummary producer = summary("BOXED_PRODUCER",
                producerInstance, 10, integer(-15),
                Collections.<String>emptyList(),
                Collections.singletonList(toConsumer),
                "java.lang.Integer");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, producer),
                Arrays.asList(region("REGION.0", "int", ""),
                        region("REGION.1", "java.lang.Integer",
                                "java.lang.Integer")),
                toFatal);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        String inputPort =
                "port__REGION_1_in_0__instance__REGION_1_Test_call20";
        String inputValue =
                "sym__port__REGION_1_Test_call20_REGION_1_in_0__int";
        assertTrue(result.smtLib, result.smtLib.contains(
                "(= " + inputPort + " (VInt " + inputValue + "))"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "sym__port__REGION_1_Test_call20_REGION_1_in_0"
                        + "__boxed_ref Ref"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= " + inputPort + " (VRef "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(= port__REGION_1_out_0__instance__REGION_1_Test_call10"
                        + " (VInt (- 15)))"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_1_1"));
    }

    @Test
    public void compositionUsesTheSameBoxedIntegralContainerTags()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.TAGGED", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject cleared = associativeOperation("CLEAR",
                associativeState("UNUSED_MAP"));
        JsonObject withByte = associativeOperation("PUT", cleared,
                typedIntegral("B", 7), typedIntegral("B", 9));
        JsonObject byteResult = associativeRead(
                withByte, typedIntegral("B", 7), "B");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("TAGGED",
                        producerInstance, 20, byteResult,
                        Collections.<String>emptyList(),
                        Collections.singletonList(edge))), edge);

        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains("(VByte 7)"));
        assertTrue(result.smtLib, result.smtLib.contains("(VByte 9)"));
        assertTrue(result.smtLib, result.smtLib.contains("(valueByte "));
        for (String tag : new String[]{"Byte", "Char", "Short", "Int",
                "Long"}) {
            assertTrue(result.smtLib,
                    result.smtLib.contains("(V" + tag + " (value"
                            + tag + " Int))"));
        }
    }

    @Test
    public void competingSummariesForOneInvocationStillFailClosed()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject producerToFatal = binding("EDGE.CONFLICT",
                producerInstance, "REGION.1.out.0", fatalInstance,
                "REGION.0.in.0", 20, 30);

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(
                        summary("FIRST", producerInstance, 20, 10,
                                Collections.<String>emptyList(),
                                Collections.singletonList(producerToFatal)),
                        summary("SECOND", producerInstance, 20, 11,
                                Collections.<String>emptyList(),
                                Collections.singletonList(producerToFatal))),
                producerToFatal);

        assertEquals("CANDIDATE_WITH_GAPS",
                result.manifest.get("state").getAsString());
        assertTrue(result.manifest.toString(),
                result.manifest.toString().contains(
                        "AmbiguousExactProducerSummary"));
        assertTrue(result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void manifestsCanonicalScalarTermsByDynamicOccurrence()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String producerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.INPUT", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject input = new JsonObject();
        input.addProperty("_type", "SymbolExpression");
        input.addProperty("_java_type", "I");
        input.addProperty("_exp", "REGION.1.in.0");

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(summary("INPUT", producerInstance,
                        20, input,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge))),
                edge);

        JsonArray catalog = result.manifest.getAsJsonArray(
                "canonicalPortOccurrences");
        assertEquals(result.manifest.toString(), 1, catalog.size());
        JsonObject occurrence = catalog.get(0).getAsJsonObject();
        assertEquals("REGION.1.in.0",
                occurrence.get("portId").getAsString());
        assertEquals(producerInstance,
                occurrence.get("regionInstanceId").getAsString());
        assertEquals("INT", occurrence.get("sort").getAsString());
        assertEquals(
                "sym__port__REGION_1_Test_call20_REGION_1_in_0__int",
                occurrence.get("solverTerm").getAsString());
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries,
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows,
            JsonObject... firstHops) throws Exception {
        Path directory = temporary.newFolder().toPath();
        Path fatal = directory.resolve("fatal.jsonl");
        Path summaryFile = directory.resolve("summaries.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("candidate.smt2");
        Path manifest = directory.resolve("manifest.json");

        writeJsonl(fatal, fatalQuery(fatalInstance, firstHops));
        StringBuilder encoded = new StringBuilder();
        for (RelationSummary summary : summaries) {
            encoded.append(summary.toJson()).append('\n');
        }
        Files.write(summaryFile, encoded.toString().getBytes(
                StandardCharsets.UTF_8));
        writeJsonl(regions, regionRows.toArray(
                new JsonObject[regionRows.size()]));

        ConcolicSmtComposer.Arguments arguments =
                ConcolicSmtComposer.Arguments.parse(new String[]{
                        "--fatal-query", fatal.toString(),
                        "--summaries", summaryFile.toString(),
                        "--regions", regions.toString(),
                        "--output", output.toString(),
                        "--manifest", manifest.toString(),
                        "--fatal-region", "REGION.0",
                        "--region-instance-id", fatalInstance
                });
        return ConcolicSmtComposer.compose(arguments);
    }

    private static RelationSummary summary(
            String id, String instance, long call, int value,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, call, integer(value), inputPorts,
                bindings);
    }

    private static RelationSummary summary(
            String id, String instance, long call, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, call, output, inputPorts, bindings,
                "int");
    }

    private static RelationSummary summary(
            String id, String instance, long call, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings, String outputJavaType) {
        JsonObject slice = emptySlice("REGION.1.out.0",
                "<Test: " + outputJavaType + " output>");
        JsonArray inputs = new JsonArray();
        for (String input : inputPorts) inputs.add(input);
        slice.add("inputPorts", inputs);
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REGION.1", instance, call, "REGION.1.out.0",
                "<Test: " + outputJavaType + " output>", "REGION_OUTPUT",
                outputJavaType, slice);

        JsonObject row = new JsonObject();
        row.addProperty("summaryId", "SUMMARY." + id);
        row.addProperty("regionId", "REGION.1");
        row.addProperty("regionInstanceId", instance);
        row.addProperty("rootCallId", call);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray encodedBindings = new JsonArray();
        for (JsonObject binding : bindings) {
            encodedBindings.add(binding.deepCopy());
        }
        row.add("edgeBindings", encodedBindings);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE." + id);
        path.addProperty("sourceTaskId", "TASK." + id);
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", output);
        path.add("outputExpressions", outputs);
        JsonArray cases = new JsonArray();
        cases.add(path);
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        return RelationSummary.decode(row);
    }

    private static JsonObject emptySlice(String port, String cell) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("causalEdges", new JsonArray());
        return slice;
    }

    private static JsonObject fatalQuery(
            String fatalInstance, JsonObject... firstHops) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion", 1);
        fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("regionInstanceId", fatalInstance);
        fatal.addProperty("targetSiteId", "<Test: void consume()>#u1");
        fatal.addProperty("constraintAuthority",
                "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1");
        JsonObject path = new JsonObject();
        path.add("constraints", new JsonArray());
        JsonArray paths = new JsonArray();
        paths.add(path);
        fatal.add("paths", paths);
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPc(
                "<Test: void consume()>#u1", "<Test: void consume()>",
                1, 1, false, binary(integer(0), "==", integer(0)),
                0, metadata);
        fatal.add("seedReplayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), witness).toJson());

        JsonArray merges = new JsonArray();
        for (JsonObject firstHop : firstHops) {
            JsonObject relation = new JsonObject();
            relation.addProperty("edgeId",
                    firstHop.get("edgeId").getAsString());
            relation.addProperty("fromEndpoint", "REGION.1.out.0");
            relation.addProperty("toEndpoint", "REGION.0.in.0");
            JsonArray selected = new JsonArray();
            selected.add(firstHop.deepCopy());
            relation.add("selectedBindings", selected);
            merges.add(relation);
        }
        JsonObject context = new JsonObject();
        context.addProperty("regionInstanceId", fatalInstance);
        context.add("equalityClasses", new JsonArray());
        context.add("equalityRelations", new JsonArray());
        context.add("versionedStateMerges", merges);
        context.add("alternativeWriterGroups", new JsonArray());
        fatal.add("symbolicContext", context);
        return fatal;
    }

    private static JsonObject binding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort, long writer, long reader) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("toRegion", regionOf(toPort));
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toInputPort", toPort);
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("writerEventSeq", writer);
        binding.addProperty("readerEventSeq", reader);
        binding.addProperty("receiverObjectId", 7);
        return binding;
    }

    private static JsonObject region(
            String id, boolean hasInput, boolean hasOutput) {
        return region(id, hasInput ? "int" : "",
                hasOutput ? "int" : "");
    }

    private static JsonObject region(
            String id, String inputType, String outputType) {
        JsonObject region = new JsonObject();
        region.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        if (!inputType.isEmpty()) {
            inputs.add(port(id + ".in.0", true, inputType));
        }
        region.add("symbolicInputs", inputs);
        JsonArray outputs = new JsonArray();
        if (!outputType.isEmpty()) {
            outputs.add(port(id + ".out.0", false, outputType));
        }
        region.add("outputs", outputs);
        return region;
    }

    private static JsonObject port(String id, boolean input) {
        return port(id, input, "int");
    }

    private static JsonObject port(
            String id, boolean input, String javaType) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", id);
        port.addProperty("cell", input
                ? "<Test: " + javaType + " input>"
                : "<Test: " + javaType + " output>");
        port.addProperty("javaType", javaType);
        return port;
    }

    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject typedIntegral(String javaType, int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", "Y_" + javaType + "_" + value);
        return result;
    }

    private static JsonObject associativeState(String symbol) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "L");
        identity.addProperty("_exp", symbol);
        return associativeOperation("STATE", identity);
    }

    private static JsonObject associativeRead(
            JsonObject receiver, JsonObject key, String javaType) {
        JsonObject read = associativeOperation("READ", receiver, key);
        read.addProperty("_java_type", javaType);
        return read;
    }

    private static JsonObject associativeOperation(
            String operation, JsonObject receiver,
            JsonObject... arguments) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ContainerRelation");
        result.addProperty("shape", "ASSOCIATIVE");
        result.addProperty("operation", operation);
        result.addProperty("_java_type", "L");
        result.add("receiver", receiver);
        JsonArray encoded = new JsonArray();
        for (JsonObject argument : arguments) encoded.add(argument);
        result.add("arguments", encoded);
        return result;
    }

    private static JsonObject binary(
            JsonObject left, String operator, JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static String regionOf(String port) {
        int marker = port.indexOf(".in.");
        return marker < 0 ? port.substring(0, port.indexOf(".out."))
                : port.substring(0, marker);
    }

    private static void writeJsonl(Path path, JsonObject... rows)
            throws Exception {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(row).append('\n');
        Files.write(path, value.toString().getBytes(StandardCharsets.UTF_8));
    }
}
