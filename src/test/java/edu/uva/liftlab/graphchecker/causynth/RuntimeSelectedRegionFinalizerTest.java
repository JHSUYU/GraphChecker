package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeSelectedRegionFinalizerTest {
    private static final Gson GSON = new Gson();
    private static final String METHOD = "<example.Root: void run(example.A)>";
    private static final String WRITER = "<example.Writer: void run()>";
    private static final String TARGET = "<example.Target: void run()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void explicitFaultReturnBecomesActivationLocalBooleanPort()
            throws Exception {
        File skeleton = skeleton("fault-port-skeleton.jsonl");
        String marker = "<edu.uva.liftlab.graphchecker.annotation."
                + "CausynthFault: boolean makeSymbolicBoolean("
                + "java.lang.String)>";
        String local = METHOD + "::rpcFails";
        Map<String, Object> binding = object(
                "regionId", "REGION.1", "rootCallId", 11,
                "callId", 101, "invocationId", 70,
                "callerMethod", METHOD, "unitIndex", 4,
                "siteId", METHOD + "#u4", "eventSeq", 7,
                "primitiveValue", "false", "accessorOccurrence", 1,
                "declaredCallee", marker, "process", "p",
                "authority", "EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1");
        Map<String, Object> markerEdge = object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.fault", "kind", "explicit_symbolic_fault",
                "transferKind", "LOCAL", "method", METHOD,
                "regionIds", Collections.singletonList("REGION.1"),
                "fromCell", marker + ".return", "toCell", local,
                "siteId", METHOD + "#u4", "unitIndex", 4,
                "unit", "rpcFails = staticinvoke " + marker,
                "invoke", marker, "explicitSymbolicFault", true,
                "explicitSymbolicFaultKind", "BOOLEAN",
                "symbolicName", "rpcFails", "runtimeObserved", true,
                "runtimeExplicitFaultBindings",
                Collections.singletonList(binding));
        Map<String, Object> guard = refinedEdge(
                "DF.fault.guard", "exception_guard", "GUARD",
                local, METHOD + "#u20#exception:example.Failure",
                METHOD + "#u9", 9,
                "if rpcFails == 0 goto return", null,
                METHOD + "#u9", true, false);
        File refined = writeRows("fault-port-refined.jsonl",
                markerEdge, guard);
        File regions = new File(folder.getRoot(), "fault-port-regions.jsonl");
        File edges = new File(folder.getRoot(), "fault-port-edges.jsonl");
        Map<String, Object> target = object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", "REGION.1", "rootCallId", 11,
                "selection", "EXCEPTION_CONTEXT",
                "callIds", Collections.singletonList(101L),
                "observedMethods", Collections.singletonList(METHOD),
                "observedFatalTargets", Collections.singletonList(
                        observedFatalTarget(METHOD + "#u9", METHOD,
                                9, 101, true)));

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD),
                Collections.singletonList(target));

        JsonObject region = GSON.fromJson(Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        JsonObject input = region.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject();
        assertEquals("EXPLICIT_SYMBOLIC_FAULT",
                input.get("sourceKind").getAsString());
        assertEquals("boolean", input.get("javaType").getAsString());
        assertEquals(marker + ".return", input.get("cell").getAsString());
        assertEquals(1, input.get("replayOccurrence").getAsInt());
    }

    @Test
    public void refinedGraphBecomesFullRegionState() throws Exception {
        File skeleton = write("skeleton.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD),
                "selection", "EXCEPTION_COMPONENT"));
        Map<String, Object> binding = object(
                "regionId", "REGION.1",
                "rootCallId", 11, "rootKind", "PARAMETER",
                "rootCell", METHOD + ".param0:example.A",
                "rootParameterIndex", 0, "rootObjectId", 10,
                "fieldReceiverObjectId", 30, "valueObjectId", 0,
                "eventSeq", 9,
                "fieldPath", Arrays.asList("b", "c", "d"),
                "fieldPathDeclarations", Arrays.asList(
                        "<example.A: example.B b>",
                        "<example.B: example.C c>",
                        "<example.C: int d>"));
        File refined = write("refined.jsonl", object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.1", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", METHOD,
                "regionIds", Collections.singletonList("REGION.1"),
                "runtimeFieldBindings", Collections.singletonList(binding)));
        File regions = new File(folder.getRoot(), "regions.jsonl");
        File edges = new File(folder.getRoot(), "edges.jsonl");

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD),
                Collections.singletonList(activation(
                        "REGION.1", 11, "EXCEPTION_CONTEXT")));

        JsonObject region = GSON.fromJson(Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        assertEquals(3, region.get("schemaVersion").getAsInt());
        assertEquals("SYMBOLIC_REGION", region.get("kind").getAsString());
        assertEquals(1, region.getAsJsonArray("symbolicInputs").size());
        assertEquals("b", region.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject().getAsJsonArray("fieldPath")
                .get(0).getAsString());
        assertFalse(region.has("planningMode"));
    }

    @Test
    public void fieldBindingIsUsedOnlyByItsConcreteRegionActivation()
            throws Exception {
        File skeleton = writeRows("overlap-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.1", "rootMethod", METHOD,
                        "anchorMethod", METHOD,
                        "methods", Collections.singletonList(METHOD),
                        "selection", "EXCEPTION_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.2", "rootMethod", METHOD,
                        "anchorMethod", METHOD,
                        "methods", Collections.singletonList(METHOD),
                        "selection", "STATE_CONTEXT"));
        Map<String, Object> binding = object(
                "regionId", "REGION.1", "rootCallId", 11,
                "rootKind", "RECEIVER", "rootCell", METHOD + ".receiver",
                "rootObjectId", 10, "fieldReceiverObjectId", 10,
                "valueObjectId", 20, "eventSeq", 9,
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations", Collections.singletonList(
                        "<example.Root: example.A value>"));
        File refined = write("overlap-refined.jsonl", object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.2", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", METHOD,
                "regionIds", Arrays.asList("REGION.1", "REGION.2"),
                "runtimeFieldBindings", Collections.singletonList(binding)));
        File regions = new File(folder.getRoot(), "overlap-regions.jsonl");
        File edges = new File(folder.getRoot(), "overlap-edges.jsonl");

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD),
                Arrays.asList(activation("REGION.1", 11,
                                "EXCEPTION_CONTEXT"),
                        activation("REGION.2", 12, "STATE_CONTEXT")));

        java.util.List<String> rows = Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8);
        JsonObject first = GSON.fromJson(rows.get(0), JsonObject.class);
        assertEquals(1, rows.size());
        assertEquals(1, first.getAsJsonArray("symbolicInputs").size());
    }

    @Test
    public void observedFatalBranchSelectsOnlyThatStaticTargetSite()
            throws Exception {
        File skeleton = skeleton("observed-target-skeleton.jsonl");
        String firstField = "<example.Root: int first>";
        String secondField = "<example.Root: int second>";
        String firstLocal = METHOD + "::$first";
        String secondLocal = METHOD + "::$second";
        File refined = writeRows("observed-target-refined.jsonl",
                heapRead("DF.first", firstField, firstLocal, "first", 3),
                heapRead("DF.second", secondField, secondLocal, "second", 4),
                refinedEdge("DF.first.failure", "exception_guard", "GUARD",
                        firstLocal, METHOD + "#u20#exception:example.First",
                        METHOD + "#u9", 9, "if first == 0 goto throw", null,
                        METHOD + "#u9", true, false),
                refinedEdge("DF.second.failure", "exception_guard", "GUARD",
                        secondLocal, METHOD + "#u21#exception:example.Second",
                        METHOD + "#u10", 10, "if second == 0 goto throw", null,
                        METHOD + "#u10", true, false));
        Map<String, Object> target = object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", "REGION.1", "rootCallId", 11,
                "selection", "EXCEPTION_CONTEXT",
                "callIds", Collections.singletonList(101L),
                "observedMethods", Collections.singletonList(METHOD));
        Map<String, Object> observation = object("kind", "BRANCH",
                "eventSeq", 50L, "method", METHOD, "callId", 101L,
                "siteId", METHOD + "#u10", "outcome", false);
        File regions = new File(folder.getRoot(),
                "observed-target-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "observed-target-edges.jsonl");

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD),
                Collections.singletonList(target),
                Collections.singletonList(observation));

        JsonObject region = GSON.fromJson(Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        assertEquals(1, region.getAsJsonArray("symbolicInputs").size());
        assertEquals(secondField, region.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject()
                .getAsJsonArray("fieldPathDeclarations").get(0)
                .getAsString());
        @SuppressWarnings("unchecked")
        Map<String, Object> evidence = ((List<Map<String, Object>>) target
                .get("observedFatalTargets")).get(0);
        assertEquals(Boolean.FALSE, evidence.get("observedOutcome"));
    }

    @Test
    public void fatalPrefixDropsPostBranchPortsAndTrimsHeapOccurrences()
            throws Exception {
        File skeleton = skeleton("fatal-prefix-skeleton.jsonl");
        String earlyField = "<example.Root: int early>";
        String lateField = "<example.Root: int late>";
        String earlyLocal = METHOD + "::$early";
        String lateLocal = METHOD + "::$late";
        String joined = METHOD + "::$joined";
        Map<String, Object> early = heapRead("DF.early", earlyField,
                earlyLocal, "early", 40);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> earlyBindings = new ArrayList<>(
                (List<Map<String, Object>>) early.get(
                        "runtimeFieldBindings"));
        early.put("runtimeFieldBindings", earlyBindings);
        Map<String, Object> after = new LinkedHashMap<>(
                earlyBindings.get(0));
        after.put("eventSeq", 60L);
        earlyBindings.add(after);
        File refined = writeRows("fatal-prefix-refined.jsonl",
                early,
                heapRead("DF.late", lateField, lateLocal, "late", 70),
                refinedEdge("DF.early.join", "local_def_use",
                        "VALUE_PASS", earlyLocal, joined, METHOD + "#u7",
                        7, "$joined = $early", null, null, null, false),
                refinedEdge("DF.late.join", "local_def_use",
                        "VALUE_PASS", lateLocal, joined, METHOD + "#u8",
                        8, "$joined = $late", null, null, null, false),
                refinedEdge("DF.failure", "exception_guard", "GUARD",
                        joined, METHOD + "#u20#exception:example.Failure",
                        METHOD + "#u9", 9,
                        "if $joined == 0 goto throw", null,
                        METHOD + "#u9", true, false));
        Map<String, Object> target = object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", "REGION.1", "rootCallId", 11,
                "selection", "EXCEPTION_CONTEXT",
                "callIds", Collections.singletonList(101L),
                "observedMethods", Collections.singletonList(METHOD));
        Map<String, Object> observation = object("kind", "BRANCH",
                "eventSeq", 50L, "method", METHOD, "callId", 101L,
                "siteId", METHOD + "#u9", "outcome", false);
        Map<String, Object> laterOccurrence = object("kind", "BRANCH",
                "eventSeq", 80L, "method", METHOD, "callId", 101L,
                "siteId", METHOD + "#u9", "outcome", false);
        File regions = new File(folder.getRoot(),
                "fatal-prefix-regions.jsonl");

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, new File(folder.getRoot(),
                "fatal-prefix-edges.jsonl"),
                Collections.singleton(METHOD),
                Collections.singletonList(target),
                Arrays.asList(observation, laterOccurrence));

        JsonObject region = GSON.fromJson(Files.readAllLines(
                regions.toPath(), StandardCharsets.UTF_8).get(0),
                JsonObject.class);
        assertEquals(1, region.getAsJsonArray("symbolicInputs").size());
        JsonObject input = region.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject();
        assertEquals(earlyField, input.getAsJsonArray(
                "fieldPathDeclarations").get(0).getAsString());
        assertEquals(1, input.getAsJsonArray("runtimeAccesses").size());
        assertEquals(40L, input.getAsJsonArray("runtimeAccesses").get(0)
                .getAsJsonObject().get("eventSeq").getAsLong());
        assertEquals(50L, input.get("fatalPrefixEventSeq").getAsLong());
    }

    @Test
    public void trustedProtocolReceiveBeforeFatalRemainsTheSourcePort()
            throws Exception {
        String producer = "<example.Producer: void run()>";
        String targetMethod = "<example.Target: void run()>";
        String wire = producer + "::$wire";
        String username = targetMethod + ".param0:java.lang.String";
        File skeleton = writeRows("fatal-prefix-rpc-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.producer",
                        "rootMethod", producer, "anchorMethod", producer,
                        "methods", Collections.singletonList(producer),
                        "selection", "PROTOCOL_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", targetMethod,
                        "anchorMethod", targetMethod,
                        "methods", Collections.singletonList(targetMethod),
                        "selection", "EXCEPTION_CONTEXT"));
        Map<String, Object> protocol = object(
                "mappingId", "example.request", "port", "username",
                "direction", "REQUEST", "transport", "RPC",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "fromRegionId", "REGION.producer",
                "toRegionId", "REGION.target",
                "fromRootCallId", 1, "toRootCallId", 2,
                "fromCell", wire, "toCell", username,
                "sendEventSeq", 30, "receiveEventSeq", 40);
        File refined = writeRows("fatal-prefix-rpc-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.rpc", "kind", "protocol_transfer",
                        "transferKind", "PROTOCOL_TRANSFER",
                        "method", producer, "regionIds", Arrays.asList(
                        "REGION.producer", "REGION.target"),
                        "runtimeObserved", true,
                        "runtimeProtocolBindings",
                        Collections.singletonList(protocol)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", targetMethod,
                        "regionIds", Collections.singletonList(
                        "REGION.target"), "fromCell", username,
                        "toCell", targetMethod
                        + "#u9#exception:example.Failure",
                        "siteId", targetMethod + "#u9", "unitIndex", 9));
        Map<String, Object> target = activationAtFatalSite(
                "REGION.target", 2, "EXCEPTION_CONTEXT", targetMethod,
                2L, targetMethod + "#u9");
        target.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(targetMethod + "#u9", targetMethod,
                        50L, 2L, false)));
        File regions = new File(folder.getRoot(),
                "fatal-prefix-rpc-regions.jsonl");

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, new File(folder.getRoot(),
                        "fatal-prefix-rpc-edges.jsonl"),
                Arrays.asList(producer, targetMethod), Arrays.asList(
                        activation("REGION.producer", 1,
                                "PROTOCOL_CONTEXT", producer), target));

        List<JsonObject> rows = readJsonLines(regions);
        JsonObject targetRegion = rows.get(0).get("regionId").getAsString()
                .equals("REGION.target") ? rows.get(0) : rows.get(1);
        assertEquals(1, targetRegion.getAsJsonArray(
                "symbolicInputs").size());
        JsonObject input = targetRegion.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject();
        assertEquals("PROTOCOL_INPUT", input.get("sourceKind")
                .getAsString());
        assertEquals(username, input.get("cell").getAsString());
        assertEquals("TRUSTED_PROTOCOL_RECEIVE_PREFIX_V1",
                input.get("fatalPrefixAuthority").getAsString());
    }

    @Test(expected = IOException.class)
    public void explicitFatalTargetRequiresActivationLocalBranchEvidence()
            throws Exception {
        File skeleton = skeleton("missing-target-evidence-skeleton.jsonl");
        String local = METHOD + "::$value";
        File refined = writeRows("missing-target-evidence-refined.jsonl",
                heapRead("DF.value", "<example.Root: int value>", local,
                        "value", 3),
                refinedEdge("DF.failure", "exception_guard", "GUARD",
                        local, METHOD + "#u20#exception:example.Failure",
                        METHOD + "#u9", 9, "if value == 0 goto throw", null,
                        METHOD + "#u9", true, false));
        Map<String, Object> target = object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", "REGION.1", "rootCallId", 11,
                "selection", "EXCEPTION_CONTEXT",
                "callIds", Collections.singletonList(101L),
                "observedMethods", Collections.singletonList(METHOD));

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                new File(folder.getRoot(), "missing-target-regions.jsonl"),
                new File(folder.getRoot(), "missing-target-edges.jsonl"),
                Collections.singleton(METHOD),
                Collections.singletonList(target),
                Collections.<Map<String, Object>>emptyList());
    }

    @Test
    public void carrierLookupFreezesGuardAndMarksExactHeapPort()
            throws Exception {
        File skeleton = skeleton("carrier-skeleton.jsonl");
        String field = "<example.Root: java.util.Map registry>";
        String map = METHOD + "::$map";
        String selected = METHOD + "::$selected";
        String site = METHOD + "#u7";
        Map<String, Object> binding = object(
                "regionId", "REGION.1", "rootCallId", 11,
                "rootKind", "RECEIVER", "rootCell", METHOD + ".receiver",
                "rootObjectId", 10, "fieldReceiverObjectId", 10,
                "valueObjectId", 20, "eventSeq", 4,
                "fieldPath", Collections.singletonList("registry"),
                "fieldPathDeclarations", Collections.singletonList(field));
        Map<String, Object> receiver = refinedEdge(
                "DF.lookup", "container_receiver", "MODEL_TRANSFORM",
                map, selected, METHOD + "#u6", 6,
                "$selected = interfaceinvoke $map.<java.util.Map: "
                        + "java.lang.Object get(java.lang.Object)>($key)",
                "<java.util.Map: java.lang.Object get(java.lang.Object)>",
                null, null, false);
        receiver.put("dependencyRole", "CONCRETE_STRUCTURE_CARRIER");
        File refined = writeRows("carrier-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.field", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", METHOD,
                        "regionIds", Collections.singletonList("REGION.1"),
                        "fromCell", field, "toCell", map,
                        "runtimeFieldBindings",
                        Collections.singletonList(binding)),
                receiver,
                refinedEdge("DF.guard", "guard_dependency", "GUARD",
                        selected, site, site, 7,
                        "if $selected == null goto return", null,
                        site, false, false));

        JsonObject region = finalizeOne(refined, skeleton,
                "carrier-regions.jsonl", "carrier-edges.jsonl");
        JsonObject port = region.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject();
        assertEquals("CONCRETE_STRUCTURE_CARRIER",
                port.get("dependencyRole").getAsString());
        JsonObject branch = branch(region, site);
        assertEquals("PATH_ASSUMPTION", branch.get("policy").getAsString());
        assertEquals("STRUCTURE_CARRIER_GUARD",
                branch.get("policyReason").getAsString());
    }

    @Test
    public void structuralCarrierFlowsOnlyFromExplicitContainerMutation()
            throws Exception {
        String normalWriter = "<example.NormalWriter: void run()>";
        String mutationWriter = "<example.MutationWriter: void run()>";
        String target = "<example.CarrierTarget: void run()>";
        String field = "<example.Owner: java.util.Map values>";
        String receiver = target + "::$receiver";
        String selected = target + "::$selected";
        String failure = target + "#u9#exception:example.Failure";
        File skeleton = writeRows("carrier-flow-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.normalWriter",
                        "rootMethod", normalWriter,
                        "anchorMethod", normalWriter,
                        "methods", Collections.singletonList(normalWriter),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.mutationWriter",
                        "rootMethod", mutationWriter,
                        "anchorMethod", mutationWriter,
                        "methods", Collections.singletonList(mutationWriter),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", target, "anchorMethod", target,
                        "methods", Collections.singletonList(target),
                        "selection", "EXCEPTION_CONTEXT"));
        Map<String, Object> normal = fieldBinding(
                "REGION.normalWriter", 1, normalWriter, 5,
                field, "", 101);
        Map<String, Object> mutation = fieldBinding(
                "REGION.mutationWriter", 2, mutationWriter, 6,
                field, "", 100);
        mutation.put("bindingKind", "CONTAINER_MUTATION");
        mutation.put("valueObjectId", 200);
        mutation.put("fieldPath", Arrays.asList("owner", "values"));
        mutation.put("fieldPathDeclarations", Arrays.asList(
                "<example.MutationWriter: example.Owner owner>", field));
        mutation.put("writerFieldReadSeq", 5);
        mutation.put("mutatorEnterSeq", 5);
        mutation.put("mutationCompletionSeq", 6);
        Map<String, Object> preState = fieldBinding(
                "REGION.mutationWriter", 2, mutationWriter, 4,
                field, "", 100);
        preState.put("callId", 20);
        preState.put("siteId", mutationWriter + "#u1");
        preState.put("valueObjectId", 200);
        preState.put("fieldPath", Arrays.asList("owner", "values"));
        preState.put("fieldPathDeclarations", Arrays.asList(
                "<example.MutationWriter: example.Owner owner>", field));
        Map<String, Object> read = fieldBinding(
                "REGION.target", 3, target, 8, field, "", 100);
        read.put("valueObjectId", 200);
        read.put("fieldPath", Arrays.asList("cache", "values"));
        read.put("fieldPathDeclarations", Arrays.asList(
                "<example.CarrierTarget: example.Owner cache>", field));
        File refined = writeRows("carrier-flow-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.normal", "kind", "field_write",
                        "transferKind", "HEAP_WRITE",
                        "method", normalWriter,
                        "regionIds", Collections.singletonList(
                                "REGION.normalWriter"),
                        "toCell", field, "runtimeFieldBindings",
                        Collections.singletonList(normal)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.prestate", "kind", "field_read",
                        "transferKind", "HEAP_READ",
                        "method", mutationWriter,
                        "regionIds", Collections.singletonList(
                                "REGION.mutationWriter"),
                        "fromCell", field,
                        "toCell", mutationWriter + "::$state",
                        "siteId", mutationWriter + "#u1",
                        "unitIndex", 1, "runtimeFieldBindings",
                        Collections.singletonList(preState)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.mutation", "kind", "field_write",
                        "transferKind", "HEAP_WRITE",
                        "method", mutationWriter,
                        "regionIds", Collections.singletonList(
                                "REGION.mutationWriter"),
                        "toCell", field, "runtimeFieldBindings",
                        Collections.singletonList(mutation)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", target,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", field, "toCell", receiver,
                        "runtimeFieldBindings",
                        Collections.singletonList(read)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.lookup", "kind", "container_receiver",
                        "transferKind", "MODEL_TRANSFORM", "method", target,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", receiver, "toCell", selected,
                        "dependencyRole", "CONCRETE_STRUCTURE_CARRIER"),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", target,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", selected, "toCell", failure,
                        "siteId", target + "#u9", "unitIndex", 9));
        File regions = new File(folder.getRoot(),
                "carrier-flow-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "carrier-flow-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(normalWriter, mutationWriter, target),
                        Arrays.asList(
                                activation("REGION.normalWriter", 1,
                                        "STATE_CONTEXT", normalWriter),
                                activation("REGION.mutationWriter", 2,
                                        "STATE_CONTEXT", mutationWriter),
                                activation("REGION.target", 3,
                                        "EXCEPTION_CONTEXT", target)));

        assertEquals(2, result.regions.size());
        assertEquals(1, result.regionEdges.size());
        String retained = Files.readAllLines(edges.toPath(),
                StandardCharsets.UTF_8).toString();
        assertTrue(retained.contains("REGION.mutationWriter"));
        assertFalse(retained.contains("REGION.normalWriter"));
        assertTrue(retained.contains("CONTAINER_MUTATION"));

        List<JsonObject> finalized = readJsonLines(regions);
        JsonObject producer = finalized.stream()
                .filter(row -> "REGION.mutationWriter".equals(
                        row.get("regionId").getAsString()))
                .findFirst().get();
        JsonObject producerInput = producer.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject();
        JsonObject producerOutput = producer.getAsJsonArray("outputs")
                .get(0).getAsJsonObject();
        assertEquals("BOUNDED_CONTAINER_STATE",
                producerInput.get("symbolicDemand").getAsString());
        assertEquals("MUTATION_PRE_STATE",
                producerInput.get("boundedContainerStateRole")
                        .getAsString());
        assertEquals("java.util.Map",
                producerInput.get("javaType").getAsString());
        assertEquals("BOUNDED_CONTAINER_STATE",
                producerOutput.get("symbolicDemand").getAsString());
        assertEquals(producerInput.get("portId").getAsString(),
                producerOutput.getAsJsonArray(
                        "boundedContainerPreStatePorts")
                        .get(0).getAsString());

        JsonObject finalizedTarget = finalized.stream()
                .filter(row -> "REGION.target".equals(
                        row.get("regionId").getAsString()))
                .findFirst().get();
        JsonObject targetInput = finalizedTarget
                .getAsJsonArray("symbolicInputs").get(0).getAsJsonObject();
        assertEquals("BOUNDED_CONTAINER_STATE",
                targetInput.get("symbolicDemand").getAsString());
        assertEquals("VALUE_FRONTIER",
                targetInput.get("dependencyRole").getAsString());
        JsonObject retainedEdge = readJsonLines(edges).get(0);
        assertEquals("EXACT_RUNTIME_CONTAINER_MUTATION_STATE_CHAIN_V1",
                retainedEdge.get("boundedContainerStateAuthority")
                        .getAsString());
    }

    @Test
    public void freezesIteratorLoopGuardButExploresSemanticBodyGuard()
            throws Exception {
        File skeleton = skeleton("branch-skeleton.jsonl");
        String iterator = METHOD + "::$iterator";
        String hasNext = METHOD + "::$hasNext";
        String comparison = METHOD + "::$comparison";
        String loopSite = METHOD + "#u6";
        String semanticSite = METHOD + "#u14";
        Map<String, Object> iteratorHasNext = refinedEdge(
                "DF.iterator", "container_receiver",
                "MODEL_TRANSFORM", iterator, hasNext,
                METHOD + "#u5", 5,
                "$hasNext = interfaceinvoke $iterator."
                        + "<java.util.Iterator: boolean hasNext()>()",
                "<java.util.Iterator: boolean hasNext()>",
                null, null, false);
        iteratorHasNext.put("dependencyRole",
                DependencyRole.CONCRETE_STRUCTURE_CARRIER);

        File refined = writeRows("branch-refined.jsonl",
                iteratorHasNext,
                refinedEdge("DF.loop", "path_guard_dependency", "GUARD",
                        hasNext, hasNext, loopSite, 6,
                        "if $hasNext == 0 goto return", null,
                        loopSite, false, true),
                refinedEdge("DF.loop.consume", "guard_dependency", "GUARD",
                        hasNext, loopSite, loopSite, 6,
                        "if $hasNext == 0 goto return", null,
                        loopSite, null, false),
                refinedEdge("DF.semantic", "guard_dependency", "GUARD",
                        comparison, semanticSite, semanticSite, 14,
                        "if $comparison >= 0 goto branch", null,
                        semanticSite, false, false));
        JsonObject region = finalizeOne(refined, skeleton,
                "branch-regions.jsonl", "branch-edges.jsonl");

        JsonObject loop = branch(region, loopSite);
        assertEquals("PATH_ASSUMPTION",
                loop.get("policy").getAsString());
        assertEquals("BOUND_LOOP_CONTROL_GUARD",
                loop.get("policyReason").getAsString());
        assertFalse(loop.get("requiredOutcome").getAsBoolean());

        JsonObject semantic = branch(region, semanticSite);
        assertEquals("EXPLORE", semantic.get("policy").getAsString());
        assertEquals("FAILURE_DIRECTED_SEMANTIC_GUARD",
                semantic.get("policyReason").getAsString());
    }

    @Test
    public void cfgLoopGuardFreezesLoopOnlyInputButSemanticUseWins()
            throws Exception {
        File skeleton = skeleton("cfg-loop-skeleton.jsonl");
        String runningField = "<example.Root: boolean running>";
        String sharedField = "<example.Root: boolean shared>";
        String running = METHOD + "::$running";
        String shared = METHOD + "::$shared";
        String loopSite = METHOD + "#u8";
        String semanticSite = METHOD + "#u18";
        Map<String, Object> loopRunning = refinedEdge(
                "DF.loop.running", "guard_dependency", "GUARD",
                running, loopSite, loopSite, 8,
                "if $running == 0 goto return", null,
                loopSite, false, false);
        loopRunning.put("loopControlGuard", true);
        Map<String, Object> loopShared = refinedEdge(
                "DF.loop.shared", "guard_dependency", "GUARD",
                shared, loopSite, loopSite, 8,
                "if $shared == 0 goto return", null,
                loopSite, false, false);
        loopShared.put("loopControlGuard", true);
        File refined = writeRows("cfg-loop-refined.jsonl",
                heapRead("DF.running", runningField, running,
                        "running", 3),
                heapRead("DF.shared", sharedField, shared,
                        "shared", 4),
                loopRunning, loopShared,
                refinedEdge("DF.semantic.shared", "guard_dependency",
                        "GUARD", shared, semanticSite, semanticSite, 18,
                        "if $shared == 0 goto body", null,
                        semanticSite, true, false));

        JsonObject region = finalizeOne(refined, skeleton,
                "cfg-loop-regions.jsonl", "cfg-loop-edges.jsonl");
        assertEquals("PATH_ASSUMPTION",
                branch(region, loopSite).get("policy").getAsString());
        assertEquals("EXPLORE",
                branch(region, semanticSite).get("policy").getAsString());
        JsonObject runningPort = inputForField(region, runningField);
        JsonObject sharedPort = inputForField(region, sharedField);
        assertTrue(runningPort.get("loopControlOnly").getAsBoolean());
        assertFalse(sharedPort.has("loopControlOnly"));
    }

    @Test
    public void semanticAccessorCreatesOccurrenceSpecificScalarPorts()
            throws Exception {
        File skeleton = skeleton("accessor-branch-skeleton.jsonl");
        String field = "<example.KeyBase: long expiryDate>";
        String callee = "<example.Key: long getExpiryDate()>";
        String local = METHOD + "::$expiry";
        String receiver = METHOD + "::$key";
        String carrier = "<example.Root: java.util.Map allKeys>";
        String site = METHOD + "#u14";
        Map<String, Object> first = object(
                "regionId", "REGION.1", "rootCallId", 11,
                "callId", 11, "invocationId", 21,
                "callerMethod", METHOD, "unitIndex", 11,
                "siteId", METHOD + "#u11", "eventSeq", 22,
                "receiverObjectId", 31, "primitiveValue", "100",
                "accessorOccurrence", 1, "declaredCallee", callee);
        Map<String, Object> second = object(
                "regionId", "REGION.1", "rootCallId", 11,
                "callId", 11, "invocationId", 23,
                "callerMethod", METHOD, "unitIndex", 11,
                "siteId", METHOD + "#u11", "eventSeq", 24,
                "receiverObjectId", 32, "primitiveValue", "200",
                "accessorOccurrence", 2, "declaredCallee", callee);
        File refined = writeRows("accessor-branch-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.accessor", "kind",
                        "accessor_field_return", "transferKind", "HEAP_READ",
                        "method", METHOD, "regionIds",
                        Collections.singletonList("REGION.1"),
                        "fromCell", field, "toCell", local,
                        "siteId", METHOD + "#u11", "unitIndex", 11,
                        "invoke", callee, "declaredFieldSignature", field,
                        "accessorImplementationMethod",
                        "<example.KeyBase: long getExpiryDate()>",
                        "runtimeObserved", true,
                        "runtimeAccessorBindings", Arrays.asList(first, second)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.accessor.receiver", "kind",
                        "accessor_receiver", "transferKind",
                        "IDENTITY_BINDING", "method", METHOD,
                        "regionIds", Collections.singletonList("REGION.1"),
                        "fromCell", receiver, "toCell", local,
                        "siteId", METHOD + "#u11", "unitIndex", 11),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.carrier.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", METHOD,
                        "regionIds", Collections.singletonList("REGION.1"),
                        "fromCell", carrier, "toCell", receiver,
                        "siteId", METHOD + "#u8", "unitIndex", 8),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.historical.key", "kind",
                        "accessor_field_return", "transferKind", "HEAP_READ",
                        "method", METHOD, "regionIds",
                        Collections.singletonList("REGION.1"),
                        "fromCell", "<example.KeyBase: int keyId>",
                        "toCell", carrier, "siteId", METHOD + "#u4",
                        "unitIndex", 4,
                        "invoke", "<example.Key: int getKeyId()>",
                        "declaredFieldSignature",
                        "<example.KeyBase: int keyId>",
                        "accessorImplementationMethod",
                        "<example.KeyBase: int getKeyId()>",
                        "runtimeObserved", true,
                        "runtimeAccessorBindings",
                        Collections.singletonList(object(
                                "regionId", "REGION.1", "rootCallId", 11,
                                "callId", 11, "invocationId", 19,
                                "callerMethod", METHOD, "unitIndex", 4,
                                "siteId", METHOD + "#u4", "eventSeq", 20,
                                "receiverObjectId", 30,
                                "primitiveValue", "7",
                                "accessorOccurrence", 1,
                                "declaredCallee",
                                "<example.Key: int getKeyId()>"))),
                refinedEdge("DF.semantic", "guard_dependency", "GUARD",
                        local, site, site, 14,
                        "if $expiry >= $now goto branch", null,
                        site, false, false));

        JsonObject region = finalizeOne(refined, skeleton,
                "accessor-branch-regions.jsonl",
                "accessor-branch-edges.jsonl");

        assertEquals(2, region.getAsJsonArray("symbolicInputs").size());
        JsonObject firstPort = region.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject();
        JsonObject secondPort = region.getAsJsonArray("symbolicInputs")
                .get(1).getAsJsonObject();
        assertEquals("ACCESSOR_RETURN",
                firstPort.get("sourceKind").getAsString());
        assertFalse(firstPort.has("materialization"));
        assertEquals(MaterializationSpec.Kind.ACCESSOR_RETURN,
                MaterializationSpec.decode(firstPort).kind());
        assertEquals(1, firstPort.get("replayOccurrence").getAsInt());
        assertEquals(2, secondPort.get("replayOccurrence").getAsInt());
        assertFalse(firstPort.get("portId").getAsString().equals(
                secondPort.get("portId").getAsString()));
    }

    @Test
    public void semanticAccessorRetainsOnlyTheCapacityPerStream()
            throws Exception {
        File skeleton = skeleton("bounded-accessor-skeleton.jsonl");
        String field = "<example.KeyBase: long value>";
        String callee = "<example.Key: long getValue()>";
        String local = METHOD + "::$value";
        String accessorSite = METHOD + "#u11";
        String guardSite = METHOD + "#u14";
        List<Map<String, Object>> bindings = new ArrayList<>();
        for (int occurrence = LoopBoundPolicy
                .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY;
                occurrence >= 1; occurrence--) {
            bindings.add(object(
                    "regionId", "REGION.1", "rootCallId", 11,
                    "callId", 11, "invocationId", 100 + occurrence,
                    "callerMethod", METHOD, "unitIndex", 11,
                    "siteId", accessorSite,
                    "eventSeq", 200 + occurrence,
                    "receiverObjectId", 300 + occurrence,
                    "primitiveValue", String.valueOf(occurrence),
                    "accessorOccurrence", occurrence,
                    "declaredCallee", callee));
        }
        File refined = writeRows("bounded-accessor-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.bounded.accessor", "kind",
                        "accessor_field_return", "transferKind", "HEAP_READ",
                        "method", METHOD, "regionIds",
                        Collections.singletonList("REGION.1"),
                        "fromCell", field, "toCell", local,
                        "siteId", accessorSite, "unitIndex", 11,
                        "invoke", callee, "declaredFieldSignature", field,
                        "accessorImplementationMethod",
                        "<example.KeyBase: long getValue()>",
                        "runtimeObserved", true,
                        "runtimeAccessorBindings", bindings),
                refinedEdge("DF.bounded.guard", "guard_dependency", "GUARD",
                        local, guardSite, guardSite, 14,
                        "if $value == 0 goto failure", null,
                        guardSite, true, false));

        JsonObject region = finalizeOne(refined, skeleton,
                "bounded-accessor-regions.jsonl",
                "bounded-accessor-edges.jsonl");

        assertEquals(LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY,
                region.getAsJsonArray("symbolicInputs").size());
        for (int index = 0; index < LoopBoundPolicy
                .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY; index++) {
            JsonObject port = region.getAsJsonArray("symbolicInputs")
                    .get(index).getAsJsonObject();
            assertEquals(index + 1,
                    port.get("replayOccurrence").getAsInt());
            assertEquals("ACCESSOR_RETURN",
                    port.get("sourceKind").getAsString());
        }
    }

    @Test
    public void boundedMutationAccessorCapacityIsPerHelperActivation()
            throws Exception {
        File skeleton = skeleton("activation-bounded-accessor-skeleton.jsonl");
        String field = "<example.KeyBase: long expiryDate>";
        String container = "<example.Keys: java.util.Map allKeys>";
        String callee = "<example.Key: long getExpiryDate()>";
        String value = METHOD + "::$expiry";
        String comparison = METHOD + "::$comparison";
        String guardSite = METHOD + "#u14";
        List<Map<String, Object>> bindings = new ArrayList<>();
        int globalOccurrence = 0;
        for (int helper = 0; helper < 2; helper++) {
            int count = helper == 0
                    ? LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY
                    : 3;
            for (int local = 1; local <= count; local++) {
                globalOccurrence++;
                bindings.add(object(
                        "regionId", "REGION.1", "rootCallId", 11,
                        "callId", 100 + helper, "invocationId",
                        1000 + globalOccurrence,
                        "callerMethod", METHOD, "unitIndex", 11,
                        "siteId", METHOD + "#u11", "eventSeq",
                        2000 + globalOccurrence,
                        "receiverObjectId", 3000 + globalOccurrence,
                        "primitiveValue", String.valueOf(globalOccurrence),
                        "accessorOccurrence", globalOccurrence,
                        "declaredCallee", callee));
            }
        }
        bindings.get(0).put("symbolicDemand",
                "CONCRETE_UNPROJECTED_BOUNDARY_ACCESS");
        bindings.get(0).put("rpcConcreteRootAuthority",
                "EXACT_ACTIVATION_EXTERNAL_PRESTATE_WRITE_V1");
        Map<String, Object> mutation = fieldBinding(
                "REGION.1", 11, METHOD, 3000, container, "", 44);
        mutation.put("bindingKind", "CONTAINER_MUTATION");
        mutation.put("mutatorDeclaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,"
                        + "java.lang.Object)>");
        mutation.put("mutationCompletionSeq", 3001);
        File refined = writeRows("activation-bounded-accessor-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.activation.accessor", "kind",
                        "accessor_field_return", "transferKind", "HEAP_READ",
                        "method", METHOD, "regionIds",
                        Collections.singletonList("REGION.1"),
                        "fromCell", field, "toCell", value,
                        "siteId", METHOD + "#u11", "unitIndex", 11,
                        "invoke", callee, "declaredFieldSignature", field,
                        "accessorImplementationMethod",
                        "<example.KeyBase: long getExpiryDate()>",
                        "runtimeObserved", true,
                        "runtimeAccessorBindings", bindings),
                refinedEdge("DF.activation.compute", "local_def_use",
                        "COMPUTE", value, comparison, METHOD + "#u12", 12,
                        "$comparison = $expiry cmp $now", null, null,
                        null, false),
                refinedEdge("DF.activation.guard",
                        "heap_mutation_path_guard", "GUARD", comparison,
                        container, guardSite, 14,
                        "if $comparison >= 0 goto branch", null,
                        guardSite, false, false),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.activation.mutation", "kind",
                        "field_write", "transferKind", "HEAP_WRITE",
                        "method", METHOD, "regionIds",
                        Collections.singletonList("REGION.1"),
                        "fromCell", METHOD + "::$value",
                        "toCell", container, "siteId", METHOD + "#u23",
                        "unitIndex", 23, "runtimeFieldBindings",
                        Collections.singletonList(mutation)));

        JsonObject region = finalizeOne(refined, skeleton,
                "activation-bounded-accessor-regions.jsonl",
                "activation-bounded-accessor-edges.jsonl");

        assertEquals(LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY + 3,
                region.getAsJsonArray("symbolicInputs").size());
        JsonObject firstSecondActivation = region
                .getAsJsonArray("symbolicInputs")
                .get(LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY)
                .getAsJsonObject();
        assertEquals(1, firstSecondActivation
                .get("helperActivationBoundedOccurrence").getAsInt());
        for (com.google.gson.JsonElement element
                : region.getAsJsonArray("symbolicInputs")) {
            JsonObject input = element.getAsJsonObject();
            if (input.has("rpcConcreteRootAuthority")) {
                assertEquals("CONCRETE_UNPROJECTED_BOUNDARY_ACCESS",
                        input.get("symbolicDemand").getAsString());
                assertFalse(input.has("boundedStateFrontierAuthority"));
                continue;
            }
            assertEquals("BOUNDED_STATE_FRONTIER",
                    input.get("symbolicDemand").getAsString());
            assertEquals("STATIC_ACCESSOR_SEMANTIC_MUTATION_GUARD_V1",
                    input.get("boundedStateFrontierAuthority")
                            .getAsString());
        }
    }

    @Test
    public void semanticCardinalityCheckOutsideLoopRemainsExplorable()
            throws Exception {
        File skeleton = skeleton("size-skeleton.jsonl");
        String collection = METHOD + "::$collection";
        String size = METHOD + "::$size";
        String site = METHOD + "#u9";
        Map<String, Object> sizeValue = refinedEdge(
                "DF.size", "container_receiver",
                "MODEL_TRANSFORM", collection, size,
                METHOD + "#u8", 8,
                "$size = interfaceinvoke $collection."
                        + "<java.util.Collection: int size()>()",
                "<java.util.Collection: int size()>",
                null, null, false);
        sizeValue.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        File refined = writeRows("size-refined.jsonl",
                sizeValue,
                refinedEdge("DF.size.guard", "guard_dependency", "GUARD",
                        size, site, site, 9,
                        "if $size == 0 goto failure", null,
                        site, true, false));
        JsonObject region = finalizeOne(refined, skeleton,
                "size-regions.jsonl", "size-edges.jsonl");

        JsonObject branch = branch(region, site);
        assertEquals("EXPLORE", branch.get("policy").getAsString());
        assertTrue(branch.get("requiredOutcome").getAsBoolean());
    }

    @Test
    public void exceptionOutcomeWinsOverNormalReturnAtSameBranch()
            throws Exception {
        File skeleton = skeleton("exception-branch-skeleton.jsonl");
        String value = METHOD + "::$value";
        String site = METHOD + "#u9";
        File refined = writeRows("exception-branch-refined.jsonl",
                refinedEdge("DF.failure", "exception_guard", "GUARD",
                        value, METHOD + "#u14#exception:example.Failure",
                        site, 9, "if $value != null goto return", null,
                        site, false, false),
                refinedEdge("DF.return", "path_guard_dependency", "GUARD",
                        value, METHOD + ".return", site, 9,
                        "if $value != null goto return", null,
                        site, true, false));
        JsonObject region = finalizeOne(refined, skeleton,
                "exception-branch-regions.jsonl",
                "exception-branch-edges.jsonl");

        JsonObject branch = branch(region, site);
        assertEquals("EXPLORE", branch.get("policy").getAsString());
        assertEquals("FAILURE_DIRECTED_SEMANTIC_GUARD",
                branch.get("policyReason").getAsString());
        assertFalse(branch.get("requiredOutcome").getAsBoolean());
    }


    @Test
    public void failureSliceCrossesObservedProtocolBeforeExactHeapReadFrom()
            throws Exception {
        String updater = "<example.Updater: void run()>";
        String staleUpdater = "<example.StaleUpdater: void run()>";
        String dispatcher = "<example.Dispatcher: void run()>";
        String target = "<example.Server: void run()>";
        String field = "<example.SecretManager: example.Key currentKey>";
        String loaded = dispatcher + "::$loaded";
        String wireValue = dispatcher + "::$wireValue";
        String request = target + ".param0:java.lang.String";
        String failure = target + "#u9#exception:example.UnknownKey";

        File skeleton = writeRows("protocol-heap-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.updater",
                        "rootMethod", updater, "anchorMethod", updater,
                        "methods", Collections.singletonList(updater),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.stale",
                        "rootMethod", staleUpdater,
                        "anchorMethod", staleUpdater,
                        "methods", Collections.singletonList(staleUpdater),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.dispatcher",
                        "rootMethod", dispatcher,
                        "anchorMethod", dispatcher,
                        "methods", Collections.singletonList(dispatcher),
                        "selection", "PROTOCOL_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", target, "anchorMethod", target,
                        "methods", Collections.singletonList(target),
                        "selection", "EXCEPTION_CONTEXT"));
        Map<String, Object> write = fieldBinding(
                "REGION.updater", 1, updater, 5, field, "", 100);
        write.put("valueObjectId", 200);
        Map<String, Object> staleWrite = fieldBinding(
                "REGION.stale", 4, staleUpdater, 6, field, "", 100);
        staleWrite.put("valueObjectId", 300);
        Map<String, Object> read = fieldBinding(
                "REGION.dispatcher", 2, dispatcher, 10, field, "", 100);
        read.put("valueObjectId", 200);
        Map<String, Object> protocolBinding = object(
                "mappingId", "example.request",
                "port", "authenticationId", "direction", "REQUEST",
                "transport", "RPC",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "fromRegionId", "REGION.dispatcher",
                "toRegionId", "REGION.target",
                "fromRootCallId", 2, "toRootCallId", 3,
                "fromCell", wireValue, "toCell", request,
                "sendEventSeq", 12, "receiveEventSeq", 13);
        File refined = writeRows("protocol-heap-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE", "method", updater,
                        "regionIds", Collections.singletonList(
                                "REGION.updater"),
                        "fromCell", updater + "::$rpcKey",
                        "toCell", field, "runtimeFieldBindings",
                        Collections.singletonList(write)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.stale.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE",
                        "method", staleUpdater,
                        "regionIds", Collections.singletonList(
                                "REGION.stale"),
                        "fromCell", staleUpdater + "::$rpcKey",
                        "toCell", field, "runtimeFieldBindings",
                        Collections.singletonList(staleWrite)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", dispatcher,
                        "regionIds", Collections.singletonList(
                                "REGION.dispatcher"),
                        "fromCell", field, "toCell", loaded,
                        "runtimeFieldBindings",
                        Collections.singletonList(read)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.encode", "kind", "local_def_use",
                        "transferKind", "VALUE_PASS", "method", dispatcher,
                        "regionIds", Collections.singletonList(
                                "REGION.dispatcher"),
                        "fromCell", loaded, "toCell", wireValue),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.protocol", "kind", "protocol_transfer",
                        "transferKind", "PROTOCOL_TRANSFER",
                        "method", dispatcher, "regionIds", Arrays.asList(
                                "REGION.dispatcher", "REGION.target"),
                        "runtimeObserved", true,
                        "runtimeProtocolBindings",
                        Collections.singletonList(protocolBinding)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", target,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", request, "toCell", failure,
                        "siteId", target + "#u9", "unitIndex", 9));
        File regions = new File(folder.getRoot(),
                "protocol-heap-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "protocol-heap-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(updater, staleUpdater, dispatcher,
                                target),
                        Arrays.asList(
                                activation("REGION.updater", 1,
                                        "STATE_CONTEXT", updater),
                                activation("REGION.stale", 4,
                                        "STATE_CONTEXT", staleUpdater),
                                activation("REGION.dispatcher", 2,
                                        "PROTOCOL_CONTEXT", dispatcher),
                                activation("REGION.target", 3,
                                        "EXCEPTION_CONTEXT", target)));

        assertEquals(3, result.regions.size());
        assertEquals(2, result.regionEdges.size());
        java.util.List<String> edgeRows = Files.readAllLines(edges.toPath(),
                StandardCharsets.UTF_8);
        assertTrue(edgeRows.toString().contains("RUNTIME_FIELD_FLOW"));
        assertTrue(edgeRows.toString().contains("RUNTIME_PROTOCOL_FLOW"));
        assertTrue(edgeRows.toString().contains("REGION.updater"));
        assertTrue(!edgeRows.toString().contains("REGION.stale"));
        assertTrue(edgeRows.toString().contains("REGION.dispatcher"));
    }

    @Test
    public void multipleTargetsRetainTheirUnionClosure()
            throws Exception {
        String producer = "<example.Producer: void run()>";
        String target = "<example.Target: void run()>";
        String wire = producer + "::$wire";
        String request = target + ".param0:int";
        String failure = target + "#u9#exception:example.Failure";
        File skeleton = writeRows("target-union-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.producer",
                        "rootMethod", producer, "anchorMethod", producer,
                        "methods", Collections.singletonList(producer),
                        "selection", "PROTOCOL_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", target, "anchorMethod", target,
                        "methods", Collections.singletonList(target),
                        "selection", "EXCEPTION_CONTEXT"));
        Map<String, Object> first = object(
                "mappingId", "example.request", "port", "request",
                "direction", "REQUEST", "transport", "RPC",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "fromRegionId", "REGION.producer",
                "toRegionId", "REGION.target",
                "fromRootCallId", 1, "toRootCallId", 2,
                "fromCell", wire, "toCell", request,
                "sendEventSeq", 10, "receiveEventSeq", 11);
        Map<String, Object> second = new LinkedHashMap<>(first);
        second.put("toRootCallId", 3);
        second.put("sendEventSeq", 20);
        second.put("receiveEventSeq", 21);
        File refined = writeRows("target-union-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.rpc", "kind", "protocol_transfer",
                        "transferKind", "PROTOCOL_TRANSFER",
                        "method", producer, "regionIds", Arrays.asList(
                                "REGION.producer", "REGION.target"),
                        "runtimeObserved", true,
                        "runtimeProtocolBindings", Arrays.asList(
                                first, second)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", target,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", request, "toCell", failure,
                        "siteId", target + "#u9", "unitIndex", 9));
        File regions = new File(folder.getRoot(),
                "target-union-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "target-union-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(producer, target), Arrays.asList(
                                activation("REGION.producer", 1,
                                        "PROTOCOL_CONTEXT", producer),
                                activation("REGION.target", 2,
                                        "EXCEPTION_CONTEXT", target),
                                activation("REGION.target", 3,
                                        "EXCEPTION_CONTEXT", target)));

        assertEquals(3, retainedInstanceCount(result));
        assertEquals(2, result.regionEdges.size());
    }

    @Test
    public void failureClosureDropsUnrelatedInputAndRpcInSameProducer()
            throws Exception {
        String neededWriter = "<example.NeededWriter: void run()>";
        String noiseWriter = "<example.NoiseWriter: void run()>";
        String producer = "<example.Producer: void run()>";
        String target = "<example.TargetServer: void run()>";
        String neededField = "<example.Shared: int needed>";
        String noiseField = "<example.Shared: int noise>";
        String neededLoaded = producer + "::$neededLoaded";
        String noiseLoaded = producer + "::$noiseLoaded";
        String neededWire = producer + "::$neededWire";
        String noiseWire = producer + "::$noiseWire";
        String neededRequest = target + ".param0:int";
        String noiseRequest = target + ".param1:int";
        String alsoNeededRequest = target + ".param2:int";
        String failure = target + "#u9#exception:example.Failure";

        File skeleton = writeRows("port-demand-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.neededWriter",
                        "rootMethod", neededWriter,
                        "anchorMethod", neededWriter,
                        "methods", Collections.singletonList(neededWriter),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.noiseWriter",
                        "rootMethod", noiseWriter,
                        "anchorMethod", noiseWriter,
                        "methods", Collections.singletonList(noiseWriter),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.producer",
                        "rootMethod", producer, "anchorMethod", producer,
                        "methods", Collections.singletonList(producer),
                        "selection", "PROTOCOL_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", target, "anchorMethod", target,
                        "methods", Collections.singletonList(target),
                        "selection", "EXCEPTION_CONTEXT"));
        Map<String, Object> neededProtocol = object(
                "mappingId", "example.needed", "port", "needed",
                "direction", "REQUEST", "transport", "RPC",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "fromRegionId", "REGION.producer",
                "toRegionId", "REGION.target",
                "fromRootCallId", 3, "toRootCallId", 4,
                "fromCell", neededWire, "toCell", neededRequest,
                "sendEventSeq", 20, "receiveEventSeq", 21);
        Map<String, Object> noiseProtocol = object(
                "mappingId", "example.noise", "port", "noise",
                "direction", "REQUEST", "transport", "RPC",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "fromRegionId", "REGION.producer",
                "toRegionId", "REGION.target",
                "fromRootCallId", 3, "toRootCallId", 4,
                "fromCell", noiseWire, "toCell", noiseRequest,
                "sendEventSeq", 22, "receiveEventSeq", 23);
        Map<String, Object> alsoNeededProtocol = object(
                "mappingId", "example.alsoNeeded", "port", "alsoNeeded",
                "direction", "REQUEST", "transport", "RPC",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "fromRegionId", "REGION.producer",
                "toRegionId", "REGION.target",
                "fromRootCallId", 3, "toRootCallId", 4,
                "fromCell", neededWire, "toCell", alsoNeededRequest,
                "sendEventSeq", 24, "receiveEventSeq", 25);
        Map<String, Object> neededWrite = fieldBinding(
                "REGION.neededWriter", 1, neededWriter, 5,
                neededField, "1", 100);
        neededWrite.put("fieldPath", Collections.singletonList("needed"));
        Map<String, Object> noiseWrite = fieldBinding(
                "REGION.noiseWriter", 2, noiseWriter, 6,
                noiseField, "2", 200);
        noiseWrite.put("fieldPath", Collections.singletonList("noise"));
        Map<String, Object> neededRead = fieldBinding(
                "REGION.producer", 3, producer, 10,
                neededField, "1", 100);
        neededRead.put("fieldPath", Collections.singletonList("needed"));
        Map<String, Object> noiseRead = fieldBinding(
                "REGION.producer", 3, producer, 11,
                noiseField, "2", 200);
        noiseRead.put("fieldPath", Collections.singletonList("noise"));
        File refined = writeRows("port-demand-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.needed.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE",
                        "method", neededWriter,
                        "regionIds", Collections.singletonList(
                                "REGION.neededWriter"),
                        "toCell", neededField,
                        "runtimeFieldBindings", Collections.singletonList(
                                neededWrite)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.noise.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE",
                        "method", noiseWriter,
                        "regionIds", Collections.singletonList(
                                "REGION.noiseWriter"),
                        "toCell", noiseField,
                        "runtimeFieldBindings", Collections.singletonList(
                                noiseWrite)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.needed.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", producer,
                        "regionIds", Collections.singletonList(
                                "REGION.producer"),
                        "fromCell", neededField, "toCell", neededLoaded,
                        "runtimeFieldBindings", Collections.singletonList(
                                neededRead)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.noise.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", producer,
                        "regionIds", Collections.singletonList(
                                "REGION.producer"),
                        "fromCell", noiseField, "toCell", noiseLoaded,
                        "runtimeFieldBindings", Collections.singletonList(
                                noiseRead)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.needed.encode", "kind", "local_def_use",
                        "transferKind", "VALUE_PASS", "method", producer,
                        "regionIds", Collections.singletonList(
                                "REGION.producer"),
                        "fromCell", neededLoaded, "toCell", neededWire),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.noise.encode", "kind", "local_def_use",
                        "transferKind", "VALUE_PASS", "method", producer,
                        "regionIds", Collections.singletonList(
                                "REGION.producer"),
                        "fromCell", noiseLoaded, "toCell", noiseWire),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.needed.rpc",
                        "kind", "protocol_transfer",
                        "transferKind", "PROTOCOL_TRANSFER",
                        "method", producer, "regionIds", Arrays.asList(
                                "REGION.producer", "REGION.target"),
                        "runtimeObserved", true,
                        "runtimeProtocolBindings",
                        Collections.singletonList(neededProtocol)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.noise.rpc", "kind", "protocol_transfer",
                        "transferKind", "PROTOCOL_TRANSFER",
                        "method", producer, "regionIds", Arrays.asList(
                                "REGION.producer", "REGION.target"),
                        "runtimeObserved", true,
                        "runtimeProtocolBindings",
                        Collections.singletonList(noiseProtocol)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.alsoNeeded.rpc",
                        "kind", "protocol_transfer",
                        "transferKind", "PROTOCOL_TRANSFER",
                        "method", producer, "regionIds", Arrays.asList(
                                "REGION.producer", "REGION.target"),
                        "runtimeObserved", true,
                        "runtimeProtocolBindings",
                        Collections.singletonList(alsoNeededProtocol)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", target,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", neededRequest, "toCell", failure,
                        "siteId", target + "#u9", "unitIndex", 9),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure.alsoNeeded",
                        "kind", "exception_guard",
                        "transferKind", "GUARD", "method", target,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", alsoNeededRequest, "toCell", failure,
                        "siteId", target + "#u9", "unitIndex", 9));
        File regions = new File(folder.getRoot(),
                "port-demand-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "port-demand-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(neededWriter, noiseWriter, producer,
                                target),
                        Arrays.asList(
                                activation("REGION.neededWriter", 1,
                                        "STATE_CONTEXT", neededWriter),
                                activation("REGION.noiseWriter", 2,
                                        "STATE_CONTEXT", noiseWriter),
                                activation("REGION.producer", 3,
                                        "PROTOCOL_CONTEXT", producer),
                                activation("REGION.target", 4,
                                        "EXCEPTION_CONTEXT", target)));

        assertEquals(3, retainedInstanceCount(result));
        assertEquals(3, result.regions.size());
        assertEquals(3, result.regionEdges.size());
        String retainedEdges = Files.readAllLines(edges.toPath(),
                StandardCharsets.UTF_8).toString();
        assertTrue(retainedEdges.contains("example.needed"));
        assertTrue(retainedEdges.contains("example.alsoNeeded"));
        assertTrue(retainedEdges.contains(neededField));
        assertFalse(retainedEdges.contains("example.noise"));
        assertFalse(retainedEdges.contains(noiseField));

        JsonObject retainedProducer = null;
        for (String row : Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8)) {
            JsonObject region = GSON.fromJson(row, JsonObject.class);
            if ("REGION.producer".equals(
                    region.get("regionId").getAsString())) {
                retainedProducer = region;
            }
        }
        assertTrue(retainedProducer != null);
        assertEquals(1, retainedProducer.getAsJsonArray(
                "symbolicInputs").size());
        assertEquals(2, retainedProducer.getAsJsonArray("outputs").size());
        assertTrue(retainedProducer.getAsJsonArray("symbolicInputs")
                .toString().contains(neededField));
        assertFalse(retainedProducer.getAsJsonArray("symbolicInputs")
                .toString().contains(noiseField));
        assertTrue(retainedProducer.getAsJsonArray("outputs")
                .toString().contains("example.needed"));
        assertTrue(retainedProducer.getAsJsonArray("outputs")
                .toString().contains("example.alsoNeeded"));
        assertFalse(retainedProducer.getAsJsonArray("outputs")
                .toString().contains("example.noise"));
    }

    @Test
    public void sharedChannelKeepsFiveOccurrenceInterleavingAlternatives()
            throws Exception {
        File skeleton = writeRows("closure-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.writer",
                        "rootMethod", WRITER, "anchorMethod", WRITER,
                        "methods", Collections.singletonList(WRITER),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", TARGET, "anchorMethod", TARGET,
                        "methods", Collections.singletonList(TARGET),
                        "selection", "EXCEPTION_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.unrelated",
                        "rootMethod", METHOD, "anchorMethod", METHOD,
                        "methods", Collections.singletonList(METHOD),
                        "selection", "STATE_CONTEXT"));
        String declaration = "<example.State: int value>";
        Map<String, Object> firstWrite = fieldBinding(
                "REGION.writer", 1, WRITER, 5, declaration, "7");
        Map<String, Object> latestWrite = fieldBinding(
                "REGION.writer", 2, WRITER, 15, declaration, "7");
        Map<String, Object> reversedSameLaneWrite = fieldBinding(
                "REGION.writer", 5, WRITER, 20, declaration, "7");
        List<Map<String, Object>> reads = new ArrayList<>();
        for (long seq : Arrays.asList(10L, 12L, 14L, 16L, 18L)) {
            Map<String, Object> read = fieldBinding(
                    "REGION.target", 3, TARGET, seq, declaration, "7");
            read.put("fieldPathDeclarations", Arrays.asList(
                    "<example.TargetRoot: example.State state>",
                    declaration));
            reads.add(read);
        }
        firstWrite.put("fieldPathDeclarations", Arrays.asList(
                "<example.WriterRoot: example.State state>", declaration));
        latestWrite.put("fieldPathDeclarations", Arrays.asList(
                "<example.WriterRoot: example.State state>", declaration));
        reversedSameLaneWrite.put("fieldPathDeclarations", Arrays.asList(
                "<example.WriterRoot: example.State state>", declaration));
        String local = TARGET + "::$value";
        String failure = TARGET + "#u12#exception:example.Failure";
        File refined = writeRows("closure-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE", "method", WRITER,
                        "toCell", declaration,
                        "regionIds", Collections.singletonList(
                                "REGION.writer"),
                        "runtimeFieldBindings", Arrays.asList(
                                firstWrite, latestWrite,
                                reversedSameLaneWrite)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", TARGET,
                        "fromCell", declaration, "toCell", local,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "runtimeFieldBindings", reads),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", TARGET,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", local, "toCell", failure,
                        "siteId", TARGET + "#u12", "unitIndex", 12));
        File regions = new File(folder.getRoot(), "closure-regions.jsonl");
        File edges = new File(folder.getRoot(), "closure-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(WRITER, TARGET, METHOD), Arrays.asList(
                                activation("REGION.writer", 1,
                                        "STATE_CONTEXT", WRITER, 13),
                                activation("REGION.writer", 2,
                                        "STATE_CONTEXT", WRITER, 12),
                                activation("REGION.writer", 5,
                                        "STATE_CONTEXT", WRITER, 13),
                                activationAtFatalSite("REGION.target", 3,
                                        "EXCEPTION_CONTEXT", TARGET, 13,
                                        TARGET + "#u12"),
                                activation("REGION.unrelated", 4,
                                        "STATE_CONTEXT", METHOD)));

        assertEquals(3, retainedInstanceCount(result));
        assertEquals(2, result.regions.size());
        java.util.List<String> rows = Files.readAllLines(edges.toPath(),
                StandardCharsets.UTF_8);
        assertEquals(10, rows.size());
        Set<Long> readerEvents = new java.util.LinkedHashSet<>();
        int sameLaneAlternatives = 0;
        int crossLaneAlternatives = 0;
        for (String row : rows) {
            JsonObject edge = GSON.fromJson(row, JsonObject.class);
            long writer = edge.get("fromRootCallId").getAsLong();
            readerEvents.add(edge.get("readerEventSeq").getAsLong());
            if (writer == 1
                    && edge.get("programOrderRequired").getAsBoolean()) {
                sameLaneAlternatives++;
            }
            if (writer == 2
                    && !edge.get("programOrderRequired").getAsBoolean()
                    && edge.get("writerEventSeq").getAsLong() == 15) {
                crossLaneAlternatives++;
            }
            assertEquals(3, edge.get("toRootCallId").getAsLong());
            assertEquals("VALUE_FRONTIER",
                    edge.get("dependencyRole").getAsString());
            assertTrue(edge.get("readerEventSeq").getAsLong() <= 18);
        }
        assertEquals(5, readerEvents.size());
        assertEquals(5, sameLaneAlternatives);
        assertEquals(5, crossLaneAlternatives);

        for (String row : Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8)) {
            JsonObject region = GSON.fromJson(row, JsonObject.class);
            if (!"REGION.target".equals(
                    region.get("regionId").getAsString())) {
                continue;
            }
            assertEquals(5, region.getAsJsonArray("symbolicInputs")
                    .get(0).getAsJsonObject()
                    .getAsJsonArray("runtimeAccesses").size());
        }
    }

    @Test
    public void sameDeclaredFieldOnDifferentObjectsCannotRetainARegion()
            throws Exception {
        File skeleton = writeRows("coordinated-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.writer",
                        "rootMethod", WRITER, "anchorMethod", WRITER,
                        "methods", Collections.singletonList(WRITER),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", TARGET, "anchorMethod", TARGET,
                        "methods", Collections.singletonList(TARGET),
                        "selection", "EXCEPTION_CONTEXT"));
        String field = "<example.State: int value>";
        String local = TARGET + "::$value";
        String failure = TARGET + "#u9#exception:example.Failure";
        File refined = writeRows("coordinated-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE", "method", WRITER,
                        "regionIds", Collections.singletonList(
                                "REGION.writer"),
                        "toCell", field,
                        "runtimeFieldBindings", Arrays.asList(
                                fieldBinding("REGION.writer", 1, WRITER,
                                        5, field, "8", 100),
                                fieldBinding("REGION.writer", 1, WRITER,
                                        15, field, "9", 100))),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", TARGET,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", field, "toCell", local,
                        "runtimeFieldBindings", Collections.singletonList(
                                fieldBinding("REGION.target", 2, TARGET,
                                        8, field, "7", 200))),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", TARGET,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", local, "toCell", failure,
                        "siteId", TARGET + "#u9", "unitIndex", 9));
        File regions = new File(folder.getRoot(),
                "coordinated-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "coordinated-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(WRITER, TARGET), Arrays.asList(
                                activation("REGION.writer", 1,
                                        "STATE_CONTEXT", WRITER, 7),
                                activation("REGION.target", 2,
                                        "EXCEPTION_CONTEXT", TARGET, 7)));

        assertEquals(1, result.regions.size());
        assertEquals(1, retainedInstanceCount(result));
        assertEquals(0, result.regionEdges.size());
        assertTrue(Files.readAllLines(edges.toPath(),
                StandardCharsets.UTF_8).isEmpty());
        JsonObject retained = GSON.fromJson(Files.readAllLines(
                regions.toPath(), StandardCharsets.UTF_8).get(0),
                JsonObject.class);
        assertEquals("REGION.target", retained.get("regionId").getAsString());
    }

    @Test
    public void constructorOnlyFieldDoesNotCreateCoordinationFlow()
            throws Exception {
        File skeleton = writeRows("constructor-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.writer",
                        "rootMethod", WRITER, "anchorMethod", WRITER,
                        "methods", Collections.singletonList(WRITER),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", TARGET, "anchorMethod", TARGET,
                        "methods", Collections.singletonList(TARGET),
                        "selection", "EXCEPTION_CONTEXT"));
        String field = "<example.State: example.Owner owner>";
        String local = TARGET + "::$owner";
        String failure = TARGET + "#u9#exception:example.Failure";
        File refined = writeRows("constructor-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE",
                        "method", "<example.State: void <init>()>",
                        "regionIds", Collections.singletonList(
                                "REGION.writer"),
                        "toCell", field,
                        "runtimeFieldBindings", Collections.singletonList(
                                fieldBinding("REGION.writer", 1, WRITER,
                                        5, field, "", 100))),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", TARGET,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", field, "toCell", local,
                        "runtimeFieldBindings", Collections.singletonList(
                                fieldBinding("REGION.target", 2, TARGET,
                                        8, field, "", 200))),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", TARGET,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "fromCell", local, "toCell", failure,
                        "siteId", TARGET + "#u9", "unitIndex", 9));
        File regions = new File(folder.getRoot(),
                "constructor-regions.jsonl");
        File edges = new File(folder.getRoot(), "constructor-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(WRITER, TARGET), Arrays.asList(
                                activation("REGION.writer", 1,
                                        "STATE_CONTEXT", WRITER),
                                activation("REGION.target", 2,
                                        "EXCEPTION_CONTEXT", TARGET)));

        assertEquals(1, result.regions.size());
        assertEquals(0, result.regionEdges.size());
    }

    @Test
    public void demandedConstructorLeafFeedsLaterActivationOfSameRegion()
            throws Exception {
        assertSameRegionConstructorDependency(true);
    }

    @Test
    public void laterActivationDoesNotRetainEarlierOccurrenceWithoutExactEdge()
            throws Exception {
        assertSameRegionConstructorDependency(false);
    }

    private void assertSameRegionConstructorDependency(boolean exactEdge)
            throws Exception {
        String root = "<example.Worker: void run()>";
        String constructor = "<example.Payload: void <init>(int)>";
        String field = "<example.Payload: int value>";
        String local = root + "::$value";
        String failure = root + "#u9#exception:example.Failure";
        File skeleton = writeRows("constructor-leaf-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.worker",
                        "rootMethod", root, "anchorMethod", root,
                        "methods", Arrays.asList(root, constructor),
                        "selection", "EXCEPTION_CONTEXT"));
        Map<String, Object> write = fieldBinding(
                "REGION.worker", 1, constructor, 5, field, "7", 100);
        write.put("fieldPath", Collections.singletonList("value"));
        Map<String, Object> read = fieldBinding(
                "REGION.worker", 2, root, 8, field, "7",
                exactEdge ? 100 : 101);
        read.put("fieldPath", Collections.singletonList("value"));
        File refined = writeRows("constructor-leaf-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.constructor.write",
                        "kind", "field_write", "transferKind", "HEAP_WRITE",
                        "method", constructor, "siteId", constructor + "#u5",
                        "unitIndex", 5, "fromCell", constructor + "::i0",
                        "toCell", field,
                        "regionIds", Collections.singletonList(
                                "REGION.worker"),
                        "runtimeFieldBindings", Collections.singletonList(
                                write)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.later.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", root,
                        "siteId", root + "#u8", "unitIndex", 8,
                        "fromCell", field, "toCell", local,
                        "regionIds", Collections.singletonList(
                                "REGION.worker"),
                        "runtimeFieldBindings", Collections.singletonList(
                                read)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", root,
                        "regionIds", Collections.singletonList(
                                "REGION.worker"),
                        "fromCell", local, "toCell", failure,
                        "siteId", root + "#u9", "unitIndex", 9));
        File regions = new File(folder.getRoot(),
                "constructor-leaf-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "constructor-leaf-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(root, constructor), Arrays.asList(
                                activation("REGION.worker", 1,
                                        "STATE_CONTEXT", root, 7),
                                activationAtFatalSite("REGION.worker", 2,
                                        "EXCEPTION_CONTEXT", root, 7,
                                        root + "#u9")));

        assertEquals(1, result.regions.size());
        assertEquals(exactEdge ? 2 : 1, retainedInstanceCount(result));
        assertEquals(exactEdge ? 1 : 0, result.regionEdges.size());
        if (!exactEdge) {
            assertTrue(Files.readAllLines(edges.toPath(),
                    StandardCharsets.UTF_8).isEmpty());
            return;
        }
        JsonObject flow = GSON.fromJson(Files.readAllLines(edges.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        assertEquals("RUNTIME_FIELD_FLOW", flow.get("kind").getAsString());
        assertEquals(1, flow.get("fromRootCallId").getAsLong());
        assertEquals(2, flow.get("toRootCallId").getAsLong());
        assertEquals(field, flow.getAsJsonArray("fieldPathDeclarations")
                .get(0).getAsString());
        assertTrue(Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8).get(0).contains(constructor));
    }

    @Test
    public void unclosedPrimitiveBelowReferenceBoundaryReplaysConcrete()
            throws Exception {
        String writer = "<example.Writer: void run()>";
        String target = "<example.Reader: void run()>";
        String holderPayload =
                "<example.Holder: example.Payload payload>";
        String payloadValue = "<example.Payload: int value>";
        String payloadLocal = target + "::$payload";
        String valueLocal = target + "::$value";
        String failure = target + "#u9#exception:example.Failure";
        File skeleton = writeRows("reference-leaf-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.writer",
                        "rootMethod", writer, "anchorMethod", writer,
                        "methods", Collections.singletonList(writer),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", target, "anchorMethod", target,
                        "methods", Collections.singletonList(target),
                        "selection", "EXCEPTION_CONTEXT"));
        Map<String, Object> write = fieldBinding(
                "REGION.writer", 1, writer, 5, holderPayload, "", 10);
        write.put("valueObjectId", 100);
        write.put("fieldPath", Collections.singletonList("payload"));
        Map<String, Object> readReference = fieldBinding(
                "REGION.target", 2, target, 7, holderPayload, "", 10);
        readReference.put("valueObjectId", 100);
        readReference.put("fieldPath",
                Collections.singletonList("payload"));
        Map<String, Object> readPrimitive = fieldBinding(
                "REGION.target", 2, target, 8, payloadValue, "7", 100);
        File refined = writeRows("reference-leaf-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.reference.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE", "method", writer,
                        "siteId", writer + "#u5", "unitIndex", 5,
                        "fromCell", writer + "::$payload",
                        "toCell", holderPayload,
                        "regionIds", Collections.singletonList(
                                "REGION.writer"),
                        "runtimeFieldBindings",
                        Collections.singletonList(write)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.reference.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", target,
                        "siteId", target + "#u7", "unitIndex", 7,
                        "fromCell", holderPayload, "toCell", payloadLocal,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "runtimeFieldBindings",
                        Collections.singletonList(readReference)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.receiver", "kind", "receiver_dependency",
                        "transferKind", "VALUE_PASS", "method", target,
                        "fromCell", payloadLocal, "toCell", valueLocal,
                        "regionIds", Collections.singletonList(
                                "REGION.target")),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.primitive.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", target,
                        "siteId", target + "#u8", "unitIndex", 8,
                        "fromCell", payloadValue, "toCell", valueLocal,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "runtimeFieldBindings",
                        Collections.singletonList(readPrimitive)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", target,
                        "fromCell", valueLocal, "toCell", failure,
                        "siteId", target + "#u9", "unitIndex", 9,
                        "regionIds", Collections.singletonList(
                                "REGION.target")));
        File regions = new File(folder.getRoot(),
                "reference-leaf-regions.jsonl");
        File edges = new File(folder.getRoot(),
                "reference-leaf-edges.jsonl");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(writer, target), Arrays.asList(
                                activation("REGION.writer", 1,
                                        "STATE_CONTEXT", writer, 1),
                                activationAtFatalSite("REGION.target", 2,
                                        "EXCEPTION_CONTEXT", target, 2,
                                        target + "#u9")));

        assertEquals(2, result.regions.size());
        assertEquals(2, retainedInstanceCount(result));
        assertEquals(1, result.regionEdges.size());
        JsonObject targetRegion = null;
        for (String row : Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8)) {
            JsonObject candidate = GSON.fromJson(row, JsonObject.class);
            if ("REGION.target".equals(
                    candidate.get("regionId").getAsString())) {
                targetRegion = candidate;
            }
        }
        assertTrue(targetRegion != null);
        JsonObject valueInput = inputForField(targetRegion, payloadValue);
        assertEquals("CONCRETE_REFERENCE_BOUNDARY_REPLAY",
                valueInput.get("symbolicDemand").getAsString());
        assertEquals("EXACT_TRACE_REFERENCE_LEAF_UNDER_APPROX_V1",
                valueInput.get("replayAuthority").getAsString());
    }


    @Test
    public void trustedResponseProjectsScalarLeafAndKeepsCarrierConcrete()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar");

        assertEquals(2, fixture.result.regions.size());
        List<JsonObject> edges = readJsonLines(fixture.edges);
        assertEquals(1, edges.size());
        JsonObject projection = edges.get(0);
        assertEquals("RUNTIME_PROTOCOL_FLOW",
                projection.get("kind").getAsString());
        assertEquals("SCALAR_LEAF_VALUE",
                projection.get("projectionKind").getAsString());
        assertEquals("CONFIGURED_RPC_BOUNDARY_SCALAR_PATH_V1",
                projection.get("projectionSelectionAuthority")
                        .getAsString());
        assertEquals("TRUSTED_CONFIGURED_RPC_BOUNDARY_SCALAR_V1",
                projection.get("rpcProjectionAuthority").getAsString());
        assertEquals("TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                projection.get("authority").getAsString());
        assertEquals("int", projection.get("javaType").getAsString());
        assertFalse(projection.has("primitiveValue"));

        JsonObject producer = fixture.region("REGION.producer");
        JsonObject derived = null;
        for (com.google.gson.JsonElement element
                : producer.getAsJsonArray("outputs")) {
            JsonObject output = element.getAsJsonObject();
            if (output.has("rpcDescendantProjectionOutput")) {
                derived = output;
            }
        }
        assertTrue(derived != null);
        assertEquals("int", derived.get("javaType").getAsString());
        assertFalse(derived.has("symbolicDemand"));
        assertFalse(derived.has("containerCapacity"));

        // The wire carrier object never becomes a symbolic port; only the
        // demanded scalar leaf below it does.
        JsonObject consumer = fixture.region("REGION.consumer");
        assertEquals(1, consumer.getAsJsonArray("symbolicInputs").size());
        JsonObject leaf = inputForField(consumer,
                "<example.WireResponse: int keyId>");
        assertEquals("int", leaf.get("javaType").getAsString());
        assertEquals(DependencyRole.VALUE_FRONTIER,
                leaf.get("dependencyRole").getAsString());
        assertTrue(leaf.get("rpcDescendantProjectionInput").getAsBoolean());
        assertFalse(leaf.has("symbolicDemand"));
        assertEquals(projection.get("toPort").getAsString(),
                leaf.get("portId").getAsString());
    }

    @Test
    public void configuredScalarUsesEarlierWriterOutsideProtocolRegion()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-earlier-region", false, true, true, "");

        JsonObject projection = null;
        for (JsonObject edge : readJsonLines(fixture.edges)) {
            if (edge.has("projectionKind")
                    && "SCALAR_LEAF_VALUE".equals(
                    edge.get("projectionKind").getAsString())) {
                projection = edge;
            }
        }
        assertTrue(projection != null);
        assertEquals("REGION.writer",
                projection.get("fromRegion").getAsString());
        assertEquals(3L, projection.get("fromRootCallId").getAsLong());
        assertEquals(14L, projection.get("writerEventSeq").getAsLong());

        JsonObject writer = fixture.region("REGION.writer");
        JsonObject derived = null;
        for (com.google.gson.JsonElement element
                : writer.getAsJsonArray("outputs")) {
            JsonObject output = element.getAsJsonObject();
            if (output.has("rpcDescendantProjectionOutput")) {
                derived = output;
            }
        }
        assertTrue(derived != null);
    }

    @Test
    public void configuredScalarWithoutConsumerReadCreatesNoBlocker()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-no-consumer", false, false, false, "");

        JsonObject consumer = fixture.region("REGION.consumer");
        assertFalse(consumer.has("rpcBoundaryScalarGaps"));
        for (com.google.gson.JsonElement element
                : consumer.getAsJsonArray("symbolicInputs")) {
            JsonObject input = element.getAsJsonObject();
            assertFalse(input.has("rpcProjectionAdmission"));
            assertFalse(input.has("rpcProjectionBlocker"));
        }
        for (JsonObject edge : readJsonLines(fixture.edges)) {
            assertFalse(edge.has("projectionKind"));
        }
    }

    @Test
    public void configuredScalarWithProvenExternalPrestateStaysConcrete()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-external-prestate", false, false, true, "",
                false, externalPrestateEvidence(
                        "server", 100,
                        "<example.WireResponse: int keyId>", 1));

        JsonObject consumer = fixture.region("REGION.consumer");
        JsonObject leaf = inputForField(consumer,
                "<example.WireResponse: int keyId>");
        assertEquals("CONCRETE_UNPROJECTED_BOUNDARY_ACCESS",
                leaf.get("symbolicDemand").getAsString());
        assertEquals("EXACT_ACTIVATION_EXTERNAL_PRESTATE_WRITE_V1",
                leaf.get("rpcConcreteRootAuthority").getAsString());
        assertEquals("ACTIVATION_EXTERNAL_PRESTATE",
                leaf.get("rpcConcreteRootReason").getAsString());
        assertEquals(1L,
                leaf.get("rpcExternalPrestateWriteEventSeq").getAsLong());
        assertFalse(leaf.has("rpcProjectionAdmission"));
        assertFalse(leaf.has("rpcProjectionBlocker"));
        assertFalse(consumer.has("rpcBoundaryScalarGaps"));
        for (JsonObject edge : readJsonLines(fixture.edges)) {
            assertFalse(edge.has("projectionKind"));
        }
    }

    @Test
    public void emptySourceWithoutExternalPrestateProofStillBlocks()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-unproved-prestate", false, false, true, "",
                false, null);

        JsonObject consumer = fixture.region("REGION.consumer");
        JsonObject leaf = inputForField(consumer,
                "<example.WireResponse: int keyId>");
        assertEquals("BLOCKED",
                leaf.get("rpcProjectionAdmission").getAsString());
        assertEquals("MISSING_CONFIGURED_BOUNDARY_SCALAR_SOURCE",
                leaf.get("rpcProjectionBlocker").getAsString());
        assertEquals(1,
                consumer.getAsJsonArray("rpcBoundaryScalarGaps").size());
    }

    @Test
    public void sourceWithoutExactOutputStillBlocks() throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-missing-source-output", false, false, true, "",
                true, null, false);

        JsonObject consumer = fixture.region("REGION.consumer");
        JsonObject leaf = inputForField(consumer,
                "<example.WireResponse: int keyId>");
        assertTrue(consumer.toString(), leaf.has("rpcProjectionAdmission"));
        assertEquals("BLOCKED",
                leaf.get("rpcProjectionAdmission").getAsString());
        assertEquals("MISSING_EXACT_CONFIGURED_BOUNDARY_SCALAR_OUTPUT",
                leaf.get("rpcProjectionBlocker").getAsString());
        assertEquals(1,
                consumer.getAsJsonArray("rpcBoundaryScalarGaps").size());
    }

    @Test
    public void boundaryGapRemainsAnExactLedgerEntryWithoutBroadcasting()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-gap", true);

        JsonObject consumer = fixture.region("REGION.consumer");
        JsonObject leaf = inputForField(consumer,
                "<example.WireResponse: int keyId>");
        assertFalse(leaf.has("rpcProjectionAdmission"));
        assertFalse(leaf.has("rpcProjectionBlocker"));
        JsonArray gaps = consumer.getAsJsonArray("rpcBoundaryScalarGaps");
        assertEquals(1, gaps.size());
        JsonObject gap = gaps.get(0).getAsJsonObject();
        assertEquals("example.fetch", gap.get("mappingId").getAsString());
        assertEquals("keyId", gap.get("leafId").getAsString());
        assertEquals(2L,
                gap.get("rpcBoundaryConsumerRootCallId").getAsLong());
    }

    @Test
    public void producerEmptyConsumerValueAttachesBlockingGap()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-empty", true, false, true,
                "NO_CONFIGURED_SCALAR_ELEMENTS");

        JsonObject consumer = fixture.region("REGION.consumer");
        JsonArray gaps = consumer.getAsJsonArray("rpcBoundaryScalarGaps");
        assertEquals(1, gaps.size());
        assertEquals("NO_CONFIGURED_SCALAR_ELEMENTS", gaps.get(0)
                .getAsJsonObject().get("gap").getAsString());
        JsonObject leaf = inputForField(consumer,
                "<example.WireResponse: int keyId>");
        assertFalse(leaf.has("rpcProjectionAdmission"));
        assertFalse(leaf.has("rpcProjectionBlocker"));

        for (JsonObject edge : readJsonLines(fixture.edges)) {
            assertFalse(edge.has("projectionKind"));
        }
    }

    @Test
    public void completeEmptyScalarSetIsDiagnosticOnly()
            throws Exception {
        ProjectionFixture fixture = rpcScalarLeafProjectionFixture(
                "rpc-scalar-both-empty", true, false, false,
                "NO_CONFIGURED_SCALAR_ELEMENTS");

        JsonObject consumer = fixture.region("REGION.consumer");
        assertFalse(consumer.has("rpcBoundaryScalarGaps"));
        for (JsonObject edge : readJsonLines(fixture.edges)) {
            assertFalse(edge.has("projectionKind"));
        }
    }

    @Test
    public void consumerFenceUsesEachCandidateDirectionAndHalfOpenCorridor()
            throws Exception {
        Map<String, Object> current = protocolFenceFlow(
                "mapping.current", "RESPONSE", 10, 11, 12);
        Map<String, Object> unrelatedRequest = protocolFenceFlow(
                "mapping.request", "REQUEST", 19, 20, 21);
        Map<String, Object> nextResponse = protocolFenceFlow(
                "mapping.next", "RESPONSE", 30, 31, 32);

        java.lang.reflect.Method fence = RuntimeSelectedRegionFinalizer.class
                .getDeclaredMethod("nextConsumerBoundary", List.class,
                        Map.class, long.class);
        fence.setAccessible(true);
        long crossDirection = ((Number) fence.invoke(null,
                Arrays.asList(current, unrelatedRequest, nextResponse),
                current, 18L)).longValue();
        assertEquals(21L, crossDirection);

        long consecutiveResponses = ((Number) fence.invoke(null,
                Arrays.asList(current, nextResponse), current, 18L))
                .longValue();
        assertEquals(30L, consecutiveResponses);
        assertTrue(29L < consecutiveResponses);
        assertFalse(30L < consecutiveResponses);
    }

    @Test
    public void boundaryScalarIdentitySeparatesExactProtocolExchanges()
            throws Exception {
        Map<String, Object> first = object(
                "mappingId", "example.fetch", "direction", "RESPONSE",
                "port", "response", "leafId", "keyId",
                "declaredPath", Collections.singletonList(
                        "<example.WireResponse: int keyId>"),
                "arrayIndices", Collections.singletonList(0),
                "javaType", "int", "containerBound", 32,
                "producerBoundaryEventSeq", 100L,
                "consumerBoundaryEventSeq", 200L);
        Map<String, Object> second = new LinkedHashMap<>(first);
        second.put("producerBoundaryEventSeq", 300L);
        second.put("consumerBoundaryEventSeq", 400L);

        java.lang.reflect.Method identity =
                RuntimeSelectedRegionFinalizer.class.getDeclaredMethod(
                        "boundaryScalarIdentity", Map.class);
        identity.setAccessible(true);
        String firstIdentity = String.valueOf(identity.invoke(null, first));
        String repeatedFirstIdentity = String.valueOf(
                identity.invoke(null, first));
        String secondIdentity = String.valueOf(
                identity.invoke(null, second));

        assertEquals(firstIdentity, repeatedFirstIdentity);
        assertFalse(firstIdentity.equals(secondIdentity));
        assertTrue(firstIdentity.endsWith("100\n200"));
        assertTrue(secondIdentity.endsWith("300\n400"));
    }


    @Test
    public void sharedCarrierAccessorLeafBindsItsExactProducerWrite()
            throws Exception {
        for (boolean accessor : new boolean[]{false, true}) {
            ProjectionFixture fixture = sharedCarrierLeafFixture(
                    "shared-carrier-" + accessor, accessor);
            JsonObject leafEdge = null;
            for (JsonObject edge : readJsonLines(fixture.edges)) {
                if ("<example.Payload: int value>".equals(
                        edge.getAsJsonArray("fieldPathDeclarations").get(0)
                                .getAsString())) {
                    leafEdge = edge;
                }
            }
            assertTrue(leafEdge != null);
            assertEquals("RUNTIME_FIELD_FLOW",
                    leafEdge.get("kind").getAsString());
            assertEquals("REGION.writer",
                    leafEdge.get("fromRegion").getAsString());

            JsonObject consumer = fixture.region("REGION.target");
            JsonObject leaf = inputForField(consumer,
                    "<example.Payload: int value>");
            assertEquals(leafEdge.get("toPort").getAsString(),
                    leaf.get("portId").getAsString());
            assertFalse(leaf.has("symbolicDemand"));

            // The shared reference carrier itself is never projected into a
            // symbolic value; it only names the object the leaf belongs to.
            JsonObject carrier = inputForField(consumer,
                    "<example.Holder: example.Payload payload>");
            assertFalse(carrier.has("symbolicDemand"));
            assertFalse(carrier.has("rpcDescendantProjectionInput"));
        }
    }

    private ProjectionFixture sharedCarrierLeafFixture(
            String prefix, boolean accessor) throws Exception {
        String writer = "<example.Writer: void run()>";
        String target = "<example.Reader: void run()>";
        String holderPayload =
                "<example.Holder: example.Payload payload>";
        String payloadValue = "<example.Payload: int value>";
        String getValue = "<example.Payload: int getValue()>";
        String payloadLocal = target + "::$payload";
        String valueLocal = target + "::$value";
        String failure = target + "#u9#exception:example.Failure";

        File skeleton = writeRows(prefix + "-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.writer",
                        "rootMethod", writer, "anchorMethod", writer,
                        "methods", Collections.singletonList(writer),
                        "selection", "STATE_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.target",
                        "rootMethod", target, "anchorMethod", target,
                        "methods", Collections.singletonList(target),
                        "selection", "EXCEPTION_CONTEXT"));

        Map<String, Object> leafWrite = object(
                "regionId", "REGION.writer", "rootCallId", 1,
                "rootKind", "OBSERVED_FIELD_RECEIVER", "rootMethod", writer,
                "rootCell", writer + "#u4.fieldReceiver",
                "rootObjectId", 100, "fieldReceiverObjectId", 100,
                "valueObjectId", 0, "primitiveValue", "7", "eventSeq", 4,
                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations",
                Collections.singletonList(payloadValue));
        Map<String, Object> publish = object(
                "regionId", "REGION.writer", "rootCallId", 1,
                "rootKind", "RECEIVER", "rootMethod", writer,
                "rootCell", writer + ".receiver", "rootObjectId", 10,
                "fieldReceiverObjectId", 10, "valueObjectId", 100,
                "eventSeq", 5, "bindingKind", "ACTIVATION_FIELD_ACCESS",
                "fieldPath", Collections.singletonList("payload"),
                "fieldPathDeclarations",
                Collections.singletonList(holderPayload));
        Map<String, Object> carrierRead = object(
                "regionId", "REGION.target", "rootCallId", 2,
                "rootKind", "RECEIVER", "rootMethod", target,
                "rootCell", target + ".receiver", "rootObjectId", 10,
                "fieldReceiverObjectId", 10, "valueObjectId", 100,
                "eventSeq", 7, "bindingKind", "ACTIVATION_FIELD_ACCESS",
                "fieldPath", Collections.singletonList("payload"),
                "fieldPathDeclarations",
                Collections.singletonList(holderPayload));
        Map<String, Object> leafRead = object(
                "regionId", "REGION.target", "rootCallId", 2,
                "rootKind", "OBSERVED_FIELD_RECEIVER", "rootMethod", target,
                "rootCell", target + "#u8.fieldReceiver",
                "rootObjectId", 100, "fieldReceiverObjectId", 100,
                "valueObjectId", 0, "primitiveValue", "7", "eventSeq", 8,
                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations",
                Collections.singletonList(payloadValue));
        Map<String, Object> accessorRead = object(
                "regionId", "REGION.target", "rootCallId", 2,
                "callId", 2, "invocationId", 41,
                "callerMethod", target, "unitIndex", 8,
                "siteId", target + "#u8", "eventSeq", 8,
                "receiverObjectId", 100,
                "receiverRuntimeType", "example.Payload",
                "valueObjectId", 0, "primitiveValue", "7",
                "accessorOccurrence", 1,
                "declaredCallee", getValue,
                "declaredFieldSignature", payloadValue,
                "accessorImplementationMethod", getValue,
                "authority", "EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1");

        Map<String, Object> leafReadRow = accessor
                ? object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.leaf.read", "kind", "accessor_field_return",
                "transferKind", "HEAP_READ", "method", target,
                "siteId", target + "#u8", "unitIndex", 8,
                "invoke", getValue,
                "accessorImplementationMethod", getValue,
                "declaredFieldSignature", payloadValue,
                "runtimeObserved", true,
                "fromCell", payloadValue, "toCell", valueLocal,
                "regionIds", Collections.singletonList("REGION.target"),
                "runtimeAccessorBindings",
                Collections.singletonList(accessorRead))
                : object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.leaf.read", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", target,
                "siteId", target + "#u8", "unitIndex", 8,
                "fromCell", payloadValue, "toCell", valueLocal,
                "regionIds", Collections.singletonList("REGION.target"),
                "runtimeFieldBindings",
                Collections.singletonList(leafRead));

        File refined = writeRows(prefix + "-refined.jsonl",
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.leaf.write", "kind", "field_write",
                        "transferKind", "HEAP_WRITE", "method", writer,
                        "siteId", writer + "#u4", "unitIndex", 4,
                        "fromCell", writer + "::$value",
                        "toCell", payloadValue,
                        "regionIds", Collections.singletonList(
                                "REGION.writer"),
                        "runtimeFieldBindings",
                        Collections.singletonList(leafWrite)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.publish", "kind", "field_write",
                        "transferKind", "HEAP_WRITE", "method", writer,
                        "siteId", writer + "#u5", "unitIndex", 5,
                        "fromCell", writer + "::$payload",
                        "toCell", holderPayload,
                        "regionIds", Collections.singletonList(
                                "REGION.writer"),
                        "runtimeFieldBindings",
                        Collections.singletonList(publish)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.carrier.read", "kind", "field_read",
                        "transferKind", "HEAP_READ", "method", target,
                        "siteId", target + "#u7", "unitIndex", 7,
                        "fromCell", holderPayload, "toCell", payloadLocal,
                        "regionIds", Collections.singletonList(
                                "REGION.target"),
                        "runtimeFieldBindings",
                        Collections.singletonList(carrierRead)),
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.receiver", "kind", "receiver_dependency",
                        "transferKind", "VALUE_PASS", "method", target,
                        "fromCell", payloadLocal, "toCell", valueLocal,
                        "regionIds", Collections.singletonList(
                                "REGION.target")),
                leafReadRow,
                object("schemaVersion", 3, "refinementSchemaVersion", 1,
                        "graphKind", "RUNTIME_REFINED_DATAFLOW",
                        "id", "DF.failure", "kind", "exception_guard",
                        "transferKind", "GUARD", "method", target,
                        "fromCell", valueLocal, "toCell", failure,
                        "siteId", target + "#u9", "unitIndex", 9,
                        "regionIds", Collections.singletonList(
                                "REGION.target")));
        File regions = new File(folder.getRoot(), prefix + "-regions.jsonl");
        File edges = new File(folder.getRoot(), prefix + "-edges.jsonl");
        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        refined, skeleton, regions, edges,
                        Arrays.asList(writer, target), Arrays.asList(
                                activation("REGION.writer", 1,
                                        "STATE_CONTEXT", writer, 1),
                                activationAtFatalSite("REGION.target", 2,
                                        "EXCEPTION_CONTEXT", target, 2,
                                        target + "#u9")));
        return new ProjectionFixture(regions, edges, result);
    }

    private ProjectionFixture rpcScalarLeafProjectionFixture(String prefix)
            throws Exception {
        return rpcScalarLeafProjectionFixture(prefix, false, false, true, "");
    }

    private ProjectionFixture rpcScalarLeafProjectionFixture(
            String prefix, boolean gapOnly) throws Exception {
        return rpcScalarLeafProjectionFixture(prefix, gapOnly, false, true,
                "MISSING_CONFIGURED_BOUNDARY_SCALAR_SIDE");
    }

    @SuppressWarnings("unchecked")
    private ProjectionFixture rpcScalarLeafProjectionFixture(
            String prefix, boolean gapOnly, boolean sourceOutsideProtocolRegion,
            boolean includeConsumerRead, String gapReason) throws Exception {
        return rpcScalarLeafProjectionFixture(prefix, gapOnly,
                sourceOutsideProtocolRegion, includeConsumerRead, gapReason,
                true, null);
    }

    @SuppressWarnings("unchecked")
    private ProjectionFixture rpcScalarLeafProjectionFixture(
            String prefix, boolean gapOnly, boolean sourceOutsideProtocolRegion,
            boolean includeConsumerRead, String gapReason,
            boolean includeSourceWrite,
            Map<String, Object> externalPrestateEvidence) throws Exception {
        return rpcScalarLeafProjectionFixture(prefix, gapOnly,
                sourceOutsideProtocolRegion, includeConsumerRead, gapReason,
                includeSourceWrite, externalPrestateEvidence, true);
    }

    @SuppressWarnings("unchecked")
    private ProjectionFixture rpcScalarLeafProjectionFixture(
            String prefix, boolean gapOnly, boolean sourceOutsideProtocolRegion,
            boolean includeConsumerRead, String gapReason,
            boolean includeSourceWrite,
            Map<String, Object> externalPrestateEvidence,
            boolean includeSourceOutput) throws Exception {
        String producer = "<example.Producer: example.WireResponse run()>";
        String consumer = "<example.Consumer: void run()>";
        String writer = "<example.Writer: void update()>";
        String store = "<example.Store: int seed>";
        String wireKeyId = "<example.WireResponse: int keyId>";
        String responsePayload =
                "<example.WireEnvelope: example.WireResponse payload>";
        String producerSeed = producer + "::$seed";
        String producerId = producer + "::$id";
        String response = producer + ".return";
        String received = consumer + "::$response";
        String consumerKeyId = consumer + "::$keyId";
        String failure = consumer + "#u9#exception:example.MissingKey";
        String sourceRegion = sourceOutsideProtocolRegion
                ? "REGION.writer" : "REGION.producer";
        long sourceRootCallId = sourceOutsideProtocolRegion ? 3L : 1L;
        String sourceMethod = sourceOutsideProtocolRegion ? writer : producer;
        String sourceValue = sourceOutsideProtocolRegion
                ? writer + "::$id" : producerId;

        List<Map<String, Object>> skeletonRows = new ArrayList<>();
        skeletonRows.add(
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.producer",
                        "rootMethod", producer, "anchorMethod", producer,
                        "methods", Collections.singletonList(producer),
                        "selection", "STATE_CONTEXT"));
        skeletonRows.add(
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.consumer",
                        "rootMethod", consumer, "anchorMethod", consumer,
                        "methods", Collections.singletonList(consumer),
                        "selection", "EXCEPTION_CONTEXT"));
        if (sourceOutsideProtocolRegion) {
            skeletonRows.add(object("schemaVersion", 3,
                    "kind", "REGION_SKELETON",
                    "regionId", "REGION.writer",
                    "rootMethod", writer, "anchorMethod", writer,
                    "methods", Collections.singletonList(writer),
                    "selection", "STATE_CONTEXT"));
        }
        File skeleton = writeRows(prefix + "-skeleton.jsonl",
                skeletonRows.toArray(new Map[0]));

        Map<String, Object> seedRead = object(
                "regionId", "REGION.producer", "rootCallId", 1,
                "rootKind", "RECEIVER", "rootMethod", producer,
                "rootCell", producer + ".receiver", "rootObjectId", 10,
                "fieldReceiverObjectId", 10, "valueObjectId", 0,
                "primitiveValue", "3", "eventSeq", 13,
                "fieldPath", Collections.singletonList("seed"),
                "fieldPathDeclarations", Collections.singletonList(store));
        Map<String, Object> keyIdWrite = object(
                "regionId", sourceRegion, "rootCallId", sourceRootCallId,
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootMethod", sourceMethod,
                "rootCell", sourceMethod + "#u3.fieldReceiver",
                "process", "server",
                "rootObjectId", 100, "fieldReceiverObjectId", 100,
                "valueObjectId", 0, "primitiveValue", "7", "eventSeq", 14,
                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                "fieldPath", Collections.singletonList("keyId"),
                "fieldPathDeclarations",
                Collections.singletonList(wireKeyId));
        Map<String, Object> payloadRead = object(
                "regionId", "REGION.consumer", "rootCallId", 2,
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootMethod", consumer,
                "rootCell", consumer + "#u3.fieldReceiver",
                "process", "client",
                "rootObjectId", 300, "fieldReceiverObjectId", 300,
                "valueObjectId", 310, "eventSeq", 18,
                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                "fieldPath", Collections.singletonList("payload"),
                "fieldPathDeclarations",
                Collections.singletonList(responsePayload));
        Map<String, Object> keyIdRead = object(
                "regionId", "REGION.consumer", "rootCallId", 2,
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootMethod", consumer,
                "rootCell", consumer + "#u4.fieldReceiver",
                "process", "client",
                "rootObjectId", 310, "fieldReceiverObjectId", 310,
                "valueObjectId", 0, "primitiveValue", "7", "eventSeq", 19,
                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                "fieldPath", Collections.singletonList("keyId"),
                "fieldPathDeclarations",
                Collections.singletonList(wireKeyId));
        Map<String, Object> protocol = object(
                "mappingId", "example.fetch", "port", "response",
                "direction", "RESPONSE", "transport", "RPC",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "fromRegionId", "REGION.producer",
                "toRegionId", "REGION.consumer",
                "fromRootCallId", 1, "toRootCallId", 2,
                "fromCell", response, "toCell", received,
                "callerSiteEventSeq", 10, "sendEventSeq", 11,
                "receiveEventSeq", 12, "producerResultEventSeq", 15,
                "producerResultObjectId", 500,
                "callerResultEventSeq", 18,
                "callerResultObjectId", 300,
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        if (gapOnly) {
            Map<String, Object> scalarGap = object(
                    "mappingId", "example.fetch",
                    "direction", "RESPONSE", "port", "response",
                    "leafId", "keyId",
                    "declaredPath", Collections.singletonList(wireKeyId),
                    "arrayIndices", Collections.emptyList(),
                    "javaType", "int", "containerBound", 0,
                    "authority",
                    "CONFIGURED_RPC_BOUNDARY_SCALAR_GAP_V1",
                    "gap", gapReason,
                    "side", "SERVER", "boundaryEventSeq", 15);
            if ("NO_CONFIGURED_SCALAR_ELEMENTS".equals(gapReason)
                    && !includeConsumerRead) {
                // This is the joined ledger row emitted by the builder only
                // after both exact endpoint observations proved empty.
                scalarGap.put("side", "CLIENT");
                scalarGap.put("boundaryEventSeq", 18L);
                scalarGap.put("bothBoundarySidesCompleteEmpty", true);
                scalarGap.put("producerSide", "SERVER");
                scalarGap.put("producerBoundaryEventSeq", 15L);
                scalarGap.put("producerValueAuthority",
                        "CONFIGURED_RPC_BOUNDARY_SCALAR_GAP_V1");
                scalarGap.put("producerLeafObservationComplete", true);
                scalarGap.put("producerLeafValueCount", 0);
                scalarGap.put("consumerSide", "CLIENT");
                scalarGap.put("consumerBoundaryEventSeq", 18L);
                scalarGap.put("consumerValueAuthority",
                        "CONFIGURED_RPC_BOUNDARY_SCALAR_GAP_V1");
                scalarGap.put("consumerLeafObservationComplete", true);
                scalarGap.put("consumerLeafValueCount", 0);
            }
            protocol.put("runtimeBoundaryScalarGaps",
                    Collections.singletonList(scalarGap));
        } else {
            Map<String, Object> boundaryBinding = object(
                        "mappingId", "example.fetch",
                        "direction", "RESPONSE", "port", "response",
                        "leafId", "keyId",
                        "declaredPath",
                        Collections.singletonList(wireKeyId),
                        "arrayIndices", Collections.emptyList(),
                        "javaType", "int", "containerBound", 0,
                        "authority",
                        "TRUSTED_CONFIGURED_RPC_BOUNDARY_SCALAR_V1",
                        "producerSide", "SERVER",
                        "producerBoundaryEventSeq", 15,
                        "producerProcess", "server",
                        "producerLeafReceiverObjectId", 100,
                        "producerValueAuthority",
                        "EXACT_CONFIGURED_RPC_BOUNDARY_SCALAR_V1",
                        "producerLeafObservationComplete", true,
                        "producerLeafValueCount", 1,
                        "consumerSide", "CLIENT",
                        "consumerBoundaryEventSeq", 18,
                        "consumerProcess", "client",
                        "consumerLeafReceiverObjectId", 310,
                        "consumerValueAuthority",
                        "EXACT_CONFIGURED_RPC_BOUNDARY_SCALAR_V1",
                        "consumerLeafObservationComplete", true,
                        "consumerLeafValueCount", 1);
            if (externalPrestateEvidence != null) {
                boundaryBinding.put("producerExternalPrestateEvidence",
                        externalPrestateEvidence);
            }
            protocol.put("runtimeBoundaryScalarBindings",
                    Collections.singletonList(boundaryBinding));
        }

        List<Map<String, Object>> refinedRows = new ArrayList<>();
        refinedRows.add(object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.seed.read", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", producer,
                "siteId", producer + "#u1", "unitIndex", 1,
                "fromCell", store, "toCell", producerSeed,
                "regionIds", Collections.singletonList("REGION.producer"),
                "runtimeFieldBindings", Collections.singletonList(seedRead)));
        refinedRows.add(object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.derive", "kind", "local_def_use",
                "transferKind", "VALUE_PASS", "method", producer,
                "siteId", producer + "#u2", "unitIndex", 2,
                "fromCell", producerSeed, "toCell", producerId,
                "regionIds", Collections.singletonList("REGION.producer")));
        if (includeSourceWrite) {
            refinedRows.add(object("schemaVersion", 3,
                    "refinementSchemaVersion", 1,
                    "graphKind", "RUNTIME_REFINED_DATAFLOW",
                    "id", "DF.keyid.write", "kind", "field_write",
                    "transferKind", "HEAP_WRITE", "method", sourceMethod,
                    "siteId", sourceMethod + "#u3", "unitIndex", 3,
                    "fromCell", sourceValue, "toCell", wireKeyId,
                    "regionIds", includeSourceOutput
                            ? Collections.singletonList(sourceRegion)
                            : Collections.emptyList(),
                    "runtimeFieldBindings",
                    Collections.singletonList(keyIdWrite)));
        }
        if (sourceOutsideProtocolRegion) {
            Map<String, Object> otherProcessWrite =
                    new LinkedHashMap<>(keyIdWrite);
            otherProcessWrite.put("regionId", "REGION.producer");
            otherProcessWrite.put("rootCallId", 1L);
            otherProcessWrite.put("rootMethod", producer);
            otherProcessWrite.put("rootCell", producer + "#u5.fieldReceiver");
            otherProcessWrite.put("process", "other");
            refinedRows.add(object("schemaVersion", 3,
                    "refinementSchemaVersion", 1,
                    "graphKind", "RUNTIME_REFINED_DATAFLOW",
                    "id", "DF.keyid.write.other-process",
                    "kind", "field_write", "transferKind", "HEAP_WRITE",
                    "method", producer, "siteId", producer + "#u5",
                    "unitIndex", 5, "fromCell", producerId,
                    "toCell", wireKeyId,
                    "regionIds", Collections.singletonList(
                            "REGION.producer"),
                    "runtimeFieldBindings",
                    Collections.singletonList(otherProcessWrite)));
        }
        refinedRows.add(object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.rpc", "kind", "protocol_transfer",
                "transferKind", "PROTOCOL_TRANSFER",
                "method", producer, "fromCell", response,
                "toCell", received, "regionIds", Arrays.asList(
                        "REGION.producer", "REGION.consumer"),
                "runtimeProtocolBindings", Collections.singletonList(
                        protocol)));
        refinedRows.add(object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.decode.owner", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", consumer,
                "siteId", consumer + "#u3", "unitIndex", 3,
                "fromCell", responsePayload,
                "toCell", consumer + "::$payload",
                "regionIds", Collections.singletonList("REGION.consumer"),
                "runtimeFieldBindings", Collections.singletonList(
                        payloadRead)));
        if (includeConsumerRead) {
            refinedRows.add(object("schemaVersion", 3,
                    "refinementSchemaVersion", 1,
                    "graphKind", "RUNTIME_REFINED_DATAFLOW",
                    "id", "DF.keyid.read", "kind", "field_read",
                    "transferKind", "HEAP_READ", "method", consumer,
                    "siteId", consumer + "#u4", "unitIndex", 4,
                    "fromCell", wireKeyId, "toCell", consumerKeyId,
                    "regionIds", Collections.singletonList(
                            "REGION.consumer"),
                    "runtimeFieldBindings",
                    Collections.singletonList(keyIdRead)));
        }
        refinedRows.add(object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.failure", "kind", "exception_guard",
                "transferKind", "GUARD", "method", consumer,
                "siteId", consumer + "#u9", "unitIndex", 9,
                "fromCell", consumerKeyId, "toCell", failure,
                "regionIds", Collections.singletonList("REGION.consumer")));
        File refined = writeRows(prefix + "-refined.jsonl",
                refinedRows.toArray(new Map[0]));
        File regions = new File(folder.getRoot(), prefix + "-regions.jsonl");
        File edges = new File(folder.getRoot(), prefix + "-edges.jsonl");
        File protocolConfig = writeRows(prefix + "-protocol.jsonl",
                object("schemaVersion", 2,
                        "kind", "PROTOCOL_STUB_MAPPING",
                        "id", "example.fetch",
                        "clientStub", "<example.Client: void fetch()>",
                        "serverStub", producer,
                        "response", true,
                        "boundaryScalarLeaves",
                        Collections.singletonList(object(
                                "leafId", "keyId",
                                "direction", "RESPONSE",
                                "port", "response",
                                "declaredPath",
                                Collections.singletonList(wireKeyId),
                                "javaType", "int"))));
        String previous = System.getProperty("causynth.protocol.stubs");
        RuntimeSelectedRegionFinalizer.Result result;
        try {
            System.setProperty("causynth.protocol.stubs",
                    protocolConfig.getAbsolutePath());
            List<String> selectedMethods = new ArrayList<>(Arrays.asList(
                    producer, consumer));
            List<Map<String, Object>> activations = new ArrayList<>();
            activations.add(activation("REGION.producer", 1,
                    "STATE_CONTEXT", producer, 1));
            activations.add(activationAtFatalSite("REGION.consumer", 2,
                    "EXCEPTION_CONTEXT", consumer, 2,
                    consumer + "#u9"));
            if (sourceOutsideProtocolRegion) {
                selectedMethods.add(writer);
                activations.add(activation("REGION.writer", 3,
                        "STATE_CONTEXT", writer, 3));
            }
            result = RuntimeSelectedRegionFinalizer.finalizeRegions(
                    refined, skeleton, regions, edges,
                    selectedMethods, activations);
        } finally {
            if (previous == null) {
                System.clearProperty("causynth.protocol.stubs");
            } else {
                System.setProperty("causynth.protocol.stubs", previous);
            }
        }
        return new ProjectionFixture(regions, edges, result);
    }

    private static Map<String, Object> heapWrite(
            String id, String method, String site, String fromCell,
            String declaration, String region,
            Map<String, Object> binding) {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", id, "kind", "field_write",
                "transferKind", "HEAP_WRITE", "method", method,
                "siteId", site, "unitIndex", 3,
                "fromCell", fromCell, "toCell", declaration,
                "regionIds", Collections.singletonList(region),
                "runtimeFieldBindings", Collections.singletonList(binding));
    }

    private static Map<String, Object> externalPrestateEvidence(
            String process, int receiver, String declaration,
            long writeEventSeq) {
        return object(
                "authority",
                "EXACT_ACTIVATION_EXTERNAL_PRESTATE_WRITE_V1",
                "producerRegionId", "REGION.producer",
                "process", process,
                "receiverObjectId", receiver,
                "declaration", declaration,
                "latestWriteEventSeq", writeEventSeq,
                "producerRootCallId", 1,
                "producerRootEventSeq", 2,
                "beforeProducerRoot", true,
                "noCoveringWrite", true);
    }

    private static final class ProjectionFixture {
        private final File regions;
        private final File edges;
        private final RuntimeSelectedRegionFinalizer.Result result;

        private ProjectionFixture(
                File regions, File edges,
                RuntimeSelectedRegionFinalizer.Result result) {
            this.regions = regions;
            this.edges = edges;
            this.result = result;
        }

        private JsonObject region(String regionId) throws Exception {
            for (String row : Files.readAllLines(regions.toPath(),
                    StandardCharsets.UTF_8)) {
                JsonObject region = GSON.fromJson(row, JsonObject.class);
                if (regionId.equals(region.get("regionId").getAsString())) {
                    return region;
                }
            }
            throw new AssertionError("missing region " + regionId);
        }
    }

    private File skeleton(String name) throws Exception {
        return write(name, object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD),
                "selection", "EXCEPTION_COMPONENT"));
    }

    private JsonObject finalizeOne(File refined, File skeleton,
                                   String regionName, String edgeName)
            throws Exception {
        File regions = new File(folder.getRoot(), regionName);
        File edges = new File(folder.getRoot(), edgeName);
        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD),
                Collections.singletonList(activation(
                        "REGION.1", 11, "EXCEPTION_CONTEXT")));
        return GSON.fromJson(Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
    }

    private static JsonObject branch(JsonObject region, String site) {
        for (com.google.gson.JsonElement element
                : region.getAsJsonArray("branchPolicies")) {
            JsonObject branch = element.getAsJsonObject();
            if (site.equals(branch.get("siteId").getAsString())) {
                return branch;
            }
        }
        throw new AssertionError("missing branch " + site);
    }

    private static JsonObject inputForField(JsonObject region,
                                            String declaration) {
        for (com.google.gson.JsonElement element
                : region.getAsJsonArray("symbolicInputs")) {
            JsonObject input = element.getAsJsonObject();
            if (!input.has("fieldPathDeclarations")) continue;
            for (com.google.gson.JsonElement field
                    : input.getAsJsonArray("fieldPathDeclarations")) {
                if (declaration.equals(field.getAsString())) return input;
            }
        }
        throw new AssertionError("missing input " + declaration);
    }

    private static Map<String, Object> heapRead(
            String id, String field, String local, String name, int seq) {
        Map<String, Object> binding = object(
                "regionId", "REGION.1", "rootCallId", 11,
                "rootKind", "RECEIVER", "rootCell", METHOD + ".receiver",
                "rootObjectId", 10, "fieldReceiverObjectId", 10,
                "valueObjectId", 0, "primitiveValue", "true",
                "eventSeq", seq,
                "fieldPath", Collections.singletonList(name),
                "fieldPathDeclarations", Collections.singletonList(field));
        return object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", id, "kind", "field_read",
                "transferKind", "HEAP_READ", "method", METHOD,
                "regionIds", Collections.singletonList("REGION.1"),
                "fromCell", field, "toCell", local,
                "siteId", METHOD + "#u" + seq, "unitIndex", seq,
                "unit", local + " = " + field,
                "runtimeFieldBindings", Collections.singletonList(binding));
    }

    private static Map<String, Object> refinedEdge(
            String id, String kind, String transfer, String from, String to,
            String site, int unitIndex, String unit, String invoke,
            String guardSite, Boolean requiredOutcome,
            boolean sameCellRedefinition) {
        Map<String, Object> edge = object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", id, "kind", kind, "transferKind", transfer,
                "method", METHOD, "regionIds",
                Collections.singletonList("REGION.1"),
                "fromCell", from, "toCell", to, "siteId", site,
                "unitIndex", unitIndex, "unit", unit);
        if (invoke != null) edge.put("invoke", invoke);
        if (guardSite != null) edge.put("guardSiteId", guardSite);
        if (requiredOutcome != null) {
            edge.put("requiredOutcome", requiredOutcome);
        }
        if (sameCellRedefinition) {
            edge.put("sameCellRedefinition", true);
        }
        return edge;
    }

    private File write(String name, Map<String, Object> row)
            throws Exception {
        return writeRows(name, row);
    }

    @SafeVarargs
    private final File writeRows(String name, Map<String, Object>... rows)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        java.util.List<String> encoded = new java.util.ArrayList<>();
        for (Map<String, Object> row : rows) {
            encoded.add(GSON.toJson(row));
        }
        Files.write(file.toPath(), encoded, StandardCharsets.UTF_8);
        return file;
    }

    private static final String LEAF =
            "<example.Key: int keyId>";

    private static Map<String, Object> leafPort(
            String portId, long rootCallId, int receiver, long seq) {
        return object("portId", portId, "transportKind", "HEAP",
                "process", "p", "rootCallId", rootCallId,
                "fieldReceiverObjectId", receiver, "valueObjectId", 0,
                "primitiveValue", "7", "eventSeq", seq,
                "dependencyRole", DependencyRole.VALUE_FRONTIER,
                "fieldPath", Collections.singletonList("keyId"),
                "fieldPathDeclarations", Collections.singletonList(LEAF));
    }

    private static Map<String, Object> leafRegion(
            String regionId, List<Map<String, Object>> outputs,
            List<Map<String, Object>> inputs) {
        return object("regionId", regionId, "outputs", outputs,
                "symbolicInputs", inputs);
    }

    @Test
    public void objectIdentityBindsADemandedLeafToItsRealProducer() throws Exception {
        // The producer builds the object activation-locally; the consumer
        // reads that exact object's leaf after it escaped through a carrier.
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(
                        leafPort("REGION.W.out.keyId", 10L, 74965, 100L)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        leafPort("REGION.R.in.keyId", 20L, 74965, 200L))));

        List<Map<String, Object>> flows =
                RuntimeSelectedRegionFinalizer.demandedLeafProducerFlows(
                        regions, new ArrayList<Map<String, Object>>(),
                        new LinkedHashMap<String, Long>());

        assertEquals(1, flows.size());
        Map<String, Object> edge = flows.get(0);
        assertEquals("REGION.W", edge.get("fromRegion"));
        assertEquals("REGION.R", edge.get("toRegion"));
        assertEquals("RUNTIME_FIELD_FLOW", edge.get("kind"));
        // Named so a composed manifest can trace the binding back.
        assertEquals(RuntimeSelectedRegionFinalizer.LEAF_PRODUCER_AUTHORITY,
                edge.get("authority"));
        assertEquals(Collections.singletonList(LEAF),
                edge.get("fieldPathDeclarations"));
    }

    @Test
    public void anAmbiguousLeafWriterLeavesTheReadUnbound() throws Exception {
        // Two distinct writer ports could have produced the value, so the
        // trace does not prove a producer and the leaf keeps its concrete
        // under-approximation.
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W1", Collections.singletonList(
                        leafPort("REGION.W1.out.keyId", 10L, 74965, 100L)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.W2", Collections.singletonList(
                        leafPort("REGION.W2.out.keyId", 11L, 74965, 110L)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        leafPort("REGION.R.in.keyId", 20L, 74965, 200L))));

        assertTrue(RuntimeSelectedRegionFinalizer
                .demandedLeafProducerFlows(regions,
                        new ArrayList<Map<String, Object>>(),
                        new LinkedHashMap<String, Long>()).isEmpty());
    }

    @Test
    public void anAlreadyClosedLeafIsNotBoundTwice() throws Exception {
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(
                        leafPort("REGION.W.out.keyId", 10L, 74965, 100L)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        leafPort("REGION.R.in.keyId", 20L, 74965, 200L))));
        List<Map<String, Object>> existing = new ArrayList<>();
        existing.add(object("toRegion", "REGION.R", "toRootCallId", 20L,
                "toPort", "REGION.R.in.keyId"));

        assertTrue(RuntimeSelectedRegionFinalizer
                .demandedLeafProducerFlows(regions, existing,
                        new LinkedHashMap<String, Long>()).isEmpty());
    }

    @Test
    public void aDifferentObjectIsNeverTreatedAsTheProducer() throws Exception {
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(
                        leafPort("REGION.W.out.keyId", 10L, 11111, 100L)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        leafPort("REGION.R.in.keyId", 20L, 74965, 200L))));

        assertTrue(RuntimeSelectedRegionFinalizer
                .demandedLeafProducerFlows(regions,
                        new ArrayList<Map<String, Object>>(),
                        new LinkedHashMap<String, Long>()).isEmpty());
    }

    /**
     * A writer port whose one static site ran many times in a single
     * long-lived activation.  Only {@code demandedIndex} wrote the object the
     * consumer later reads.
     */
    private static Map<String, Object> leafWriterPort(
            String portId, long rootCallId, int receiver,
            int demandedIndex, int total) {
        List<Map<String, Object>> accesses = new ArrayList<>();
        for (int index = 0; index < total; index++) {
            accesses.add(object("eventSeq", 100L + index,
                    "process", "p", "rootCallId", rootCallId,
                    "fieldReceiverObjectId",
                    index == demandedIndex ? receiver : 90000 + index,
                    "valueObjectId", 0, "primitiveValue", "7",
                    "fieldPathDeclarations",
                    Collections.singletonList(LEAF),
                    "staticAccessSiteId", "SITE"));
        }
        Map<String, Object> port = leafPort(portId, rootCallId, 0, 100L);
        port.put("runtimeAccesses", accesses);
        return port;
    }

    @Test
    public void aDemandedWritePastTheResourceCapStillProducesTheLeaf()
            throws Exception {
        // The site occurrence index accumulates over nested calls, so the one
        // write that built the consumed object landed far past the resource
        // default.  Truncating it would hide a producer the trace proves.
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(
                        leafWriterPort("REGION.W.out.keyId", 10L, 74965,
                                21, 29)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        leafPort("REGION.R.in.keyId", 20L, 74965, 5000L))));

        List<Map<String, Object>> flows =
                RuntimeSelectedRegionFinalizer.demandedLeafProducerFlows(
                        regions, new ArrayList<Map<String, Object>>(),
                        new LinkedHashMap<String, Long>());

        assertEquals(1, flows.size());
        Map<String, Object> edge = flows.get(0);
        assertEquals("REGION.W", edge.get("fromRegion"));
        assertEquals("REGION.R", edge.get("toRegion"));
        // The retained access keeps its true occurrence index; the cap is a
        // resource default, not a claim about how often the site ran.
        assertEquals(22, edge.get("writerOccurrence"));
    }

    @Test
    public void anUndemandedLateWriteStaysBoundedByTheResourceDefault()
            throws Exception {
        // Nothing reads the object written at occurrence 22, so the resource
        // default still applies and no relation is invented.
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(
                        leafWriterPort("REGION.W.out.keyId", 10L, 74965,
                                21, 29)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        leafPort("REGION.R.in.keyId", 20L, 90021, 5000L))));

        assertTrue(RuntimeSelectedRegionFinalizer
                .demandedLeafProducerFlows(regions,
                        new ArrayList<Map<String, Object>>(),
                        new LinkedHashMap<String, Long>()).isEmpty());
    }

    @Test
    public void tooManyDemandedAccessesAtOneSiteRefuseByName()
            throws Exception {
        // Keeping an arbitrary subset of the demanded accesses would be the
        // silent truncation this pass exists to remove, so the port says it
        // cannot be served and its leaves stay under-approximated.
        int total = RuntimeSelectedRegionFinalizer
                .MAX_RETAINED_SITE_ACCESSES + 1;
        List<Map<String, Object>> accesses = new ArrayList<>();
        for (int index = 0; index < total; index++) {
            accesses.add(object("eventSeq", 100L + index,
                    "process", "p", "rootCallId", 10L,
                    "fieldReceiverObjectId", 74965,
                    "fieldPathDeclarations",
                    Collections.singletonList(LEAF),
                    "staticAccessSiteId", "SITE"));
        }
        Map<String, Object> writer = leafPort("REGION.W.out.keyId", 10L, 0,
                100L);
        writer.put("runtimeAccesses", accesses);
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(writer),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        leafPort("REGION.R.in.keyId", 20L, 74965, 5000L))));

        RuntimeSelectedRegionFinalizer.demandedLeafProducerFlows(regions,
                new ArrayList<Map<String, Object>>(),
                new LinkedHashMap<String, Long>());

        String refusal = String.valueOf(writer.get(
                RuntimeSelectedRegionFinalizer.DEMAND_RETENTION_REFUSAL));
        assertTrue(refusal, refusal.startsWith("BOUND_INSUFFICIENT: "));
    }

    @Test
    public void demandedMemberLeavesProjectByMutationTokenNotSlotOrValue() {
        String keyId = "<example.Member: int keyId>";
        String expiry = "<example.Member: long expiry>";
        String ignored = "<example.Member: int unrelated>";
        Map<String, Object> access = object(
                "process", "p", "rootCallId", 11L,
                "mutatorDeclaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                "mutationInvocationId", 31L,
                "containerMemberToken", "MEMBER.trace-definition",
                "containerMemberIdentityAuthority",
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1",
                "containerObjectId", 50,
                "containerKeyObjectId", 59,
                "containerValueObjectId", 60,
                "containerMemberFieldBindings", Arrays.asList(
                        object("field", keyId, "eventSeq", 7L),
                        object("field", expiry, "eventSeq", 8L),
                        object("field", ignored, "eventSeq", 9L)));
        Map<String, Object> pre = object(
                "portId", "REGION.1.in.state", "rootCallId", 11L,
                "boundedContainerStateRole", "MUTATION_PRE_STATE");
        Map<String, Object> post = object(
                "portId", "REGION.1.out.state", "rootCallId", 11L,
                "boundedContainerStateRole", "MUTATION_POST_STATE",
                "boundedContainerPreStatePorts",
                Collections.singletonList("REGION.1.in.state"),
                "runtimeAccesses", Collections.singletonList(access));
        Map<String, Object> region = object(
                "regionId", "REGION.1",
                "symbolicInputs", Collections.singletonList(pre),
                "outputs", Collections.singletonList(post));
        Map<String, Long> lanes = new LinkedHashMap<>();
        lanes.put("REGION.1\n11", 4L);

        RuntimeSelectedRegionFinalizer.projectDemandedContainerMembers(
                Collections.singletonList(region),
                new LinkedHashSet<>(Arrays.asList(keyId, expiry)), lanes);

        JsonObject encoded = GSON.toJsonTree(region).getAsJsonObject();
        JsonObject preProjection = encoded.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject()
                .getAsJsonArray("boundedContainerMemberProjections")
                .get(0).getAsJsonObject();
        JsonObject postProjection = encoded.getAsJsonArray("outputs")
                .get(0).getAsJsonObject()
                .getAsJsonArray("boundedContainerMemberProjections")
                .get(0).getAsJsonObject();
        assertEquals("MEMBER.trace-definition",
                preProjection.get("memberToken").getAsString());
        assertEquals(preProjection.get("memberToken"),
                postProjection.get("memberToken"));
        assertEquals("PRE_STATE",
                preProjection.get("stateRole").getAsString());
        assertEquals("POST_STATE",
                postProjection.get("stateRole").getAsString());
        assertEquals(3, postProjection.getAsJsonArray("leaves").size());
        assertEquals("PRESENT", postProjection.getAsJsonArray("leaves")
                .get(0).getAsJsonObject().get("kind").getAsString());
        String projection = postProjection.toString();
        assertTrue(projection.contains(keyId));
        assertTrue(projection.contains(expiry));
        assertFalse(projection.contains(ignored));
        assertFalse(postProjection.has("index"));
        assertFalse(postProjection.has("keyValue"));
        assertEquals("SINGLE_WRITER_REQUIRED", encoded
                .getAsJsonArray("outputs").get(0).getAsJsonObject()
                .get("containerTimelineWriterPolicy").getAsString());
    }

    @Test
    public void demandedMemberProjectionRequiresExactContainerIdentity() {
        String field = "<example.Member: int keyId>";
        Map<String, Object> access = object(
                "process", "p", "rootCallId", 11L,
                "mutatorDeclaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                "mutationInvocationId", 31L,
                "containerMemberToken", "MEMBER.exact-mutation",
                "containerMemberIdentityAuthority",
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1",
                // A payload/value identity is deliberately present.  It is
                // not the container whose state the mutation changes.
                "valueObjectId", 50,
                "containerKeyObjectId", 59,
                "containerValueObjectId", 60,
                "containerMemberFieldBindings", Collections.singletonList(
                        object("field", field, "eventSeq", 7L)));
        Map<String, Object> post = object(
                "portId", "REGION.1.out.state", "rootCallId", 11L,
                "boundedContainerStateRole", "MUTATION_POST_STATE",
                "runtimeAccesses", Collections.singletonList(access));
        Map<String, Object> region = object(
                "regionId", "REGION.1",
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.singletonList(post));
        Map<String, Long> lanes = new LinkedHashMap<>();
        lanes.put("REGION.1\n11", 4L);

        RuntimeSelectedRegionFinalizer.projectDemandedContainerMembers(
                Collections.singletonList(region),
                Collections.singleton(field), lanes);

        assertEquals("BLOCKED",
                post.get("boundedContainerMemberProjectionAdmission"));
        assertEquals("MISSING_EXACT_CONTAINER_IDENTITY",
                post.get("boundedContainerMemberProjectionBlocker"));
        assertFalse(post.containsKey("boundedContainerMemberProjections"));
    }

    @Test
    public void memberProjectionRecomputesFieldsOnRetainedProgram() {
        String kept = "<example.Member: int keyId>";
        String discarded = "<example.Member: long unrelated>";
        String guard = METHOD + "::z0";
        Map<String, Object> access = object(
                "process", "p", "rootCallId", 11L,
                "mutatorDeclaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                "mutationInvocationId", 31L,
                "containerMemberToken", "MEMBER.retained",
                "containerMemberIdentityAuthority",
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1",
                "containerObjectId", 50,
                "containerKeyObjectId", 59,
                "containerValueObjectId", 60,
                "containerMemberFieldBindings", Arrays.asList(
                        object("field", kept, "eventSeq", 7L),
                        object("field", discarded, "eventSeq", 8L)));
        Map<String, Object> post = object(
                "portId", "REGION.1.out.state", "rootCallId", 11L,
                "boundedContainerStateRole", "MUTATION_POST_STATE",
                "runtimeAccesses", Collections.singletonList(access));
        Map<String, Object> retained = object(
                "regionId", "REGION.1", "selection",
                "EXCEPTION_CONTEXT", "symbolicInputs",
                Collections.emptyList(), "outputs",
                Collections.singletonList(post));
        List<Map<String, Object>> graph = Arrays.asList(
                object("transferKind", "GUARD", "fromCell", guard,
                        "toCell", METHOD + "#u9#exception:example.Fatal",
                        "regionIds", Collections.singletonList("REGION.1")),
                object("transferKind", "HEAP_READ", "fromCell", kept,
                        "toCell", guard, "regionIds",
                        Collections.singletonList("REGION.1")),
                object("transferKind", "HEAP_WRITE", "fromCell",
                        METHOD + "::i0", "toCell", kept, "regionIds",
                        Collections.singletonList("REGION.1")),
                // This field belonged only to a definition removed by the
                // target-first closure and must not widen the retained member.
                object("transferKind", "HEAP_READ", "fromCell", discarded,
                        "toCell", "<discarded.Root: void run()>::z0",
                        "regionIds", Collections.singletonList("REGION.D")),
                object("transferKind", "HEAP_WRITE", "fromCell",
                        "<discarded.Root: void run()>::j0", "toCell",
                        discarded, "regionIds",
                        Collections.singletonList("REGION.D")));
        Map<String, Long> lanes = new LinkedHashMap<>();
        lanes.put("REGION.1\n11", 4L);

        RuntimeSelectedRegionFinalizer
                .projectFailureRelevantContainerMembers(
                        Collections.singletonList(retained), graph, lanes);

        String projection = String.valueOf(
                post.get("boundedContainerMemberProjections"));
        assertTrue(projection.contains(kept));
        assertFalse(projection.contains(discarded));
    }

    private static Map<String, Object> protocolFenceFlow(
            String mapping, String direction, long caller, long send,
            long receive) {
        return object("kind", "RUNTIME_PROTOCOL_FLOW",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "mappingId", mapping, "direction", direction,
                "toRegion", "REGION.consumer", "toRootCallId", 2L,
                "callerSiteEventSeq", caller, "sendEventSeq", send,
                "receiveEventSeq", receive);
    }

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }

    private static Map<String, Object> activation(
            String region, long rootCallId, String selection) {
        return activation(region, rootCallId, selection, METHOD);
    }

    private static Map<String, Object> activation(
            String region, long rootCallId, String selection, String method) {
        Map<String, Object> result = object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", region,
                "rootCallId", rootCallId,
                "selection", selection,
                "observedMethods", Collections.singletonList(method));
        if (selection != null && selection.startsWith("EXCEPTION")) {
            result.put("observedFatalTargets", Collections.singletonList(
                    observedFatalTarget(method + "#u9", method,
                            Long.MAX_VALUE,
                            rootCallId, true)));
        }
        return result;
    }

    private static Map<String, Object> activation(
            String region, long rootCallId, String selection, String method,
            long laneId) {
        Map<String, Object> result = activation(region, rootCallId,
                selection, method);
        result.put("laneId", laneId);
        return result;
    }

    private static Map<String, Object> activationAtFatalSite(
            String region, long rootCallId, String selection, String method,
            long laneId, String site) {
        Map<String, Object> result = activation(region, rootCallId,
                selection, method, laneId);
        result.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(site, method, Long.MAX_VALUE,
                        rootCallId, true)));
        return result;
    }

    private static Map<String, Object> observedFatalTarget(
            String site, String method, long eventSeq, long callId,
            boolean outcome) {
        return object("schemaVersion", 1,
                "kind", "OBSERVED_FATAL_TARGET",
                "evidenceAuthority", "EXACT_RUNTIME_BRANCH_SITE_V1",
                "siteId", site, "method", method,
                "observedOutcome", outcome,
                "eventSeq", eventSeq, "callId", callId);
    }

    private static List<JsonObject> readJsonLines(File file)
            throws IOException {
        List<JsonObject> result = new ArrayList<>();
        for (String line : Files.readAllLines(file.toPath(),
                StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) {
                result.add(GSON.fromJson(line, JsonObject.class));
            }
        }
        return result;
    }

    private static int retainedInstanceCount(
            RuntimeSelectedRegionFinalizer.Result result) {
        int count = 0;
        for (Map<String, Object> region : result.regions) {
            count += ((List<?>) region.get("runtimeRootCallIds")).size();
        }
        return count;
    }

    private static Map<String, Object> fieldBinding(
            String region, long rootCallId, String method, long seq,
            String declaration, String primitiveValue) {
        return fieldBinding(region, rootCallId, method, seq, declaration,
                primitiveValue, 99);
    }

    private static Map<String, Object> fieldBinding(
            String region, long rootCallId, String method, long seq,
            String declaration, String primitiveValue, int receiver) {
        return object("regionId", region, "rootCallId", rootCallId,
                "rootKind", "RECEIVER", "rootMethod", method,
                "rootCell", method + ".receiver", "rootObjectId", 10,
                "fieldReceiverObjectId", receiver, "valueObjectId", 0,
                "primitiveValue", primitiveValue, "eventSeq", seq,
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations",
                Collections.singletonList(declaration));
    }
}
