package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceMinter;
import org.junit.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeSelectedRegionFinalizerAccessorTest {
    private static final String REGION = "REGION.reader";
    private static final String METHOD = "<example.Reader: void run()>";
    private static final String CALLEE = "<example.Value: long getValue()>";
    private static final String SITE = METHOD + "#u12";
    private static final String RETURN = CALLEE + ".return";
    private static final String LOCAL = METHOD + "::$l1";

    @Test
    public void exactAccessorOwnsOnlyItsMatchingReturnEvent() {
        StaticProgram program = programWithExactAccessor(88L);
        List<Map<String, Object>> branches = Collections.singletonList(row(
                "policy", "EXPLORE",
                "operandCells", Collections.singletonList(LOCAL)));

        assertEquals(0, RuntimeSelectedRegionFinalizer
                .externalCallReturnPorts(program, REGION, branches,
                        Collections.singletonList(returnObservation(88L)))
                .size());
        assertEquals(1, RuntimeSelectedRegionFinalizer
                .externalCallReturnPorts(program, REGION, branches,
                        Collections.singletonList(returnObservation(89L)))
                .size());
    }

    /**
     * A call-return port id is published identity, so it must not be spelled
     * from the recorder's callId.
     *
     * <p>callId is a global per-run event counter, so naming a port after it
     * gave the same call return a different symbol in every recording, and
     * two runs of one flip obligation then produced queries that differed by
     * symbol name alone. The same return, reached under a different callId,
     * has to be named the same.</p>
     */
    @Test
    public void callReturnPortIdDoesNotDependOnTheRecordedCallId() {
        StaticProgram program = programWithExactAccessor(88L);
        // The occurrence recorded both calls; only their callId differs.
        program.activations.put("node/region/REGION.reader#1", row(
                "callIds", Arrays.asList(77L, 78L)));
        List<Map<String, Object>> branches = Collections.singletonList(row(
                "policy", "EXPLORE",
                "operandCells", Collections.singletonList(LOCAL)));

        List<Map<String, Object>> first = RuntimeSelectedRegionFinalizer
                .externalCallReturnPorts(program, REGION, branches,
                        Collections.singletonList(
                                returnObservation(77L, 89L)));
        List<Map<String, Object>> second = RuntimeSelectedRegionFinalizer
                .externalCallReturnPorts(program, REGION, branches,
                        Collections.singletonList(
                                returnObservation(78L, 90L)));

        assertEquals(1, first.size());
        assertEquals(1, second.size());
        assertEquals(String.valueOf(first.get(0).get("portId")),
                String.valueOf(second.get(0).get("portId")));

        // Two return events of one occurrence are still two ports: the
        // ordinal that separates them is what replaced the callId, so it has
        // to keep separating them.
        List<Map<String, Object>> both = RuntimeSelectedRegionFinalizer
                .externalCallReturnPorts(program, REGION, branches,
                        Arrays.asList(returnObservation(77L, 89L),
                                returnObservation(78L, 90L)));
        assertEquals(2, both.size());
        assertNotEquals(String.valueOf(both.get(0).get("portId")),
                String.valueOf(both.get(1).get("portId")));
    }

    @Test
    public void admittedRegionPathKeepsItsExternalExploreInput()
            throws Exception {
        String occurrence = "source/region/" + REGION + "#1";
        String local = METHOD + "::$now";
        String predicate = METHOD + "::$predicate";
        String portId = REGION + ".in.now";
        Map<String, Object> input = row(
                "occurrenceId", occurrence,
                "portId", portId,
                "sourceKind", RuntimeSelectedRegionFinalizer
                        .EXTERNAL_CALL_RETURN,
                "dependencyRole", "VALUE_FRONTIER",
                "cell", RETURN,
                "dependencyCells", Collections.singletonList(local),
                "siteId", SITE,
                "eventSeq", 20L,
                "symbolicDemand", "BOUNDED_STATE_FRONTIER");
        Map<String, Object> region = row(
                "regionId", REGION,
                "symbolicInputs", Collections.singletonList(input),
                "outputs", Collections.emptyList(),
                "branchPolicies", Collections.singletonList(row(
                        "siteId", METHOD + "#u15",
                        "policy", "EXPLORE",
                        "operandCells", Collections.singletonList(
                                predicate))));
        List<Map<String, Object>> graph = Arrays.asList(
                row("fromCell", RETURN, "toCell", local,
                        "regionIds", Collections.singletonList(REGION)),
                row("fromCell", local, "toCell", predicate,
                        "regionIds", Collections.singletonList(REGION)));

        Class<?> indexType = Class.forName(
                RuntimeSelectedRegionFinalizer.class.getName()
                        + "$RegionDemandIndex");
        Constructor<?> constructor = indexType.getDeclaredConstructor(
                List.class, List.class);
        constructor.setAccessible(true);
        Object index = constructor.newInstance(
                Collections.singletonList(region), graph);
        Method closure = RuntimeSelectedRegionFinalizer.class
                .getDeclaredMethod("walkFailureClosure",
                        java.util.Collection.class, Map.class, indexType,
                        Map.class, java.util.Collection.class, Map.class,
                        Set.class);
        closure.setAccessible(true);
        Object result = closure.invoke(null,
                Collections.emptySet(),
                Collections.singletonMap(occurrence, row(
                        "regionId", REGION,
                        "occurrenceId", occurrence)),
                index, Collections.emptyMap(), Collections.emptySet(),
                Collections.emptyMap(),
                Collections.singleton(occurrence));
        Field demanded = result.getClass().getDeclaredField(
                "demandedInputs");
        demanded.setAccessible(true);

        assertTrue(((Set<?>) demanded.get(result)).contains(
                occurrence + "\n" + portId));
    }

    @Test
    public void exactRequestTransactionSelectsOnlyItsFaultOccurrence() {
        String faultOccurrence = "source/region/REGION.fault#1";
        String unrelatedOccurrence = "source/region/REGION.fault#2";
        String earlyOccurrence = "source/region/REGION.fault#3";
        String consumerOccurrence = "source/region/REGION.consumer#1";
        String targetOccurrence = "target/region/REGION.target#1";
        String targetFaultOccurrence = "target/region/REGION.fault#1";
        String targetStateOccurrence =
                "target/region/REGION.consumer#1";
        StaticProgram program = new StaticProgram();
        program.activations.put(faultOccurrence, activation(
                "AF", "REGION.fault", faultOccurrence, "source", 10L));
        program.activations.put(unrelatedOccurrence, activation(
                "AU", "REGION.fault", unrelatedOccurrence, "source", 20L));
        program.activations.put(earlyOccurrence, activation(
                "AE", "REGION.fault", earlyOccurrence, "source", 25L));
        program.activations.put(consumerOccurrence, activation(
                "AC", "REGION.consumer", consumerOccurrence, "source",
                30L));
        Map<String, Object> target = activation(
                "AT", "REGION.target", targetOccurrence, "target", 40L);
        target.put("selection", "EXCEPTION_CONTEXT");
        target.put("observedFatalTargets", Collections.singletonList(
                row("eventSeq", 100L)));
        program.activations.put(targetOccurrence, target);
        program.activations.put(targetFaultOccurrence, activation(
                "TF", "REGION.fault", targetFaultOccurrence, "target",
                50L));
        program.activations.put(targetStateOccurrence, activation(
                "TC", "REGION.consumer", targetStateOccurrence, "target",
                60L));
        program.regions.add(row(
                "regionId", "REGION.fault",
                "symbolicInputs", Arrays.asList(
                        faultPort(faultOccurrence, "PORT.fault", 2L),
                        faultPort(unrelatedOccurrence, "PORT.unrelated", 12L),
                        faultPort(earlyOccurrence, "PORT.early", 1L),
                        faultPort(targetFaultOccurrence,
                                "PORT.target-state", 7L))));
        program.regions.add(row(
                "regionId", "REGION.consumer",
                "symbolicInputs", Collections.emptyList()));
        program.regions.add(row(
                "regionId", "REGION.target",
                "symbolicInputs", Collections.emptyList()));
        program.regionEdges.add(row(
                "schemaVersion", 3,
                "edgeId", "RPC.response",
                "kind", "RUNTIME_PROTOCOL_FLOW",
                "direction", "RESPONSE",
                "fromOccurrenceId", "source/region/REGION.server#1",
                "toOccurrenceId", consumerOccurrence,
                "toRegion", "REGION.consumer",
                "exchangeLeg", "exchange\n1\nRESPONSE",
                "requestKey", "REQUEST.1",
                "requestApi", "api",
                "transportKind", "RPC",
                "attemptId", "1",
                "senderEventSeq", 4L,
                "receiverEventSeq", 5L));
        program.regionEdges.add(row(
                "schemaVersion", 3,
                "edgeId", "RPC.target-input",
                "kind", "RUNTIME_PROTOCOL_FLOW",
                "direction", "REQUEST",
                "dependencyRole", "VALUE_FRONTIER",
                "fromOccurrenceId", consumerOccurrence,
                "toOccurrenceId", targetOccurrence,
                "fromRegion", "REGION.consumer",
                "toRegion", "REGION.target"));
        program.regionEdges.add(row(
                "schemaVersion", 3,
                "edgeId", "RPC.target-state-response",
                "kind", "RUNTIME_PROTOCOL_FLOW",
                "direction", "RESPONSE",
                "fromOccurrenceId", "target/region/REGION.server#1",
                "toOccurrenceId", targetStateOccurrence,
                "toRegion", "REGION.consumer",
                "exchangeLeg", "target-state\n1\nRESPONSE",
                "requestKey", "REQUEST.target-state",
                "requestApi", "api",
                "transportKind", "RPC",
                "attemptId", "1",
                "senderEventSeq", 9L,
                "receiverEventSeq", 10L));
        List<Map<String, Object>> links = Arrays.asList(
                requestLink("AF", "exchange\n1\nREQUEST", "REQUEST.1",
                        1L, 3L),
                requestLink("AE", "exchange\n1\nREQUEST", "REQUEST.1",
                        1L, 3L),
                requestLink("AU", "other\n1\nREQUEST", "REQUEST.2",
                        11L, 13L),
                requestLink("TF", "target-state\n1\nREQUEST",
                        "REQUEST.target-state", 6L, 8L));

        List<Map<String, Object>> controls = RuntimeSelectedRegionFinalizer
                .exactRequestFaultControlEdges(program,
                        Arrays.asList("RPC.response", "RPC.target-input",
                                "RPC.target-state-response"), links);

        assertEquals(1, controls.size());
        Map<String, Object> control = controls.get(0);
        assertEquals(faultOccurrence, control.get("fromOccurrenceId"));
        assertEquals(consumerOccurrence, control.get("toOccurrenceId"));
        assertEquals("PORT.fault", control.get("faultPortId"));
        assertTrue(AutomaticRegionEdge.trustedRequestFaultControl(
                new Gson().toJsonTree(control).getAsJsonObject()));
        Map<String, Object> tooEarly = new LinkedHashMap<>(control);
        tooEarly.put("faultEventSeq", control.get(
                "requestSenderEventSeq"));
        assertFalse(AutomaticRegionEdge.trustedRequestFaultControl(
                new Gson().toJsonTree(tooEarly).getAsJsonObject()));
        Map<String, Object> unboundResponse = new LinkedHashMap<>(control);
        unboundResponse.remove("controlledResponseEdgeId");
        assertFalse(AutomaticRegionEdge.trustedRequestFaultControl(
                new Gson().toJsonTree(unboundResponse).getAsJsonObject()));
        Map<String, Object> unknownSource = new LinkedHashMap<>(control);
        unknownSource.put("sourceKey",
                OccurrenceMinter.UNREGISTERED_SOURCE_KEY);
        unknownSource.put("consumerSourceKey",
                OccurrenceMinter.UNREGISTERED_SOURCE_KEY);
        assertFalse(AutomaticRegionEdge.trustedRequestFaultControl(
                new Gson().toJsonTree(unknownSource).getAsJsonObject()));

        program.activations.get(faultOccurrence).put("sourceKey",
                OccurrenceMinter.UNREGISTERED_SOURCE_KEY);
        program.activations.get(consumerOccurrence).put("sourceKey",
                OccurrenceMinter.UNREGISTERED_SOURCE_KEY);
        assertTrue(RuntimeSelectedRegionFinalizer
                .exactRequestFaultControlEdges(program,
                        Arrays.asList("RPC.response", "RPC.target-input"),
                        links).isEmpty());
    }

    @Test
    public void repeatedPortReceiversPairByCaptureOrdinal() {
        String exchange = "exchange\n1\nRESPONSE";
        String port = "PORT.block-key-id";
        String producerOccurrence = "nn/region/REGION.encoder#1";
        String firstOccurrence = "dn/region/REGION.decoder#1";
        String secondOccurrence = "dn/region/REGION.decoder#2";
        Map<String, Object> producer = activation(
                "AP", "REGION.encoder", producerOccurrence, "nn", 10L);
        producer.put(RuntimeSelectedRegionFinalizer
                        .OBSERVED_COMMUNICATION_CAPTURES,
                Arrays.asList(
                        communicationCapture("OUT", port, exchange,
                                10L, 50L),
                        communicationCapture("OUT", port, exchange,
                                20L, 50L)));
        Map<String, Object> envelope = activation(
                "AE", "REGION.envelope",
                "dn/region/REGION.envelope#1", "dn", 20L);
        Map<String, Object> first = activation(
                "AR1", "REGION.decoder", firstOccurrence, "dn", 21L);
        first.put("enclosingActivationIds", Collections.singletonList("AE"));
        first.put(RuntimeSelectedRegionFinalizer
                        .OBSERVED_COMMUNICATION_CAPTURES,
                Collections.singletonList(communicationCapture(
                        "IN", port, exchange, 70L, 60L)));
        Map<String, Object> second = activation(
                "AR2", "REGION.decoder", secondOccurrence, "dn", 22L);
        second.put("enclosingActivationIds", Collections.singletonList("AE"));
        second.put(RuntimeSelectedRegionFinalizer
                        .OBSERVED_COMMUNICATION_CAPTURES,
                Collections.singletonList(communicationCapture(
                        "IN", port, exchange, 80L, 60L)));

        StaticProgram program = new StaticProgram();
        program.activations.put(producerOccurrence, producer);
        program.activations.put("envelope", envelope);
        program.activations.put(firstOccurrence, first);
        program.activations.put(secondOccurrence, second);
        program.regions.add(row(
                "regionId", "REGION.encoder",
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.singletonList(communicationPort(
                        port, "RESPONSE"))));
        program.regions.add(row(
                "regionId", "REGION.decoder",
                "symbolicInputs", Collections.singletonList(
                        communicationPort(port, "RESPONSE")),
                "outputs", Collections.emptyList()));
        Map<String, Object> link = row(
                "authority", "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1",
                "fromActivationId", "AP",
                "toActivationId", "AE",
                "direction", "RESPONSE",
                "exchangeLeg", exchange,
                "requestKey", "REQUEST.1",
                "requestApi", "heartbeat",
                "transport", "RPC",
                "attemptId", "1",
                "senderEventSeq", 50L,
                "receiverEventSeq", 60L);

        List<Map<String, Object>> flows = RuntimeSelectedRegionFinalizer
                .recordedOccurrenceProducerFlows(program,
                        Collections.singletonList(link));

        assertEquals(2, flows.size());
        Set<String> receivers = new LinkedHashSet<>();
        for (Map<String, Object> flow : flows) {
            receivers.add(String.valueOf(flow.get("toOccurrenceId")));
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                firstOccurrence, secondOccurrence)), receivers);
    }

    @Test
    public void wholeStateWriterRetainsItsMutationValues() throws Exception {
        String occurrence = "dn/region/REGION.writer#1";
        String outputPort = "REGION.writer.out.map";
        String keyPort = "REGION.writer.in.key";
        String carrierPort = "REGION.writer.in.carrier";
        Map<String, Object> region = row(
                "regionId", "REGION.writer",
                "symbolicInputs", Arrays.asList(
                        row("occurrenceId", occurrence,
                                "portId", keyPort,
                                "dependencyRole", "VALUE_FRONTIER",
                                "cell", "key"),
                        row("occurrenceId", occurrence,
                                "portId", carrierPort,
                                "dependencyRole",
                                "CONCRETE_STRUCTURE_CARRIER",
                                "cell", "carrier")),
                "outputs", Collections.singletonList(row(
                        "occurrenceId", occurrence,
                        "portId", outputPort,
                        "dependencyRole", "VALUE_FRONTIER",
                        "cell", "map",
                        "bindingKind", "CONTAINER_MUTATION")),
                "branchPolicies", Collections.emptyList());
        Class<?> indexType = Class.forName(
                RuntimeSelectedRegionFinalizer.class.getName()
                        + "$RegionDemandIndex");
        Constructor<?> constructor = indexType.getDeclaredConstructor(
                List.class, List.class);
        constructor.setAccessible(true);
        Object index = constructor.newInstance(
                Collections.singletonList(region), Collections.emptyList());
        Method inputsForOutput = indexType.getDeclaredMethod(
                "inputsForOutput", String.class, String.class);
        inputsForOutput.setAccessible(true);

        @SuppressWarnings("unchecked")
        List<String> inputs = (List<String>) inputsForOutput.invoke(index,
                occurrence, outputPort);

        assertTrue(inputs.contains(occurrence + "\n" + keyPort));
        assertFalse(inputs.contains(occurrence + "\n" + carrierPort));
    }

    private static Map<String, Object> activation(
            String activationId, String regionId, String occurrenceId,
            String sourceKey, long rootCallId) {
        return row(
                "activationId", activationId,
                "regionId", regionId,
                "occurrenceId", occurrenceId,
                "rootCallId", rootCallId,
                "rootAuthority", "REGION.fault".equals(regionId)
                        ? "EXPLICIT_FAULT_ENTRY" : "FAILURE_TARGET_ENTRY",
                "sourceKey", sourceKey);
    }

    private static Map<String, Object> faultPort(
            String occurrenceId, String portId, long eventSeq) {
        return row(
                "occurrenceId", occurrenceId,
                "portId", portId,
                "sourceKind", "EXPLICIT_SYMBOLIC_FAULT",
                "symbolicName", "requestFails",
                "eventSeq", eventSeq);
    }

    private static Map<String, Object> requestLink(
            String activationId, String exchangeLeg, String requestKey,
            long sender, long receiver) {
        return row(
                "authority", "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1",
                "fromActivationId", activationId,
                "direction", "REQUEST",
                "exchangeLeg", exchangeLeg,
                "requestKey", requestKey,
                "requestApi", "api",
                "transport", "RPC",
                "attemptId", "1",
                "senderEventSeq", sender,
                "receiverEventSeq", receiver);
    }

    private static StaticProgram programWithExactAccessor(long eventSeq) {
        Map<String, Object> callReturn = row(
                "id", "DF.return",
                "kind", "call_return",
                "transferKind", "FUNCTION_RETURN",
                "runtimeObserved", true,
                "regionIds", Collections.singletonList(REGION),
                "method", METHOD,
                "unitIndex", 12,
                "siteId", SITE,
                "invoke", CALLEE,
                "fromCell", RETURN,
                "toCell", LOCAL);
        Map<String, Object> accessorBinding = row(
                "authority", "EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1",
                "regionId", REGION,
                "siteId", SITE,
                "declaredCallee", CALLEE,
                "callId", 77L,
                "eventSeq", eventSeq);
        Map<String, Object> accessor = row(
                "id", "DF.accessor",
                "kind", "accessor_field_return",
                "transferKind", "HEAP_READ",
                "runtimeObserved", true,
                "regionIds", Collections.singletonList(REGION),
                "method", METHOD,
                "unitIndex", 12,
                "siteId", SITE,
                "invoke", CALLEE,
                "fromCell", "<example.Value: long value>",
                "toCell", LOCAL,
                "runtimeAccessorBindings",
                Collections.singletonList(accessorBinding));
        StaticProgram program = new StaticProgram();
        program.refinedGraph = Arrays.asList(callReturn, accessor);
        program.activations.put("node/region/REGION.reader#1", row(
                "callIds", Collections.singletonList(77L)));
        return program;
    }

    private static Map<String, Object> returnObservation(long eventSeq) {
        return returnObservation(77L, eventSeq);
    }

    private static Map<String, Object> returnObservation(long callId,
                                                         long eventSeq) {
        return row(
                "kind", "CALL_SITE_RETURN",
                "siteId", SITE,
                "declaredCallee", CALLEE,
                "callId", callId,
                "eventSeq", eventSeq,
                "primitiveValue", "5");
    }

    private static Map<String, Object> communicationCapture(
            String side, String port, String exchange, long eventSeq,
            long transportEventSeq) {
        return row(
                "side", side,
                "portId", port,
                "exchangeLeg", exchange,
                "eventSeq", eventSeq,
                "transportEventSeq", transportEventSeq);
    }

    private static Map<String, Object> communicationPort(
            String port, String direction) {
        return row(
                "portId", port,
                "sourceKind", RuntimeSelectedRegionFinalizer
                        .COMMUNICATION_SITE_PORT,
                "direction", direction,
                "dependencyRole", "VALUE_FRONTIER",
                "javaType", "long");
    }

    private static Map<String, Object> row(Object... fields) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < fields.length; index += 2) {
            result.put((String) fields[index], fields[index + 1]);
        }
        return result;
    }
}
