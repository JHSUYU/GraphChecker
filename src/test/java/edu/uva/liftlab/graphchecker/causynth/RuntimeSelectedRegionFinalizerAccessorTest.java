package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.SharedFieldFlow;
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
import static org.junit.Assert.assertNull;
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
                        Set.class, java.util.Collection.class);
        closure.setAccessible(true);
        Object result = closure.invoke(null,
                Collections.emptySet(),
                Collections.singletonMap(occurrence, row(
                        "regionId", REGION,
                        "occurrenceId", occurrence)),
                index, Collections.emptyMap(), Collections.emptySet(),
                Collections.emptyMap(),
                Collections.singleton(occurrence),
                Collections.emptySet());
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

    /**
     * Two shared-location demand hops.  The fatal target reads a location the
     * middle region wrote, and the middle region reads a location of its own
     * that only the outer writer wrote.  The first hop is first-order demand;
     * the second exists only because an admitted occurrence reads it, which is
     * the demand the port-gated rule alone never reaches.
     */
    @Test
    public void secondOrderSharedLocationDemandAdmitsTheWritersWriter()
            throws Exception {
        String source = "cluster/node#epoch0";
        String target = source + "/region/REGION.fatal#1";
        String middle = source + "/region/REGION.middle#1";
        String outer = source + "/region/REGION.outer#1";
        String farSide = "cluster/other#epoch0/region/REGION.outer#1";
        String fatalPort = "REGION.fatal.in.consumed";
        String middlePort = "REGION.middle.in.currentKey";
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        instances.put(target, demandActivation(
                "AT", "REGION.fatal", target, source));
        instances.put(middle, demandActivation(
                "AM", "REGION.middle", middle, source));
        instances.put(outer, demandActivation(
                "AO", "REGION.outer", outer, source));
        instances.put(farSide, demandActivation(
                "AF", "REGION.outer", farSide, "cluster/other#epoch0"));
        List<Map<String, Object>> edges = Arrays.asList(
                fieldFlow("SF.first", middle, target, fatalPort,
                        "example.Owner#consumed"),
                fieldFlow("SF.second", outer, middle, middlePort,
                        "example.Owner#currentKey"),
                fieldFlow("SF.cross", farSide, middle, middlePort,
                        "example.Owner#currentKey"));
        Set<String> fatalInputs = new LinkedHashSet<>(
                Collections.singletonList(target + "\n" + fatalPort));
        Map<String, Integer> depths = new LinkedHashMap<>();
        depths.put(target, 0);

        // Hop one: today's rule, unchanged.  Only the location the failure
        // closure demanded through a port admits its writer.
        assertEquals(Collections.singleton(middle),
                RuntimeSelectedRegionFinalizer.admitWritersOfDemands(
                        Collections.singletonList(target), fatalInputs,
                        instances, edges, depths, null, null, null));
        assertEquals("SHARED_LOCATION_DEMAND_V1",
                instances.get(middle).get("admissionBasis"));
        assertEquals(1, instances.get(middle).get(
                RuntimeSelectedRegionFinalizer.DEMAND_DEPTH));
        // The outer writer is invisible to it: nothing demands the middle
        // region's own read yet.
        assertNull(instances.get(outer).get("admissionBasis"));

        // Hop two: the middle region's own shared read becomes demanded.
        // Only the writer on its own node opens the hop -- the cross-node
        // pairing on the same port does not.
        Set<String> transitive = RuntimeSelectedRegionFinalizer
                .transitiveSharedLocationDemand(
                        Arrays.asList(target, middle), fatalInputs,
                        instances, edges, depths, Integer.MAX_VALUE,
                        null, null);
        assertEquals(Collections.singleton(middle + "\n" + middlePort),
                transitive);
        Set<String> reDemanded = new LinkedHashSet<>(fatalInputs);
        reDemanded.addAll(transitive);
        // Once the read is demanded, every recorded writer of that exact
        // receiver and leaf is one of its replay arms -- the first-order
        // rule's standing contract, which this rule does not narrow.
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                        middle, outer, farSide)),
                RuntimeSelectedRegionFinalizer.admitWritersOfDemands(
                        Arrays.asList(target, middle), reDemanded,
                        instances, edges, depths, null, null, null));
        assertEquals("SHARED_LOCATION_DEMAND_V1",
                instances.get(outer).get("admissionBasis"));
        assertEquals(2, instances.get(outer).get(
                RuntimeSelectedRegionFinalizer.DEMAND_DEPTH));
        assertEquals(Collections.singletonList("example.Owner#currentKey"),
                instances.get(outer).get("demandedSharedLocations"));
        assertEquals(Collections.singletonList("REGION.middle"),
                instances.get(outer).get("demandedByRegionIds"));
        // The already-admitted first hop keeps the depth it was admitted at.
        assertEquals(1, instances.get(middle).get(
                RuntimeSelectedRegionFinalizer.DEMAND_DEPTH));
    }

    /**
     * A read whose only recorded writer sits on another node opens no hop: a
     * heap location is private to the node and epoch holding the object, so
     * such a pairing is a receiver coincidence, not shared state.
     */
    @Test
    public void crossNodeWriterAloneOpensNoSharedLocationHop() {
        String source = "cluster/node#epoch0";
        String target = source + "/region/REGION.fatal#1";
        String middle = source + "/region/REGION.middle#1";
        String farSide = "cluster/other#epoch0/region/REGION.outer#1";
        String middlePort = "REGION.middle.in.currentKey";
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        instances.put(target, demandActivation(
                "AT", "REGION.fatal", target, source));
        instances.put(middle, demandActivation(
                "AM", "REGION.middle", middle, source));
        instances.put(farSide, demandActivation(
                "AF", "REGION.outer", farSide, "cluster/other#epoch0"));
        List<Map<String, Object>> edges = Collections.singletonList(
                fieldFlow("SF.cross", farSide, middle, middlePort,
                        "example.Owner#currentKey"));
        Map<String, Integer> depths = new LinkedHashMap<>();
        depths.put(target, 0);
        depths.put(middle, 1);

        assertTrue(RuntimeSelectedRegionFinalizer
                .transitiveSharedLocationDemand(
                        Arrays.asList(target, middle),
                        Collections.<String>emptySet(), instances, edges,
                        depths, Integer.MAX_VALUE, null, null).isEmpty());
    }

    @Test
    public void configuredDemandDepthStopsTheTransitiveHop()
            throws Exception {
        String source = "cluster/node#epoch0";
        String target = source + "/region/REGION.fatal#1";
        String middle = source + "/region/REGION.middle#1";
        String outer = source + "/region/REGION.outer#1";
        String middlePort = "REGION.middle.in.currentKey";
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        instances.put(target, demandActivation(
                "AT", "REGION.fatal", target, source));
        instances.put(middle, demandActivation(
                "AM", "REGION.middle", middle, source));
        instances.put(outer, demandActivation(
                "AO", "REGION.outer", outer, source));
        List<Map<String, Object>> edges = Collections.singletonList(
                fieldFlow("SF.second", outer, middle, middlePort,
                        "example.Owner#currentKey"));
        Map<String, Integer> depths = new LinkedHashMap<>();
        depths.put(target, 0);
        depths.put(middle, 1);

        // The middle region sits one hop out, so its own read is a second
        // hop and a bound of one refuses it.
        assertTrue(RuntimeSelectedRegionFinalizer
                .transitiveSharedLocationDemand(
                        Arrays.asList(target, middle),
                        Collections.<String>emptySet(), instances, edges,
                        depths, 1, null, null).isEmpty());
        // Zero turns the rule off outright, leaving the first-order
        // admissions this bound never gates.
        assertTrue(RuntimeSelectedRegionFinalizer
                .transitiveSharedLocationDemand(
                        Arrays.asList(target, middle),
                        Collections.<String>emptySet(), instances, edges,
                        depths, 0, null, null).isEmpty());
        assertEquals(Collections.singleton(middle + "\n" + middlePort),
                RuntimeSelectedRegionFinalizer
                        .transitiveSharedLocationDemand(
                                Arrays.asList(target, middle),
                                Collections.<String>emptySet(), instances,
                                edges, depths, 2, null, null));
        assertEquals(0, RuntimeSelectedRegionFinalizer.configuredDemandDepth(
                "0"));
        assertEquals(Integer.MAX_VALUE, RuntimeSelectedRegionFinalizer
                .configuredDemandDepth("  "));
        assertEquals(3, RuntimeSelectedRegionFinalizer.configuredDemandDepth(
                " 3 "));
        for (String refused : new String[] {"-1", "two"}) {
            try {
                RuntimeSelectedRegionFinalizer.configuredDemandDepth(refused);
                org.junit.Assert.fail("accepted " + refused);
            } catch (java.io.IOException expected) {
                assertTrue(expected.getMessage().contains(refused));
            }
        }
    }

    /**
     * The care set is the intersection of the two conditions: a field must
     * appear on the backward slice AND be forward-reachable from a symbolic
     * root.  A field the slice names but no root reaches is a constant for
     * this failure and stays out.
     */
    @Test
    public void careSetKeepsOnlySliceFieldsASymbolicRootReaches() {
        List<Map<String, Object>> graph = Arrays.asList(
                // The fault symbol enters at the wire and flows to a cell
                // that reads the rolled key.
                row("kind", "explicit_symbolic_fault",
                        "explicitSymbolicFault", true,
                        "fromCell", "cell.fault", "toCell", "cell.request"),
                row("kind", "field_read", "fromCell", "cell.request",
                        "toCell", "cell.key",
                        "declaredFieldSignature",
                        "<example.Owner: example.Key currentKey>"),
                // On the slice, but nothing symbolic reaches it: a harness
                // setter writing its own island.
                row("kind", "field_write", "fromCell", "cell.harness",
                        "toCell", "cell.interval",
                        "declaredFieldSignature",
                        "<example.Owner: long keyUpdateInterval>"));

        Set<String> cared = RuntimeSelectedRegionFinalizer
                .caredSharedLocations(graph);
        assertTrue(cared.contains("example.Owner#currentKey"));
        assertFalse(cared.contains("example.Owner#keyUpdateInterval"));
    }

    /** A wire attach point is a symbolic root of the same standing. */
    @Test
    public void careSetTreatsWireHandoffAsASymbolicRoot() {
        List<Map<String, Object>> graph = Arrays.asList(
                row("kind", "wire_handoff", "fromCell", "cell.send",
                        "toCell", "cell.receive"),
                row("kind", "field_write", "fromCell", "cell.receive",
                        "toCell", "cell.keys",
                        "fieldPathDeclarations", Collections.singletonList(
                                "<example.Owner: java.util.Map allKeys>")));
        assertTrue(RuntimeSelectedRegionFinalizer.caredSharedLocations(graph)
                .contains("example.Owner#allKeys"));
    }

    /**
     * The care set gates the transitive hop only.  A demanded location
     * inside the set still opens its hop; one outside stops the walk and is
     * recorded as pruned, naming the location and the region that read it.
     */
    @Test
    public void uncaredLocationStopsTheHopAndIsRecorded() {
        String source = "cluster/node#epoch0";
        String target = source + "/region/REGION.fatal#1";
        String middle = source + "/region/REGION.middle#1";
        String outer = source + "/region/REGION.outer#1";
        String caredPort = "REGION.middle.in.currentKey";
        String uncaredPort = "REGION.middle.in.interval";
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        instances.put(target, demandActivation(
                "AT", "REGION.fatal", target, source));
        instances.put(middle, demandActivation(
                "AM", "REGION.middle", middle, source));
        instances.put(outer, demandActivation(
                "AO", "REGION.outer", outer, source));
        List<Map<String, Object>> edges = Arrays.asList(
                fieldFlow("SF.cared", outer, middle, caredPort,
                        "example.Owner#currentKey"),
                fieldFlow("SF.uncared", outer, middle, uncaredPort,
                        "example.Owner#keyUpdateInterval"));
        Map<String, Integer> depths = new LinkedHashMap<>();
        depths.put(target, 0);
        depths.put(middle, 1);
        Set<String> cared = new LinkedHashSet<>(
                Collections.singletonList("example.Owner#currentKey"));
        Map<String, Map<String, Object>> pruned = new LinkedHashMap<>();

        // Only the cared location seeds a demand.
        assertEquals(Collections.singleton(middle + "\n" + caredPort),
                RuntimeSelectedRegionFinalizer
                        .transitiveSharedLocationDemand(
                                Arrays.asList(target, middle),
                                Collections.<String>emptySet(), instances,
                                edges, depths, Integer.MAX_VALUE, cared,
                                pruned));
        // The refused hop is named rather than silent.
        assertEquals(1, pruned.size());
        Map<String, Object> refusal = pruned.values().iterator().next();
        assertEquals(RuntimeSelectedRegionFinalizer.DEMAND_PRUNED_UNCARED_KIND,
                refusal.get("kind"));
        assertEquals("example.Owner#keyUpdateInterval",
                refusal.get(SharedFieldFlow.EDGE_LOCATION));
        assertEquals(middle, refusal.get("readerOccurrenceId"));
        assertEquals("REGION.middle", refusal.get("readerRegionId"));

        // A null care set is the ungated rule: both locations seed again.
        assertEquals(2, RuntimeSelectedRegionFinalizer
                .transitiveSharedLocationDemand(
                        Arrays.asList(target, middle),
                        Collections.<String>emptySet(), instances, edges,
                        depths, Integer.MAX_VALUE, null, null).size());
    }

    private static Map<String, Object> demandActivation(
            String activationId, String regionId, String occurrenceId,
            String sourceKey) {
        return row(
                "activationId", activationId,
                "regionId", regionId,
                "occurrenceId", occurrenceId,
                "sourceKey", sourceKey);
    }

    private static Map<String, Object> fieldFlow(
            String edgeId, String writer, String reader, String readPort,
            String location) {
        return row(
                "schemaVersion", 3,
                "kind", "RUNTIME_FIELD_FLOW",
                "edgeId", edgeId,
                "fromOccurrenceId", writer,
                "toOccurrenceId", reader,
                "toPort", readPort,
                SharedFieldFlow.EDGE_LOCATION, location);
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
