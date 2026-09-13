package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceMinter;
import org.junit.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
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

    private static final String FAULT_OCCURRENCE =
            "source/region/REGION.fault#1";
    private static final String CONSUMER_OCCURRENCE =
            "source/region/REGION.consumer#1";
    private static final String TARGET_OCCURRENCE =
            "target/region/REGION.target#1";
    private static final String TARGET_FAULT_OCCURRENCE =
            "target/region/REGION.fault#1";
    private static final String TARGET_STATE_OCCURRENCE =
            "target/region/REGION.consumer#1";
    private static final List<String> TWO_SIDED_FAULT_RETAINED =
            Arrays.asList("RPC.response", "RPC.target-input",
                    "RPC.target-state-response");

    /**
     * One request whose response supplies the value the fatal target checks,
     * and one request on the target's own node whose response maintains
     * target-local state.  Both fire the same fault marker.
     */
    private static StaticProgram twoSidedFaultProgram() {
        String faultOccurrence = FAULT_OCCURRENCE;
        String unrelatedOccurrence = "source/region/REGION.fault#2";
        String earlyOccurrence = "source/region/REGION.fault#3";
        String consumerOccurrence = CONSUMER_OCCURRENCE;
        String targetOccurrence = TARGET_OCCURRENCE;
        String targetFaultOccurrence = TARGET_FAULT_OCCURRENCE;
        String targetStateOccurrence = TARGET_STATE_OCCURRENCE;
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
        return program;
    }

    private static List<Map<String, Object>> twoSidedFaultLinks() {
        return Arrays.asList(
                requestLink("AF", "exchange\n1\nREQUEST", "REQUEST.1",
                        1L, 3L),
                requestLink("AE", "exchange\n1\nREQUEST", "REQUEST.1",
                        1L, 3L),
                requestLink("AU", "other\n1\nREQUEST", "REQUEST.2",
                        11L, 13L),
                requestLink("TF", "target-state\n1\nREQUEST",
                        "REQUEST.target-state", 6L, 8L));
    }

    private static StaticProgram twoSidedFaultProgramWith(
            Map<String, Object> extraEdge) {
        StaticProgram program = twoSidedFaultProgram();
        program.regionEdges.add(extraEdge);
        return program;
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
