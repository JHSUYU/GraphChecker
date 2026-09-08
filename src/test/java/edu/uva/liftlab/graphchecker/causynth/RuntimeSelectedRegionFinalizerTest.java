package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeSelectedRegionFinalizerTest {
    private static final Gson GSON = new Gson();

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void sharedJvmReceiverIdentityCrossesLogicalSources()
            throws Exception {
        List<Map<String, Object>> regions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(
                                leafPort("REGION.W.out.keyId",
                                        "node-a/region/REGION.W#1", "node-a",
                                        74965, 100L)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                                leafPort("REGION.R.in.keyId",
                                        "node-b/region/REGION.R#1", "node-b",
                                        74965, 200L))));

        List<Map<String, Object>> flows =
                RuntimeSelectedRegionFinalizer.demandedLeafProducerFlows(
                        regions, new ArrayList<Map<String, Object>>());

        assertEquals(1, flows.size());
        assertEquals("node-a/region/REGION.W#1",
                flows.get(0).get("fromOccurrenceId"));
        assertEquals("node-b/region/REGION.R#1",
                flows.get(0).get("toOccurrenceId"));
        assertEquals("node-b",
                flows.get(0).get("readFromSourceKey"));
    }

    @Test
    public void atomicMutationFlowsToItsValueAccessor() throws Exception {
        String outerField = "<example.Owner: "
                + "java.util.concurrent.atomic.AtomicInteger counter>";
        String atomicValue = "<java.util.concurrent.atomic.AtomicInteger: "
                + "int value>";
        String mutator = "<java.util.concurrent.atomic.AtomicInteger: "
                + "int getAndDecrement()>";
        Map<String, Object> mutation = object(
                "portId", "REGION.writer.out.counter",
                "transportKind", "HEAP",
                "sourceKey", "cluster/node#epoch0",
                "occurrenceId", "node/region/REGION.writer#1",
                "rootCallId", 10L,
                "fieldReceiverObjectId", 100,
                "valueObjectId", 200,
                "eventSeq", 20L,
                "bindingKind", "CONTAINER_MUTATION",
                "writerFieldReadSeq", 16L,
                "mutatorEnterSeq", 17L,
                "mutationCompletionSeq", 20L,
                "mutationInvocationId", 7L,
                "mutatorDeclaredCallee", mutator,
                "dependencyRole", DependencyRole.VALUE_FRONTIER,
                "fieldPathDeclarations",
                Collections.singletonList(outerField));
        Map<String, Object> accessor = object(
                "portId", "REGION.reader.in.value",
                "sourceKind", "ACCESSOR_RETURN",
                "sourceKey", "cluster/node#epoch0",
                "occurrenceId", "node/region/REGION.reader#1",
                "rootCallId", 30L,
                "fieldReceiverObjectId", 200,
                "valueObjectId", 0,
                "primitiveValue", "1",
                "eventSeq", 40L,
                "dependencyRole", DependencyRole.VALUE_FRONTIER,
                "fieldPathDeclarations",
                Collections.singletonList(atomicValue));

        List<Map<String, Object>> flows =
                RuntimeSelectedRegionFinalizer.fieldFlows(
                        Arrays.asList(
                                leafRegion("REGION.writer",
                                        Collections.singletonList(mutation),
                                        Collections.<Map<String, Object>>
                                                emptyList()),
                                leafRegion("REGION.reader",
                                        Collections.<Map<String, Object>>
                                                emptyList(),
                                        Collections.singletonList(accessor))),
                        Collections.singleton(atomicValue));

        assertEquals(String.valueOf(flows), 1, flows.size());
        assertEquals("RUNTIME_FIELD_FLOW", flows.get(0).get("kind"));
        assertEquals(Collections.singletonList(atomicValue),
                flows.get(0).get("fieldPathDeclarations"));
        assertEquals(200, flows.get(0).get("receiverObjectId"));
        assertEquals(200, flows.get(0).get("valueObjectId"));
        assertEquals(200, flows.get(0).get("readerValueObjectId"));
    }

    @Test
    public void rpcProducerRetainsExactPriorHeapWriter() throws Exception {
        String writerRoot = "<example.Writer: void run()>";
        String futureWriterRoot = "<example.FutureWriter: void run()>";
        String producerRoot = "<example.Client: void run()>";
        String targetRoot = "<example.Server: int consume(int)>";
        String field = "<example.Shared: int keyId>";
        String local = producerRoot + "::$keyId";
        String portId = "XCH.example.req.keyId";

        File skeleton = writeRows("rpc-heap-skeleton.jsonl",
                communicationSkeleton("REGION.writer", writerRoot,
                        "STATE_CONTEXT", null),
                communicationSkeleton("REGION.future", futureWriterRoot,
                        "STATE_CONTEXT", null),
                communicationSkeleton("REGION.producer", producerRoot,
                        "STATE_CONTEXT",
                        communicationPort(portId, "OUT", "CLIENT")),
                communicationSkeleton("REGION.target", targetRoot,
                        "EXCEPTION_CONTEXT",
                        communicationPort(portId, "IN", "SERVER")));
        Map<String, Object> write = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.rpc.heap.write", "kind", "field_write",
                "transferKind", "HEAP_WRITE", "method", writerRoot,
                "siteId", writerRoot + "#u5", "unitIndex", 5,
                "fromCell", writerRoot + "::i0", "toCell", field,
                "regionIds", Collections.singletonList("REGION.writer"),
                "runtimeFieldBindings", Collections.singletonList(
                        fieldBinding("REGION.writer", 10L, writerRoot,
                                20L, field, "7", 100)));
        Map<String, Object> read = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.rpc.heap.read", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", producerRoot,
                "siteId", producerRoot + "#u8", "unitIndex", 8,
                "fromCell", field, "toCell", local,
                "regionIds", Collections.singletonList("REGION.producer"),
                "runtimeFieldBindings", Collections.singletonList(
                        fieldBinding("REGION.producer", 20L, producerRoot,
                                40L, field, "7", 100)));
        Map<String, Object> futureWrite = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.rpc.heap.future", "kind", "field_write",
                "transferKind", "HEAP_WRITE", "method", futureWriterRoot,
                "siteId", futureWriterRoot + "#u5", "unitIndex", 5,
                "fromCell", futureWriterRoot + "::i0", "toCell", field,
                "regionIds", Collections.singletonList("REGION.future"),
                "runtimeFieldBindings", Collections.singletonList(
                        fieldBinding("REGION.future", 40L,
                                futureWriterRoot, 80L, field, "9", 100)));
        Map<String, Object> fatal = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.rpc.failure", "kind", "exception_guard",
                "transferKind", "GUARD", "method", targetRoot,
                "regionIds", Collections.singletonList("REGION.target"),
                "fromCell", targetRoot + "::$keyId",
                "toCell", targetRoot + "#u9#exception:example.Failure",
                "siteId", targetRoot + "#u9", "unitIndex", 9);
        File refined = writeRows("rpc-heap-refined.jsonl",
                write, futureWrite, read, fatal);

        Map<String, Object> writer = activation("ACT.writer",
                "REGION.writer", 10L, writerRoot, "STATE_CONTEXT");
        Map<String, Object> futureWriter = activation("ACT.future",
                "REGION.future", 40L, futureWriterRoot, "STATE_CONTEXT");
        Map<String, Object> producer = activation("ACT.producer",
                "REGION.producer", 20L, producerRoot, "STATE_CONTEXT");
        Map<String, Object> target = activation("ACT.target",
                "REGION.target", 30L, targetRoot, "EXCEPTION_CONTEXT");
        target.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(targetRoot + "#u9", targetRoot,
                        70L, 30L, false)));
        String exchangeLeg = "exchange-1\nattempt-1\nREQUEST";
        observeCommunication(producer, "OUT", portId, exchangeLeg,
                49L, 50L);
        observeCommunication(target, "IN", portId, exchangeLeg,
                61L, 60L);
        Map<String, Object> link = object("schemaVersion", 3,
                "kind", "RUNTIME_OCCURRENCE_LINK",
                "linkKind", "SERVER_ENTRY",
                "fromActivationId", "ACT.producer",
                "toActivationId", "ACT.target",
                "exchangeLeg", exchangeLeg,
                "attemptId", "attempt-1", "direction", "REQUEST",
                "transport", "EXAMPLE", "senderEventSeq", 50L,
                "receiverEventSeq", 60L,
                "authority", "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        Arrays.asList(write, futureWrite, read, fatal),
                        refined, skeleton,
                        Arrays.asList(writerRoot, futureWriterRoot,
                                producerRoot, targetRoot),
                        Arrays.asList(writer, futureWriter, producer, target),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(link));

        assertEquals(String.valueOf(result.regions), 3,
                result.regions.size());
        boolean protocol = false;
        boolean fieldFlow = false;
        for (Map<String, Object> edge : result.regionEdges) {
            protocol |= "RUNTIME_PROTOCOL_FLOW".equals(edge.get("kind"))
                    && "REGION.producer".equals(edge.get("fromRegion"))
                    && "REGION.target".equals(edge.get("toRegion"));
            fieldFlow |= "RUNTIME_FIELD_FLOW".equals(edge.get("kind"))
                    && "REGION.writer".equals(edge.get("fromRegion"))
                    && "REGION.producer".equals(edge.get("toRegion"));
        }
        assertTrue(String.valueOf(result.regionEdges), protocol);
        assertTrue(String.valueOf(result.regionEdges), fieldFlow);
        assertFalse(String.valueOf(result.regions), result.regions.stream()
                .anyMatch(region -> "REGION.future".equals(
                        region.get("regionId"))));
        assertFalse(String.valueOf(result.regionEdges),
                result.regionEdges.stream().anyMatch(edge ->
                        "REGION.future".equals(edge.get("fromRegion"))));

        // The exact occurrence link owns the crossing order.  Its send and
        // receive sequence must reach the occurrence-owned OUT/IN copies so
        // fatal-prefix slicing can compare a demanded communication value
        // with the target event without inventing a second timing source.
        long producerEvent = -1L;
        long targetEvent = -1L;
        for (Map<String, Object> region : result.regions) {
            if ("REGION.producer".equals(region.get("regionId"))) {
                for (Map<String, Object> port : rows(region.get("outputs"))) {
                    if (portId.equals(port.get("portId"))
                            && port.get("occurrenceId") != null) {
                        producerEvent = ((Number) port.get("eventSeq"))
                                .longValue();
                    }
                }
            } else if ("REGION.target".equals(region.get("regionId"))) {
                for (Map<String, Object> port
                        : rows(region.get("symbolicInputs"))) {
                    if (portId.equals(port.get("portId"))
                            && port.get("occurrenceId") != null) {
                        targetEvent = ((Number) port.get("eventSeq"))
                                .longValue();
                    }
                }
            }
        }
        assertEquals(50L, producerEvent);
        assertEquals(60L, targetEvent);
    }

    /**
     * Each bounded write version of a repeated output keeps the delivery that
     * preceded it, so the late version's own protocol edge exists as a region
     * edge of its own.
     *
     * <p>This is a requirement about versions staying distinguishable, not
     * about how they are scheduled.  Under README REGION-1 the two versions
     * are two guarded cases of one coarse producer occurrence rather than two
     * producer goals, and both deliveries stay on that one occurrence's
     * binding ledger - which is exactly what this asserts.  If the late edge
     * ever stopped being published here, the later version would have no
     * incoming evidence to guard its case with.</p>
     */
    @Test
    public void repeatedOutputVersionsExpandTheirOwnPriorDelivery()
            throws Exception {
        String upstreamRoot = "<example.NameNode: void respond()>";
        String producerRoot = "<example.DataNode: void update()>";
        String targetRoot = "<example.Server: int consume()>";
        String field = "<example.Shared: int value>";
        String local = targetRoot + "::$value";
        String responsePort = "XCH.example.resp";

        File skeleton = writeRows("event-local-demand-skeleton.jsonl",
                communicationSkeleton("REGION.upstream", upstreamRoot,
                        "COMMUNICATION_CONTEXT",
                        communicationPort(responsePort, "OUT", "SERVER",
                                "RESPONSE")),
                communicationSkeleton("REGION.producer", producerRoot,
                        "STATE_CONTEXT",
                        communicationPort(responsePort, "IN", "CLIENT",
                                "RESPONSE")),
                communicationSkeleton("REGION.target", targetRoot,
                        "EXCEPTION_CONTEXT", null));
        Map<String, Object> write = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.event.local.write", "kind", "field_write",
                "transferKind", "HEAP_WRITE", "method", producerRoot,
                "siteId", producerRoot + "#u5", "unitIndex", 5,
                "fromCell", producerRoot + "::i0", "toCell", field,
                "regionIds", Collections.singletonList("REGION.producer"),
                "runtimeFieldBindings", Arrays.asList(
                        fieldBinding("REGION.producer", 20L, producerRoot,
                                30L, field, "1", 100),
                        fieldBinding("REGION.producer", 20L, producerRoot,
                                90L, field, "2", 100)));
        Map<String, Object> read = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.event.local.read", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", targetRoot,
                "siteId", targetRoot + "#u8", "unitIndex", 8,
                "fromCell", field, "toCell", local,
                "regionIds", Collections.singletonList("REGION.target"),
                "runtimeFieldBindings", Arrays.asList(
                        fieldBinding("REGION.target", 30L, targetRoot,
                                50L, field, "1", 100),
                        fieldBinding("REGION.target", 50L, targetRoot,
                                110L, field, "2", 100)));
        Map<String, Object> fatal = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.event.local.failure", "kind", "exception_guard",
                "transferKind", "GUARD", "method", targetRoot,
                "regionIds", Collections.singletonList("REGION.target"),
                "fromCell", local,
                "toCell", targetRoot + "#u9#exception:example.Failure",
                "siteId", targetRoot + "#u9", "unitIndex", 9);
        File refined = writeRows("event-local-demand-refined.jsonl",
                write, read, fatal);

        Map<String, Object> earlyUpstream = activation("ACT.upstream.early",
                "REGION.upstream", 10L, upstreamRoot,
                "COMMUNICATION_CONTEXT");
        Map<String, Object> producer = activation("ACT.producer",
                "REGION.producer", 20L, producerRoot, "STATE_CONTEXT");
        Map<String, Object> earlyTarget = activation("ACT.target.early",
                "REGION.target", 30L, targetRoot, "EXCEPTION_CONTEXT");
        earlyTarget.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(targetRoot + "#u9", targetRoot,
                        55L, 30L, false)));
        Map<String, Object> lateUpstream = activation("ACT.upstream.late",
                "REGION.upstream", 40L, upstreamRoot,
                "COMMUNICATION_CONTEXT");
        Map<String, Object> lateTarget = activation("ACT.target.late",
                "REGION.target", 50L, targetRoot, "EXCEPTION_CONTEXT");
        lateTarget.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(targetRoot + "#u9", targetRoot,
                        115L, 50L, false)));
        Map<String, Object> earlyLink = occurrenceLink(
                "ACT.upstream.early", "ACT.producer", "early", 10L, 15L);
        Map<String, Object> lateLink = occurrenceLink(
                "ACT.upstream.late", "ACT.producer", "late", 60L, 70L);
        observeCommunication(earlyUpstream, "OUT", responsePort,
                "early\nattempt-1\nRESPONSE", 9L, 10L);
        observeCommunication(producer, "IN", responsePort,
                "early\nattempt-1\nRESPONSE", 16L, 15L);
        observeCommunication(lateUpstream, "OUT", responsePort,
                "late\nattempt-1\nRESPONSE", 59L, 60L);
        observeCommunication(producer, "IN", responsePort,
                "late\nattempt-1\nRESPONSE", 71L, 70L);

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        Arrays.asList(write, read, fatal), refined, skeleton,
                        Arrays.asList(upstreamRoot, producerRoot, targetRoot),
                        Arrays.asList(earlyUpstream, producer, earlyTarget,
                                lateUpstream, lateTarget),
                        Collections.<Map<String, Object>>emptyList(),
                        Arrays.asList(earlyLink, lateLink));

        String lateOccurrence = String.valueOf(
                lateUpstream.get("occurrenceId"));
        assertTrue(String.valueOf(result.regionEdges),
                result.regionEdges.stream().anyMatch(edge ->
                        "RUNTIME_PROTOCOL_FLOW".equals(edge.get("kind"))
                                && lateOccurrence.equals(
                                edge.get("fromOccurrenceId"))
                                && Long.valueOf(70L).equals(
                                edge.get("receiverEventSeq"))));
    }

    @Test
    public void requestPrefixKeepsOnlyTheExactlyCapturedTransaction()
            throws Exception {
        String producerRoot = "<example.Transport: int send()>";
        String consumerRoot = "<example.Client: int receive()>";
        String targetRoot = "<example.Client: void fail()>";
        String portId = "XCH.example.response.status";
        String request = "cluster/client#epoch0/request/work#1";
        String otherRequest = "cluster/client#epoch0/request/work#2";

        File skeleton = writeRows("request-prefix-skeleton.jsonl",
                communicationSkeleton("REGION.producer", producerRoot,
                        "COMMUNICATION_CONTEXT",
                        communicationPort(portId, "OUT", "SERVER",
                                "RESPONSE")),
                communicationSkeleton("REGION.consumer", consumerRoot,
                        "STATE_CONTEXT",
                        communicationPort(portId, "IN", "CLIENT",
                                "RESPONSE")),
                communicationSkeleton("REGION.target", targetRoot,
                        "EXCEPTION_CONTEXT", null));
        Map<String, Object> fatal = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.request.prefix.failure",
                "kind", "exception_guard", "transferKind", "GUARD",
                "method", targetRoot,
                "regionIds", Collections.singletonList("REGION.target"),
                "fromCell", targetRoot + "::$failed",
                "toCell", targetRoot + "#u9#exception:example.Failure",
                "siteId", targetRoot + "#u9", "unitIndex", 9);
        File refined = writeRows("request-prefix-refined.jsonl", fatal);

        Map<String, Object> firstProducer = activation("ACT.producer.first",
                "REGION.producer", 10L, producerRoot,
                "COMMUNICATION_CONTEXT");
        Map<String, Object> secondProducer = activation(
                "ACT.producer.second", "REGION.producer", 20L,
                producerRoot, "COMMUNICATION_CONTEXT");
        Map<String, Object> sharedConsumer = activation("ACT.consumer.shared",
                "REGION.consumer", 30L, consumerRoot, "STATE_CONTEXT");
        Map<String, Object> otherProducer = activation("ACT.producer.other",
                "REGION.producer", 40L, producerRoot,
                "COMMUNICATION_CONTEXT");
        Map<String, Object> otherConsumer = activation("ACT.consumer.other",
                "REGION.consumer", 50L, consumerRoot, "STATE_CONTEXT");
        Map<String, Object> lateProducer = activation("ACT.producer.late",
                "REGION.producer", 60L, producerRoot,
                "COMMUNICATION_CONTEXT");
        Map<String, Object> lateConsumer = activation("ACT.consumer.late",
                "REGION.consumer", 70L, consumerRoot, "STATE_CONTEXT");
        Map<String, Object> target = activation("ACT.target",
                "REGION.target", 80L, targetRoot, "EXCEPTION_CONTEXT");
        for (Map<String, Object> activation : Arrays.asList(firstProducer,
                secondProducer, sharedConsumer, lateProducer, lateConsumer,
                target)) {
            activation.put("requestKey", request);
        }
        otherProducer.put("requestKey", otherRequest);
        otherConsumer.put("requestKey", otherRequest);
        target.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(targetRoot + "#u9", targetRoot,
                        100L, 80L, false)));

        Map<String, Object> first = requestFlowLink("ACT.producer.first",
                "ACT.consumer.shared", "exchange-first", "attempt-1",
                request, 10L, 20L);
        Map<String, Object> second = requestFlowLink("ACT.producer.second",
                "ACT.consumer.shared", "exchange-second", "attempt-2",
                request, 30L, 40L);
        Map<String, Object> other = requestFlowLink("ACT.producer.other",
                "ACT.consumer.other", "exchange-other", "attempt-1",
                otherRequest, 50L, 60L);
        Map<String, Object> late = requestFlowLink("ACT.producer.late",
                "ACT.consumer.late", "exchange-late", "attempt-3",
                request, 110L, 120L);

        observeCommunication(firstProducer, "OUT", portId,
                "exchange-first\nattempt-1\nRESPONSE", 9L, 10L);
        observeCommunication(secondProducer, "OUT", portId,
                "exchange-second\nattempt-2\nRESPONSE", 29L, 30L);
        // The same coarse consumer received both responses, but its cut ran
        // only after the second one.  The first delivery is not observed at
        // this port and must not acquire an edge.
        observeCommunication(sharedConsumer, "IN", portId,
                "exchange-second\nattempt-2\nRESPONSE", 41L, 40L);
        observeCommunication(otherProducer, "OUT", portId,
                "exchange-other\nattempt-1\nRESPONSE", 49L, 50L);
        observeCommunication(otherConsumer, "IN", portId,
                "exchange-other\nattempt-1\nRESPONSE", 61L, 60L);
        observeCommunication(lateProducer, "OUT", portId,
                "exchange-late\nattempt-3\nRESPONSE", 109L, 110L);
        observeCommunication(lateConsumer, "IN", portId,
                "exchange-late\nattempt-3\nRESPONSE", 121L, 120L);

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        Collections.singletonList(fatal), refined, skeleton,
                        Arrays.asList(producerRoot, consumerRoot, targetRoot),
                        Arrays.asList(firstProducer, secondProducer,
                                sharedConsumer, otherProducer, otherConsumer,
                                lateProducer, lateConsumer, target),
                        Collections.<Map<String, Object>>emptyList(),
                        Arrays.asList(first, second, other, late));

        List<Map<String, Object>> protocol = new ArrayList<>();
        for (Map<String, Object> edge : result.regionEdges) {
            if ("RUNTIME_PROTOCOL_FLOW".equals(edge.get("kind"))) {
                protocol.add(edge);
            }
        }
        assertEquals(String.valueOf(protocol), 1, protocol.size());
        assertEquals("exchange-second\nattempt-2\nRESPONSE",
                protocol.get(0).get("exchangeLeg"));
        assertEquals(request, protocol.get(0).get("requestKey"));
        assertEquals(secondProducer.get("occurrenceId"),
                protocol.get(0).get("fromOccurrenceId"));
        assertEquals(sharedConsumer.get("occurrenceId"),
                protocol.get(0).get("toOccurrenceId"));
    }

    private static Map<String, Object> requestFlowLink(
            String fromActivation, String toActivation, String exchange,
            String attempt, String requestKey, long senderEventSeq,
            long receiverEventSeq) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_OCCURRENCE_LINK",
                "linkKind", "CLIENT_RETURN",
                "fromActivationId", fromActivation,
                "toActivationId", toActivation,
                "exchangeLeg", exchange + "\n" + attempt + "\nRESPONSE",
                "attemptId", attempt, "direction", "RESPONSE",
                "transport", "EXAMPLE", "requestKey", requestKey,
                "senderEventSeq", senderEventSeq,
                "receiverEventSeq", receiverEventSeq,
                "authority", "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1");
    }

    private static Map<String, Object> occurrenceLink(
            String fromActivation, String toActivation, String exchange,
            long senderEventSeq, long receiverEventSeq) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_OCCURRENCE_LINK",
                "linkKind", "SERVER_ENTRY",
                "fromActivationId", fromActivation,
                "toActivationId", toActivation,
                "exchangeLeg", exchange + "\nattempt-1\nRESPONSE",
                "attemptId", "attempt-1", "direction", "RESPONSE",
                "transport", "EXAMPLE",
                "senderEventSeq", senderEventSeq,
                "receiverEventSeq", receiverEventSeq,
                "authority", "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1");
    }

    private static void observeCommunication(
            Map<String, Object> activation, String side, String portId,
            String exchangeLeg, long eventSeq, long transportEventSeq) {
        List<Map<String, Object>> captures = new ArrayList<>(rows(
                activation.get(RuntimeSelectedRegionFinalizer
                        .OBSERVED_COMMUNICATION_CAPTURES)));
        captures.add(object("side", side, "portId", portId,
                "exchangeLeg", exchangeLeg, "eventSeq", eventSeq,
                "transportEventSeq", transportEventSeq));
        activation.put(RuntimeSelectedRegionFinalizer
                .OBSERVED_COMMUNICATION_CAPTURES, captures);
    }

    private static Map<String, Object> communicationSkeleton(
            String regionId, String root, String selection,
            Map<String, Object> port) {
        Map<String, Object> result = object("schemaVersion", 3,
                "kind", "REGION_SKELETON", "regionId", regionId,
                "rootMethod", root, "rootAuthority", "TASK_ENTRY",
                "anchorMethod", root,
                "methods", Collections.singletonList(root),
                "selection", selection);
        if (port != null) {
            result.put(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                    Collections.singletonList(port));
        }
        return result;
    }

    private static Map<String, Object> communicationPort(
            String portId, String side, String role) {
        return communicationPort(portId, side, role, "REQUEST");
    }

    private static Map<String, Object> communicationPort(
            String portId, String side, String role, String direction) {
        return object("portId", portId,
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, side,
                "sourceKind",
                RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT,
                "dependencyRole", DependencyRole.VALUE_FRONTIER,
                "javaType", "int",
                CommunicationCatalogContract.PORT_DIRECTION, direction,
                "portRole", role);
    }

    private static Map<String, Object> activation(
            String activationId, String regionId, long callId,
            String root, String selection) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "activationId", activationId, "regionId", regionId,
                "rootCallId", callId, "rootMethod", root,
                "selection", selection,
                "sourceKey", "cluster/node#epoch0",
                "sourceId", "cluster/node", "sourceEpoch", 0,
                "callIds", Collections.singletonList(callId),
                "observedMethods", Collections.singletonList(root));
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        return value instanceof List
                ? (List<Map<String, Object>>) value
                : Collections.<Map<String, Object>>emptyList();
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
            String portId, String occurrenceId, String sourceKey,
            int receiver, long seq) {
        return object("portId", portId, "transportKind", "HEAP",
                "sourceKey", sourceKey, "occurrenceId", occurrenceId,
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

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
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
