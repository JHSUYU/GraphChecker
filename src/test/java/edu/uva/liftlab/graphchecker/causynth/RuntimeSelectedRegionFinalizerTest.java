package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeSelectedRegionFinalizerTest {
    private static final Gson GSON = new Gson();

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void onlyTheActivationThatObservedTheFatalSiteIsAClosureTarget()
            throws Exception {
        // One thread-entry region with three concurrent activations.
        // `selection` belongs to the static skeleton, so all three inherit
        // EXCEPTION_CONTEXT, but the failure site executed in exactly one of
        // them.  Demanding per-activation fatal evidence from all three
        // aborts the whole workload; demanding it only from the activations
        // that actually observed the site keeps the producers as ordinary
        // closure participants.
        String root = "<example.Worker: void run()>";
        String field = "<example.Shared: int value>";
        String local = root + "::$value";
        Map<String, Object> skeletonRow = threadEntrySkeleton(root);
        skeletonRow.put(StaticSymbolicSourceDeclaration.FIELD,
                Collections.singletonList(staticSource("SOURCE.VALUE",
                        field, root, 1)));
        skeletonRow.put(ConfiguredSourcePhaseContract.DECLARATION_FIELD,
                Collections.singletonList(
                        ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                "SOURCE.VALUE", field, root, 1)));
        File skeleton = writeRows("thread-entry-skeleton.jsonl",
                skeletonRow);
        File refined = writeRows("thread-entry-refined.jsonl",
                sharedFieldWrite(root, field, Arrays.asList(
                        fieldBinding("REGION.worker", 1, root, 5, field,
                                "7", 100),
                        fieldBinding("REGION.worker", 2, root, 6, field,
                                "7", 100))),
                sharedFieldRead(root, field, local,
                        fieldBinding("REGION.worker", 3, root, 8, field,
                                "7", 100)),
                fatalGuard(root, local));
        Map<String, Object> producerOne = exceptionContextActivation(
                "REGION.worker", 1, root);
        Map<String, Object> producerTwo = exceptionContextActivation(
                "REGION.worker", 2, root);
        Map<String, Object> consumer = exceptionContextActivation(
                "REGION.worker", 3, root);
        consumer.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(root + "#u9", root, 50L, 3L, false)));

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeleton,
                        Collections.singleton(root),
                        Arrays.asList(producerOne, producerTwo, consumer),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.<Map<String, Object>>emptyList());

        assertEquals(1, result.regions.size());
        List<Map<String, Object>> retainedSources = rows(result.regions
                .get(0).get(StaticSymbolicSourceDeclaration.FIELD));
        assertEquals(1, retainedSources.size());
        assertEquals("SOURCE.VALUE",
                retainedSources.get(0).get("sourceId"));
        assertEquals(field,
                retainedSources.get(0).get("fieldSignature"));
        List<Map<String, Object>> retainedPhases = rows(result.regions
                .get(0).get(ConfiguredSourcePhaseContract.DECLARATION_FIELD));
        assertEquals(1, retainedPhases.size());
        assertEquals("PUBLISH", retainedPhases.get(0).get("phase"));
        // Exactly one activation carries the fatal prefix the target slice is
        // cut against; the producers were never treated as targets.
        assertTrue(consumer.containsKey("fatalPrefixContexts"));
        assertFalse(producerOne.containsKey("fatalPrefixContexts"));
        assertFalse(producerTwo.containsKey("fatalPrefixContexts"));
        List<?> retained = (List<?>) result.regions.get(0).get(
                "runtimeOccurrenceIds");
        assertTrue(String.valueOf(retained),
                retained.contains(consumer.get("occurrenceId")));
        assertTrue(String.valueOf(retained),
                retained.contains(producerOne.get("occurrenceId"))
                        || retained.contains(
                        producerTwo.get("occurrenceId")));

        // Folded Phase 2 field acceptance: two writers of one field, both
        // storing the same concrete 7 into the same receiver, are both
        // retained as candidates of the one read.  Aggregation runs before
        // any symbolic session exists, so it has nothing that could decide
        // between them - and the value they share is precisely the thing that
        // cannot.  Neither is stamped as an observed edge.
        List<Map<String, Object>> fieldFlows = new ArrayList<>();
        for (Map<String, Object> edge : result.regionEdges) {
            if ("RUNTIME_FIELD_FLOW".equals(edge.get("kind"))) {
                fieldFlows.add(edge);
            }
        }
        assertEquals(String.valueOf(fieldFlows), 2, fieldFlows.size());
        List<Object> candidateWriters = new ArrayList<>();
        for (Map<String, Object> edge : fieldFlows) {
            assertEquals("TRACE_CANDIDATE_WRITER",
                    edge.get("readFromProvenance"));
            assertEquals("SHARED_STATE_NOT_SELECTED",
                    edge.get("readFromProvenanceGap"));
            assertEquals("example.Shared#value", edge.get("readFromField"));
            candidateWriters.add(edge.get("fromOccurrenceId"));
        }
        assertTrue(String.valueOf(candidateWriters),
                candidateWriters.contains(producerOne.get("occurrenceId"))
                        && candidateWriters.contains(
                        producerTwo.get("occurrenceId")));

        // The unambiguous-producer rule for a still-unclosed demanded leaf is
        // unchanged in what it binds, and changed in what it claims: the one
        // writer the run leaves possible is a candidate, not a proven edge.
        List<Map<String, Object>> leafRegions = Arrays.asList(
                leafRegion("REGION.W", Collections.singletonList(
                                leafPort("REGION.W.out.keyId",
                                        "p/region/REGION.W#1", 74965, 100L)),
                        Collections.<Map<String, Object>>emptyList()),
                leafRegion("REGION.R",
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                                leafPort("REGION.R.in.keyId",
                                        "p/region/REGION.R#1", 74965, 200L))));

        List<Map<String, Object>> leafFlows =
                RuntimeSelectedRegionFinalizer.demandedLeafProducerFlows(
                        leafRegions, new ArrayList<Map<String, Object>>());

        assertEquals(1, leafFlows.size());
        assertEquals("TRACE_CANDIDATE_WRITER",
                leafFlows.get(0).get("readFromProvenance"));
        assertEquals("SHARED_STATE_NOT_SELECTED",
                leafFlows.get(0).get("readFromProvenanceGap"));
        assertEquals("p", leafFlows.get(0).get("readFromSourceKey"));
    }

    @Test
    public void semanticSourceOwnsFinalizedOccurrenceOrdinals()
            throws Exception {
        String root = "<example.Worker: void run()>";
        File skeleton = writeRows("semantic-ordinal-skeleton.jsonl",
                threadEntrySkeleton(root));
        File refined = writeRows("semantic-ordinal-refined.jsonl",
                fatalGuard(root, root + "::$guard"));
        Map<String, Object> dn0 = exceptionContextActivation(
                "REGION.worker", 1L, root);
        dn0.put("sourceKey", "cluster0/dn0#epoch1");
        Map<String, Object> dn1 = exceptionContextActivation(
                "REGION.worker", 2L, root);
        dn1.put("sourceKey", "cluster0/dn1#epoch1");
        List<Map<String, Object>> observations = Arrays.asList(
                object("kind", "BRANCH", "eventSeq", 10L,
                        "method", root, "callId", 1L,
                        "siteId", root + "#u9", "outcome", false,
                        "callSourceKey", "cluster0/client0#epoch0"),
                object("kind", "BRANCH", "eventSeq", 20L,
                        "method", root, "callId", 2L,
                        "siteId", root + "#u9", "outcome", false,
                        "callSourceKey", "cluster0/client0#epoch0"));

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeleton,
                        Collections.singleton(root),
                        Arrays.asList(dn0, dn1),
                        observations,
                        Collections.<Map<String, Object>>emptyList());

        assertEquals("cluster0/client0#epoch0/region/REGION.worker#1",
                dn0.get("occurrenceId"));
        assertEquals("cluster0/client0#epoch0/region/REGION.worker#2",
                dn1.get("occurrenceId"));
        assertEquals(1, result.regions.size());
        assertEquals(Arrays.asList(dn0.get("occurrenceId"),
                        dn1.get("occurrenceId")),
                result.regions.get(0).get("runtimeOccurrenceIds"));
    }

    @Test
    public void identicalRuntimeActivationRowsAreCanonicalizedBeforeMinting()
            throws Exception {
        String region = "REGION.d842447f-37ce-3501-854b-9388704c804e";
        String root = "<example.Worker: void run()>";
        Map<String, Object> skeletonRow = threadEntrySkeleton(root);
        skeletonRow.put("regionId", region);
        File skeleton = writeRows("duplicate-activation-skeleton.jsonl",
                skeletonRow);
        Map<String, Object> fatal = fatalGuard(root, root + "::$guard");
        fatal.put("regionIds", Collections.singletonList(region));
        File refined = writeRows("duplicate-activation-refined.jsonl", fatal);

        Map<String, Object> activation = exceptionContextActivation(
                region, 1684443L, root);
        activation.put("sourceKey", "cluster0/client0#epoch0");
        // The same parsed JSON object with the member insertion order reversed
        // is canonically identical, not a second execution.
        Map<String, Object> reordered = new LinkedHashMap<>();
        List<Map.Entry<String, Object>> entries = new ArrayList<>(
                activation.entrySet());
        Collections.reverse(entries);
        for (Map.Entry<String, Object> entry : entries) {
            reordered.put(entry.getKey(), entry.getValue());
        }
        Map<String, Object> observation = object("kind", "BRANCH",
                "eventSeq", 1684448L, "method", root,
                "callId", 1684443L, "siteId", root + "#u9",
                "outcome", false,
                "callSourceKey", "cluster0/client0#epoch0");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeleton,
                        Collections.singleton(root),
                        Arrays.asList(activation, reordered),
                        Collections.singletonList(observation),
                        Collections.<Map<String, Object>>emptyList());

        String occurrence = "cluster0/client0#epoch0/region/" + region + "#1";
        assertEquals(occurrence, activation.get("occurrenceId"));
        assertEquals(Collections.singletonList(occurrence),
                result.regions.get(0).get("runtimeOccurrenceIds"));
    }

    @Test
    public void conflictingPayloadForOneRecordedActivationFailsClosed()
            throws Exception {
        String root = "<example.Worker: void run()>";
        File skeleton = writeRows("conflicting-activation-skeleton.jsonl",
                threadEntrySkeleton(root));
        File refined = writeRows("conflicting-activation-refined.jsonl",
                fatalGuard(root, root + "::$guard"));
        Map<String, Object> first = exceptionContextActivation(
                "REGION.worker", 1684443L, root);
        first.put("sourceKey", "cluster0/dn0#epoch0");
        Map<String, Object> conflicting = new LinkedHashMap<>(first);
        conflicting.put("sourceKey", "cluster0/dn1#epoch0");

        try {
            RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeleton,
                        Collections.singleton(root),
                        Arrays.asList(first, conflicting),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.<Map<String, Object>>emptyList());
            throw new AssertionError("conflicting activation must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().startsWith(
                    "conflicting runtime region activation payload:"));
            assertFalse(first.containsKey("occurrenceId"));
        }
    }

    private static Map<String, Object> staticSource(
            String sourceId, String field, String method, int unitIndex) {
        Map<String, Object> source = new LinkedHashMap<>();
        source.put("schemaVersion",
                StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
        source.put("kind", StaticSymbolicSourceDeclaration.KIND);
        source.put("authority", StaticSymbolicSourceDeclaration.AUTHORITY);
        source.put("sourceId", sourceId);
        source.put("fieldSignature", field);
        source.put("declarationMethod", method);
        source.put("declarationUnitIndex", unitIndex);
        return source;
    }

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
    public void noActivationObservingTheFatalSiteFailsClosedByName()
            throws Exception {
        // Several concurrent activations of one exception-context region and
        // not one of them reached the declared failure site.  A workload that
        // never failed has no failure to explain, so the closure must name
        // that gap instead of planning an evidence-free target.
        String root = "<example.Worker: void run()>";
        String field = "<example.Shared: int value>";
        String local = root + "::$value";
        File skeleton = writeRows("unreached-target-skeleton.jsonl",
                threadEntrySkeleton(root));
        File refined = writeRows("unreached-target-refined.jsonl",
                sharedFieldWrite(root, field, Collections.singletonList(
                        fieldBinding("REGION.worker", 1, root, 5, field,
                                "7", 100))),
                sharedFieldRead(root, field, local,
                        fieldBinding("REGION.worker", 2, root, 8, field,
                                "7", 100)),
                fatalGuard(root, local));

        try {
            RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeleton,
                        Collections.singleton(root),
                        Arrays.asList(
                            exceptionContextActivation("REGION.worker", 1,
                                    root),
                            exceptionContextActivation("REGION.worker", 2,
                                    root)),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.<Map<String, Object>>emptyList());
            throw new AssertionError("unreached target must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .startsWith("FATAL_TARGET_OBSERVATION_GAP:"));
        }
    }

    @Test
    public void anUndeclaredFatalTargetFailsClosedByName() throws Exception {
        // The same region, this time with no exception guard at all: nothing
        // in it declares a failureTarget site.  README TARGET-1 binds target
        // existence to a selected concrete branch event, and a region that
        // names no site has no event to bind to, so every one of its
        // exception-context activations used to become a closure target on
        // the strength of its `selection` label alone - a target with zero
        // observed branch evidence, whose slice was then the activation's
        // whole observed input set.  The absent declaration is the gap.
        String root = "<example.Worker: void run()>";
        String field = "<example.Shared: int value>";
        String local = root + "::$value";
        File skeleton = writeRows("undeclared-target-skeleton.jsonl",
                threadEntrySkeleton(root));
        File refined = writeRows("undeclared-target-refined.jsonl",
                sharedFieldWrite(root, field, Collections.singletonList(
                        fieldBinding("REGION.worker", 1, root, 5, field,
                                "7", 100))),
                sharedFieldRead(root, field, local,
                        fieldBinding("REGION.worker", 2, root, 8, field,
                                "7", 100)));
        Map<String, Object> observing = exceptionContextActivation(
                "REGION.worker", 2, root);
        // Recorded branch evidence does not rescue it either: with no
        // declared site the evidence names no target predicate.
        observing.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(root + "#u9", root, 50L, 2L, false)));

        try {
            RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeleton,
                        Collections.singleton(root),
                        Arrays.asList(
                            exceptionContextActivation("REGION.worker", 1,
                                    root),
                            observing),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.<Map<String, Object>>emptyList());
            throw new AssertionError("undeclared target must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .startsWith("FATAL_TARGET_POLICY_ABSENT:"));
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("REGION.worker"));
        }
    }

    /**
     * README section 3's cut ports reach the region port catalog the composer
     * reads.
     *
     * <p>They are not heap ports: no recorded access, no field path, no demand
     * key, so the closure's port filter - which retains a port by exactly
     * those - discards every one of them.  Declaring them after that filter is
     * what makes {@code Req_in = Req_out} and {@code Live_in = Live_out}
     * statable at all; without it the composer keeps the equality as a model
     * row, lowers no SMT term and reports
     * {@code SEGMENT_PORT_NOT_IN_REGION_CATALOG}.</p>
     */
    @Test
    public void declaredCutPortsSurviveTheClosurePortFilter()
            throws Exception {
        String root = "<example.Worker: void run()>";
        String field = "<example.Shared: int value>";
        String local = root + "::$value";
        String request = "XCH.test.req.p0";
        String response = "XCH.test.resp";
        String live = "XCH.test.live.local#$i2";
        Map<String, Object> skeleton = threadEntrySkeleton(root);
        skeleton.put(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                Arrays.asList(
                        cutPort(request, "OUT", "int"),
                        cutPort(response, "IN", "int"),
                        cutPort(live, "OUT", "int"),
                        cutPort(live, "IN", "int")));
        File skeletonFile = writeRows("cut-port-skeleton.jsonl", skeleton);
        File refined = writeRows("cut-port-refined.jsonl",
                sharedFieldWrite(root, field, Collections.singletonList(
                        fieldBinding("REGION.worker", 1, root, 5, field,
                                "7", 100))),
                sharedFieldRead(root, field, local,
                        fieldBinding("REGION.worker", 2, root, 8, field,
                                "7", 100)),
                fatalGuard(root, local));
        Map<String, Object> producer = exceptionContextActivation(
                "REGION.worker", 1, root);
        Map<String, Object> consumer = exceptionContextActivation(
                "REGION.worker", 2, root);
        consumer.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(root + "#u9", root, 50L, 2L, false)));

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeletonFile,
                        Collections.singleton(root),
                        Arrays.asList(producer, consumer),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.<Map<String, Object>>emptyList());

        assertEquals(1, result.regions.size());
        Map<String, Object> region = result.regions.get(0);
        assertTrue(portIds(region, "outputs").toString(),
                portIds(region, "outputs").contains(request));
        assertTrue(portIds(region, "symbolicInputs").toString(),
                portIds(region, "symbolicInputs").contains(response));
        // Live_in = Live_out: one id, an output of the prefix and an input of
        // the continuation.
        assertTrue(portIds(region, "outputs").contains(live));
        assertTrue(portIds(region, "symbolicInputs").contains(live));
        assertFalse(portIds(region, "symbolicInputs").contains(request));
        // The side is how the declaration was routed, not a port field.
        for (Map<String, Object> port : rows(region.get("outputs"))) {
            assertFalse(port.containsKey(
                    RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE));
        }
    }

    /**
     * State used by an injected Causynth adapter is not application shared
     * state.  The transported value has an explicit communication port; the
     * helper's pending table must not create a second heap channel between
     * otherwise independent attempts.
     */
    @Test
    public void causynthSupportHeapIsExcludedFromCausalState()
            throws Exception {
        String root = "<example.Worker: void run()>";
        String support = "<example.CausynthHandoff: int pending>";
        String local = root + "::$pending";
        File skeleton = writeRows("support-state-skeleton.jsonl",
                threadEntrySkeleton(root));
        File refined = writeRows("support-state-refined.jsonl",
                sharedFieldWrite(root, support,
                        Collections.singletonList(fieldBinding(
                                "REGION.worker", 1, root, 5, support,
                                "7", 100))),
                sharedFieldRead(root, support, local,
                        fieldBinding("REGION.worker", 2, root, 8,
                                support, "7", 100)),
                fatalGuard(root, local));
        Map<String, Object> producer = exceptionContextActivation(
                "REGION.worker", 1, root);
        Map<String, Object> consumer = exceptionContextActivation(
                "REGION.worker", 2, root);
        consumer.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(root + "#u9", root, 50L, 2L,
                        false)));

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(refined),
                        refined,
                        skeleton,
                        Collections.singleton(root),
                        Arrays.asList(producer, consumer),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.<Map<String, Object>>emptyList());

        for (Map<String, Object> edge : result.regionEdges) {
            assertFalse(String.valueOf(edge),
                    "RUNTIME_FIELD_FLOW".equals(edge.get("kind")));
        }
        for (String member : new String[]{"symbolicInputs", "outputs"}) {
            for (Map<String, Object> port
                    : rows(result.regions.get(0).get(member))) {
                assertFalse(String.valueOf(port),
                        String.valueOf(port.get("fieldPathDeclarations"))
                                .contains("CausynthHandoff"));
            }
        }
    }

    @Test
    public void recordedEnvelopeRetainsUniqueNestedTypedReceiver()
            throws Exception {
        String producerRoot = "<example.Client: void run()>";
        String envelopeRoot = "<example.Transport: void run()>";
        String targetRoot = "<example.Server: int consume(int)>";
        String portId = "XCH.example.req.keyId";

        Map<String, Object> producerSkeleton = communicationSkeleton(
                "REGION.producer", producerRoot, "STATE_CONTEXT",
                communicationPort(portId, "OUT", "CLIENT"));
        Map<String, Object> envelopeSkeleton = communicationSkeleton(
                "REGION.envelope", envelopeRoot,
                "COMMUNICATION_CONTEXT", null);
        Map<String, Object> targetSkeleton = communicationSkeleton(
                "REGION.target", targetRoot, "EXCEPTION_CONTEXT",
                communicationPort(portId, "IN", "SERVER"));
        File skeleton = writeRows("nested-receiver-skeleton.jsonl",
                producerSkeleton, envelopeSkeleton, targetSkeleton);
        Map<String, Object> fatal = object("schemaVersion", 3,
                "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.nested.failure", "kind", "exception_guard",
                "transferKind", "GUARD", "method", targetRoot,
                "regionIds", Collections.singletonList("REGION.target"),
                "fromCell", targetRoot + "::$keyId",
                "toCell", targetRoot + "#u9#exception:example.Failure",
                "siteId", targetRoot + "#u9", "unitIndex", 9);
        File refined = writeRows("nested-receiver-refined.jsonl", fatal);

        Map<String, Object> producer = activation("ACT.producer",
                "REGION.producer", 10L, producerRoot, "STATE_CONTEXT");
        Map<String, Object> envelope = activation("ACT.envelope",
                "REGION.envelope", 20L, envelopeRoot,
                "COMMUNICATION_CONTEXT");
        Map<String, Object> target = activation("ACT.target",
                "REGION.target", 30L, targetRoot, "EXCEPTION_CONTEXT");
        target.put("enclosingActivationIds",
                Collections.singletonList("ACT.envelope"));
        target.put("observedFatalTargets", Collections.singletonList(
                observedFatalTarget(targetRoot + "#u9", targetRoot,
                        50L, 30L, false)));
        Map<String, Object> link = object("schemaVersion", 3,
                "kind", "RUNTIME_OCCURRENCE_LINK",
                "linkKind", "SERVER_ENTRY",
                "fromActivationId", "ACT.producer",
                "toActivationId", "ACT.envelope",
                "exchangeLeg", "exchange-1\nattempt-2\nREQUEST",
                "attemptId", "attempt-2", "direction", "REQUEST",
                "transport", "EXAMPLE",
                "authority", "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1");

        RuntimeSelectedRegionFinalizer.Result result =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        Collections.singletonList(fatal), refined, skeleton,
                        Arrays.asList(producerRoot, envelopeRoot, targetRoot),
                        Arrays.asList(producer, envelope, target),
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(link));

        assertEquals(2, result.regions.size());
        assertFalse(String.valueOf(result.regions), result.regions.stream()
                .anyMatch(row -> "REGION.envelope".equals(
                        row.get("regionId"))));
        List<Map<String, Object>> protocol = new ArrayList<>();
        for (Map<String, Object> edge : result.regionEdges) {
            if ("RUNTIME_PROTOCOL_FLOW".equals(edge.get("kind"))) {
                protocol.add(edge);
            }
        }
        assertEquals(String.valueOf(protocol), 1, protocol.size());
        assertEquals("REGION.producer", protocol.get(0).get("fromRegion"));
        assertEquals("REGION.target", protocol.get(0).get("toRegion"));
        assertEquals("attempt-2", protocol.get(0).get("attemptId"));
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
        Map<String, Object> link = object("schemaVersion", 3,
                "kind", "RUNTIME_OCCURRENCE_LINK",
                "linkKind", "SERVER_ENTRY",
                "fromActivationId", "ACT.producer",
                "toActivationId", "ACT.target",
                "exchangeLeg", "exchange-1\nattempt-1\nREQUEST",
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

    private static Map<String, Object> cutPort(String portId, String side,
                                               String javaType) {
        return object("portId", portId,
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, side,
                "sourceKind",
                RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT,
                "dependencyRole", DependencyRole.VALUE_FRONTIER,
                "javaType", javaType);
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        return value instanceof List
                ? (List<Map<String, Object>>) value
                : Collections.<Map<String, Object>>emptyList();
    }

    private static List<String> portIds(Map<String, Object> region,
                                        String member) {
        List<String> ids = new ArrayList<>();
        for (Map<String, Object> port : rows(region.get(member))) {
            ids.add(String.valueOf(port.get("portId")));
        }
        return ids;
    }

    private static Map<String, Object> threadEntrySkeleton(String root) {
        return object("schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.worker", "rootMethod", root,
                "rootAuthority", "THREAD_ENTRY", "anchorMethod", root,
                "methods", Collections.singletonList(root),
                "selection", "EXCEPTION_CONTEXT");
    }

    /** One activation of a shared thread-entry region, with no evidence. */
    private static Map<String, Object> exceptionContextActivation(
            String region, long rootCallId, String root) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", region, "rootCallId", rootCallId,
                "selection", "EXCEPTION_CONTEXT", "laneId", rootCallId,
                "callIds", Collections.singletonList(rootCallId),
                "observedMethods", Collections.singletonList(root));
    }

    private static Map<String, Object> sharedFieldWrite(
            String root, String field, List<Map<String, Object>> bindings) {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.shared.write", "kind", "field_write",
                "transferKind", "HEAP_WRITE", "method", root,
                "siteId", root + "#u5", "unitIndex", 5,
                "fromCell", root + "::i0", "toCell", field,
                "regionIds", Collections.singletonList("REGION.worker"),
                "runtimeFieldBindings", bindings);
    }

    private static Map<String, Object> sharedFieldRead(
            String root, String field, String local,
            Map<String, Object> binding) {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.shared.read", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", root,
                "siteId", root + "#u8", "unitIndex", 8,
                "fromCell", field, "toCell", local,
                "regionIds", Collections.singletonList("REGION.worker"),
                "runtimeFieldBindings", Collections.singletonList(binding));
    }

    private static Map<String, Object> fatalGuard(String root, String local) {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.failure", "kind", "exception_guard",
                "transferKind", "GUARD", "method", root,
                "regionIds", Collections.singletonList("REGION.worker"),
                "fromCell", local,
                "toCell", root + "#u9#exception:example.Failure",
                "siteId", root + "#u9", "unitIndex", 9);
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
            String portId, String occurrenceId, int receiver, long seq) {
        return leafPort(portId, occurrenceId, "p", receiver, seq);
    }

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
