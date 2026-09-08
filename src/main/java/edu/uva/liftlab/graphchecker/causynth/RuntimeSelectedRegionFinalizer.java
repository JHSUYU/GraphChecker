package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceMinter;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Predicate;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.booleanValue;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.readRows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.strings;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/** Builds executable region state exclusively from a runtime-refined graph. */
public final class RuntimeSelectedRegionFinalizer {
    private static final String REFINED_KIND = "RUNTIME_REFINED_DATAFLOW";

    /** A boolean returned by the explicit application-side fault marker. */
    public static final String EXPLICIT_SYMBOLIC_FAULT =
            "EXPLICIT_SYMBOLIC_FAULT";
    /** An unanalyzed primitive call return that reaches an explored branch. */
    public static final String EXTERNAL_CALL_RETURN =
            "EXTERNAL_CALL_RETURN";
    /**
     * Skeleton field naming the methods reached from the anchors that admitted
     * the region.
     */
    public static final String DEMAND_SCOPE = "demandScopeMethods";

    /** Existing planner admission vocabulary for a bounded state writer. */
    private static final String ADMISSION_BASIS = "admissionBasis";
    private static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    private static final String DEMANDED_BY_REGIONS = "demandedByRegionIds";
    private static final String DEMANDED_SHARED_LOCATIONS =
            "demandedSharedLocations";

    /**
     * Skeleton field carrying the communication ports of every cut whose
     * client or server side this region holds. README section 3's composition
     * is a chain of equalities between one region's port and another's, so the
     * composer can only state one over ports a region catalog declares.
     */
    public static final String COMMUNICATION_PORTS = "communicationPorts";

    /** {@code IN} or {@code OUT}: which catalog a declared port belongs in. */
    public static final String REGION_PORT_SIDE = "regionPortSide";
    /** {@code sourceKind} of a port that carries a value across a call. */
    public static final String COMMUNICATION_SITE_PORT =
            "COMMUNICATION_SITE_PORT";
    /** Exact IN/OUT cut captures observed inside one runtime activation. */
    public static final String OBSERVED_COMMUNICATION_CAPTURES =
            "observedCommunicationCaptures";
    /** Which side of one communication site a declared port belongs to. */
    public static final String PORT_ROLE = "portRole";
    /** The frame that issues the call. */
    public static final String PORT_ROLE_CLIENT = "CLIENT";
    /** The remote handler, which is its own region occurrence. */
    public static final String PORT_ROLE_SERVER = "SERVER";
    /** Region-row member carrying the retained loops of its methods. */
    public static final String RETAINED_LOOPS = "retainedLoops";
    /** Schema every region skeleton row and its refined row are stated in. */
    public static final int REGION_SCHEMA_VERSION = 3;
    /** {@code kind} of one planned region skeleton row. */
    public static final String SKELETON_KIND = "REGION_SKELETON";

    private RuntimeSelectedRegionFinalizer() {
    }

    /**
     * Finalizes the selected runtime graph using the occurrence links already
     * produced by the runtime planner.  Those links are scheduling evidence;
     * symbolic values still cross only through VM VALUE_HANDOFF edges.
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph, File refinedGraph,
            File selectedSkeletons, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeObservations,
            Collection<Map<String, Object>> runtimeOccurrenceLinks)
            throws IOException {
        requireRefinedGraph(graph, refinedGraph);
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }

        StaticProgram program = new StaticProgram();
        program.refinedGraph = graph;
        // One decode of the selected skeletons: consumers below take the
        // typed row, nobody re-reads the map behind it.
        Map<String, StaticProgram.RegionRow> skeletonRows =
                new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : StaticProgram.regionRows(
                readRows(selectedSkeletons), SKELETON_KIND,
                selectedSkeletons)) {
            skeletonRows.put(skeleton.regionId, skeleton);
            program.skeletons.put(skeleton.regionId, skeleton.json);
        }

        // Activation identity is minted before the first port of a region is
        // built.
        Map<String, List<Map<String, Object>>> targetPoliciesByRegion =
                new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : program.skeletons.entrySet()) {
            if (!selectedRegion(entry.getValue(), observed)) continue;
            targetPoliciesByRegion.put(entry.getKey(), failureTargetPolicies(
                    program.regionGraph(entry.getKey())));
        }
        List<Map<String, Object>> branchOrder = orderedBranchObservations(
                runtimeObservations);
        mintOccurrences(program, targetPoliciesByRegion, runtimeInstances,
                branchOrder, selectedSkeletons);
        Map<String, String> occurrenceByRecordedRootCall =
                recordedRootCallIndex(program.activations);

        for (Map.Entry<String, Map<String, Object>> entry
                : program.skeletons.entrySet()) {
            String regionId = entry.getKey();
            Map<String, Object> skeleton = entry.getValue();
            List<String> methods = strings(skeleton.get("methods"));
            if (!selectedRegion(skeleton, observed)) {
                continue;
            }
            Map<String, Object> region = new LinkedHashMap<>();
            region.put("schemaVersion", 3);
            region.put("kind", "SYMBOLIC_REGION");
            region.put("graphKind", REFINED_KIND);
            region.put("regionId", regionId);
            region.put("rootMethod", skeleton.get("rootMethod"));
            // The once-only-root rule: a service loop's iteration, not the
            // one entry above it, is the activation this region describes.
            Map<String, Object> rootLoop = program.loopBodyRoot(skeleton,
                    program.regionActivations(regionId), branchOrder);
            if (rootLoop != null) {
                region.put("rootAuthority", LoopBoundPolicy.LOOP_BODY_ROOT);
                region.put(LoopBoundPolicy.ROOT_LOOP, rootLoop);
            }
            region.put("anchorMethod", skeleton.get("anchorMethod"));
            if (skeleton.containsKey("anchorMethods")) {
                region.put("anchorMethods", skeleton.get("anchorMethods"));
            }
            region.put("selection", skeleton.get("selection"));
            region.put("methods", methods);
            // The refined row is built fresh, so anything the skeleton carries
            // has to be carried over by name.
            if (skeleton.get(RETAINED_LOOPS) != null) {
                region.put(RETAINED_LOOPS, skeleton.get(RETAINED_LOOPS));
            }
            if (skeleton.get(StaticSymbolicSourceDeclaration.FIELD) != null) {
                region.put(StaticSymbolicSourceDeclaration.FIELD,
                        skeleton.get(StaticSymbolicSourceDeclaration.FIELD));
            }
            if (skeleton.get(
                    ConfiguredSourcePhaseContract.DECLARATION_FIELD) != null) {
                region.put(ConfiguredSourcePhaseContract.DECLARATION_FIELD,
                        skeleton.get(ConfiguredSourcePhaseContract
                                .DECLARATION_FIELD));
            }

            List<Map<String, Object>> regionGraph =
                    program.regionGraph(regionId);
            List<Map<String, Object>> outputs = statePorts(program,
                    regionId, "HEAP_WRITE", "OUT",
                    occurrenceByRecordedRootCall);
            outputs.removeIf(RuntimeSelectedRegionFinalizer
                    ::toolBookkeepingPort);
            List<Map<String, Object>> branchPolicies = branches(program,
                    regionId, demandScope(skeletonRows.get(regionId),
                            outputs));
            List<Map<String, Object>> inputs = statePorts(program,
                    regionId, "HEAP_READ", "IN",
                    occurrenceByRecordedRootCall);
            inputs.addAll(accessorPorts(program, regionId,
                    occurrenceByRecordedRootCall));
            inputs.addAll(externalCallReturnPorts(program, regionId,
                    branchPolicies, runtimeObservations));
            inputs.removeIf(RuntimeSelectedRegionFinalizer
                    ::toolBookkeepingPort);
            inputs.addAll(explicitFaultPorts(regionId, regionGraph,
                    occurrenceByRecordedRootCall));
            markLoopControlOnlyInputs(inputs, regionGraph, branchPolicies);
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
            region.put("branchPolicies", branchPolicies);
            program.regions.add(region);
        }
        bindObservedFatalTargets(program.regions, runtimeInstances,
                branchOrder);
        Set<String> demandedFields = failureRelevantFields(program);
        List<Map<String, Object>> runtimeFieldFlows = fieldFlows(
                program.regions, demandedFields);
        program.regionEdges.addAll(runtimeFieldFlows);
        stampEdgeOccurrences(program.regionEdges,
                occurrenceByRecordedRootCall);
        program.regionEdges.addAll(demandedLeafProducerFlows(
                program.regions, program.regionEdges));
        stampEdgeOccurrences(program.regionEdges,
                occurrenceByRecordedRootCall);
        annotateFlowContexts(program.regionEdges, program.activations);
        markBoundedMutationStateFrontiers(program);
        // The declarations are static and the occurrence-owned copies below
        // are dynamic, so this remains a typed-port join rather than a value
        // or payload guess.  applyClosure removes every declaration and edge
        // not reached by the target-directed walk; the declaration pass after
        // it restores only the region-level catalog rows used downstream.
        declareCommunicationPorts(program, skeletonRows);
        markUnclosedReferenceLeavesConcrete(program.regions,
                program.regionEdges, graph, occurrenceByRecordedRootCall);
        program.regionEdges.addAll(recordedOccurrenceProducerFlows(
                program, runtimeOccurrenceLinks));
        // One index over the region catalog: the occurrence-owned ports are
        // stamped above, so the frontier pass and the closure walk read the
        // same declaration table.
        RegionDemandIndex demands = new RegionDemandIndex(program.regions,
                program.refinedGraph);
        applyClosure(program, failureDirectedClosure(program, demands,
                selectedSkeletons));
        // A Map becomes symbolic only when the retained target slice contains
        // its exact declared mutation-to-read flow.
        markBoundedContainerStatePorts(program);
        // Declared last, and deliberately after the closure filter.
        declareCommunicationPorts(program, skeletonRows);
        canonicalizeRegionEdges(program);
        return new Result(program.regions, program.regionEdges);
    }

    /** The edge id is the canonical semantic identity. */
    static void canonicalizeRegionEdges(StaticProgram program)
            throws IOException {
        Map<String, Map<String, Object>> byId = new LinkedHashMap<>();
        for (Map<String, Object> edge : program.regionEdges) {
            String edgeId = edge.get("edgeId") == null ? ""
                    : String.valueOf(edge.get("edgeId"));
            if (edgeId.isEmpty()) {
                throw new IOException("runtime region edge has no edgeId");
            }
            Map<String, Object> previous = byId.putIfAbsent(edgeId, edge);
            if (previous != null && !previous.equals(edge)) {
                throw new IOException("conflicting runtime region edge "
                        + "payload for edgeId " + edgeId);
            }
        }
        List<Map<String, Object>> canonical = new ArrayList<>(byId.values());
        program.regionEdges.clear();
        program.regionEdges.addAll(canonical);
    }

    /** Publishes the ports of every cut this region holds a side of. */
    private static void declareCommunicationPorts(StaticProgram program,
            Map<String, StaticProgram.RegionRow> skeletons) {
        for (Map<String, Object> region : program.regions) {
            StaticProgram.RegionRow skeleton = skeletons.get(
                    text(region.get("regionId")));
            List<Map<String, Object>> declared = skeleton == null
                    ? Collections.<Map<String, Object>>emptyList()
                    : skeleton.communicationPorts;
            if (declared.isEmpty()) {
                continue;
            }
            List<Map<String, Object>> inputs = rows(
                    region.get("symbolicInputs"));
            List<Map<String, Object>> outputs = rows(region.get("outputs"));
            // A cut has one region-level declaration and zero or more
            // occurrence-owned instances of that declaration.
            Set<String> inputIds = declaredPortIds(inputs);
            Set<String> outputIds = declaredPortIds(outputs);
            for (Map<String, Object> port : declared) {
                String portId = text(port.get("portId"));
                String side = text(port.get(REGION_PORT_SIDE));
                if (portId.isEmpty()) {
                    continue;
                }
                Map<String, Object> row = new LinkedHashMap<>(port);
                row.remove(REGION_PORT_SIDE);
                Set<String> cells = callReturnValueCells(
                        program.regionGraph(text(region.get("regionId"))),
                        row);
                if (cells.size() == 1) {
                    row.put("dependencyCells", new ArrayList<>(cells));
                }
                if ("IN".equals(side)) {
                    if (inputIds.add(portId)) inputs.add(row);
                } else if ("OUT".equals(side)) {
                    if (outputIds.add(portId)) outputs.add(row);
                }
            }
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
        }
    }

    /** The value cell one declared cut port's capture names, or {@code ""}. */
    private static String declaredCutPortCell(Map<String, Object> port) {
        String capture = text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = text(port.get("javaType"));
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return definitionMethod.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : definitionMethod + ".param" + argumentIndex + ":"
                    + javaType;
        }
        if (CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                capture)) {
            return definitionMethod.isEmpty() ? ""
                    : definitionMethod + ".return";
        }
        String callee = text(port.get(
                CommunicationCatalogContract.DECLARED_CALLEE));
        if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)) {
            return callee.isEmpty() ? "" : callee + ".return";
        }
        if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                capture)) {
            // The cut argument is the one client output never written to the
            // heap, so the only cell that names it is the callee parameter the
            // value is bound into at the cut unit.
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return callee.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : callee + ".param" + argumentIndex + ":" + javaType;
        }
        return "";
    }

    /**
     * Names every recorded exchange whose producing occurrence this stage can
     * no longer offer the failure closure as a typed producer edge.
     */
    private static List<Map<String, Object>> recordedOccurrenceProducerFlows(
            StaticProgram program,
            Collection<Map<String, Object>> occurrenceLinks) {
        Map<String, Map<String, Object>> activationsById =
                program.activationsByActivationId();
        Map<String, Map<String, Object>> regionsById = program.regionsById();
        Map<String, Map<Long, Integer>> captureOrdinals =
                communicationCaptureOrdinals(activationsById.values());
        List<Map<String, Object>> flows = new ArrayList<>();
        Set<String> emitted = new LinkedHashSet<>();
        for (Map<String, Object> link : occurrenceLinks == null
                ? Collections.<Map<String, Object>>emptyList()
                : occurrenceLinks) {
            if (!"RECORDED_EXCHANGE_OCCURRENCE_LINK_V1".equals(
                    text(link.get("authority")))) {
                continue;
            }
            Map<String, Object> from = activationsById.get(
                    text(link.get("fromActivationId")));
            Map<String, Object> to = activationsById.get(
                    text(link.get("toActivationId")));
            if (from == null || to == null) {
                continue;
            }
            Map<String, Object> fromRegion = regionsById.get(
                    text(from.get("regionId")));
            if (fromRegion == null) {
                continue;
            }
            String direction = text(link.get("direction")).toUpperCase();
            List<TypedReceiver> receivers = typedReceivers(to, direction,
                    fromRegion, activationsById, regionsById);
            Map<String, Set<String>> receivingActivationsByPort =
                    new LinkedHashMap<>();
            for (TypedReceiver receiver : receivers) {
                String portId = text(receiver.port.get("portId"));
                receivingActivationsByPort.computeIfAbsent(portId,
                        ignored -> new LinkedHashSet<>()).add(text(
                        receiver.activation.get("activationId")));
            }
            for (TypedReceiver receiver : receivers) {
                Map<String, Object> exactTo = receiver.activation;
                Map<String, Object> toRegion = receiver.region;
                Map<String, Object> receiving = receiver.port;
                String portId = text(receiving.get("portId"));
                if (receivingActivationsByPort.getOrDefault(portId,
                        Collections.<String>emptySet()).size() > 1) {
                    continue;
                }
                Map<String, Object> sending = declaredOutputPort(fromRegion,
                        portId);
                String exchangeLeg = text(link.get("exchangeLeg"));
                long senderEventSeq = longNumber(
                        link.get("senderEventSeq"), -1L);
                long receiverEventSeq = longNumber(
                        link.get("receiverEventSeq"), -1L);
                Set<Integer> sent = observedCommunicationCaptureOrdinals(
                        from, "OUT", portId, exchangeLeg, senderEventSeq,
                        captureOrdinals);
                Set<Integer> received = observedCommunicationCaptureOrdinals(
                        exactTo, "IN", portId, exchangeLeg,
                        receiverEventSeq, captureOrdinals);
                if (Collections.disjoint(sent, received)) {
                    continue;
                }
                String identity = text(from.get("occurrenceId")) + "\n"
                        + text(exactTo.get("occurrenceId")) + "\n" + portId
                        + "\n" + text(link.get("requestKey")) + "\n"
                        + exchangeLeg;
                if (!emitted.add(identity)) continue;
                stampOccurrenceOwnedPort(fromRegion, "outputs", sending,
                        text(from.get("occurrenceId")),
                        longNumber(link.get("senderEventSeq"), -1L));
                stampOccurrenceOwnedPort(toRegion, "symbolicInputs",
                        receiving, text(exactTo.get("occurrenceId")),
                        longNumber(link.get("receiverEventSeq"), -1L));
                flows.add(exchangeProducerEdge(from, exactTo, link,
                        receiving));
            }
        }
        return flows;
    }

    private static Map<String, Map<Long, Integer>>
    communicationCaptureOrdinals(
            Collection<Map<String, Object>> activations) {
        Map<String, Set<Long>> events = new LinkedHashMap<>();
        for (Map<String, Object> activation : activations) {
            for (Map<String, Object> capture : rows(activation.get(
                    OBSERVED_COMMUNICATION_CAPTURES))) {
                String key = captureOrdinalKey(capture);
                long event = longNumber(capture.get("eventSeq"), -1L);
                if (!key.isEmpty() && event >= 0L) {
                    events.computeIfAbsent(key,
                            ignored -> new TreeSet<>()).add(event);
                }
            }
        }
        Map<String, Map<Long, Integer>> result = new LinkedHashMap<>();
        for (Map.Entry<String, Set<Long>> entry : events.entrySet()) {
            Map<Long, Integer> ordinals = new LinkedHashMap<>();
            int ordinal = 0;
            for (Long event : entry.getValue()) ordinals.put(event, ordinal++);
            result.put(entry.getKey(), ordinals);
        }
        return result;
    }

    private static String captureOrdinalKey(Map<String, Object> capture) {
        String side = text(capture.get("side"));
        String port = text(capture.get("portId"));
        String exchange = text(capture.get("exchangeLeg"));
        return side.isEmpty() || port.isEmpty() || exchange.isEmpty() ? ""
                : side + '\n' + port + '\n' + exchange;
    }

    private static Set<Integer> observedCommunicationCaptureOrdinals(
            Map<String, Object> activation, String side, String portId,
            String exchangeLeg, long transportEventSeq,
            Map<String, Map<Long, Integer>> captureOrdinals) {
        Set<Integer> result = new LinkedHashSet<>();
        if (exchangeLeg.isEmpty() || transportEventSeq < 0L) return result;
        for (Map<String, Object> capture : rows(activation.get(
                OBSERVED_COMMUNICATION_CAPTURES))) {
            long capturedAt = longNumber(capture.get("eventSeq"), -1L);
            if (side.equals(text(capture.get("side")))
                    && portId.equals(text(capture.get("portId")))
                    && exchangeLeg.equals(text(capture.get("exchangeLeg")))
                    && transportEventSeq == longNumber(
                    capture.get("transportEventSeq"), -1L)
                    && ("OUT".equals(side)
                    ? capturedAt >= 0L && capturedAt < transportEventSeq
                    : capturedAt > transportEventSeq)) {
                Integer ordinal = captureOrdinals.getOrDefault(
                        captureOrdinalKey(capture),
                        Collections.<Long, Integer>emptyMap()).get(capturedAt);
                if (ordinal != null) result.add(ordinal);
            }
        }
        return result;
    }

    /**
     * Resolves a recorded receiver envelope to typed receiving occurrences.
     * A nested occurrence is eligible only through exact dynamic call
     * containment plus a shared declared port.  This is scheduling topology;
     * the VM handoff remains the only value authority.
     */
    private static List<TypedReceiver> typedReceivers(
            Map<String, Object> recordedReceiver, String direction,
            Map<String, Object> fromRegion,
            Map<String, Map<String, Object>> activationsById,
            Map<String, Map<String, Object>> regionsById) {
        List<TypedReceiver> result = new ArrayList<>();
        String envelopeId = text(recordedReceiver.get("activationId"));
        for (Map<String, Object> candidate : activationsById.values()) {
            if (!envelopeId.equals(text(candidate.get("activationId")))
                    && !strings(candidate.get("enclosingActivationIds"))
                    .contains(envelopeId)) {
                continue;
            }
            Map<String, Object> region = regionsById.get(
                    text(candidate.get("regionId")));
            if (region == null) continue;
            for (Map<String, Object> receiving
                    : rows(region.get("symbolicInputs"))) {
                if (!COMMUNICATION_SITE_PORT.equals(
                        text(receiving.get("sourceKind")))
                        || !direction.equals(text(receiving.get(
                        CommunicationCatalogContract.PORT_DIRECTION)))) {
                    continue;
                }
                Map<String, Object> sending = declaredOutputPort(fromRegion,
                        text(receiving.get("portId")));
                if (sending != null && direction.equals(text(sending.get(
                        CommunicationCatalogContract.PORT_DIRECTION)))) {
                    result.add(new TypedReceiver(candidate, region,
                            receiving));
                }
            }
        }
        return result;
    }

    private static final class TypedReceiver {
        private final Map<String, Object> activation;
        private final Map<String, Object> region;
        private final Map<String, Object> port;

        private TypedReceiver(Map<String, Object> activation,
                              Map<String, Object> region,
                              Map<String, Object> port) {
            this.activation = activation;
            this.region = region;
            this.port = port;
        }
    }

    /**
     * Adds the occurrence-owned instance of one declared cut port, so demand
     * propagation can reach the exact activation that used it.
     */
    private static void stampOccurrenceOwnedPort(
            Map<String, Object> region, String listName,
            Map<String, Object> port, String occurrenceId, long eventSeq) {
        List<Map<String, Object>> rows = rows(region.get(listName));
        String portId = text(port.get("portId"));
        if (portId.isEmpty() || occurrenceId.isEmpty()) {
            return;
        }
        for (Map<String, Object> existing : rows) {
            if (portId.equals(text(existing.get("portId")))
                    && occurrenceId.equals(
                    text(existing.get("occurrenceId")))) {
                long previous = longNumber(existing.get("eventSeq"), -1L);
                if (eventSeq >= 0L && (previous < 0L || eventSeq < previous)) {
                    existing.put("eventSeq", eventSeq);
                }
                return;
            }
        }
        Map<String, Object> owned = new LinkedHashMap<>(port);
        owned.put("occurrenceId", occurrenceId);
        if (eventSeq >= 0L) owned.put("eventSeq", eventSeq);
        rows.add(owned);
        region.put(listName, rows);
    }

    /** The exporting region's own declaration of one declared cut port. */
    private static Map<String, Object> declaredOutputPort(
            Map<String, Object> region, String portId) {
        if (portId.isEmpty()) return null;
        for (Map<String, Object> port : rows(region.get("outputs"))) {
            if (COMMUNICATION_SITE_PORT.equals(text(port.get("sourceKind")))
                    && portId.equals(text(port.get("portId")))) {
                return port;
            }
        }
        return null;
    }

    /** One scheduling candidate for a recorded delivery of a declared port. */
    private static Map<String, Object> exchangeProducerEdge(
            Map<String, Object> from, Map<String, Object> to,
            Map<String, Object> link, Map<String, Object> receiving) {
        String portId = text(receiving.get("portId"));
        String identity = text(from.get("occurrenceId")) + "\n"
                + text(to.get("occurrenceId")) + "\n" + portId + "\n"
                + text(link.get("requestKey")) + "\n"
                + text(link.get("exchangeLeg"));
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.put("transportKind", text(link.get("transport")));
        edge.put("edgeId", CausynthStaticFacts.nameId("RPC.", identity));
        edge.put("fromRegion", text(from.get("regionId")));
        edge.put("toRegion", text(to.get("regionId")));
        edge.put("fromPort", portId);
        edge.put("toPort", portId);
        edge.put("fromOccurrenceId", text(from.get("occurrenceId")));
        edge.put("toOccurrenceId", text(to.get("occurrenceId")));
        edge.put("fromRootCallId", from.get("rootCallId"));
        edge.put("toRootCallId", to.get("rootCallId"));
        edge.put("direction", text(link.get("direction")).toUpperCase());
        edge.put("exchangeLeg", text(link.get("exchangeLeg")));
        edge.put("attemptId", text(link.get("attemptId")));
        edge.put("senderEventSeq", link.get("senderEventSeq"));
        edge.put("receiverEventSeq", link.get("receiverEventSeq"));
        edge.put("requestApi", text(link.get("requestApi")));
        edge.put("requestKey", text(link.get("requestKey")));
        for (String field : new String[]{
                CommunicationCatalogContract.CALL_SITE_ID,
                CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH}) {
            Object value = receiving.get(field);
            if (value != null && !text(value).isEmpty()) {
                edge.put(field, value);
            }
        }
        edge.put("dependencyRole", DependencyRole.normalize(
                receiving.get("dependencyRole")));
        edge.put("javaType", text(receiving.get("javaType")));
        edge.put("correlationAuthority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        edge.put("authority", AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        return edge;
    }

    /** Region-level port declarations, excluding occurrence-owned copies. */
    private static Set<String> declaredPortIds(
            List<Map<String, Object>> ports) {
        Set<String> ids = new LinkedHashSet<>();
        for (Map<String, Object> port : ports) {
            if (!text(port.get("occurrenceId")).isEmpty()) continue;
            String id = text(port.get("portId"));
            if (!id.isEmpty()) ids.add(id);
        }
        return ids;
    }

    /**
     * Mints one {@code occurrenceId} per observed region activation and stamps
     * it onto every row the recorded root call named.
     */
    private static void mintOccurrences(
            StaticProgram program,
            Map<String, List<Map<String, Object>>> targetPoliciesByRegion,
            Collection<Map<String, Object>> runtimeInstances,
            List<Map<String, Object>> observations,
            File source) throws IOException {
        OccurrenceMinter minter = new OccurrenceMinter();
        for (Map<String, Object> instance : canonicalRuntimeActivations(
                runtimeInstances, source)) {
            String regionId = text(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            String rootSourceKey = activationSourceKey(instance);
            String semanticSourceKey = semanticSourceKey(
                    targetPoliciesByRegion.get(regionId), instance,
                    observations, rootSourceKey);
            int ordinal = minter.reserveOrdinal(semanticSourceKey, regionId);
            String occurrenceId;
            try {
                occurrenceId = minter.mint(regionId, rootCallId,
                        semanticSourceKey,
                        ordinal);
            } catch (IllegalArgumentException duplicate) {
                throw new IOException("duplicate runtime region activation: "
                        + regionId + "\n" + rootCallId);
            }
            instance.put("occurrenceId", occurrenceId);
            program.activations.put(occurrenceId, instance);
        }
    }

    /** Canonical activation records at the trace-aggregation boundary. */
    private static List<Map<String, Object>> canonicalRuntimeActivations(
            Collection<Map<String, Object>> runtimeInstances, File source)
            throws IOException {
        Map<String, Map<String, Object>> byRecordedActivation =
                new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeInstances) {
            if (!"RUNTIME_REGION_ACTIVATION".equals(
                    text(instance.get("kind")))) {
                throw new IOException("invalid runtime region activation: "
                        + source);
            }
            String regionId = text(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            if (regionId.isEmpty() || rootCallId < 0L) {
                throw new IOException("runtime region activation requires "
                        + "regionId and rootCallId: " + source);
            }
            String identity = recordedRootCallKey(regionId, rootCallId);
            Map<String, Object> previous = byRecordedActivation.putIfAbsent(
                    identity, instance);
            if (previous != null && !previous.equals(instance)) {
                throw new IOException("conflicting runtime region activation "
                        + "payload: " + regionId + "\n" + rootCallId);
            }
        }
        return new ArrayList<>(byRecordedActivation.values());
    }

    /** True when this skeleton's methods were observed in the trace. */
    private static boolean selectedRegion(Map<String, Object> skeleton,
                                          Set<String> observed) {
        List<String> methods = strings(skeleton.get("methods"));
        return !methods.isEmpty()
                && (observed.isEmpty()
                || !Collections.disjoint(methods, observed));
    }

    /**
     * The failure-target guard sites of one region, in the order {@link
     * #branches} would publish them.
     */
    public static final String FAILURE_TARGET_CELLS = "failureTargetCells";

    private static List<Map<String, Object>> failureTargetPolicies(
            List<Map<String, Object>> regionGraph) {
        Map<String, List<Map<String, Object>>> failureGuardsBySite =
                guardsBySite(regionGraph, RuntimeSelectedRegionFinalizer
                        ::isExceptionTargetEdge);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : failureGuardsBySite.entrySet()) {
            if (entry.getValue().isEmpty()) continue;
            Map<String, Object> policy = new LinkedHashMap<>();
            policy.put("siteId", entry.getKey());
            policy.put("failureTarget", true);
            policy.put("requiredOutcome",
                    consistentRequiredOutcome(entry.getValue()));
            result.add(policy);
        }
        return result;
    }

    /**
     * The stable logical scope current when this activation's root method was
     * entered.
     */
    private static String activationSourceKey(Map<String, Object> instance) {
        String sourceKey = text(instance.get("sourceKey"));
        return sourceKey.isEmpty()
                ? OccurrenceMinter.UNREGISTERED_SOURCE_KEY : sourceKey;
    }

    /** The source that owns the relation of this activation. */
    private static String semanticSourceKey(
            List<Map<String, Object>> targetPolicies,
            Map<String, Object> instance,
            List<Map<String, Object>> observations, String rootSourceKey) {
        if (targetPolicies == null || !text(instance.get("selection"))
                .startsWith("EXCEPTION")) {
            return rootSourceKey;
        }
        Set<Long> calls = StaticProgram.longValues(instance.get("callIds"));
        for (Map<String, Object> branch : targetPolicies) {
            Map<String, Object> selected = selectedBranchObservation(branch,
                    calls, observations);
            if (selected == null) continue;
            String selectedSourceKey = text(selected.get("callSourceKey"));
            if (selectedSourceKey.isEmpty()) continue;
            return selectedSourceKey;
        }
        return rootSourceKey;
    }

    /**
     * The exact branch occurrence a replay of this activation would select:
     * the first observation of the site whose outcome equals the required
     * one, or the first observation when the policy demands no outcome.
     */
    private static Map<String, Object> selectedBranchObservation(
            Map<String, Object> branch, Set<Long> calls,
            List<Map<String, Object>> observations) {
        String site = text(branch.get("siteId"));
        if (site.isEmpty()) return null;
        List<Map<String, Object>> occurrences = new ArrayList<>();
        for (Map<String, Object> observation : observations) {
            if (site.equals(text(observation.get("siteId")))
                    && calls.contains(longNumber(
                    observation.get("callId"), -1L))) {
                occurrences.add(observation);
            }
        }
        if (occurrences.isEmpty()) return null;
        Object required = branch.get("requiredOutcome");
        if (required instanceof Boolean) {
            for (Map<String, Object> occurrence : occurrences) {
                if (required.equals(occurrence.get("outcome"))) {
                    return occurrence;
                }
            }
        }
        return occurrences.get(0);
    }

    /** Exact BRANCH observations in observed order. */
    private static List<Map<String, Object>> orderedBranchObservations(
            Collection<Map<String, Object>> runtimeBranchObservations) {
        List<Map<String, Object>> observations = new ArrayList<>();
        if (runtimeBranchObservations != null) {
            for (Map<String, Object> observation
                    : runtimeBranchObservations) {
                if ("BRANCH".equals(text(observation.get("kind")))) {
                    observations.add(observation);
                }
            }
        }
        sortByEventSeq(observations);
        return observations;
    }

    /**
     * Adds activation-local fatal-target evidence by intersecting exact
     * runtime BRANCH sites with static {@code failureTarget} branch policies.
     */
    private static void bindObservedFatalTargets(
            List<Map<String, Object>> regions,
            Collection<Map<String, Object>> runtimeInstances,
            List<Map<String, Object>> observations) {
        Map<String, Map<String, Map<String, Object>>> targets =
                new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            for (Map<String, Object> branch
                    : rows(region.get("branchPolicies"))) {
                if (!Boolean.TRUE.equals(booleanValue(
                        branch.get("failureTarget")))) {
                    continue;
                }
                String site = text(branch.get("siteId"));
                if (!site.isEmpty()) {
                    targets.computeIfAbsent(regionId,
                            ignored -> new LinkedHashMap<>()).put(site,
                            branch);
                }
            }
        }
        if (targets.isEmpty() || runtimeInstances == null) return;

        for (Map<String, Object> instance : runtimeInstances) {
            String regionId = text(instance.get("regionId"));
            Map<String, Map<String, Object>> regionTargets = targets.get(
                    regionId);
            if (regionTargets == null || regionTargets.isEmpty()) continue;

            Set<Long> calls = StaticProgram.longValues(
                    instance.get("callIds"));
            List<Map<String, Object>> bound = rows(
                    instance.get("observedFatalTargets"));
            for (Map<String, Object> observation : observations) {
                long callId = longNumber(observation.get("callId"), -1L);
                if (!calls.contains(callId)) continue;
                String site = text(observation.get("siteId"));
                Map<String, Object> target = regionTargets.get(site);
                if (target == null
                        || !text(target.get("method")).equals(
                        text(observation.get("method")))
                        || !(observation.get("outcome") instanceof Boolean)) {
                    continue;
                }
                Map<String, Object> evidence = new LinkedHashMap<>();
                evidence.put("schemaVersion", 1);
                evidence.put("kind", "OBSERVED_FATAL_TARGET");
                evidence.put("evidenceAuthority",
                        "EXACT_RUNTIME_BRANCH_SITE_V1");
                evidence.put("siteId", site);
                evidence.put("method", target.get("method"));
                evidence.put("unitIndex", target.get("unitIndex"));
                evidence.put("operandCells", target.get("operandCells"));
                evidence.put("requiredOutcome", target.get(
                        "requiredOutcome"));
                evidence.put("observedOutcome", observation.get("outcome"));
                evidence.put("eventSeq", observation.get("eventSeq"));
                evidence.put("callId", callId);
                bound.add(evidence);
            }
            if (!bound.isEmpty()) {
                sortByEventSeq(bound);
                instance.put("observedFatalTargets", bound);
            }
        }
    }

    private static boolean isExceptionTargetEdge(Map<String, Object> edge) {
        return "exception_guard".equals(text(edge.get("kind")))
                || text(edge.get("toCell")).contains("#exception:");
    }

    /**
     * Retains the concrete producer activations and ports that can reach an
     * observed exception through confirmed heap or protocol flow.
     */
    private static ClosureWalk failureDirectedClosure(
            StaticProgram program, RegionDemandIndex demands, File source)
            throws IOException {
        Map<String, Map<String, Object>> instances = program.activations;
        if (instances.isEmpty()) {
            throw new IOException("runtime failure closure requires concrete "
                    + "region activations: " + source);
        }
        // `selection` describes the static region skeleton, so every
        // activation of an exception-context region inherits it, including the
        // concurrent activations that only produced inputs for the one that
        // failed.
        Set<String> contexts = new LinkedHashSet<>();
        Set<String> targets = new LinkedHashSet<>();
        Set<String> policylessRegions = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : program.activations.entrySet()) {
            if (!text(entry.getValue().get("selection"))
                    .startsWith("EXCEPTION")) {
                continue;
            }
            contexts.add(entry.getKey());
            if (!demands.declaresExplicitFatalTarget(entry.getValue())) {
                policylessRegions.add(text(
                        entry.getValue().get("regionId")));
            } else if (demands.observedExplicitFatalTarget(
                    entry.getValue())) {
                targets.add(entry.getKey());
            }
        }
        if (contexts.isEmpty()) {
            throw new IOException("runtime failure closure found no observed "
                    + "exception-context activation: " + source);
        }
        if (targets.isEmpty() && !policylessRegions.isEmpty()) {
            // README TARGET-1: target existence binds to a selected concrete
            // branch event.
            throw new IOException("FATAL_TARGET_POLICY_ABSENT: "
                    + "exception-context region declares no failure target "
                    + "site to bind the target to: " + policylessRegions
                    + " " + source);
        }
        if (targets.isEmpty()) {
            // A workload that never reached the declared failure site has no
            // failure to explain.
            throw new IOException("FATAL_TARGET_OBSERVATION_GAP: no "
                    + "exception-context activation observed its explicit "
                    + "fatal target branch: " + source);
        }
        // Materialize the exact fatal prefix before request-flow selection;
        // requestFlowPrefixInputs reads its recorded event cutoff directly.
        for (String target : targets) {
            demands.targetInputs(instances.get(target));
        }
        Set<String> admittedStateWriters = new LinkedHashSet<>(
                admitSharedLocationWriters(targets, instances, demands,
                        program.regionEdges));

        Map<String, List<Map<String, Object>>> predecessors =
                new LinkedHashMap<>();
        Set<String> targetInteractionInputs = new LinkedHashSet<>();
        // The declared carriers of the demanded component leaves above. A
        // structured leaf has no capture of its own: the producer's relation
        // for it is anchored on the carrier's own observed delivery, so the
        // carrier is demanded together with the leaf it transported.
        for (Map<String, Object> edge : program.regionEdges) {
            if (!causalRegionRetentionEdge(edge)) {
                continue;
            }
            String from = text(edge.get("fromOccurrenceId"));
            String to = text(edge.get("toOccurrenceId"));
            if (!instances.containsKey(from) || !instances.containsKey(to)) {
                throw new IOException("runtime causal edge references an "
                        + "unselected activation: "
                        + text(edge.get("edgeId")));
            }
            String toPort = text(edge.get("toPort"));
            String fromPort = text(edge.get("fromPort"));
            if (toPort.isEmpty() || fromPort.isEmpty()
                    || !demands.hasInput(to, toPort)
                    || !demands.hasOutput(from, fromPort)) {
                throw new IOException("runtime causal edge references an "
                        + "unknown exact port: " + text(edge.get("edgeId")));
            }
            predecessors.computeIfAbsent(portDemandKey(to, toPort),
                    ignored -> new ArrayList<>()).add(edge);
            if ("RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))
                    && targets.contains(to)) {
                if (DependencyRole.valueFrontier(
                        edge.get("dependencyRole"))) {
                    // The fatal region instance was entered through this
                    // exact observed interaction.
                    targetInteractionInputs.add(portDemandKey(to, toPort));
                }
            }
        }

        Map<String, Long> requestFlowPrefixInputs =
                requestFlowPrefixInputs(targets, instances,
                        program.regionEdges);

        ClosureWalk union = walkFailureClosure(targets, instances,
                demands, predecessors, targetInteractionInputs,
                requestFlowPrefixInputs, admittedStateWriters);
        // Heap demand is transitive with port demand: each walk may reach a
        // producer that itself reads a written location, so admit the writers
        // of what this walk demanded and walk again.
        while (true) {
            Set<String> grown = admitWritersOfDemands(union.reached,
                    union.demandedInputs, instances, program.regionEdges);
            if (!admittedStateWriters.addAll(grown)) break;
            union = walkFailureClosure(targets, instances, demands,
                    predecessors, targetInteractionInputs,
                    requestFlowPrefixInputs, admittedStateWriters);
        }
        return union;
    }

    /**
     * Every observed wire delivery in the bounded prefix of a failed logical
     * request.  The request key, both endpoint activations, and the fatal
     * event are recorded evidence; no transport name or application command
     * participates in the selection.
     */
    private static Map<String, Long> requestFlowPrefixInputs(
            Collection<String> targets,
            Map<String, Map<String, Object>> instances,
            Collection<Map<String, Object>> edges) {
        Map<String, Long> fatalCutoffByRequest = new LinkedHashMap<>();
        for (String target : targets) {
            Map<String, Object> instance = instances.get(target);
            String requestKey = text(instance == null
                    ? null : instance.get("requestKey"));
            long cutoff = fatalPrefixCutoff(instance);
            if (!requestKey.isEmpty() && cutoff >= 0L) {
                fatalCutoffByRequest.merge(requestKey, cutoff, Math::max);
            }
        }

        Map<String, Long> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))
                    || !DependencyRole.valueFrontier(
                    edge.get("dependencyRole"))) {
                continue;
            }
            Map<String, Object> from = instances.get(
                    text(edge.get("fromOccurrenceId")));
            Map<String, Object> to = instances.get(
                    text(edge.get("toOccurrenceId")));
            String fromRequest = text(from == null
                    ? null : from.get("requestKey"));
            String toRequest = text(to == null
                    ? null : to.get("requestKey"));
            String edgeRequest = text(edge.get("requestKey"));
            Long cutoff = fatalCutoffByRequest.get(edgeRequest);
            long sentAt = longNumber(edge.get("senderEventSeq"), -1L);
            long receivedAt = longNumber(edge.get("receiverEventSeq"), -1L);
            if (cutoff == null || edgeRequest.isEmpty()
                    || !edgeRequest.equals(fromRequest)
                    || !edgeRequest.equals(toRequest)
                    || sentAt < 0L || receivedAt <= sentAt
                    || receivedAt >= cutoff.longValue()) {
                continue;
            }
            String input = portDemandKey(
                    text(edge.get("toOccurrenceId")),
                    text(edge.get("toPort")));
            result.merge(input, cutoff, Math::max);
        }
        return result;
    }

    private static long fatalPrefixCutoff(Map<String, Object> instance) {
        long cutoff = -1L;
        if (instance == null) return cutoff;
        for (Map<String, Object> context
                : rows(instance.get("fatalPrefixContexts"))) {
            cutoff = Math.max(cutoff,
                    longNumber(context.get("eventSeq"), -1L));
        }
        return cutoff;
    }

    /**
     * Admits only an observed production writer joined to a fatal input by an
     * exact runtime field-flow edge.
     */
    private static Set<String> admitSharedLocationWriters(
            Set<String> targets,
            Map<String, Map<String, Object>> instances,
            RegionDemandIndex demands,
            List<Map<String, Object>> regionEdges) throws IOException {
        Set<String> fatalInputs = new LinkedHashSet<>();
        for (String target : targets) {
            fatalInputs.addAll(demands.targetInputs(instances.get(target)));
        }
        return admitWritersOfDemands(targets, fatalInputs, instances,
                regionEdges);
    }

    /**
     * Admits the observed writers of the shared locations {@code demanding}
     * occurrences read, joined by exact runtime field-flow edges.
     */
    private static Set<String> admitWritersOfDemands(
            Collection<String> demanding,
            Set<String> demandedInputs,
            Map<String, Map<String, Object>> instances,
            List<Map<String, Object>> regionEdges) throws IOException {
        Set<String> targets = new LinkedHashSet<>(demanding);
        Set<String> fatalInputs = demandedInputs;
        Map<String, Set<String>> locationsByWriter = new LinkedHashMap<>();
        Map<String, Set<String>> targetRegionsByWriter =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : regionEdges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                continue;
            }
            String consumer = text(edge.get("toOccurrenceId"));
            String writer = text(edge.get("fromOccurrenceId"));
            String input = portDemandKey(consumer,
                    text(edge.get("toPort")));
            if (!targets.contains(consumer) || writer.equals(consumer)
                    || !fatalInputs.contains(input)
                    || !instances.containsKey(writer)) {
                continue;
            }
            String location = text(edge.get(RecordedReadFrom.EDGE_FIELD));
            if (location.isEmpty()) {
                continue;
            }
            locationsByWriter.computeIfAbsent(writer,
                    ignored -> new LinkedHashSet<>()).add(location);
            targetRegionsByWriter.computeIfAbsent(writer,
                    ignored -> new TreeSet<>()).add(text(
                    instances.get(consumer).get("regionId")));
        }

        Set<String> admitted = new LinkedHashSet<>();
        for (Map.Entry<String, Set<String>> entry
                : locationsByWriter.entrySet()) {
            String writer = entry.getKey();
            Set<String> consumerRegions = targetRegionsByWriter.getOrDefault(
                    writer, Collections.<String>emptySet());
            if (consumerRegions.isEmpty()) {
                continue;
            }
            Map<String, Object> activation = instances.get(writer);
            String existingBasis = text(activation.get(ADMISSION_BASIS));
            if (!existingBasis.isEmpty()
                    && !SHARED_LOCATION_DEMAND_ADMISSION.equals(
                    existingBasis)) {
                throw new IOException("conflicting runtime activation "
                        + "admission basis for " + writer + ": "
                        + existingBasis);
            }
            Set<String> demandedBy = new TreeSet<>(strings(
                    activation.get(DEMANDED_BY_REGIONS)));
            demandedBy.addAll(consumerRegions);
            Set<String> locations = new LinkedHashSet<>(strings(
                    activation.get(DEMANDED_SHARED_LOCATIONS)));
            locations.addAll(entry.getValue());
            activation.put(ADMISSION_BASIS,
                    SHARED_LOCATION_DEMAND_ADMISSION);
            activation.put(DEMANDED_BY_REGIONS,
                    new ArrayList<>(demandedBy));
            activation.put(DEMANDED_SHARED_LOCATIONS,
                    new ArrayList<>(locations));
            admitted.add(writer);
        }
        return admitted;
    }

    private static ClosureWalk walkFailureClosure(
            Collection<String> targets,
            Map<String, Map<String, Object>> instances,
            RegionDemandIndex demands,
            Map<String, List<Map<String, Object>>> predecessors,
            Collection<String> targetInteractionInputs,
            Map<String, Long> requestFlowPrefixInputs,
            Set<String> admittedStateWriters)
            throws IOException {
        Set<String> reached = new LinkedHashSet<>(targets);
        Set<String> retainedEdges = new LinkedHashSet<>();
        Set<String> demandedInputs = new LinkedHashSet<>();
        Set<String> demandedOutputs = new LinkedHashSet<>();
        Set<String> expandedOutputOccurrences = new LinkedHashSet<>();
        List<String> seeds = new ArrayList<>();
        for (String target : targets) {
            Map<String, Object> instance = instances.get(target);
            // A target input serves the failure itself and no producer
            // write, so it states no order for its predecessors to precede.
            long cutoff = fatalPrefixCutoff(instance);
            addDemands(seeds, demands.targetInputs(instance),
                    cutoff < 0L ? NO_ORDER : cutoff);
        }
        for (String input : targetInteractionInputs) {
            int at = input.indexOf('\n');
            Map<String, Object> instance = at < 0 ? null
                    : instances.get(input.substring(0, at));
            long cutoff = fatalPrefixCutoff(instance);
            addDemand(seeds, input, cutoff < 0L ? NO_ORDER : cutoff);
        }
        for (Map.Entry<String, Long> prefix
                : requestFlowPrefixInputs.entrySet()) {
            addDemand(seeds, prefix.getKey(), prefix.getValue());
        }
        // A selected writer is retained even when nothing demands one of its
        // outputs yet: the bounded NN heartbeat predecessors stay in the
        // closure without any of them becoming a read-from arm before replay
        // records a write/version.
        for (String writer : admittedStateWriters) {
            Map<String, Object> instance = instances.get(writer);
            if (instance == null) continue;
            reached.add(writer);
        }
        // Communication is represented by exact occurrence-owned IN/OUT
        // ports in predecessors, so the walk crosses a call the same way it
        // crosses any other edge: from the demanded input port to the output
        // port some other occurrence declared for it.  One coarse occurrence
        // can receive the same port many times and publish several dynamic
        // versions of one output, so the walk's node is the demand together
        // with the order it was demanded at.
        List<IOException> refused = new ArrayList<>();
        StaticProgram.closure(seeds, demanded -> {
            int at = demanded.indexOf('\n');
            long order = Long.parseLong(demanded.substring(0, at));
            String key = demanded.substring(at + 1);
            demandedInputs.add(key);
            List<String> next = new ArrayList<>();
            for (Map<String, Object> edge : boundedPredecessors(
                    predecessors.getOrDefault(key,
                            Collections.<Map<String, Object>>emptyList()),
                    order)) {
                String edgeId = text(edge.get("edgeId"));
                if (edgeId.isEmpty()) {
                    refused.add(new IOException("runtime causal edge has no "
                            + "identity"));
                    // A null adjacency ends the whole walk.
                    return null;
                }
                retainedEdges.add(edgeId);
                String fromOccurrence = text(edge.get("fromOccurrenceId"));
                reached.add(fromOccurrence);
                reached.add(text(edge.get("toOccurrenceId")));
                String outputDemand = portDemandKey(fromOccurrence,
                        text(edge.get("fromPort")));
                demandedOutputs.add(outputDemand);
                long producedAt = producerEventSeq(edge);
                if (expandedOutputOccurrences.add(outputOccurrenceDemandKey(
                        outputDemand, producedAt))) {
                    addDemands(next, demands.inputsForOutput(fromOccurrence,
                            text(edge.get("fromPort")), producedAt),
                            producedAt);
                    addDemands(next, demands.priorCommunicationInputs(
                            fromOccurrence, producedAt), producedAt);
                    addDemands(next, demands.priorValueInputs(
                            fromOccurrence, producedAt), producedAt);
                }
            }
            return next;
        });
        if (!refused.isEmpty()) throw refused.get(0);
        return new ClosureWalk(reached, retainedEdges, demandedInputs,
                demandedOutputs);
    }

    /** A demand that states no order: nothing is known to follow it. */
    private static final long NO_ORDER = -1L;

    /** One demanded input port, tagged with the order its producers precede. */
    private static void addDemands(Collection<String> work,
                                   Collection<String> keys, long order) {
        for (String key : keys) addDemand(work, key, order);
    }

    private static void addDemand(Collection<String> work,
                                  String key, long order) {
        work.add(order + "\n" + key);
    }

    /**
     * Materializes only the bounded selection of repeated writer occurrences.
     */
    private static List<Map<String, Object>> boundedPredecessors(
            Collection<Map<String, Object>> candidates, long demandedOrder) {
        List<Map<String, Object>> eligible = new ArrayList<>();
        for (Map<String, Object> edge : candidates) {
            if (demandedOrder >= 0L) {
                String kind = text(edge.get("kind"));
                long producedAt = "RUNTIME_FIELD_FLOW".equals(kind)
                        ? producerEventSeq(edge)
                        : "RUNTIME_PROTOCOL_FLOW".equals(kind)
                        ? longNumber(edge.get("senderEventSeq"), -1L)
                        : -1L;
                long consumedAt = "RUNTIME_FIELD_FLOW".equals(kind)
                        ? longNumber(edge.get("readerEventSeq"), -1L)
                        : "RUNTIME_PROTOCOL_FLOW".equals(kind)
                        ? longNumber(edge.get("receiverEventSeq"), -1L)
                        : -1L;
                if (("RUNTIME_FIELD_FLOW".equals(kind)
                        || "RUNTIME_PROTOCOL_FLOW".equals(kind))
                        && (producedAt < 0L || consumedAt < 0L
                        || producedAt >= consumedAt
                        || consumedAt >= demandedOrder)) {
                    continue;
                }
            }
            eligible.add(edge);
        }
        if (eligible.size()
                <= LoopBoundPolicy.MAX_STATE_TIMELINE_TRANSITIONS) {
            return eligible;
        }
        List<Map<String, Object>> ordered = new ArrayList<>(eligible);
        ordered.sort((left, right) -> {
            int precedence = Boolean.compare(
                    !precedes(right, demandedOrder),
                    !precedes(left, demandedOrder));
            return precedence != 0 ? precedence : Long.compare(
                    causalEventSeq(right), causalEventSeq(left));
        });
        Map<String, Integer> retainedByChannel = new LinkedHashMap<>();
        List<Map<String, Object>> retained = new ArrayList<>();
        for (Map<String, Object> edge : ordered) {
            String channel = text(edge.get("kind")) + "\n"
                    + text(edge.get("fromRegion")) + "\n"
                    + text(edge.get("fromPort"));
            int count = retainedByChannel.getOrDefault(channel, 0);
            if (count >= LoopBoundPolicy.MAX_STATE_TIMELINE_TRANSITIONS) {
                continue;
            }
            retainedByChannel.put(channel, count + 1);
            retained.add(edge);
        }
        return retained;
    }

    /** Whether one candidate is ordered before the read it would serve. */
    private static boolean precedes(Map<String, Object> edge,
                                    long demandedOrder) {
        long seq = causalEventSeq(edge);
        return demandedOrder >= 0L && seq >= 0L && seq < demandedOrder;
    }

    private static long causalEventSeq(Map<String, Object> edge) {
        if ("RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))) {
            return longNumber(edge.get("receiverEventSeq"), -1L);
        }
        long result = -1L;
        for (String field : new String[]{"writerEventSeq",
                "mutationCompletionSeq"}) {
            result = Math.max(result, longNumber(edge.get(field), -1L));
        }
        return result;
    }

    /** Exact instant at which one demanded producer published its output. */
    private static long producerEventSeq(Map<String, Object> edge) {
        if ("RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))) {
            return longNumber(edge.get("senderEventSeq"), -1L);
        }
        return longNumber(edge.get("writerEventSeq"), -1L);
    }

    /**
     * Region retention needs an executable channel, not a same-declaration
     * hint.
     */
    private static boolean causalRegionRetentionEdge(
            Map<String, Object> edge) {
        String kind = text(edge.get("kind"));
        return "RUNTIME_FIELD_FLOW".equals(kind)
                || "RUNTIME_PROTOCOL_FLOW".equals(kind);
    }

    private static void applyClosure(StaticProgram program,
                                     ClosureWalk walk)
            throws IOException {
        Set<String> retainedRegions = new LinkedHashSet<>();
        for (String key : walk.reached) {
            retainedRegions.add(text(program.activations.get(key).get(
                    "regionId")));
        }
        program.regionEdges.removeIf(edge -> !walk.retainedEdges
                .contains(text(edge.get("edgeId"))));
        program.regions.removeIf(region -> !retainedRegions.contains(
                text(region.get("regionId"))));
        Map<String, Set<Long>> demandedAccesses =
                demandedRuntimeAccesses(program.regionEdges);
        // fatalPrefixContexts is the per-site authority.
        Map<String, Long> fatalPrefixCutoffs = new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : program.activations.entrySet()) {
            List<Map<String, Object>> contexts = rows(
                    entry.getValue().get("fatalPrefixContexts"));
            if (contexts.size() != 1) continue;
            long cutoff = longNumber(contexts.get(0).get("eventSeq"), -1L);
            if (cutoff >= 0L) fatalPrefixCutoffs.put(entry.getKey(), cutoff);
        }

        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            Set<String> occurrences = new LinkedHashSet<>();
            for (String key : walk.reached) {
                Map<String, Object> instance = program.activations.get(key);
                if (!regionId.equals(text(instance.get("regionId")))) {
                    continue;
                }
                occurrences.add(key);
            }
            // The activations this closure retained, named by identity.
            region.put("runtimeOccurrenceIds",
                    new ArrayList<>(occurrences));
            region.put("symbolicInputs", filterPorts(
                    rows(region.get("symbolicInputs")),
                    occurrences, false, walk.demandedInputs,
                    demandedAccesses, fatalPrefixCutoffs));
            region.put("outputs", filterPorts(
                    rows(region.get("outputs")),
                    occurrences, true, walk.demandedOutputs,
                    demandedAccesses, fatalPrefixCutoffs));
        }
    }

    private static List<Map<String, Object>> filterPorts(
            List<Map<String, Object>> ports, Set<String> occurrences,
            boolean output,
            Set<String> demandedPorts,
            Map<String, Set<Long>> demandedAccesses,
            Map<String, Long> fatalPrefixCutoffs)
            throws IOException {
        List<Map<String, Object>> retained = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            String occurrenceId = text(port.get("occurrenceId"));
            String demand = portDemandKey(occurrenceId,
                    text(port.get("portId")));
            if (!occurrences.contains(occurrenceId)
                    || !demandedPorts.contains(demand)) {
                continue;
            }
            // Region definitions are shared by all observed target
            // occurrences.
            Map<String, Object> selected = new LinkedHashMap<>(port);
            Long cutoff = output ? null
                    : fatalPrefixCutoffs.get(occurrenceId);
            if (cutoff != null && DependencyRole.valueFrontier(
                    selected.get("dependencyRole"))) {
                trimFatalPrefixAccesses(selected, cutoff);
            }
            retainExactRuntimeAccesses(selected, demand,
                    demandedAccesses.getOrDefault(demand,
                            Collections.<Long>emptySet()));
            retained.add(selected);
        }
        return retained;
    }

    private static void trimFatalPrefixAccesses(
            Map<String, Object> port, long cutoff) {
        List<Map<String, Object>> accesses = rows(
                port.get("runtimeAccesses"));
        if (accesses.isEmpty()) return;
        List<Map<String, Object>> prefix = new ArrayList<>();
        for (Map<String, Object> access : accesses) {
            long event = longNumber(access.get("eventSeq"), -1L);
            if (event >= 0L && event <= cutoff) prefix.add(access);
        }
        port.put("runtimeAccesses", prefix);
    }

    /** Keeps only concrete accesses selected by retained causal edges. */
    private static Map<String, Set<Long>> demandedRuntimeAccesses(
            Collection<Map<String, Object>> edges) {
        Map<String, Set<Long>> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                continue;
            }
            addDemandedAccess(result, text(edge.get("fromOccurrenceId")),
                    text(edge.get("fromPort")),
                    longNumber(edge.get("writerEventSeq"), -1L));
            addDemandedAccess(result, text(edge.get("toOccurrenceId")),
                    text(edge.get("toPort")),
                    longNumber(edge.get("readerEventSeq"), -1L));
        }
        return result;
    }

    private static void addDemandedAccess(
            Map<String, Set<Long>> target, String occurrenceId,
            String port, long eventSeq) {
        if (occurrenceId.isEmpty() || port.isEmpty() || eventSeq < 0L) {
            return;
        }
        target.computeIfAbsent(portDemandKey(occurrenceId, port),
                ignored -> new LinkedHashSet<>()).add(eventSeq);
    }

    private static void retainExactRuntimeAccesses(
            Map<String, Object> port, String demand,
            Set<Long> eventSeqs) throws IOException {
        if (!"HEAP".equals(text(port.get("transportKind")))) return;
        // The retained edges name their occurrences exactly, so those survive
        // the per-site resource cap; anything else stays a bounded default.
        List<Map<String, Object>> accesses = boundedRuntimeAccesses(port,
                (owner, access) -> eventSeqs.contains(longNumber(
                        access.get("eventSeq"), -1L)));
        if (accesses.isEmpty()) {
            throw new IOException("demanded heap port has no runtime access: "
                    + demand);
        }
        sortByEventSeq(accesses);
        List<Map<String, Object>> exact = new ArrayList<>();
        if (!eventSeqs.isEmpty()) {
            for (Map<String, Object> access : accesses) {
                if (eventSeqs.contains(longNumber(
                        access.get("eventSeq"), -1L))) {
                    exact.add(access);
                }
            }
        } else {
            // No edge selected an individual occurrence.
            exact.addAll(accesses);
        }
        if (exact.isEmpty()) {
            throw new IOException("causal edge occurrence is absent from "
                    + "demanded heap port: " + demand + " events="
                    + eventSeqs);
        }
        port.put("runtimeAccesses", exact);
        if (exact.size() == 1) {
            copyRuntimeOccurrence(exact.get(0), port);
            String site = text(port.get("staticAccessSiteId"));
            if (!site.isEmpty()) port.put("siteId", site);
        }
    }

    /** The deterministic identity of one region-local port key. */
    private static String portId(String regionId, String direction,
                                 String key) {
        return CausynthStaticFacts.nameId(regionId + direction,
                regionId + "\n" + key);
    }

    private static String portDemandKey(String occurrenceId,
                                        String portId) {
        return occurrenceId + "\n" + portId;
    }

    private static String outputOccurrenceDemandKey(
            String outputDemand, long writerEventSeq) {
        return outputDemand + "\nEVENT\n" + writerEventSeq;
    }

    /**
     * Resolves the recorded root call each observed flow endpoint named to the
     * activation identity minted for it.
     */
    private static void stampEdgeOccurrences(
            Collection<Map<String, Object>> edges,
            Map<String, String> byRecordedRootCall) {
        for (Map<String, Object> edge : edges) {
            String from = byRecordedRootCall.get(recordedRootCallKey(
                    text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L)));
            if (from != null) edge.put("fromOccurrenceId", from);
            String to = byRecordedRootCall.get(recordedRootCallKey(
                    text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L)));
            if (to != null) edge.put("toOccurrenceId", to);
        }
    }

    /**
     * Recorded root call of each activation, mapped to the identity minted
     * for it.  Raw refined-graph rows carry only that trace evidence, so
     * this table is the single place they are resolved to an occurrence.
     */
    private static Map<String, String> recordedRootCallIndex(
            Map<String, Map<String, Object>> activations) {
        Map<String, String> result = new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : activations.entrySet()) {
            result.put(recordedRootCallKey(
                    text(entry.getValue().get("regionId")),
                    longNumber(entry.getValue().get("rootCallId"), -1L)),
                    entry.getKey());
        }
        return result;
    }

    private static String recordedRootCallKey(String regionId,
                                              long rootCallId) {
        return regionId + "\n" + rootCallId;
    }

    private static void annotateFlowContexts(
            List<Map<String, Object>> edges,
            Map<String, Map<String, Object>> activations) {
        for (Map<String, Object> edge : edges) {
            Map<String, Object> from = activations.get(
                    text(edge.get("fromOccurrenceId")));
            Map<String, Object> to = activations.get(
                    text(edge.get("toOccurrenceId")));
            copyContext(edge, "from", from);
            copyContext(edge, "to", to);
            long writerLane = longNumber(edge.get("fromLaneId"), -1L);
            long readerLane = longNumber(edge.get("toLaneId"), -1L);
            if (writerLane > 0L) edge.put("writerLaneId", writerLane);
            if (readerLane > 0L) edge.put("readerLaneId", readerLane);
            edge.put("programOrderRequired",
                    writerLane > 0L && writerLane == readerLane);
        }
    }

    /** Marks retained, failure-directed container flows as symbolic state. */
    private static void markBoundedContainerStatePorts(
            StaticProgram program) {
        Map<String, Map<String, Object>> regionsById = program.regionsById();
        for (Map<String, Object> edge : program.regionEdges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                continue;
            }
            List<String> declarations = strings(
                    edge.get("fieldPathDeclarations"));
            DeclaredFieldCell leaf = declarations.isEmpty() ? null
                    : DeclaredFieldCell.parse(
                    declarations.get(declarations.size() - 1));
            if (leaf == null || JavaContainerTypes.shape(leaf.type)
                    == JavaContainerTypes.Shape.NONE) {
                continue;
            }

            String fromRegion = text(edge.get("fromRegion"));
            String toRegion = text(edge.get("toRegion"));
            String fromOccurrence = text(edge.get("fromOccurrenceId"));
            String toOccurrence = text(edge.get("toOccurrenceId"));
            Map<String, Object> producerRegion = regionsById.get(fromRegion);
            Map<String, Object> consumerRegion = regionsById.get(toRegion);
            Map<String, Object> output = exactRegionPort(producerRegion,
                    "outputs", text(edge.get("fromPort")), fromOccurrence);
            Map<String, Object> consumer = exactRegionPort(consumerRegion,
                    "symbolicInputs", text(edge.get("toPort")), toOccurrence);
            if (output == null || consumer == null) continue;
            markBoundedContainerPort(output, leaf.type);
            markBoundedContainerPort(consumer, leaf.type);
        }
    }

    private static Map<String, Object> exactRegionPort(
            Map<String, Object> region, String field, String portId,
            String occurrenceId) {
        if (region == null || portId.isEmpty() || occurrenceId.isEmpty()) {
            return null;
        }
        Map<String, Object> selected = null;
        for (Map<String, Object> port : rows(region.get(field))) {
            if (!portId.equals(text(port.get("portId")))
                    || !occurrenceId.equals(
                    text(port.get("occurrenceId")))) {
                continue;
            }
            if (selected != null) return null;
            selected = port;
        }
        return selected;
    }

    private static void markBoundedContainerPort(
            Map<String, Object> port, String javaType) {
        port.put("javaType", javaType);
        port.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
    }

    /**
     * Marks primitive element fields that are part of a demanded container
     * transition rather than unrelated leaves of a transported reference.
     */
    private static void markBoundedMutationStateFrontiers(
            StaticProgram program) {
        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            List<Map<String, Object>> edges = program.regionGraph(regionId);
            if (edges.isEmpty()) continue;

            Set<String> semanticSites = new LinkedHashSet<>();
            for (Map<String, Object> branch
                    : rows(region.get("branchPolicies"))) {
                if ("EXPLORE".equals(text(branch.get("policy")))
                        && !Boolean.TRUE.equals(booleanValue(
                        branch.get("loopControlGuard")))) {
                    String site = text(branch.get("siteId"));
                    if (!site.isEmpty()) semanticSites.add(site);
                }
            }
            if (semanticSites.isEmpty()) continue;

            Map<String, List<Map<String, Object>>> incoming =
                    program.regionIncoming(regionId);
            Map<String, List<Map<String, Object>>> inputBoundaries =
                    new LinkedHashMap<>();
            for (Map<String, Object> input
                    : rows(region.get("symbolicInputs"))) {
                for (String cell : RegionDemandIndex.boundaryCells(input)) {
                    inputBoundaries.computeIfAbsent(cell,
                            ignored -> new ArrayList<>()).add(input);
                }
            }

            for (Map<String, Object> output : rows(region.get("outputs"))) {
                if (!containerMutationPort(output)) {
                    continue;
                }
                String outputPort = text(output.get("portId"));
                for (String outputCell : mutationOutputCells(output)) {
                    for (Map<String, Object> guard : incoming.getOrDefault(
                            outputCell,
                            Collections.<Map<String, Object>>emptyList())) {
                        String guardSite = first(
                                text(guard.get("guardSiteId")),
                                text(guard.get("siteId")));
                        if (!"GUARD".equals(text(guard.get("transferKind")))
                                || !semanticSites.contains(guardSite)) {
                            continue;
                        }
                        markMutationValueFrontiers(
                                text(guard.get("fromCell")), incoming,
                                inputBoundaries, outputCell, outputPort,
                                guardSite);
                    }
                }
            }
        }
    }

    /**
     * Walks value sources backward from {@code seeds}, stopping at every cell
     * {@code leaf} accepts.
     */
    private static Set<String> walkValueSources(
            Collection<String> seeds,
            Map<String, List<Map<String, Object>>> incoming,
            Predicate<String> leaf) {
        return StaticProgram.closure(seeds, cell -> {
            if (leaf.test(cell)) return Collections.<String>emptyList();
            List<String> sources = new ArrayList<>();
            for (Map<String, Object> edge : incoming.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if ("GUARD".equals(text(edge.get("transferKind")))) continue;
                String from = text(edge.get("fromCell"));
                if (!from.isEmpty()) sources.add(from);
            }
            return sources;
        });
    }

    /**
     * The nearest container role reachable from {@code start} over exact
     * local passes: a value frontier as soon as one container receiver
     * declares one, a structure carrier when only carriers were seen.
     */
    private static String containerRole(
            Map<String, List<Map<String, Object>>> adjacency,
            String nextField, String start) {
        boolean[] frontier = new boolean[1];
        boolean[] carrier = new boolean[1];
        StaticProgram.closure(Collections.singletonList(start), cell -> {
            List<String> next = new ArrayList<>();
            for (Map<String, Object> edge : adjacency.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if ("container_receiver".equals(text(edge.get("kind")))) {
                    if (DependencyRole.VALUE_FRONTIER.equals(
                            DependencyRole.normalize(
                                    edge.get("dependencyRole")))) {
                        frontier[0] = true;
                        return null;
                    }
                    carrier[0] = true;
                    continue;
                }
                if (exactLocalPass(edge)) {
                    String value = text(edge.get(nextField));
                    if (!value.isEmpty()) next.add(value);
                }
            }
            return next;
        });
        return !frontier[0] && carrier[0]
                ? DependencyRole.CONCRETE_STRUCTURE_CARRIER
                : DependencyRole.VALUE_FRONTIER;
    }

    /**
     * One flow row per (read, writer port) pair: the latest write to the same
     * receiver and leaf that {@code excluded} admits.
     */
    private static List<Map<String, Object>> latestWriterFlows(
            List<BoundPort> reads,
            Map<String, List<BoundPort>> writesByReceiverLeaf,
            BiPredicate<BoundPort, BoundPort> excluded,
            BiFunction<BoundPort, BoundPort, Map<String, Object>> flow) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (BoundPort read : reads) {
            Map<String, BoundPort> selectedByPort = new LinkedHashMap<>();
            for (BoundPort write : writesByReceiverLeaf.getOrDefault(
                    read.receiver + "\n" + read.leafDeclaration(),
                    Collections.<BoundPort>emptyList())) {
                if (excluded.test(write, read)) continue;
                String writerPort = portDemandKey(write.occurrenceId,
                        write.port);
                BoundPort selected = selectedByPort.get(writerPort);
                if (selected == null || write.seq > selected.seq) {
                    selectedByPort.put(writerPort, write);
                }
            }
            for (BoundPort write : selectedByPort.values()) {
                result.add(flow.apply(write, read));
            }
        }
        return result;
    }

    /** The writes of every region's outputs, keyed by receiver and leaf. */
    private static Map<String, List<BoundPort>> writesByReceiverLeaf(
            List<Map<String, Object>> regions, RuntimeAccessDemand demand,
            Predicate<BoundPort> retained) throws IOException {
        List<BoundPort> writes = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(writes, text(region.get("regionId")),
                    rows(region.get("outputs")), demand);
        }
        Map<String, List<BoundPort>> index = new LinkedHashMap<>();
        for (BoundPort write : writes) {
            if (write.receiver == 0 || !retained.test(write)) continue;
            index.computeIfAbsent(
                    write.receiver + "\n" + write.leafDeclaration(),
                    ignored -> new ArrayList<>()).add(write);
        }
        return index;
    }

    /** The input ports a retained causal edge already closes. */
    private static Set<String> closedInputPorts(
            List<Map<String, Object>> regionEdges) {
        Set<String> closed = new LinkedHashSet<>();
        for (Map<String, Object> edge : regionEdges) {
            String toOccurrence = text(edge.get("toOccurrenceId"));
            String toPort = text(edge.get("toPort"));
            if (!toOccurrence.isEmpty() && !toPort.isEmpty()) {
                closed.add(portDemandKey(toOccurrence, toPort));
            }
        }
        return closed;
    }

    private static void markMutationValueFrontiers(
            String start,
            Map<String, List<Map<String, Object>>> incoming,
            Map<String, List<Map<String, Object>>> inputBoundaries,
            String outputCell, String outputPort, String guardSite) {
        walkValueSources(start.isEmpty()
                ? Collections.<String>emptyList()
                : Collections.singletonList(start), incoming, cell -> {
            boolean foundFrontier = false;
            for (Map<String, Object> input : inputBoundaries.getOrDefault(
                    cell, Collections.<Map<String, Object>>emptyList())) {
                String sourceKind = text(input.get("sourceKind"));
                if (!("ACCESSOR_RETURN".equals(sourceKind)
                        || EXTERNAL_CALL_RETURN.equals(sourceKind))
                        || !primitiveValuePort(input)) {
                    continue;
                }
                foundFrontier = true;
                if (text(input.get("symbolicDemand")).startsWith(
                        "CONCRETE_")
                        || !text(input.get(
                        "rpcConcreteRootAuthority")).isEmpty()) {
                    continue;
                }
                input.put("symbolicDemand", "BOUNDED_STATE_FRONTIER");
                input.put("boundedStateFrontierAuthority",
                        "STATIC_VALUE_SEMANTIC_MUTATION_GUARD_V1");
                addUniqueValue(input, "boundedMutationOutputCells",
                        outputCell);
                addUniqueValue(input, "boundedMutationOutputPorts",
                        outputPort);
                addUniqueValue(input, "boundedMutationGuardSites",
                        guardSite);
            }
            return foundFrontier;
        });
    }

    private static void addUniqueValue(Map<String, Object> row, String key,
                                       String value) {
        if (value.isEmpty()) return;
        List<String> values = strings(row.get(key));
        if (!values.contains(value)) values.add(value);
        row.put(key, values);
    }

    private static boolean containerMutationPort(
            Map<String, Object> port) {
        if ("CONTAINER_MUTATION".equals(
                text(port.get("bindingKind")))) {
            return true;
        }
        for (Map<String, Object> access : rows(port.get("runtimeAccesses"))) {
            if ("CONTAINER_MUTATION".equals(
                    text(access.get("bindingKind")))) {
                return true;
            }
        }
        return false;
    }

    private static boolean primitiveValuePort(Map<String, Object> port) {
        if (primitiveLeaf(port)) return true;
        String type = text(port.get("javaType"));
        return "boolean".equals(type) || "byte".equals(type)
                || "char".equals(type) || "short".equals(type)
                || "int".equals(type) || "long".equals(type)
                || "float".equals(type) || "double".equals(type);
    }

    private static List<String> mutationOutputCells(
            Map<String, Object> output) {
        Set<String> result = new LinkedHashSet<>();
        String cell = text(output.get("cell"));
        if (!cell.isEmpty()) result.add(cell);
        List<String> declarations = strings(
                output.get("fieldPathDeclarations"));
        if (!declarations.isEmpty()) {
            result.add(declarations.get(declarations.size() - 1));
        }
        result.addAll(RegionDemandIndex.boundaryCells(output));
        return new ArrayList<>(result);
    }

    /**
     * Prevents a primitive reached through a transferred reference from
     * silently becoming a new, unrelated symbolic variable.
     */
    static void markUnclosedReferenceLeavesConcrete(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges,
            List<Map<String, Object>> refinedGraph,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Set<Integer>> boundaryObjects = new LinkedHashMap<>();
        // The same deliveries, kept unexpanded and with the edge that made
        // them.
        Map<String, Map<Integer, List<Map<String, Object>>>> carriers =
                new LinkedHashMap<>();
        Set<String> closedInputs = closedInputPorts(regionEdges);
        for (Map<String, Object> edge : regionEdges) {
            String toOccurrence = text(edge.get("toOccurrenceId"));
            String toPort = text(edge.get("toPort"));
            // A heap flow delivers an object this trace can name.  A protocol
            // delivery does not: the receiver deserializes its own object, and
            // the reconstructed caller-result identity that used to stand in
            // for it was a value guess about a boundary the trace only ever
            // correlated by exchange.
            int deliveredObject = "RUNTIME_FIELD_FLOW".equals(
                    text(edge.get("kind")))
                    ? number(edge.get("valueObjectId"), 0) : 0;
            if (deliveredObject > 0 && !toOccurrence.isEmpty()) {
                boundaryObjects.computeIfAbsent(toOccurrence,
                        ignored -> new LinkedHashSet<>())
                        .add(deliveredObject);
                if (!toPort.isEmpty()) {
                    carriers.computeIfAbsent(toOccurrence,
                            ignored -> new LinkedHashMap<>())
                            .computeIfAbsent(deliveredObject,
                                    ignored -> new ArrayList<>()).add(edge);
                }
            }
        }
        if (boundaryObjects.isEmpty()) return;

        Map<String, Map<Integer, Set<Integer>>> objectLinks =
                new LinkedHashMap<>();
        Map<String, Set<String>> writtenLeaves = new LinkedHashMap<>();
        indexReferenceGraph(refinedGraph, occurrenceByRecordedRootCall,
                objectLinks, writtenLeaves);
        for (Map.Entry<String, Set<Integer>> entry
                : boundaryObjects.entrySet()) {
            Set<Integer> reachable = entry.getValue();
            Map<Integer, Set<Integer>> links = objectLinks.getOrDefault(
                    entry.getKey(), Collections.<Integer, Set<Integer>>emptyMap());
            reachable.addAll(StaticProgram.closure(
                    new ArrayList<Integer>(reachable), object -> {
                List<Integer> children = new ArrayList<>();
                for (Integer child : links.getOrDefault(object,
                        Collections.<Integer>emptySet())) {
                    if (child != null && child > 0) children.add(child);
                }
                return children;
            }));
        }

        List<Map<String, Object>> projections = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            for (Map<String, Object> port
                    : rows(region.get("symbolicInputs"))) {
                String occurrenceId = text(port.get("occurrenceId"));
                String demand = portDemandKey(occurrenceId,
                        text(port.get("portId")));
                if (closedInputs.contains(demand)
                        || "BOUNDED_STATE_FRONTIER".equals(
                        text(port.get("symbolicDemand")))
                        || !primitiveLeaf(port)) {
                    continue;
                }
                Set<Integer> receivers = receiverObjects(port);
                Set<Integer> reachable = boundaryObjects.get(occurrenceId);
                if (reachable == null || reachable.isEmpty()
                        || Collections.disjoint(reachable, receivers)
                        || writesLeafItself(writtenLeaves.get(occurrenceId),
                        leafDeclaration(port), receivers)) {
                    continue;
                }
                List<Map<String, Object>> projected = boxedLeafProjections(
                        carriers.getOrDefault(occurrenceId,
                                Collections.<Integer,
                                        List<Map<String, Object>>>emptyMap()),
                        port, receivers);
                if (projected != null) {
                    // The producer of the reference is the producer of the
                    // value, so the leaf is closed rather than replayed.
                    projections.addAll(projected);
                    continue;
                }
                port.put("symbolicDemand",
                        "CONCRETE_REFERENCE_BOUNDARY_REPLAY");
            }
        }
        regionEdges.addAll(projections);
    }

    /**
     * The one pass over the refined graph the unclosed-leaf decision needs:
     * {@code objectLinks} takes the reference edges each occurrence observed
     * ({@code receiver -> value}), {@code writtenLeaves} the exact leaves it
     * installs itself, as {@code receiverObjectId + declaration}.
     */
    private static void indexReferenceGraph(
            List<Map<String, Object>> graph,
            Map<String, String> occurrenceByRecordedRootCall,
            Map<String, Map<Integer, Set<Integer>>> objectLinks,
            Map<String, Set<String>> writtenLeaves) {
        for (Map<String, Object> edge : graph) {
            String transfer = text(edge.get("transferKind"));
            boolean write = "HEAP_WRITE".equals(transfer);
            List<Map<String, Object>> fieldBindings =
                    write || "HEAP_READ".equals(transfer)
                            ? rows(edge.get("runtimeFieldBindings"))
                            : Collections.<Map<String, Object>>emptyList();
            List<Map<String, Object>> linked =
                    rows(edge.get("runtimeAccessorBindings"));
            if (!write) linked.addAll(fieldBindings);
            for (Map<String, Object> binding : linked) {
                int receiver = number(binding.containsKey("receiverObjectId")
                        ? binding.get("receiverObjectId")
                        : binding.get("fieldReceiverObjectId"), 0);
                int value = number(binding.get("valueObjectId"), 0);
                String occurrenceId = occurrenceByRecordedRootCall.getOrDefault(
                        recordedRootCallKey(text(binding.get("regionId")),
                                longNumber(binding.get("rootCallId"), -1L)),
                        "");
                if (receiver <= 0 || value <= 0 || occurrenceId.isEmpty()) {
                    continue;
                }
                objectLinks.computeIfAbsent(occurrenceId,
                        ignored -> new LinkedHashMap<>())
                        .computeIfAbsent(receiver,
                                ignored -> new LinkedHashSet<>()).add(value);
            }
            if (!write) continue;
            for (Map<String, Object> binding : fieldBindings) {
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(text(binding.get("regionId")),
                                longNumber(binding.get("rootCallId"), -1L)));
                int receiver = number(
                        binding.get("fieldReceiverObjectId"), 0);
                String declaration = leafDeclaration(binding);
                if (occurrenceId == null || receiver <= 0
                        || declaration.isEmpty()) {
                    continue;
                }
                writtenLeaves.computeIfAbsent(occurrenceId,
                        ignored -> new LinkedHashSet<>())
                        .add(receiver + "\n" + declaration);
            }
        }
    }

    /** Whether one of {@code receivers} holds a leaf this occurrence wrote. */
    private static boolean writesLeafItself(Set<String> written,
                                            String declaration,
                                            Set<Integer> receivers) {
        if (written == null || declaration.isEmpty()) return false;
        for (Integer receiver : receivers) {
            if (written.contains(receiver + "\n" + declaration)) return true;
        }
        return false;
    }

    /**
     * The carrier edges of one immutable boxed leaf, or {@code null} when this
     * leaf is not that shape.
     *
     * <p>The wrapper test is the exact boundary, not a conservative one.  A
     * carrier edge names the producer of the <em>reference</em>, and its
     * output port stands for the object; only for a wrapper does that port
     * carry the leaf's own value and the leaf's own solver sort.  For any
     * other owner the projection would bind a primitive input to a reference
     * output, which the composer refuses as a sort mismatch - leaving the
     * leaf a free solver variable, a freedom the run never had and strictly
     * worse than the named demotion below.</p>
     */
    private static List<Map<String, Object>> boxedLeafProjections(
            Map<Integer, List<Map<String, Object>>> carriers,
            Map<String, Object> leaf, Set<Integer> receivers) {
        String declaration = leafDeclaration(leaf);
        DeclaredFieldCell field = DeclaredFieldCell.parse(declaration);
        if (field == null
                || !JavaPrimitiveBoxing.wrapperType(field.owner)) {
            return null;
        }
        List<Map<String, Object>> projected = new ArrayList<>();
        for (Integer receiver : receivers) {
            for (Map<String, Object> carrier : carriers.getOrDefault(receiver,
                    Collections.<Map<String, Object>>emptyList())) {
                projected.add(boxedLeafProjection(carrier, leaf));
            }
        }
        return projected.isEmpty() ? null : projected;
    }

    /**
     * One carrier edge restated as the producer of the boxed value it carried.
     */
    private static Map<String, Object> boxedLeafProjection(
            Map<String, Object> carrier, Map<String, Object> leaf) {
        String leafPort = text(leaf.get("portId"));
        String identity = text(carrier.get("edgeId")) + "\n" + leafPort;
        Map<String, Object> edge = new LinkedHashMap<>(carrier);
        edge.put("edgeId", CausynthStaticFacts.nameId("BX.", identity));
        edge.put("toPort", leafPort);
        String role = text(leaf.get("dependencyRole"));
        if (!role.isEmpty()) {
            edge.put("dependencyRole", role);
        }
        return edge;
    }

    /** The declared field a port's leaf reads, by its own path or its cell. */
    private static String leafDeclaration(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        return declarations.isEmpty() ? text(port.get("cell"))
                : declarations.get(declarations.size() - 1);
    }

    private static boolean primitiveLeaf(Map<String, Object> port) {
        DeclaredFieldCell field = DeclaredFieldCell.parse(
                leafDeclaration(port));
        return field != null && field.primitive();
    }

    private static Set<Integer> receiverObjects(Map<String, Object> port) {
        Set<Integer> result = new LinkedHashSet<>();
        int receiver = number(port.get("fieldReceiverObjectId"), 0);
        if (receiver > 0) result.add(receiver);
        receiver = number(port.get("rootObjectId"), 0);
        if (receiver > 0 && "OBSERVED_FIELD_RECEIVER".equals(
                text(port.get("rootKind")))) {
            result.add(receiver);
        }
        for (Map<String, Object> access
                : rows(port.get("runtimeAccesses"))) {
            receiver = number(access.get("fieldReceiverObjectId"), 0);
            if (receiver > 0) result.add(receiver);
        }
        return result;
    }

    private static void copyContext(Map<String, Object> edge, String prefix,
                                    Map<String, Object> instance) {
        if (instance == null) return;
        putIfMissing(edge, prefix + "LaneId", instance.get("laneId"));
        putIfMissing(edge, prefix + "SpanId", instance.get("spanId"));
    }

    private static void putIfMissing(Map<String, Object> target, String key,
                                     Object value) {
        if (!target.containsKey(key) && value != null
                && !text(value).isEmpty()) {
            target.put(key, value);
        }
    }

    /** Republishes one recorded access as the port's own replay address. */
    private static void copyRuntimeOccurrence(
            Map<String, Object> access, Map<String, Object> port) {
        for (String key : new String[]{"eventSeq", "staticAccessSiteId",
                "activationLocalStaticSiteOccurrence",
                "accessorOccurrence", "helperActivationBoundedOccurrence",
                "fieldReceiverObjectId", "rootCallId", "callId"}) {
            if (access.containsKey(key) && access.get(key) != null) {
                port.put(key, access.get(key));
            }
        }
        int occurrence = number(access.get(
                "activationLocalStaticSiteOccurrence"),
                number(access.get("accessorOccurrence"), -1));
        if (occurrence > 0) {
            port.put("replayOccurrence", occurrence);
            port.put("activationLocalStaticSiteOccurrence", occurrence);
        }
    }

    private static List<Map<String, Object>> statePorts(
            StaticProgram program, String regionId,
            String transfer, String prefix,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Set<String>> seenAccesses = new LinkedHashMap<>();
        Map<String, List<Map<String, Object>>> roleOutgoing =
                program.regionOutgoing(regionId);
        for (Map<String, Object> edge : program.regionGraph(regionId)) {
            if (!transfer.equals(text(edge.get("transferKind")))) {
                continue;
            }
            String roleCell = "HEAP_READ".equals(transfer)
                    ? text(edge.get("toCell")) : "";
            String dependencyRole = roleCell.isEmpty()
                    ? DependencyRole.VALUE_FRONTIER
                    : containerRole(roleOutgoing, "toCell", roleCell);
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeFieldBindings"))) {
                if (!regionId.equals(text(binding.get("regionId")))) {
                    continue;
                }
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(regionId, longNumber(
                                binding.get("rootCallId"), -1L)));
                if (occurrenceId == null) continue;
                String key = occurrenceId + "\n"
                        + text(binding.get("rootCell")) + "\n"
                        + strings(binding.get("fieldPath"));
                Map<String, Object> port = unique.get(key);
                if (port == null) {
                    port = new LinkedHashMap<>(binding);
                    port.put("portId", portId(regionId,
                            "IN".equals(prefix) ? ".in." : ".out.", key));
                    port.put("occurrenceId", occurrenceId);
                    port.put("cell", binding.get("rootCell"));
                    port.put("transportKind", "HEAP");
                    String rootKind = text(binding.get("rootKind"));
                    port.put("sourceKind", "PARAMETER".equals(rootKind)
                            ? "ROOT_ARGUMENT"
                            : "OBSERVED_FIELD_RECEIVER".equals(rootKind)
                            ? "ACTIVATION_FIELD_RECEIVER"
                            : "RECEIVER_FIELD");
                    port.put("runtimeAccesses", new ArrayList<>());
                    port.put("dependencyCells", new ArrayList<String>());
                    unique.put(key, port);
                }
                if (!port.containsKey("dependencyRole")) {
                    port.put("dependencyRole", dependencyRole);
                } else {
                    port.put("dependencyRole", DependencyRole.merge(
                            port.get("dependencyRole"), dependencyRole));
                }
                addRuntimeAccess(port, binding, edge, occurrenceId,
                        seenAccesses.computeIfAbsent(key,
                                ignored -> new LinkedHashSet<>()));
                addUniqueValue(port, "dependencyCells",
                        text(edge.get("fromCell")));
            }
        }
        return new ArrayList<>(unique.values());
    }

    @SuppressWarnings("unchecked")
    private static void addRuntimeAccess(Map<String, Object> port,
                                         Map<String, Object> binding,
                                         Map<String, Object> edge,
                                         String occurrenceId,
                                         Set<String> seen) {
        // statePorts installs the list, so the cast is exact; the seen set
        // replaces a quadratic rescan with the same (eventSeq, receiver)
        // dedup identity and the same append order.
        List<Map<String, Object>> accesses = (List<Map<String, Object>>)
                port.get("runtimeAccesses");
        long seq = longNumber(binding.get("eventSeq"), 0L);
        int receiver = number(binding.get("fieldReceiverObjectId"), 0);
        if (!seen.add(seq + "\n" + receiver)) {
            return;
        }
        Map<String, Object> access = new LinkedHashMap<>();
        access.put("eventSeq", binding.get("eventSeq"));
        access.put("callId", binding.get("callId"));
        access.put("sourceKey", binding.get("sourceKey"));
        access.put("occurrenceId", occurrenceId);
        // Recorded trace evidence for the observed access.
        for (String key : new String[]{"rootCallId",
                "fieldReceiverObjectId", "valueObjectId", "primitiveValue",
                "fieldPathDeclarations", "bindingKind",
                "writerFieldReadSeq", "mutatorEnterSeq",
                "mutationCompletionSeq", "mutationInvocationId",
                "mutatorDeclaredCallee", "containerMemberToken",
                "containerMemberIdentityAuthority", "containerObjectId",
                "containerKeyObjectId", "containerValueObjectId",
                "containerMemberFieldBindings"}) {
            access.put(key, binding.get(key));
        }
        access.put("staticAccessSiteId", first(
                text(binding.get("siteId")), staticAccessSiteId(edge)));
        accesses.add(access);
    }

    private static String staticAccessSiteId(Map<String, Object> edge) {
        String site = text(edge.get("siteId"));
        if (!site.isEmpty()) return site;
        String method = text(edge.get("method"));
        int unit = number(edge.get("unitIndex"), -1);
        if (!method.isEmpty() && unit >= 0) return method + "#u" + unit;
        return text(edge.get("id"));
    }

    private static List<Map<String, Object>> accessorPorts(
            StaticProgram program, String regionId,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Integer> retainedByActivationStream =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : program.regionGraph(regionId)) {
            if (!"accessor_field_return".equals(text(edge.get("kind")))
                    || !Boolean.TRUE.equals(booleanValue(
                    edge.get("runtimeObserved")))) {
                continue;
            }
            String field = first(text(edge.get("declaredFieldSignature")),
                    text(edge.get("fromCell")));
            DeclaredFieldCell declaration = DeclaredFieldCell.parse(field);
            if (declaration == null || !declaration.primitive()) continue;
            String caller = text(edge.get("method"));
            int unitIndex = number(edge.get("unitIndex"), -1);
            String declaredCallee = text(edge.get("invoke"));
            String implementation = text(
                    edge.get("accessorImplementationMethod"));
            if (caller.isEmpty() || unitIndex < 0
                    || declaredCallee.isEmpty() || implementation.isEmpty()) {
                continue;
            }
            List<Map<String, Object>> bindings = new ArrayList<>(
                    rows(edge.get("runtimeAccessorBindings")));
            bindings.sort(Comparator
                    .comparingLong((Map<String, Object> binding) ->
                            longNumber(binding.get("rootCallId"),
                                    Long.MAX_VALUE))
                    .thenComparingLong(binding -> longNumber(
                            binding.get("eventSeq"), Long.MAX_VALUE)));
            for (Map<String, Object> binding : bindings) {
                if (!regionId.equals(text(binding.get("regionId")))) continue;
                int occurrence = number(binding.get("accessorOccurrence"), -1);
                long callId = longNumber(binding.get("callId"), -1L);
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(regionId, longNumber(
                                binding.get("rootCallId"), -1L)));
                if (occurrence < 1 || occurrenceId == null || callId < 0L) {
                    continue;
                }
                String key = occurrenceId + "\n" + text(edge.get("id"))
                        + "\n" + callId + "\n" + occurrence;
                if (unique.containsKey(key)) continue;
                // The root can be a long-lived service loop.
                String stream = occurrenceId + "\n" + callId
                        + "\nACCESSOR_RETURN\n"
                        + caller + "#u" + unitIndex + "\n" + field + "\n"
                        + declaredCallee + "\n" + implementation;
                int retained = retainedByActivationStream.getOrDefault(
                        stream, 0);
                if (retained >= LoopBoundPolicy
                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
                    continue;
                }
                retainedByActivationStream.put(stream, retained + 1);
                Map<String, Object> port = new LinkedHashMap<>(binding);
                port.put("occurrenceId", occurrenceId);
                port.put("portId", portId(regionId, ".in.", key));
                port.put("cell", field);
                port.put("sourceKind", "ACCESSOR_RETURN");
                port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
                port.put("transportKind", "ACTIVATION_LOCAL");
                port.put("rootKind", "OBSERVED_FIELD_RECEIVER");
                port.put("rootObjectId", binding.get("receiverObjectId"));
                port.put("fieldReceiverObjectId",
                        binding.get("receiverObjectId"));
                port.put("fieldPath",
                        Collections.singletonList(declaration.name));
                port.put("fieldPathDeclarations",
                        Collections.singletonList(field));
                port.put("javaType", declaration.type);
                port.put("callerMethod", caller);
                port.put("unitIndex", unitIndex);
                port.put("siteId", staticAccessSiteId(edge));
                port.put("staticAccessSiteId", staticAccessSiteId(edge));
                port.put("declaredCallee", declaredCallee);
                port.put("declaredFieldSignature", field);
                port.put("accessorImplementationMethod", implementation);
                port.put("dependencyCells",
                        Collections.singletonList(text(edge.get("toCell"))));
                port.put("replayOccurrence", occurrence);
                port.put("helperActivationBoundedOccurrence", retained + 1);
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    /**
     * Primitive results produced outside the analyzed graph are semantic
     * inputs when they reach an explored branch.  The runtime occurrence is
     * retained so replay can replace the exact local definition; modeled
     * container operations and primitive unboxing remain derived values.
     */
    private static List<Map<String, Object>> externalCallReturnPorts(
            StaticProgram program, String regionId,
            List<Map<String, Object>> branchPolicies,
            Collection<Map<String, Object>> runtimeObservations) {
        Set<String> demanded = semanticExternalCallReturnEdges(
                program, regionId, branchPolicies);
        if (demanded.isEmpty() || runtimeObservations == null) {
            return Collections.emptyList();
        }
        Map<Long, List<String>> occurrencesByCall = new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> activation
                : program.activations.entrySet()) {
            for (Long callId : StaticProgram.longValues(
                    activation.getValue().get("callIds"))) {
                occurrencesByCall.computeIfAbsent(callId,
                        ignored -> new ArrayList<>()).add(activation.getKey());
            }
        }
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Integer> ordinals = new LinkedHashMap<>();
        for (Map<String, Object> edge : program.regionGraph(regionId)) {
            if (!demanded.contains(text(edge.get("id")))) continue;
            String caller = text(edge.get("method"));
            String site = staticAccessSiteId(edge);
            String callee = text(edge.get("invoke"));
            String javaType = primitiveReturnType(callee);
            int unitIndex = number(edge.get("unitIndex"), -1);
            if (caller.isEmpty() || site.isEmpty() || callee.isEmpty()
                    || javaType.isEmpty() || unitIndex < 0) {
                continue;
            }
            for (Map<String, Object> observation : runtimeObservations) {
                if (!"CALL_SITE_RETURN".equals(
                        text(observation.get("kind")))
                        || !site.equals(text(observation.get("siteId")))
                        || !callee.equals(
                        text(observation.get("declaredCallee")))) {
                    continue;
                }
                long callId = longNumber(observation.get("callId"), -1L);
                List<String> occurrenceIds = occurrencesByCall.get(callId);
                if (occurrenceIds == null) continue;
                for (String occurrenceId : occurrenceIds) {
                    String stream = occurrenceId + "\n" + callId + "\n"
                            + site;
                    int ordinal = ordinals.getOrDefault(stream, 0) + 1;
                    ordinals.put(stream, ordinal);
                    String key = stream + "\n" + ordinal;
                    Map<String, Object> port = new LinkedHashMap<>();
                    port.put("occurrenceId", occurrenceId);
                    port.put("portId", portId(regionId, ".in.", key));
                    port.put("cell", text(edge.get("fromCell")));
                    port.put("sourceKind", EXTERNAL_CALL_RETURN);
                    port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
                    port.put("transportKind", "ACTIVATION_LOCAL");
                    port.put("rootKind", "CALL_RETURN");
                    port.put("javaType", javaType);
                    port.put("method", caller);
                    port.put("rootMethod", caller);
                    port.put("callerMethod", caller);
                    port.put("definitionMethod", caller);
                    port.put("unitIndex", unitIndex);
                    port.put("definitionUnitIndex", unitIndex);
                    port.put("siteId", site);
                    port.put("staticAccessSiteId", site);
                    port.put("declaredCallee", callee);
                    port.put("eventSeq", observation.get("eventSeq"));
                    port.put("callId", callId);
                    port.put("primitiveValue",
                            observation.get("primitiveValue"));
                    port.put("dependencyCells", Collections.singletonList(
                            text(edge.get("toCell"))));
                    port.put("replayOccurrence", ordinal);
                    port.put("observed", true);
                    for (String context : new String[]{"callSourceKey",
                            "requestKey", "requestApi"}) {
                        if (!text(observation.get(context)).isEmpty()) {
                            port.put("callSourceKey".equals(context)
                                    ? "sourceKey" : context,
                                    observation.get(context));
                        }
                    }
                    unique.put(key, port);
                }
            }
        }
        return new ArrayList<>(unique.values());
    }

    /** Exact external primitive definitions reached by explored guards. */
    private static Set<String> semanticExternalCallReturnEdges(
            StaticProgram program, String regionId,
            List<Map<String, Object>> branchPolicies) {
        List<String> seeds = new ArrayList<>();
        for (Map<String, Object> branch : branchPolicies) {
            if ("EXPLORE".equals(text(branch.get("policy")))) {
                seeds.addAll(strings(branch.get("operandCells")));
            }
        }
        Set<String> selected = new LinkedHashSet<>();
        Map<String, List<Map<String, Object>>> incoming =
                program.regionIncoming(regionId);
        StaticProgram.closure(seeds, cell -> {
            List<String> next = new ArrayList<>();
            for (Map<String, Object> edge : incoming.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                String callee = text(edge.get("invoke"));
                String returnCell = text(edge.get("fromCell"));
                boolean callReturn = "call_return".equals(
                        text(edge.get("kind")))
                        && Boolean.TRUE.equals(booleanValue(
                        edge.get("runtimeObserved")))
                        && !primitiveReturnType(callee).isEmpty()
                        && program.regionsHolding(callee).isEmpty()
                        && !JavaContainerTypes.symbolicResultOperation(callee)
                        && !JavaPrimitiveBoxing.unboxReturn(returnCell)
                        && !JavaPrimitiveBoxing.deterministicValueOfReturn(
                        returnCell);
                if (callReturn) {
                    selected.add(text(edge.get("id")));
                } else if (!"GUARD".equals(
                        text(edge.get("transferKind")))) {
                    String from = text(edge.get("fromCell"));
                    if (!from.isEmpty()) next.add(from);
                }
            }
            return next;
        });
        selected.remove("");
        return selected;
    }

    private static String primitiveReturnType(String signature) {
        java.util.regex.Matcher method = CausynthStaticFacts
                .METHOD_SIGNATURE.matcher(signature == null ? "" : signature);
        if (!method.matches()) return "";
        String type = method.group(2).trim();
        return "boolean".equals(type) || "byte".equals(type)
                || "char".equals(type) || "short".equals(type)
                || "int".equals(type) || "long".equals(type)
                || "float".equals(type) || "double".equals(type)
                ? type : "";
    }

    private static List<Map<String, Object>> explicitFaultPorts(
            String regionId, List<Map<String, Object>> edges,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!Boolean.TRUE.equals(booleanValue(
                    edge.get("explicitSymbolicFault")))) {
                continue;
            }
            String returnCell = text(edge.get("fromCell"));
            String caller = text(edge.get("method"));
            int unitIndex = number(edge.get("unitIndex"), -1);
            if (returnCell.isEmpty() || caller.isEmpty() || unitIndex < 0) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeExplicitFaultBindings"))) {
                if (!regionId.equals(text(binding.get("regionId")))
                        || !"EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                        text(binding.get("authority")))) {
                    continue;
                }
                long eventSeq = longNumber(binding.get("eventSeq"), -1L);
                int occurrence = number(binding.get("accessorOccurrence"), -1);
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(regionId, longNumber(
                                binding.get("rootCallId"), -1L)));
                if (occurrenceId == null || eventSeq < 0L || occurrence < 1) {
                    continue;
                }
                String key = occurrenceId + "\n" + caller + "#u"
                        + unitIndex + "\n" + occurrence;
                Map<String, Object> port = new LinkedHashMap<>(binding);
                port.put("occurrenceId", occurrenceId);
                port.put("portId", portId(regionId, ".in.", key));
                // The caller local is the region input consumed by the
                // branch.  The call-return identity remains on the exact
                // site/callee binding below; naming the callee's abstract
                // return cell here leaves the real guard operand outside the
                // occurrence boundary.
                port.put("cell", edge.get("toCell"));
                port.put("sourceKind", EXPLICIT_SYMBOLIC_FAULT);
                port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
                port.put("transportKind", "ACTIVATION_LOCAL");
                port.put("rootKind", "ACTIVATION_LOCAL");
                port.put("javaType", "boolean");
                port.put("callerMethod", caller);
                port.put("unitIndex", unitIndex);
                port.put("siteId", caller + "#u" + unitIndex);
                port.put("declaredCallee", edge.get("invoke"));
                port.put("symbolicName", edge.get("symbolicName"));
                port.put("dependencyCells",
                        Collections.singletonList(edge.get("toCell")));
                port.put("replayOccurrence", occurrence);
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    /** Caller locals assigned by one declared application call return. */
    private static Set<String> callReturnValueCells(
            Collection<Map<String, Object>> edges,
            Map<String, Object> port) {
        Set<String> cells = new LinkedHashSet<>();
        if (!CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                text(port.get(CommunicationCatalogContract
                        .PORT_OUTPUT_CAPTURE_KIND)))) return cells;
        String returned = text(port.get(CommunicationCatalogContract
                .DECLARED_CALLEE)) + ".return";
        for (Map<String, Object> edge : edges) {
            if ("call_return".equals(text(edge.get("kind")))
                    && text(port.get(CommunicationCatalogContract
                    .PORT_DEFINITION_METHOD)).equals(text(edge.get("method")))
                    && text(port.get(CommunicationCatalogContract
                    .CALL_SITE_ID)).equals(text(edge.get("siteId")))
                    && returned.equals(text(edge.get("fromCell")))) {
                cells.add(text(edge.get("toCell")));
            }
        }
        cells.remove("");
        return cells;
    }

    /**
     * A live-in used only to replay a bounded loop's continuation decision is
     * retained in the task, but must not become a symbolic search dimension.
     */
    private static void markLoopControlOnlyInputs(
            List<Map<String, Object>> inputs,
            List<Map<String, Object>> edges,
            List<Map<String, Object>> branchPolicies) {
        Set<String> loopOperands = new LinkedHashSet<>();
        Set<String> semanticOperands = new LinkedHashSet<>();
        for (Map<String, Object> branch : branchPolicies) {
            Set<String> target = Boolean.TRUE.equals(booleanValue(
                    branch.get("loopControlGuard")))
                    ? loopOperands : semanticOperands;
            target.addAll(strings(branch.get("operandCells")));
        }
        if (loopOperands.isEmpty()) return;

        Map<String, List<String>> outgoing = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if ("GUARD".equals(text(edge.get("transferKind")))) continue;
            String from = text(edge.get("fromCell"));
            String to = text(edge.get("toCell"));
            if (!from.isEmpty() && !to.isEmpty()) {
                outgoing.computeIfAbsent(from,
                        ignored -> new ArrayList<>()).add(to);
            }
        }
        for (Map<String, Object> input : inputs) {
            Set<String> starts = new LinkedHashSet<>(
                    strings(input.get("dependencyCells")));
            String cell = text(input.get("cell"));
            if (!cell.isEmpty()) starts.add(cell);
            // One walk answers both questions: any flow reaching a non-loop
            // branch operand wins and keeps the value symbolic.
            Set<String> reached = StaticProgram.closure(starts,
                    node -> outgoing.getOrDefault(node,
                            Collections.<String>emptyList()));
            if (!Collections.disjoint(reached, loopOperands)
                    && Collections.disjoint(reached, semanticOperands)) {
                input.put("loopControlOnly", true);
                input.put("symbolicDemand", "CONCRETE_LOOP_CONTROL");
            }
        }
    }

    /**
     * The methods whose guards decide the region's demanded behaviour: what
     * the admitting anchors reach, widened by the methods that define this
     * region's own outputs.
     */
    private static Set<String> demandScope(
            StaticProgram.RegionRow skeleton,
            List<Map<String, Object>> outputs) {
        Set<String> result = new LinkedHashSet<>(
                skeleton.demandScopeMethods);
        if (result.isEmpty()) {
            return result;
        }
        for (Map<String, Object> output : outputs) {
            String site = text(output.get("siteId"));
            int marker = site.indexOf('#');
            if (marker > 0) {
                result.add(site.substring(0, marker));
            }
            String owner = text(output.get("rootMethod"));
            if (!owner.isEmpty()) {
                result.add(owner);
            }
        }
        return result;
    }

    /** Builds the region's branch policies. */
    private static List<Map<String, Object>> branches(
            StaticProgram program, String regionId,
            Set<String> demandScope) {
        Map<String, List<Map<String, Object>>> bySite = guardsBySite(
                program.regionGraph(regionId), edge -> true);
        BranchPolicyClassifier classifier = new BranchPolicyClassifier(
                program.regionIncoming(regionId));
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : bySite.entrySet()) {
            String site = entry.getKey();
            List<Map<String, Object>> guards = entry.getValue();
            Map<String, Object> representative = guards.get(0);
            Map<String, Object> branch = new LinkedHashMap<>();
            branch.put("siteId", site);
            branch.put("method", representative.get("method"));
            branch.put("unitIndex", number(
                    representative.get("unitIndex"), -1));
            List<Map<String, Object>> failureGuards = new ArrayList<>();
            for (Map<String, Object> guard : guards) {
                if (isExceptionTargetEdge(guard)) failureGuards.add(guard);
            }
            Collection<Map<String, Object>> decisiveGuards =
                    failureGuards.isEmpty() ? guards : failureGuards;
            branch.put("failureTarget", !failureGuards.isEmpty());
            // Which throw this guard controls, not merely that it controls
            // one.
            List<String> guardedTargets = new ArrayList<>();
            for (Map<String, Object> guard : failureGuards) {
                String cell = text(guard.get("toCell"));
                if (!cell.isEmpty() && !guardedTargets.contains(cell)) {
                    guardedTargets.add(cell);
                }
            }
            if (!guardedTargets.isEmpty()) {
                branch.put(FAILURE_TARGET_CELLS, guardedTargets);
            }
            branch.put("operandCells", operandCells(decisiveGuards));
            Boolean required = consistentRequiredOutcome(decisiveGuards);
            branch.put("requiredOutcome", required);
            branch.put("guardedSiteOutcomes", guardedSiteOutcomes(guards));

            boolean cfgLoopControl = classifier.cfgLoopControlGuard(guards);
            boolean loopStructure = cfgLoopControl
                    || classifier.structuralLoopGuard(site, guards);
            boolean carrierStructure = classifier.structureCarrierGuard(
                    guards);
            boolean outsideDemand = !demandScope.isEmpty()
                    && failureGuards.isEmpty()
                    && !demandScope.contains(text(
                    representative.get("method")));
            branch.put("loopControlGuard", loopStructure);
            // Opposite required outcomes mean this guard selects between
            // alternative demanded semantics.
            branch.put("policy", loopStructure
                    || carrierStructure || outsideDemand
                    ? "PATH_ASSUMPTION" : "EXPLORE");
            result.add(branch);
        }
        return result;
    }

    /** Guard rows by the site they decide, in first-seen order. */
    private static Map<String, List<Map<String, Object>>> guardsBySite(
            Collection<Map<String, Object>> edges,
            Predicate<Map<String, Object>> retained) {
        Map<String, List<Map<String, Object>>> bySite = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) continue;
            String site = first(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            if (site.isEmpty()) continue;
            List<Map<String, Object>> guards = bySite.computeIfAbsent(site,
                    ignored -> new ArrayList<>());
            if (retained.test(edge)) guards.add(edge);
        }
        return bySite;
    }

    private static List<String> operandCells(
            Collection<Map<String, Object>> guards) {
        Set<String> cells = new LinkedHashSet<>();
        for (Map<String, Object> guard : guards) {
            String cell = text(guard.get("fromCell"));
            if (!cell.isEmpty()) cells.add(cell);
        }
        List<String> result = new ArrayList<>(cells);
        Collections.sort(result);
        return result;
    }

    /**
     * Names, per site this branch decides, the Jimple outcome the analyzer
     * proved is required to reach that site.
     */
    private static List<Map<String, Object>> guardedSiteOutcomes(
            Collection<Map<String, Object>> guards) {
        Map<String, Boolean> proved = new TreeMap<>();
        Set<String> unproved = new TreeSet<>();
        for (Map<String, Object> guard : guards) {
            List<Map<String, Object>> controlled = new ArrayList<>();
            controlled.addAll(rows(guard.get("guardedMutations")));
            controlled.addAll(rows(guard.get("controlledDefinitions")));
            controlled.addAll(rows(guard.get("guardedEffects")));
            for (Map<String, Object> row : controlled) {
                String site = first(first(
                        text(row.get("guardedMutationSiteId")),
                        text(row.get("controlledDefinitionSiteId"))),
                        text(row.get("effectSiteId")));
                if (site.isEmpty()) continue;
                Boolean outcome = booleanValue(row.get("requiredOutcome"));
                if (outcome == null) {
                    unproved.add(site);
                    continue;
                }
                Boolean prior = proved.putIfAbsent(site, outcome);
                if (prior != null && !prior.equals(outcome)) {
                    unproved.add(site);
                }
            }
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, Boolean> entry : proved.entrySet()) {
            if (unproved.contains(entry.getKey())) continue;
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("siteId", entry.getKey());
            row.put("requiredOutcome", entry.getValue());
            result.add(row);
        }
        return result;
    }

    private static Boolean consistentRequiredOutcome(
            Collection<Map<String, Object>> guards) {
        Set<Boolean> values = new LinkedHashSet<>();
        for (Map<String, Object> guard : guards) {
            List<Map<String, Object>> controlled = new ArrayList<>();
            controlled.addAll(rows(guard.get("guardedMutations")));
            controlled.addAll(rows(guard.get("controlledDefinitions")));
            controlled.addAll(rows(guard.get("guardedEffects")));
            if (controlled.isEmpty()) {
                Boolean value = booleanValue(guard.get("requiredOutcome"));
                if (value != null) values.add(value);
                continue;
            }
            for (Map<String, Object> row : controlled) {
                Boolean value = booleanValue(row.get("requiredOutcome"));
                if (value == null) return null;
                values.add(value);
            }
        }
        return values.size() == 1 ? values.iterator().next() : null;
    }

    /** Classifies only positively proven structural traversal guards. */
    private static final class BranchPolicyClassifier {
        private final Map<String, List<Map<String, Object>>> incoming;

        private BranchPolicyClassifier(
                Map<String, List<Map<String, Object>>> incoming) {
            this.incoming = incoming;
        }

        private boolean structuralLoopGuard(
                String site, Collection<Map<String, Object>> guards) {
            if (!loopRecurrence(site, guards)) return false;
            for (String operand : operandCells(guards)) {
                if (hasStructuralSource(operand)) return true;
            }
            return false;
        }

        private boolean cfgLoopControlGuard(
                Collection<Map<String, Object>> guards) {
            for (Map<String, Object> guard : guards) {
                if (Boolean.TRUE.equals(booleanValue(
                        guard.get("loopControlGuard")))) {
                    return true;
                }
            }
            return false;
        }

        private boolean structureCarrierGuard(
                Collection<Map<String, Object>> guards) {
            for (String operand : operandCells(guards)) {
                if (containerRole(incoming, "fromCell", operand).equals(
                        DependencyRole.CONCRETE_STRUCTURE_CARRIER)) {
                    return true;
                }
            }
            return false;
        }

        private boolean loopRecurrence(
                String site, Collection<Map<String, Object>> guards) {
            for (Map<String, Object> guard : guards) {
                String guardSite = first(text(guard.get("guardSiteId")),
                        text(guard.get("siteId")));
                if (!site.equals(guardSite)) continue;
                if (Boolean.TRUE.equals(booleanValue(
                        guard.get("sameCellRedefinition")))) {
                    return true;
                }
                for (Map<String, Object> definition
                        : rows(guard.get("controlledDefinitions"))) {
                    if (Boolean.TRUE.equals(booleanValue(
                            definition.get("sameCellRedefinition")))) {
                        return true;
                    }
                }
            }
            return false;
        }

        private boolean hasStructuralSource(String start) {
            Set<String> visitedEdges = new LinkedHashSet<>();
            boolean[] structural = new boolean[1];
            StaticProgram.closure(Collections.singletonList(start), cell -> {
                List<String> sources = new ArrayList<>();
                for (Map<String, Object> edge : incoming.getOrDefault(
                        cell, Collections.<Map<String, Object>>emptyList())) {
                    String identity = first(text(edge.get("id")),
                            text(edge.get("siteId")) + "\n"
                                    + text(edge.get("fromCell")) + "\n"
                                    + text(edge.get("toCell")));
                    if (!visitedEdges.add(identity)
                            || "GUARD".equals(text(
                            edge.get("transferKind")))) {
                        continue;
                    }
                    String invoke = text(edge.get("invoke"));
                    if (JavaContainerTypes
                            .structuralIterationPredicate(invoke)
                            || JavaContainerTypes
                            .structuralCardinalityOperation(invoke)
                            || Boolean.TRUE.equals(booleanValue(
                            edge.get("arrayLengthOperation")))) {
                        structural[0] = true;
                        return null;
                    }
                    String predecessor = text(edge.get("fromCell"));
                    if (!predecessor.isEmpty()) sources.add(predecessor);
                }
                return sources;
            });
            return structural[0];
        }
    }

    private static boolean exactLocalPass(Map<String, Object> edge) {
        return "local_def_use".equals(text(edge.get("kind")))
                && ("VALUE_PASS".equals(text(edge.get("transferKind")))
                || !text(edge.get("valueFlowAuthority")).isEmpty());
    }

    /** Every writer the trace observed for each demanded shared-field read. */
    static List<Map<String, Object>> fieldFlows(
            List<Map<String, Object>> regions,
            Set<String> demandedFields) throws IOException {
        // Reads state the demand, so they are collected first under the plain
        // resource default; the writes are then filtered relative to each
        // read and the latest preceding access of each writer port is kept.
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(reads, text(region.get("regionId")),
                    rows(region.get("symbolicInputs")), NO_ACCESS_DEMAND);
        }
        reads.removeIf(port -> !demandedFields.contains(
                port.leafDeclaration()));
        RuntimeAccessDemand demand = leafReceiverDemand(reads);
        Map<String, List<BoundPort>> writesByReceiverAndField =
                writesByReceiverLeaf(regions, demand,
                        write -> demandedFields.contains(
                                write.leafDeclaration()));
        return latestWriterFlows(reads, writesByReceiverAndField,
                (write, read) -> sameActivation(write, read)
                        || write.seq >= read.seq
                        || (read.valueObject > 0 || write.valueObject > 0)
                        && read.valueObject != write.valueObject
                        || DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(
                        read.dependencyRole)
                        && !"CONTAINER_MUTATION".equals(write.bindingKind)
                        && read.valueObject <= 0,
                (write, read) -> {
                    Map<String, Object> edge = fieldFlowEdge(write, read,
                            "", "RF.");
                    if ("CONTAINER_MUTATION".equals(write.bindingKind)) {
                        edge.put("writerFieldReadSeq",
                                write.writerFieldReadSeq);
                        edge.put("mutatorEnterSeq", write.mutatorEnterSeq);
                        edge.put("mutationCompletionSeq",
                                write.mutationCompletionSeq);
                        edge.put("mutationInvocationId",
                                write.mutationInvocationId);
                        edge.put("mutatorDeclaredCallee",
                                write.mutatorDeclaredCallee);
                        edge.put("readerValueObjectId",
                                write.atomicValueProjection
                                        ? read.receiver
                                        : read.evidenceValueObject);
                    }
                    return edge;
                });
    }

    /**
     * Keeps an exact reference-field conduit when its writer occurrence had
     * already received a configured symbolic component.
     */
    /**
     * Binds a still-unclosed demanded leaf to the region that actually wrote
     * it.
     */
    static List<Map<String, Object>> demandedLeafProducerFlows(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges) throws IOException {
        Set<String> closedInputs = closedInputPorts(regionEdges);
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            // Only a semantic scalar leaf is at stake here.
            List<Map<String, Object>> leaves = new ArrayList<>();
            for (Map<String, Object> port
                    : rows(region.get("symbolicInputs"))) {
                if (primitiveLeaf(port)) leaves.add(port);
            }
            collectPorts(reads, regionId, leaves, NO_ACCESS_DEMAND);
        }
        reads.removeIf(read -> read.receiver == 0
                || read.leafDeclaration().isEmpty()
                || DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(
                read.dependencyRole)
                || closedInputs.contains(portDemandKey(read.occurrenceId,
                read.port)));
        // The producing write is activation-local to a long-lived root, so
        // the trace may record it far past the resource default; demanding it
        // by receiver and leaf is what keeps it visible here.
        RuntimeAccessDemand demand = leafReceiverDemand(reads);
        Map<String, List<BoundPort>> writesByReceiverAndField =
                writesByReceiverLeaf(regions, demand, write -> true);
        return latestWriterFlows(reads, writesByReceiverAndField,
                (write, read) -> sameActivation(write, read)
                        || write.seq >= read.seq,
                (write, read) -> fieldFlowEdge(write, read,
                        LEAF_PRODUCER_AUTHORITY, "RF.LEAF."));
    }

    /** The cross-run identity of the read leaf: its owner and its name. */
    private static String recordedFieldKey(BoundPort read) {
        DeclaredFieldCell field = DeclaredFieldCell.parse(
                read.leafDeclaration());
        return field == null ? ""
                : RecordedReadFrom.fieldKey(field.owner, field.name);
    }

    /** Renders one write/read pair as a runtime field-flow candidate edge. */
    private static Map<String, Object> fieldFlowEdge(
            BoundPort write, BoundPort read, String authority,
            String edgeIdPrefix) {
        String alternative = write.occurrenceId + "\n" + write.port
                + "\n" + write.site
                + "\n" + write.occurrence + "\n" + read.occurrenceId
                + "\n" + read.port
                + "\n" + read.site + "\n" + read.occurrence;
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind", "RUNTIME_FIELD_FLOW");
        edge.put("transportKind", "HEAP");
        if (!authority.isEmpty()) {
            edge.put("authority", authority);
        }
        edge.put("edgeId", CausynthStaticFacts.nameId(edgeIdPrefix,
                alternative));
        edge.put("fromRegion", write.region);
        edge.put("toRegion", read.region);
        edge.put("fromPort", write.port);
        edge.put("toPort", read.port);
        edge.put("fromOccurrenceId", write.occurrenceId);
        edge.put("toOccurrenceId", read.occurrenceId);
        // Recorded trace evidence for the observed endpoints; selection and
        // identity above are by occurrence only.
        edge.put("fromRootCallId", write.rootCallId);
        edge.put("toRootCallId", read.rootCallId);
        edge.put("receiverObjectId", write.receiver);
        edge.put("valueObjectId", write.evidenceValueObject);
        edge.put("primitiveValue", write.primitiveValue);
        edge.put("writerEventSeq", write.seq);
        edge.put("readerEventSeq", read.seq);
        edge.put("bindingKind", write.bindingKind);
        edge.put("dependencyRole", read.dependencyRole);
        edge.put("fieldPathDeclarations", Collections.singletonList(
                write.leafDeclaration()));
        // The join address this candidate will be resolved under, and the
        // state it is in.
        edge.put(RecordedReadFrom.EDGE_FIELD, recordedFieldKey(read));
        edge.put(RecordedReadFrom.EDGE_SOURCE_KEY, read.sourceKey);
        edge.put(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        edge.put(RecordedReadFrom.EDGE_PROVENANCE_GAP,
                SharedStateEvidence.reason(
                        SharedStateEvidence.NOT_SELECTED));
        return edge;
    }

    /** Names the leaf-producer binding for downstream manifest tracing. */
    static final String LEAF_PRODUCER_AUTHORITY =
            "RUNTIME_FIELD_FLOW_LEAF_PRODUCER_V1";

    private static Set<String> failureRelevantFields(StaticProgram program) {
        List<Map<String, Object>> graph = program.refinedGraph;
        Set<String> targetRegions = new LinkedHashSet<>();
        Set<String> selectedRegions = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            selectedRegions.add(text(region.get("regionId")));
            if (text(region.get("selection")).startsWith("EXCEPTION")) {
                targetRegions.add(text(region.get("regionId")));
            }
        }
        Map<String, List<Map<String, Object>>> localIncoming =
                new LinkedHashMap<>();
        Set<String> observedSelectedReads = new LinkedHashSet<>();
        List<String> seeds = new ArrayList<>();
        for (Map<String, Object> edge : graph) {
            String from = text(edge.get("fromCell"));
            if ("HEAP_READ".equals(text(edge.get("transferKind")))
                    && StaticProgram.declaredField(from)) {
                for (Map<String, Object> binding
                        : rows(edge.get("runtimeFieldBindings"))) {
                    if (selectedRegions.contains(
                            text(binding.get("regionId")))) {
                        observedSelectedReads.add(from);
                        break;
                    }
                }
            }
            String to = text(edge.get("toCell"));
            if (to.isEmpty()) continue;
            for (String region : strings(edge.get("regionIds"))) {
                if (!selectedRegions.contains(region)) continue;
                localIncoming.computeIfAbsent(contextKey(region, to),
                        ignored -> new ArrayList<>()).add(edge);
                if (targetRegions.contains(region)
                        && to.contains("#exception:")) {
                    seeds.add(contextKey(region, to));
                }
            }
        }
        Set<String> fields = new LinkedHashSet<>();
        // The region a cell was reached in is the first half of its key, so
        // one walk over region-local cells answers for every region at once.
        StaticProgram.closure(seeds, key -> {
            String region = key.substring(0, key.indexOf('\n'));
            List<String> next = new ArrayList<>();
            for (Map<String, Object> edge : localIncoming.getOrDefault(key,
                    Collections.<Map<String, Object>>emptyList())) {
                String from = text(edge.get("fromCell"));
                if ("HEAP_READ".equals(text(edge.get("transferKind")))
                        && StaticProgram.declaredField(from)) {
                    fields.add(from);
                }
                if (!from.isEmpty()) next.add(contextKey(region, from));
            }
            return next;
        });
        // Communication output components deliberately carry no static
        // inputPorts: their live expression is a VM handoff, not a Java
        // equality.
        fields.addAll(observedSelectedReads);
        Set<String> dynamicallyDefined = new LinkedHashSet<>();
        for (Map<String, Object> edge : graph) {
            String field = text(edge.get("toCell"));
            if ("HEAP_WRITE".equals(text(edge.get("transferKind")))
                    && StaticProgram.declaredField(field)) {
                // Constructor writes are ordinary definitions of the
                // constructed object's scalar leaves.
                dynamicallyDefined.add(field);
                String atomicValue = atomicMutationValueField(field,
                        first(text(edge.get("mutatorDeclaredCallee")),
                                text(edge.get("invoke"))));
                if (!atomicValue.isEmpty()) {
                    dynamicallyDefined.add(atomicValue);
                }
            }
        }
        fields.retainAll(dynamicallyDefined);
        fields.removeIf(RuntimeSelectedRegionFinalizer
                ::toolBookkeepingField);
        return fields;
    }

    /**
     * Heap owned by an injected Causynth support class is tracing metadata,
     * never application shared state.
     */
    private static boolean toolBookkeepingPort(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        if (declarations.isEmpty()) {
            String cell = text(port.get("cell"));
            if (StaticProgram.declaredField(cell)) declarations.add(cell);
        }
        if (declarations.isEmpty()) return false;
        for (String declaration : declarations) {
            if (!toolBookkeepingField(declaration)) return false;
        }
        return true;
    }

    private static boolean toolBookkeepingField(String declaration) {
        DeclaredFieldCell field = DeclaredFieldCell.parse(declaration);
        if (field == null) return false;
        String owner = field.owner;
        int packageEnd = owner.lastIndexOf('.');
        String simple = packageEnd < 0 ? owner
                : owner.substring(packageEnd + 1);
        return simple.startsWith("Causynth");
    }

    private static String contextKey(String region, String cell) {
        return region + "\n" + cell;
    }

    private static boolean sameActivation(BoundPort left,
                                          BoundPort right) {
        return left.occurrenceId.equals(right.occurrenceId);
    }

    /** Ports that read or write one declared field of one observed object. */
    private static boolean causalHeapPort(Map<String, Object> port) {
        if ("HEAP".equals(text(port.get("transportKind")))) return true;
        return "ACCESSOR_RETURN".equals(text(port.get("sourceKind")))
                && number(port.get("fieldReceiverObjectId"), 0) > 0
                && !strings(port.get("fieldPathDeclarations")).isEmpty();
    }

    private static void collectPorts(List<BoundPort> target, String region,
                                     List<Map<String, Object>> ports,
                                     RuntimeAccessDemand demand)
            throws IOException {
        for (Map<String, Object> port : ports) {
            if (!causalHeapPort(port)) {
                continue;
            }
            List<Map<String, Object>> accesses = boundedRuntimeAccesses(
                    port, demand);
            if (accesses.isEmpty()) {
                accesses = Collections.singletonList(port);
            }
            for (Map<String, Object> access : accesses) {
                SemanticHeapAddress address = semanticHeapAddress(
                        port, access);
                target.add(new BoundPort(region, text(port.get("portId")),
                        first(text(access.get("sourceKey")),
                                text(port.get("sourceKey"))),
                        first(text(access.get("occurrenceId")),
                                text(port.get("occurrenceId"))),
                        longNumber(access.get("rootCallId"),
                                longNumber(port.get("rootCallId"), 0L)),
                        address.receiver,
                        longNumber(access.get("eventSeq"),
                                longNumber(port.get("eventSeq"), 0L)),
                        address.declarations,
                        address.valueObject,
                        address.evidenceValueObject,
                        address.atomicValueProjection,
                        first(text(access.get("primitiveValue")),
                                text(port.get("primitiveValue"))),
                        first(text(access.get("bindingKind")),
                                text(port.get("bindingKind"))),
                        longNumber(access.get("writerFieldReadSeq"), -1L),
                        longNumber(access.get("mutatorEnterSeq"), -1L),
                        longNumber(access.get("mutationCompletionSeq"), -1L),
                        longNumber(access.get("mutationInvocationId"), -1L),
                        first(text(access.get("mutatorDeclaredCallee")),
                                text(port.get("mutatorDeclaredCallee"))),
                        DependencyRole.normalize(
                                port.get("dependencyRole")),
                        first(text(access.get("staticAccessSiteId")),
                                text(port.get("portId"))),
                        number(access.get(
                                "activationLocalStaticSiteOccurrence"),
                                1)));
            }
        }
    }

    /**
     * Gives a supported Atomic arithmetic mutation the same semantic heap
     * address as an accessor of the Atomic's primitive value. The trace keeps
     * the outer field receiver as provenance, while {@code valueObjectId}
     * identifies the concrete Atomic instance whose state changed.
     */
    private static SemanticHeapAddress semanticHeapAddress(
            Map<String, Object> port, Map<String, Object> access) {
        int receiver = number(access.get("fieldReceiverObjectId"),
                number(port.get("fieldReceiverObjectId"), 0));
        List<String> declarations = strings(
                access.containsKey("fieldPathDeclarations")
                        ? access.get("fieldPathDeclarations")
                        : port.get("fieldPathDeclarations"));
        int valueObject = number(access.get("valueObjectId"),
                number(port.get("valueObjectId"), 0));
        String bindingKind = first(text(access.get("bindingKind")),
                text(port.get("bindingKind")));
        String declaredCallee = first(
                text(access.get("mutatorDeclaredCallee")),
                text(port.get("mutatorDeclaredCallee")));
        String atomicValue = "CONTAINER_MUTATION".equals(bindingKind)
                && !declarations.isEmpty()
                ? atomicMutationValueField(
                declarations.get(declarations.size() - 1), declaredCallee)
                : "";
        if (!atomicValue.isEmpty() && valueObject > 0
                && !declarations.isEmpty()) {
            FieldPathSpec.DeclaredField leaf =
                    FieldPathSpec.declaredField(atomicValue);
            if (leaf != null) {
                List<String> semanticDeclarations =
                        new ArrayList<>(declarations);
                semanticDeclarations.add(leaf.signature());
                return new SemanticHeapAddress(valueObject,
                        semanticDeclarations, 0, valueObject, true);
            }
        }
        return new SemanticHeapAddress(receiver, declarations, valueObject,
                valueObject, false);
    }

    /** Primitive value field summarized by a supported Atomic mutation. */
    private static String atomicMutationValueField(
            String carrierDeclaration, String declaredCallee) {
        String atomicValue = OutputCaptureSpec
                .atomicArithmeticValueFieldSignature(declaredCallee);
        FieldPathSpec.DeclaredField carrier =
                FieldPathSpec.declaredField(carrierDeclaration);
        FieldPathSpec.DeclaredField leaf =
                FieldPathSpec.declaredField(atomicValue);
        return carrier != null && leaf != null
                && carrier.type().equals(leaf.owner())
                ? leaf.signature() : "";
    }

    /**
     * Assigns a replay-stable occurrence within one activation and static
     * access site.
     */
    private interface RuntimeAccessDemand {
        boolean required(Map<String, Object> port, Map<String, Object> access);
    }

    /** Nothing is demanded yet; only the resource default applies. */
    private static final RuntimeAccessDemand NO_ACCESS_DEMAND =
            (port, access) -> false;

    /**
     * Resource ceiling on the accesses one static site may contribute to one
     * port.
     */
    static final int MAX_RETAINED_SITE_ACCESSES = 64;

    /**
     * Keeps a bounded, demand-aware view of one port's recorded accesses. Such
     * a port keeps only the plain resource default and carries the refusal by
     * name, so the leaves below it stay under-approximated and the reason
     * travels with the artifact instead of ending the whole refinement over
     * one hot site.
     */
    private static List<Map<String, Object>> boundedRuntimeAccesses(
            Map<String, Object> port, RuntimeAccessDemand demand)
            throws IOException {
        List<Map<String, Object>> accesses = new ArrayList<>(
                rows(port.get("runtimeAccesses")));
        sortByEventSeq(accesses);
        Map<String, Integer> occurrences = new LinkedHashMap<>();
        Map<String, Integer> retained = new LinkedHashMap<>();
        List<Map<String, Object>> bounded = new ArrayList<>();
        List<Map<String, Object>> resourceDefault = new ArrayList<>();
        String refusal = "";
        for (Map<String, Object> access : accesses) {
            String site = first(text(access.get("staticAccessSiteId")),
                    text(port.get("portId")));
            int occurrence = occurrences.getOrDefault(site, 0) + 1;
            occurrences.put(site, occurrence);
            access.put("staticAccessSiteId", site);
            access.put("activationLocalStaticSiteOccurrence", occurrence);
            boolean withinDefault =
                    occurrence <= LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
            if (withinDefault) resourceDefault.add(access);
            if (!withinDefault && !demand.required(port, access)) continue;
            int kept = retained.getOrDefault(site, 0) + 1;
            retained.put(site, kept);
            if (kept > MAX_RETAINED_SITE_ACCESSES) {
                if (refusal.isEmpty()) {
                    refusal = "BOUND_INSUFFICIENT: static site " + site
                            + " demands more than " + MAX_RETAINED_SITE_ACCESSES
                            + " activation-local accesses";
                }
                continue;
            }
            bounded.add(access);
        }
        if (!refusal.isEmpty()) return resourceDefault;
        return bounded;
    }

    /**
     * Demands exactly the writes that could answer a collected read: the same
     * receiver object and the same declared leaf.
     */
    private static RuntimeAccessDemand leafReceiverDemand(
            List<BoundPort> reads) {
        Set<String> demanded = new LinkedHashSet<>();
        Set<String> demandedReferenceValues = new LinkedHashSet<>();
        for (BoundPort read : reads) {
            if (read.receiver != 0 && !read.leafDeclaration().isEmpty()) {
                String location = read.receiver + "\n"
                        + read.leafDeclaration();
                demanded.add(location);
                if (read.valueObject > 0) {
                    demandedReferenceValues.add(location + "\n"
                            + read.valueObject);
                }
            }
        }
        return (port, access) -> {
            SemanticHeapAddress address = semanticHeapAddress(port, access);
            if (address.receiver == 0 || address.declarations.isEmpty()) {
                return false;
            }
            String location = address.receiver + "\n"
                    + address.declarations.get(
                    address.declarations.size() - 1);
            return address.valueObject > 0
                    ? demandedReferenceValues.contains(location + "\n"
                    + address.valueObject)
                    : demanded.contains(location);
        };
    }

    private static void requireRefinedGraph(
            List<Map<String, Object>> rows, File source) throws IOException {
        if (rows.isEmpty()) {
            throw new IOException("refined graph is empty: " + source);
        }
        for (Map<String, Object> row : rows) {
            if (number(row.get("schemaVersion"), -1) != 3
                    || number(row.get("refinementSchemaVersion"), -1) != 1
                    || !REFINED_KIND.equals(text(row.get("graphKind")))) {
                throw new IOException("full region planning requires a "
                        + "schema-3 runtime-refined graph: " + source);
            }
        }
    }

    /** Recorded rows in observed order; unstamped rows sort last. */
    private static void sortByEventSeq(List<Map<String, Object>> rows) {
        rows.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
    }

    private static String first(String left, String right) {
        return left.isEmpty() ? right : left;
    }

    /**
     * Activation-local backward slices from demanded outputs (or a fatal
     * branch) to exact boundary input ports.
     */
    private static final class RegionDemandIndex {
        private final Map<String, Map<String, Object>> inputs =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Object>> outputs =
                new LinkedHashMap<>();
        private final Map<String, List<String>> inputsByInstance =
                new LinkedHashMap<>();
        /** Static region scope of each indexed activation occurrence. */
        private final Map<String, String> regionByOccurrence =
                new LinkedHashMap<>();
        private final Map<String, List<String>> inputsByBoundary =
                new LinkedHashMap<>();
        private final Map<String, List<String>>
                boundedMutationFrontiersByOutput = new LinkedHashMap<>();
        private final Map<String, List<String>> localIncoming =
                new LinkedHashMap<>();
        /** Control predecessors remain live when value flow hits a port. */
        private final Map<String, List<String>> guardIncoming =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                explicitFatalSeedsBySite = new LinkedHashMap<>();
        private final Map<String, List<String>> fatalSeeds =
                new LinkedHashMap<>();
        /**
         * inputsForOutput is a pure function of the frozen index; the union
         * walk and every per-target closure walk repeat the same demands, so
         * each backward walk is computed once.
         */
        private final Map<String, List<String>> inputsForOutputCache =
                new LinkedHashMap<>();
        private final Map<Map<String, Object>, List<String>>
                targetInputsCache = new java.util.IdentityHashMap<>();

        private RegionDemandIndex(
                List<Map<String, Object>> regions,
                List<Map<String, Object>> graph) {
            Set<String> selectedRegions = new LinkedHashSet<>();
            for (Map<String, Object> region : regions) {
                String regionId = text(region.get("regionId"));
                selectedRegions.add(regionId);
                for (Map<String, Object> input
                        : rows(region.get("symbolicInputs"))) {
                    indexPort(regionId, input, false);
                }
                for (Map<String, Object> output
                        : rows(region.get("outputs"))) {
                    indexPort(regionId, output, true);
                }
                for (Map<String, Object> branch
                        : rows(region.get("branchPolicies"))) {
                    String site = text(branch.get("siteId"));
                    if (site.isEmpty() || !Boolean.TRUE.equals(booleanValue(
                            branch.get("failureTarget")))) {
                        continue;
                    }
                    List<String> seeds = explicitFatalSeedsBySite
                            .computeIfAbsent(regionId,
                                    ignored -> new LinkedHashMap<>())
                            .computeIfAbsent(site,
                                    ignored -> new ArrayList<>());
                    for (String operand : strings(
                            branch.get("operandCells"))) {
                        if (!seeds.contains(operand)) seeds.add(operand);
                    }
                }
            }
            for (Map<String, Object> edge : graph) {
                String from = text(edge.get("fromCell"));
                String to = text(edge.get("toCell"));
                if (from.isEmpty() || to.isEmpty()) continue;
                for (String regionId : strings(edge.get("regionIds"))) {
                    if (!selectedRegions.contains(regionId)) continue;
                    addUnique(localIncoming, contextKey(regionId, to),
                            from);
                    if ("GUARD".equals(text(edge.get("transferKind")))) {
                        addUnique(guardIncoming, contextKey(regionId, to),
                                from);
                    }
                    // A generic exception cell is only a fallback for a region
                    // without an explicit failureTarget policy.
                    if (to.contains("#exception:")
                            && !explicitFatalSeedsBySite.containsKey(
                            regionId)) {
                        addUnique(fatalSeeds, regionId, to);
                    }
                }
            }
        }

        private void indexPort(String regionId, Map<String, Object> port,
                               boolean output) {
            String occurrenceId = text(port.get("occurrenceId"));
            String portId = text(port.get("portId"));
            if (occurrenceId.isEmpty() || portId.isEmpty()) return;
            regionByOccurrence.putIfAbsent(occurrenceId, regionId);
            String demand = portDemandKey(occurrenceId, portId);
            (output ? outputs : inputs).put(demand, port);
            if (output) return;
            addUnique(inputsByInstance, occurrenceId, demand);
            boolean structuredCommunicationParent =
                    COMMUNICATION_SITE_PORT.equals(
                            text(port.get("sourceKind")))
                            && !DependencyRole.valueFrontier(
                            port.get("dependencyRole"));
            if (!structuredCommunicationParent) {
                for (String cell : boundaryCells(port)) {
                    addUnique(inputsByBoundary,
                            instanceCellKey(occurrenceId, cell), demand);
                }
            }
            for (String outputCell : strings(
                    port.get("boundedMutationOutputCells"))) {
                addUnique(boundedMutationFrontiersByOutput,
                        instanceCellKey(occurrenceId, outputCell), demand);
            }
        }

        private boolean hasInput(String occurrenceId, String portId) {
            return inputs.containsKey(portDemandKey(occurrenceId, portId));
        }

        private boolean hasOutput(String occurrenceId, String portId) {
            return outputs.containsKey(portDemandKey(occurrenceId, portId));
        }

        /**
         * Every declared communication input observed before one demanded
         * production in the same occurrence.
         */
        private List<String> priorCommunicationInputs(
                String occurrenceId, long producedAt) {
            return instanceInputs(occurrenceId, port -> {
                if (!COMMUNICATION_SITE_PORT.equals(
                        text(port.get("sourceKind")))) {
                    return false;
                }
                long receivedAt = longNumber(port.get("eventSeq"), -1L);
                return producedAt < 0L || receivedAt < producedAt;
            });
        }

        /** The demanded input ports one activation actually holds. */
        private List<String> instanceInputs(String occurrenceId,
                Predicate<Map<String, Object>> keep) {
            List<String> result = new ArrayList<>();
            for (String demand : inputsByInstance.getOrDefault(occurrenceId,
                    Collections.<String>emptyList())) {
                Map<String, Object> port = inputs.get(demand);
                if (port != null && keep.test(port)) result.add(demand);
            }
            return result;
        }

        /** Exact observed value inputs before one demanded output. */
        private List<String> priorValueInputs(
                String occurrenceId, long producedAt) {
            if (producedAt < 0L) return Collections.emptyList();
            return instanceInputs(occurrenceId, port -> {
                if ("ACCESSOR_RETURN".equals(
                        text(port.get("sourceKind")))) {
                    long event = longNumber(port.get("eventSeq"), -1L);
                    return event >= 0L && event <= producedAt;
                }
                if (!"HEAP".equals(text(port.get("transportKind")))
                        || !DependencyRole.valueFrontier(
                        port.get("dependencyRole"))) {
                    return false;
                }
                for (Map<String, Object> access
                        : rows(port.get("runtimeAccesses"))) {
                    long event = longNumber(access.get("eventSeq"), -1L);
                    if (event >= 0L && event < producedAt) return true;
                }
                return false;
            });
        }

        private List<String> targetInputs(Map<String, Object> instance)
                throws IOException {
            List<String> cached = targetInputsCache.get(instance);
            if (cached != null) {
                return cached;
            }
            List<String> computed = computeTargetInputs(instance);
            targetInputsCache.put(instance, computed);
            return computed;
        }

        /**
         * Activation-local evidence that this activation reached one of the
         * explicit {@code failureTarget} sites of its region, grouped by site.
         */
        private Map<String, List<Map<String, Object>>> observedFatalEvidence(
                Map<String, Object> instance) {
            Map<String, List<Map<String, Object>>> evidenceBySite =
                    new LinkedHashMap<>();
            Map<String, List<String>> explicit = explicitFatalSeedsBySite.get(
                    text(instance.get("regionId")));
            if (explicit == null || explicit.isEmpty()) {
                return evidenceBySite;
            }
            for (Map<String, Object> evidence
                    : rows(instance.get("observedFatalTargets"))) {
                if (!"OBSERVED_FATAL_TARGET".equals(
                        text(evidence.get("kind")))
                        || !"EXACT_RUNTIME_BRANCH_SITE_V1".equals(
                        text(evidence.get("evidenceAuthority")))
                        || !(evidence.get("observedOutcome")
                        instanceof Boolean)) {
                    continue;
                }
                String site = text(evidence.get("siteId"));
                if (explicit.containsKey(site)) {
                    evidenceBySite.computeIfAbsent(site,
                            ignored -> new ArrayList<>()).add(evidence);
                }
            }
            return evidenceBySite;
        }

        /**
         * Whether this activation qualifies as an exception-context closure
         * target. README {@code TARGET-1} binds target existence to the
         * selected concrete branch event, so this is one question about
         * observed evidence and never about the shape of the plan: a region
         * without an explicit {@code failureTarget} policy declares no site to
         * attest, which makes every one of its activations a target with no
         * branch evidence at all - exactly the freely-true target the item
         * forbids.
         */
        private boolean observedExplicitFatalTarget(
                Map<String, Object> instance) {
            return !observedFatalEvidence(instance).isEmpty();
        }

        /** Whether this activation's region declares a fatal target site. */
        private boolean declaresExplicitFatalTarget(
                Map<String, Object> instance) {
            Map<String, List<String>> explicit = explicitFatalSeedsBySite.get(
                    text(instance.get("regionId")));
            return explicit != null && !explicit.isEmpty();
        }

        private List<String> computeTargetInputs(
                Map<String, Object> instance) throws IOException {
            String regionId = text(instance.get("regionId"));
            String occurrenceId = text(instance.get("occurrenceId"));
            Map<String, List<String>> explicit =
                    explicitFatalSeedsBySite.get(regionId);
            if (explicit != null && !explicit.isEmpty()) {
                // Selection above already required this evidence; keeping the
                // check here keeps the slice fail-closed for any other caller.
                Map<String, List<Map<String, Object>>> evidenceBySite =
                        observedFatalEvidence(instance);
                if (evidenceBySite.isEmpty()) {
                    throw new IOException("exception-context activation did "
                            + "not observe its explicit fatal target branch: "
                            + occurrenceId);
                }
                Set<String> retained = new LinkedHashSet<>();
                List<Map<String, Object>> contexts = new ArrayList<>();
                for (Map.Entry<String, List<Map<String, Object>>> entry
                        : evidenceBySite.entrySet()) {
                    List<Map<String, Object>> occurrences = entry.getValue();
                    sortByEventSeq(occurrences);
                    int selectedIndex = selectedFatalOccurrence(occurrences);
                    Map<String, Object> selected = occurrences.get(
                            selectedIndex);
                    long cutoff = longNumber(selected.get("eventSeq"), -1L);
                    if (cutoff < 0L) {
                        throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: "
                                + "observed fatal target has no eventSeq: "
                                + occurrenceId + " " + entry.getKey());
                    }
                    List<String> inputs = retainFatalPrefixInputs(instance,
                            backwardInputs(occurrenceId,
                                    explicit.get(entry.getKey())), cutoff);
                    retained.addAll(inputs);
                    Map<String, Object> context = new LinkedHashMap<>();
                    context.put("schemaVersion", 1);
                    context.put("authority",
                            "EXACT_FATAL_BRANCH_OCCURRENCE_PREFIX_V1");
                    context.put("siteId", entry.getKey());
                    context.put("occurrence", selectedIndex + 1);
                    context.put("eventSeq", cutoff);
                    context.put("observedOutcome",
                            selected.get("observedOutcome"));
                    if (selected.get("requiredOutcome") instanceof Boolean) {
                        context.put("requiredOutcome",
                                selected.get("requiredOutcome"));
                    }
                    List<String> ports = new ArrayList<>();
                    for (String demand : inputs) {
                        Map<String, Object> port = this.inputs.get(demand);
                        String portId = port == null ? ""
                                : text(port.get("portId"));
                        if (!portId.isEmpty()) ports.add(portId);
                    }
                    context.put("inputPorts", ports);
                    contexts.add(context);
                }
                instance.put("fatalPrefixContexts", contexts);
                return new ArrayList<>(retained);
            }
            List<String> seeds = fatalSeeds.getOrDefault(regionId,
                    Collections.<String>emptyList());
            if (seeds.isEmpty()) {
                // Returning every observed input of the activation instead
                // made the target slice the whole occurrence, which is the
                // free target README TARGET-1 forbids: nothing in it is bound
                // to a decided lookup or branch event.
                throw new IOException("FATAL_TARGET_SEED_GAP: region names "
                        + "no failure target site and no exception cell: "
                        + regionId + " " + occurrenceId);
            }
            return backwardInputs(occurrenceId, seeds);
        }

        /** Same occurrence rule as Scheduler.TargetBranch.select. */
        private int selectedFatalOccurrence(
                List<Map<String, Object>> occurrences) {
            for (int index = 0; index < occurrences.size(); index++) {
                Map<String, Object> occurrence = occurrences.get(index);
                Object required = occurrence.get("requiredOutcome");
                Object observed = occurrence.get("observedOutcome");
                if (required instanceof Boolean
                        && observed instanceof Boolean
                        && required.equals(observed)) {
                    return index;
                }
            }
            return 0;
        }

        /**
         * A static backward slice says which boundary ports may feed the fatal
         * predicate; the exact trace says which of those ports existed when
         * that predicate was reached.
         */
        private List<String> retainFatalPrefixInputs(
                Map<String, Object> instance, List<String> candidates,
                long fatalEventSeq) throws IOException {
            List<String> retained = new ArrayList<>();
            List<String> missingEvidence = new ArrayList<>();
            for (String demand : candidates) {
                Map<String, Object> port = inputs.get(demand);
                if (port == null) continue;
                // Structural owners remain concrete replay support.
                if (!DependencyRole.valueFrontier(
                        port.get("dependencyRole"))) {
                    retained.add(demand);
                    continue;
                }
                int evidence = fatalPrefixEvidence(port, fatalEventSeq);
                if (evidence > 0) {
                    retained.add(demand);
                } else if (evidence == 0) {
                    missingEvidence.add(text(port.get("portId")));
                }
            }
            if (!missingEvidence.isEmpty()) {
                throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: target "
                        + text(instance.get("occurrenceId"))
                        + " has demanded ports without exact runtime order: "
                        + missingEvidence);
            }
            return retained;
        }

        /**
         * Whether this port was observed at or before the fatal event
         * ({@code 1}), only after it ({@code -1}), or never ({@code 0}).
         */
        private int fatalPrefixEvidence(
                Map<String, Object> port, long fatalEventSeq) {
            List<Map<String, Object>> accesses = rows(
                    port.get("runtimeAccesses"));
            if (!accesses.isEmpty()) {
                List<Map<String, Object>> prefix = new ArrayList<>();
                boolean observed = false;
                boolean after = false;
                for (Map<String, Object> access : accesses) {
                    long event = longNumber(access.get("eventSeq"), -1L);
                    if (event < 0L) continue;
                    observed = true;
                    if (event <= fatalEventSeq) {
                        prefix.add(access);
                    } else {
                        after = true;
                    }
                }
                if (!prefix.isEmpty()) return 1;
                return observed && after ? -1 : 0;
            }
            // Accessor-return ports are emitted only from an exact runtime
            // binding and carry that occurrence directly on the port.
            if ("ACCESSOR_RETURN".equals(text(port.get("sourceKind")))
                    || COMMUNICATION_SITE_PORT.equals(
                    text(port.get("sourceKind")))
                    || EXPLICIT_SYMBOLIC_FAULT.equals(
                    text(port.get("sourceKind")))
                    || EXTERNAL_CALL_RETURN.equals(
                    text(port.get("sourceKind")))) {
                long event = longNumber(port.get("eventSeq"), -1L);
                if (event < 0L) return 0;
                return event <= fatalEventSeq ? 1 : -1;
            }
            return 0;
        }

        private List<String> inputsForOutput(String occurrenceId,
                                             String portId,
                                             long writerEventSeq) {
            String demand = portDemandKey(occurrenceId, portId);
            String occurrenceDemand = outputOccurrenceDemandKey(demand,
                    writerEventSeq);
            List<String> cached = inputsForOutputCache.get(
                    occurrenceDemand);
            if (cached != null) {
                return cached;
            }
            List<String> computed = computeInputsForOutput(occurrenceId,
                    portId);
            inputsForOutputCache.put(occurrenceDemand, computed);
            return computed;
        }

        private List<String> computeInputsForOutput(String occurrenceId,
                                             String portId) {
            String demand = portDemandKey(occurrenceId, portId);
            Map<String, Object> output = outputs.get(demand);
            if (output == null) return Collections.emptyList();
            Set<String> result = new LinkedHashSet<>(backwardInputs(
                    occurrenceId, boundaryCells(output)));
            if (containerMutationPort(output)) {
                for (String cell : mutationOutputCells(output)) {
                    result.addAll(boundedMutationFrontiersByOutput
                            .getOrDefault(instanceCellKey(occurrenceId, cell),
                                    Collections.<String>emptyList()));
                }
            }
            return new ArrayList<>(result);
        }

        /**
         * Walks the region's local dataflow backward from {@code seeds} to the
         * boundary ports of one activation.
         */
        private List<String> backwardInputs(String occurrenceId,
                                            Collection<String> seeds) {
            String regionId = regionByOccurrence.getOrDefault(
                    occurrenceId, "");
            Set<String> result = new LinkedHashSet<>();
            StaticProgram.closure(seeds, cell -> {
                if (cell.isEmpty()) return Collections.<String>emptyList();
                List<String> boundary = inputsByBoundary.getOrDefault(
                        instanceCellKey(occurrenceId, cell),
                        Collections.<String>emptyList());
                if (!boundary.isEmpty()) {
                    result.addAll(boundary);
                    // A value boundary stops value provenance, but not the
                    // guard deciding whether the consuming operation runs.
                    return guardIncoming.getOrDefault(
                            contextKey(regionId, cell),
                            Collections.<String>emptyList());
                }
                return localIncoming.getOrDefault(
                        contextKey(regionId, cell),
                        Collections.<String>emptyList());
            });
            return new ArrayList<>(result);
        }

        private static List<String> boundaryCells(
                Map<String, Object> port) {
            List<String> result = strings(port.get("dependencyCells"));
            if (result.isEmpty()) {
                String cell = text(port.get("cell"));
                if (!cell.isEmpty()) result.add(cell);
            }
            // A declared server response is captured at the semantic handler's
            // normal return.
            if (result.isEmpty()
                    && COMMUNICATION_SITE_PORT.equals(
                    text(port.get("sourceKind")))) {
                String cell = declaredCutPortCell(port);
                if (!cell.isEmpty()) result.add(cell);
            }
            return result;
        }

        private static String instanceCellKey(String occurrenceId,
                                              String cell) {
            return occurrenceId + "\nCELL\n" + cell;
        }

        private static void addUnique(Map<String, List<String>> target,
                                      String key, String value) {
            if (value.isEmpty()) return;
            List<String> values = target.computeIfAbsent(key,
                    ignored -> new ArrayList<>());
            if (!values.contains(value)) values.add(value);
        }
    }

    private static final class BoundPort {
        private final String region;
        private final String port;
        private final String sourceKey;
        /** Activation identity; the only activation discriminator here. */
        private final String occurrenceId;
        /** Recorded trace evidence republished on the emitted edge. */
        private final long rootCallId;
        private final int receiver;
        private final long seq;
        private final List<String> declarations;
        private final int valueObject;
        /** Reference identity retained while an Atomic join uses its leaf. */
        private final int evidenceValueObject;
        private final boolean atomicValueProjection;
        private final String primitiveValue;
        private final String bindingKind;
        private final long writerFieldReadSeq;
        private final long mutatorEnterSeq;
        private final long mutationCompletionSeq;
        private final long mutationInvocationId;
        private final String mutatorDeclaredCallee;
        private final String dependencyRole;
        private final String site;
        private final int occurrence;

        private BoundPort(String region, String port, String sourceKey,
                          String occurrenceId,
                          long rootCallId, int receiver, long seq,
                          List<String> declarations, int valueObject,
                          int evidenceValueObject,
                          boolean atomicValueProjection,
                          String primitiveValue, String bindingKind,
                          long writerFieldReadSeq, long mutatorEnterSeq,
                          long mutationCompletionSeq,
                          long mutationInvocationId,
                          String mutatorDeclaredCallee,
                          String dependencyRole, String site,
                          int occurrence) {
            this.region = region;
            this.port = port;
            this.sourceKey = sourceKey;
            this.occurrenceId = occurrenceId;
            this.rootCallId = rootCallId;
            this.receiver = receiver;
            this.seq = seq;
            this.declarations = declarations;
            this.valueObject = valueObject;
            this.evidenceValueObject = evidenceValueObject;
            this.atomicValueProjection = atomicValueProjection;
            this.primitiveValue = primitiveValue;
            this.bindingKind = bindingKind;
            this.writerFieldReadSeq = writerFieldReadSeq;
            this.mutatorEnterSeq = mutatorEnterSeq;
            this.mutationCompletionSeq = mutationCompletionSeq;
            this.mutationInvocationId = mutationInvocationId;
            this.mutatorDeclaredCallee = mutatorDeclaredCallee;
            this.dependencyRole = dependencyRole;
            this.site = site;
            this.occurrence = occurrence;
        }

        private String leafDeclaration() {
            return declarations.isEmpty() ? ""
                    : declarations.get(declarations.size() - 1);
        }

    }

    /** Canonical runtime address used only to join observed heap accesses. */
    private static final class SemanticHeapAddress {
        private final int receiver;
        private final List<String> declarations;
        private final int valueObject;
        private final int evidenceValueObject;
        private final boolean atomicValueProjection;

        private SemanticHeapAddress(int receiver,
                                    List<String> declarations,
                                    int valueObject,
                                    int evidenceValueObject,
                                    boolean atomicValueProjection) {
            this.receiver = receiver;
            this.declarations = declarations;
            this.valueObject = valueObject;
            this.evidenceValueObject = evidenceValueObject;
            this.atomicValueProjection = atomicValueProjection;
        }
    }

    private static final class DeclaredFieldCell {
        private static final Set<String> PRIMITIVES = new LinkedHashSet<>(
                Arrays.asList("boolean", "byte", "short", "char",
                        "int", "long", "float", "double"));
        /** Declaring class, which with the name is the cross-run identity. */
        private final String owner;
        private final String type;
        private final String name;

        private DeclaredFieldCell(String owner, String type, String name) {
            this.owner = owner;
            this.type = type;
            this.name = name;
        }

        private boolean primitive() {
            return PRIMITIVES.contains(type);
        }

        private static DeclaredFieldCell parse(String cell) {
            String value = text(cell).trim();
            if (!StaticProgram.declaredField(value)) return null;
            int colon = value.indexOf(':');
            int separator = value.lastIndexOf(' ', value.length() - 2);
            if (colon < 1 || separator <= colon + 1) return null;
            String owner = value.substring(1, colon).trim();
            String type = value.substring(colon + 1, separator).trim();
            String name = value.substring(separator + 1,
                    value.length() - 1).trim();
            return type.isEmpty() || name.isEmpty() ? null
                    : new DeclaredFieldCell(owner, type, name);
        }
    }

    private static final class ClosureWalk {
        private final Set<String> reached;
        private final Set<String> retainedEdges;
        private final Set<String> demandedInputs;
        private final Set<String> demandedOutputs;

        private ClosureWalk(Set<String> reached, Set<String> retainedEdges,
                            Set<String> demandedInputs,
                            Set<String> demandedOutputs) {
            this.reached = reached;
            this.retainedEdges = retainedEdges;
            this.demandedInputs = demandedInputs;
            this.demandedOutputs = demandedOutputs;
        }
    }

    public static final class Result {
        /** Finalized region rows exactly as written to the artifact. */
        public final List<Map<String, Object>> regions;
        /** Canonicalized region edges exactly as written to the artifact. */
        public final List<Map<String, Object>> regionEdges;
        private Result(List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges) {
            this.regions = regions;
            this.regionEdges = regionEdges;
        }
    }
}
