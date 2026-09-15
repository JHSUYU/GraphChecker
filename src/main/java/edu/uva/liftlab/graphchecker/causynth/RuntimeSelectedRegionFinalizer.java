package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DependencyRole;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceBinding;
import edu.uva.liftlab.graphchecker.plan.SiteId;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Predicate;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.booleanValue;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.firstNonEmpty;
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

    /**
     * Existing planner admission vocabulary for a bounded state writer.  Why
     * this activation is in the plan at all, when it is there for anything
     * other than reaching the fatal target: the planner publishes it on the
     * occurrence's plan row so a reader of the frozen artifact can tell a
     * demanded state writer from a target-reachable region.
     */
    public static final String ADMISSION_BASIS = "admissionBasis";
    private static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    /**
     * Which shared locations a demand admission was asked for.  Published on
     * the plan row beside {@link #ADMISSION_BASIS} so a reader of the frozen
     * artifact can tell which location bought each admission, rather than
     * having to re-derive it from the retained edges.
     */
    /**
     * How many shared-location demand hops separate this admission from the
     * fatal target.  A writer the failure closure's own port demand asked for
     * is one hop; a writer asked for only because an already admitted
     * occurrence reads the location is one hop further out.  Published on
     * the plan row beside {@link #ADMISSION_BASIS}: it is the only place the
     * frozen artifact records how far a demand travelled, and it cannot be
     * reconstructed from the retained edges, which carry port demand and
     * protocol closure as well as this rule's hops.
     *
     * <p>It is the shortest demand chain that reached the admission, not a
     * statement about the configured bound, and it can exceed that bound: an
     * admission the failure closure's own port demand asked for is made
     * whatever the bound says, and is then labelled with the chain it sits
     * on.  Only {@code transitiveSharedLocationDemand} refuses a hop, so a
     * row deeper than the bound is a first-order admission and not evidence
     * that the bound leaked.
     */
    public static final String DEMAND_DEPTH = "demandDepth";
    /** The fatal target is the origin of every shared-location demand. */
    private static final int TARGET_DEMAND_DEPTH = 0;
    /** Communication ports whose exact export/attach sites need hooks. */
    public static final String COMMUNICATION_PORTS = "communicationPorts";

    /** {@code IN} or {@code OUT}: which catalog a declared port belongs in. */
    public static final String REGION_PORT_SIDE = "regionPortSide";
    /** {@code sourceKind} of a port that carries a value across a call. */
    public static final String COMMUNICATION_SITE_PORT =
            "COMMUNICATION_SITE_PORT";
    /** Exact IN/OUT cut captures observed inside one runtime activation. */
    public static final String OBSERVED_COMMUNICATION_CAPTURES =
            "observedCommunicationCaptures";
    /** Region-row member carrying the retained loops of its methods. */
    public static final String RETAINED_LOOPS = "retainedLoops";
    /** Schema every region skeleton row and its refined row are stated in. */
    public static final int REGION_SCHEMA_VERSION = 3;
    /** {@code kind} of one planned region skeleton row. */
    public static final String SKELETON_KIND = "REGION_SKELETON";
    /** Gap code: several activations, one occurrence address. */
    /** Activation member listing the root calls that share its address. */
    public static final String SHARED_ADDRESS_ROOT_CALLS =
            "sharedAddressRootCallIds";

    private RuntimeSelectedRegionFinalizer() {
    }

    /**
     * Finalizes the selected runtime graph using the occurrence links already
     * produced by the runtime planner.  Those links are scheduling evidence;
     * symbolic values still cross only through VM VALUE_HANDOFF edges.
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph,
            List<StaticProgram.RegionRow> selectedSkeletons,
            String skeletonSource, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeObservations,
            Collection<Map<String, Object>> runtimeOccurrenceLinks)
            throws IOException {
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }

        StaticProgram program = new StaticProgram();
        program.refinedGraph = graph;
        for (StaticProgram.RegionRow skeleton : selectedSkeletons) {
            program.skeletons.put(skeleton.regionId, skeleton);
        }

        // Activation identity is read off the trace before the first port of
        // a region is built.
        Map<String, List<Map<String, Object>>> targetPoliciesByRegion =
                new LinkedHashMap<>();
        for (Map.Entry<String, StaticProgram.RegionRow> entry
                : program.skeletons.entrySet()) {
            if (!selectedRegion(entry.getValue(), observed)) continue;
            targetPoliciesByRegion.put(entry.getKey(), failureTargetPolicies(
                    program.regionGraph(entry.getKey())));
        }
        List<Map<String, Object>> branchOrder = orderedBranchObservations(
                runtimeObservations);
        Map<String, String> occurrenceByRecordedRootCall =
                readOccurrences(program, runtimeInstances, skeletonSource);

        for (Map.Entry<String, StaticProgram.RegionRow> entry
                : program.skeletons.entrySet()) {
            String regionId = entry.getKey();
            StaticProgram.RegionRow skeleton = entry.getValue();
            if (!selectedRegion(skeleton, observed)) {
                continue;
            }
            Map<String, Object> region = new LinkedHashMap<>();
            region.put("schemaVersion", 3);
            region.put("kind", "SYMBOLIC_REGION");
            region.put("graphKind", REFINED_KIND);
            region.put("regionId", regionId);
            region.put("rootMethod", skeleton.rootMethod);
            if (!skeleton.rootAuthority.isEmpty()) {
                region.put("rootAuthority", skeleton.rootAuthority);
            }
            // The once-only-root rule: a service loop's iteration, not the
            // one entry above it, is the activation this region describes.
            Map<String, Object> rootLoop = program.loopBodyRoot(skeleton,
                    program.regionActivations(regionId), branchOrder);
            if (rootLoop != null) {
                region.put("rootAuthority", LoopBoundPolicy.LOOP_BODY_ROOT);
                region.put(LoopBoundPolicy.ROOT_LOOP, rootLoop);
            }
            region.put("anchorMethod", skeleton.anchorMethod);
            if (skeleton.json.containsKey("anchorMethods")) {
                region.put("anchorMethods",
                        skeleton.json.get("anchorMethods"));
            }
            region.put("selection", skeleton.selection);
            region.put("methods", new ArrayList<>(skeleton.methods));
            // The refined row is built fresh, so anything the skeleton carries
            // has to be carried over by name.
            for (String carried : new String[]{RETAINED_LOOPS,
                    StaticSymbolicSourceDeclaration.FIELD,
                    ConfiguredSourcePhaseContract.DECLARATION_FIELD}) {
                Object value = skeleton.json.get(carried);
                if (value != null) region.put(carried, value);
            }

            List<Map<String, Object>> regionGraph =
                    program.regionGraph(regionId);
            List<Map<String, Object>> outputs = statePorts(program,
                    regionId, "HEAP_WRITE", "OUT",
                    occurrenceByRecordedRootCall);
            outputs.removeIf(RuntimeSelectedRegionFinalizer
                    ::toolBookkeepingPort);
            List<Map<String, Object>> branchPolicies = branches(program,
                    regionId);
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
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
            region.put("branchPolicies", branchPolicies);
            program.regions.add(region);
        }
        bindObservedFatalTargets(program.regions, runtimeInstances,
                branchOrder);
        Set<String> demandedFields = failureRelevantFields(program);
        List<Map<String, Object>> runtimeFieldFlows = fieldFlows(
                program.regions, demandedFields, program.planGaps);
        program.regionEdges.addAll(runtimeFieldFlows);
        stampEdgeOccurrences(program.regionEdges,
                occurrenceByRecordedRootCall);
        // The declarations are static and the occurrence-owned copies below
        // are dynamic, so this remains a typed-port join rather than a value
        // or payload guess.  applyClosure removes every declaration and edge
        // not reached by the target-directed walk; the declaration pass after
        // it restores only the region-level catalog rows used downstream.
        Map<String, List<CutPort>> cutPorts = declaredCutPorts(program);
        declareCommunicationPorts(program, cutPorts);
        program.regionEdges.addAll(recordedOccurrenceProducerFlows(
                program, runtimeOccurrenceLinks));
        // One index over the region catalog: the occurrence-owned ports are
        // stamped above, so the frontier pass and the closure walk read the
        // same declaration table.
        RegionDemandIndex demands = new RegionDemandIndex(program.regions,
                program.refinedGraph);
        ClosureWalk closure = failureDirectedClosure(program, demands,
                skeletonSource);
        program.regionEdges.addAll(retainExactRequestFaultControls(
                program, closure, runtimeOccurrenceLinks));
        applyClosure(program, closure);
        // Declared last, and deliberately after the closure filter.
        declareCommunicationPorts(program, cutPorts);
        canonicalizeRegionEdges(program);
        return new Result(program.regions, program.regionEdges,
                program.planGaps);
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

    /** One declared cut port of one region, built once from its skeleton. */
    private static final class CutPort {
        private final String side;
        private final String portId;
        private final Map<String, Object> row;

        private CutPort(String side, String portId,
                        Map<String, Object> row) {
            this.side = side;
            this.portId = portId;
            this.row = row;
        }
    }

    /**
     * The cut ports every region declares, derived once.  The closure filter
     * drops the region-level declarations it cannot reach, so the catalog is
     * published again after it from this same table rather than rebuilt.
     */
    private static Map<String, List<CutPort>> declaredCutPorts(
            StaticProgram program) {
        Map<String, List<CutPort>> byRegion = new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : program.skeletons.values()) {
            List<CutPort> ports = new ArrayList<>();
            for (Map<String, Object> port : skeleton.communicationPorts) {
                String portId = text(port.get("portId"));
                if (portId.isEmpty()) {
                    continue;
                }
                Map<String, Object> row = new LinkedHashMap<>(port);
                row.remove(REGION_PORT_SIDE);
                Set<String> cells = callReturnValueCells(
                        program.regionGraph(skeleton.regionId), row);
                if (cells.size() == 1) {
                    row.put("dependencyCells", new ArrayList<>(cells));
                }
                ports.add(new CutPort(text(port.get(REGION_PORT_SIDE)),
                        portId, row));
            }
            if (!ports.isEmpty()) byRegion.put(skeleton.regionId, ports);
        }
        return byRegion;
    }

    /** Publishes the ports of every cut this region holds a side of. */
    private static void declareCommunicationPorts(StaticProgram program,
            Map<String, List<CutPort>> declaredByRegion) {
        for (Map<String, Object> region : program.regions) {
            List<CutPort> declared = declaredByRegion.get(
                    text(region.get("regionId")));
            if (declared == null) {
                continue;
            }
            List<Map<String, Object>> inputs = rows(
                    region.get("symbolicInputs"));
            List<Map<String, Object>> outputs = rows(region.get("outputs"));
            // A cut has one region-level declaration and zero or more
            // occurrence-owned instances of that declaration.
            Set<String> inputIds = declaredPortIds(inputs);
            Set<String> outputIds = declaredPortIds(outputs);
            for (CutPort port : declared) {
                if ("IN".equals(port.side)) {
                    if (inputIds.add(port.portId)) {
                        inputs.add(new LinkedHashMap<>(port.row));
                    }
                } else if ("OUT".equals(port.side)) {
                    if (outputIds.add(port.portId)) {
                        outputs.add(new LinkedHashMap<>(port.row));
                    }
                }
            }
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
        }
    }

    /** The value cell one declared cut port's capture names, or {@code ""}. */
    public static String declaredCutPortCell(Map<String, Object> port) {
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
    static List<Map<String, Object>> recordedOccurrenceProducerFlows(
            StaticProgram program,
            Collection<Map<String, Object>> occurrenceLinks) {
        Map<String, Map<String, Object>> activationsById =
                program.activationsByActivationId();
        Map<String, Map<String, Object>> regionsById = program.regionsById();
        Map<String, Map<Long, Integer>> captureOrdinals =
                communicationCaptureOrdinals(activationsById.values());
        List<Map<String, Object>> flows = new ArrayList<>();
        Set<String> emitted = new LinkedHashSet<>();
        // The wire transaction one exchange ran on -- Hadoop's IPC client id
        // and call number, or a SASL negotiation uuid -- is minted fresh by
        // the workload in every run.  It correlates a request with its own
        // response and is kept for that, but it cannot name the edge: an
        // ordinal counted per producing and consuming occurrence, port and
        // direction says which exchange this is in terms the next recording
        // of the same obligation reproduces.
        Map<String, Map<String, Integer>> exchangeOrdinals =
                new LinkedHashMap<>();
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
            String exchangeLeg = text(link.get("exchangeLeg"));
            long senderEventSeq = longNumber(
                    link.get("senderEventSeq"), -1L);
            long receiverEventSeq = longNumber(
                    link.get("receiverEventSeq"), -1L);
            Map<TypedReceiver, Set<Integer>> matches = new LinkedHashMap<>();
            Map<String, Map<Integer, Set<String>>> receiversByPortOrdinal =
                    new LinkedHashMap<>();
            for (TypedReceiver receiver : receivers) {
                String portId = text(receiver.port.get("portId"));
                Set<Integer> sent = observedCommunicationCaptureOrdinals(
                        from, "OUT", portId, exchangeLeg, senderEventSeq,
                        captureOrdinals);
                Set<Integer> received = observedCommunicationCaptureOrdinals(
                        receiver.activation, "IN", portId, exchangeLeg,
                        receiverEventSeq, captureOrdinals);
                received.retainAll(sent);
                matches.put(receiver, received);
                for (Integer ordinal : received) {
                    receiversByPortOrdinal.computeIfAbsent(portId,
                                    ignored -> new LinkedHashMap<>())
                            .computeIfAbsent(ordinal,
                                    ignored -> new LinkedHashSet<>())
                            .add(text(receiver.activation.get(
                                    "activationId")));
                }
            }
            for (TypedReceiver receiver : receivers) {
                Map<String, Object> exactTo = receiver.activation;
                Map<String, Object> toRegion = receiver.region;
                Map<String, Object> receiving = receiver.port;
                String portId = text(receiving.get("portId"));
                Map<String, Object> sending = declaredOutputPort(fromRegion,
                        portId);
                Set<Integer> matched = matches.getOrDefault(receiver,
                        Collections.<Integer>emptySet());
                boolean exactCapture = false;
                for (Integer ordinal : matched) {
                    if (receiversByPortOrdinal.getOrDefault(portId,
                                    Collections.<Integer, Set<String>>emptyMap())
                            .getOrDefault(ordinal,
                                    Collections.<String>emptySet()).size()
                            == 1) {
                        exactCapture = true;
                        break;
                    }
                }
                if (!exactCapture) {
                    continue;
                }
                String exchangeSite = occurrenceKey(
                        from.get("occurrenceId")) + "\n"
                        + occurrenceKey(exactTo.get("occurrenceId"))
                        + "\n" + portId + "\n" + direction;
                String identity = exchangeSite + "\n"
                        + exchangeOrdinal(exchangeOrdinals, exchangeSite,
                        text(link.get("requestKey")) + "\n" + exchangeLeg);
                if (!emitted.add(identity)) continue;
                stampOccurrenceOwnedPort(fromRegion, "outputs", sending,
                        occurrenceKey(from.get("occurrenceId")),
                        longNumber(link.get("senderEventSeq"), -1L));
                stampOccurrenceOwnedPort(toRegion, "symbolicInputs",
                        receiving, occurrenceKey(
                                exactTo.get("occurrenceId")),
                        longNumber(link.get("receiverEventSeq"), -1L));
                flows.add(exchangeProducerEdge(from, exactTo, link,
                        receiving, identity));
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

    /**
     * Capture ordinals carried by one exact logical delivery.
     *
     * <p>The transport may emit several physical frames for one exchange.
     * The capture binder deliberately associates an input with the first
     * frame that carried the value, while the handler occurrence link may be
     * bracketed by a later frame of that same exchange.  The exchange leg and
     * activation are the identities here; both recorded boundaries only need
     * to be on the causal side of the capture.</p>
     */
    static Set<Integer> observedCommunicationCaptureOrdinals(
            Map<String, Object> activation, String side, String portId,
            String exchangeLeg, long transportEventSeq,
            Map<String, Map<Long, Integer>> captureOrdinals) {
        Set<Integer> result = new LinkedHashSet<>();
        if (exchangeLeg.isEmpty() || transportEventSeq < 0L) return result;
        for (Map<String, Object> capture : rows(activation.get(
                OBSERVED_COMMUNICATION_CAPTURES))) {
            long capturedAt = longNumber(capture.get("eventSeq"), -1L);
            long capturedBoundary = longNumber(
                    capture.get("transportEventSeq"), -1L);
            if (side.equals(text(capture.get("side")))
                    && portId.equals(text(capture.get("portId")))
                    && exchangeLeg.equals(text(capture.get("exchangeLeg")))
                    && capturedBoundary >= 0L
                    && ("OUT".equals(side)
                    ? capturedAt >= 0L && capturedBoundary > capturedAt
                    && transportEventSeq > capturedAt
                    : capturedAt > capturedBoundary
                    && capturedAt > transportEventSeq)) {
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
    /**
     * The structural key of one planned occurrence, or {@code ""} for none.
     *
     * <p>These joins decide which rows belong to one occurrence, and they did
     * it by string equality on {@code occurrenceId}.  That is correct exactly
     * while every id they see is a planned address; it silently merges two
     * activations the moment one carries an {@code #a<n>} suffix, because the
     * address deliberately drops the suffix and the string does not.  So the
     * key is now parsed and re-rendered, and a value that does not spell one
     * planned address is refused rather than joined on.</p>
     *
     * <p>Byte-neutral today: every {@code occurrenceId} the region graph
     * carries is a planned address (505 of 505 in lane BC's
     * {@code concolic_region_plan.jsonl}), so the rendered key is the string
     * it parsed.  The value is that the two can no longer drift apart in
     * silence.</p>
     */
    static String occurrenceKey(Object encoded) {
        String occurrenceId = text(encoded);
        if (occurrenceId.isEmpty()) return "";
        String rendered;
        try {
            rendered = OccurrenceAddress.parse(occurrenceId).render();
        } catch (RuntimeException notAnAddress) {
            throw new IllegalArgumentException("region graph occurrence id "
                    + "is not one planned address: " + occurrenceId,
                    notAnAddress);
        }
        if (!rendered.equals(occurrenceId)) {
            throw new IllegalArgumentException("region graph occurrence id "
                    + "is not one planned address: " + occurrenceId);
        }
        return rendered;
    }

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
                    occurrenceKey(existing.get("occurrenceId")))) {
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

    /**
     * Which exchange of one producing/consuming occurrence pair this is.
     *
     * <p>Counts the distinct wire transactions seen at {@code exchangeSite}
     * in recorded order and answers the same ordinal every time one
     * transaction is offered again, so a retry and its original keep the
     * numbers they were first given.</p>
     */
    static int exchangeOrdinal(
            Map<String, Map<String, Integer>> ordinals, String exchangeSite,
            String transaction) {
        Map<String, Integer> perSite = ordinals.computeIfAbsent(exchangeSite,
                ignored -> new LinkedHashMap<>());
        Integer existing = perSite.get(transaction);
        if (existing != null) return existing;
        int assigned = perSite.size() + 1;
        perSite.put(transaction, assigned);
        return assigned;
    }

    /** One scheduling candidate for a recorded delivery of a declared port. */
    private static Map<String, Object> exchangeProducerEdge(
            Map<String, Object> from, Map<String, Object> to,
            Map<String, Object> link, Map<String, Object> receiving,
            String identity) {
        String portId = text(receiving.get("portId"));
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
     * The node this activation ran on, as its own ADDRESS states it.
     *
     * <p>A component of the occurrence address the recording computed, read
     * back out of it -- not a second reading of the trace rows.  Every
     * activation in the program has an address ({@link #readOccurrences}
     * refuses one that has none), so a string here that is not an address is
     * a corrupt seed and says so by throwing.</p>
     */
    private static String activationSourceKey(Map<String, Object> instance) {
        return instance == null
                ? OccurrenceBinding.UNREGISTERED_SOURCE_KEY
                : edu.uva.liftlab.graphchecker.contract.OccurrenceAddress
                        .parse(text(instance.get("occurrenceId")))
                        .node().render();
    }

    /**
     * Reads the occurrence address of every observed region activation and
     * stamps it onto every row the recorded root call named.
     *
     * <p>READS.  The address was computed once, by {@code
     * Identity.occurrence}, at the entry the recording woved it at, and a
     * replay of the same occurrence computes the same string with the same
     * function; an offline re-derivation here would be a second identity,
     * and the two disagreed on 44 activations of hdfs-17960 (REPORT-M2
     * §5).</p>
     *
     * <p>Two activations may still land on one address -- nothing IDENTITY-V3
     * names separates them (same node, same region, same context, same
     * index).  They are published under that one address and the collision
     * is stated as a named diagnostic gap; their rows keep their own events,
     * and the declared selector's {@code k} picks among them in seed order.
     * Renumbering them would be an ordinal, which is what v3 exists to
     * remove.</p>
     *
     * @return every recorded root call, by the occurrence it belongs to
     */
    private static Map<String, String> readOccurrences(
            StaticProgram program,
            Collection<Map<String, Object>> runtimeInstances,
            String source) throws IOException {
        Map<String, String> occurrenceByRecordedRootCall =
                new LinkedHashMap<>();
        Map<String, List<Long>> rootCallsByAddress = new LinkedHashMap<>();
        for (Map<String, Object> instance : canonicalRuntimeActivations(
                runtimeInstances, source)) {
            String regionId = text(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            String occurrenceId = text(instance.get("occurrenceAddress"));
            if (occurrenceId.isEmpty()) {
                throw new IOException("runtime region activation states no "
                        + "occurrence address, so the recording computed "
                        + "none for it: " + regionId + "\n" + rootCallId);
            }
            instance.put("occurrenceId", occurrenceId);
            occurrenceByRecordedRootCall.put(
                    recordedRootCallKey(regionId, rootCallId), occurrenceId);
            rootCallsByAddress.computeIfAbsent(occurrenceId,
                    ignored -> new ArrayList<>()).add(rootCallId);
            program.activations.putIfAbsent(occurrenceId, instance);
        }
        for (Map.Entry<String, List<Long>> entry
                : rootCallsByAddress.entrySet()) {
            if (entry.getValue().size() < 2) continue;
            program.activations.get(entry.getKey()).put(
                    SHARED_ADDRESS_ROOT_CALLS, entry.getValue());
            planGap(program.planGaps, GapKind.OCCURRENCE_ADDRESS_SHARED,
                    GapClass.DIAGNOSTIC,
                    entry.getKey(), entry.getValue().size() + " activations "
                            + "of this region share one address: nothing "
                            + "IDENTITY-V3 names distinguishes them (same "
                            + "node, causal context and execution index); "
                            + "recorded root calls " + entry.getValue()
                            + "; a declared selector's k picks among them in "
                            + "seed order");
        }
        return occurrenceByRecordedRootCall;
    }

    /** Canonical activation records at the trace-aggregation boundary. */
    private static List<Map<String, Object>> canonicalRuntimeActivations(
            Collection<Map<String, Object>> runtimeInstances, String source)
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
    private static boolean selectedRegion(StaticProgram.RegionRow skeleton,
                                          Set<String> observed) {
        return !skeleton.methods.isEmpty()
                && (observed.isEmpty()
                || !Collections.disjoint(skeleton.methods, observed));
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
            result.add(policy);
        }
        return result;
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

            Set<Long> calls = MapFields.longValues(
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
            StaticProgram program, RegionDemandIndex demands, String source)
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
        // Hop count per admitted occurrence, seeded on the fatal target(s).
        // It is written by the two admission rules below and read by the
        // transitive rule, which refuses a hop past the configured bound.
        Map<String, Integer> demandDepths = new LinkedHashMap<>();
        for (String target : targets) {
            demandDepths.put(target, TARGET_DEMAND_DEPTH);
        }
        // The locations transitive demand may travel through, decided once
        // per finalization off the runtime-refined graph.
        Set<String> caredLocations = caredSharedLocations(
                program.refinedGraph);
        Set<String> admittedStateWriters = new LinkedHashSet<>(
                admitSharedLocationWriters(targets, instances, demands,
                        program.regionEdges, demandDepths));

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

        // Shared reads an admitted occurrence holds that no port demand asked
        // for yet.  They are the second-order demand: the target demands one
        // location, the occurrence admitted to write it reads a location of
        // its own, and that read stays a single INITIAL arm pinned to its
        // recorded constant until the writers on its own node are demanded
        // too.  Seeding them into the walk is what makes the read a
        // multi-writer GuardedRead, so the seeds and the admission below grow
        // together to one fixed point.
        Set<String> transitiveDemands = new LinkedHashSet<>();
        ClosureWalk union = walkFailureClosure(targets, instances,
                demands, predecessors, targetInteractionInputs,
                requestFlowPrefixInputs, admittedStateWriters,
                transitiveDemands);
        // Heap demand is transitive with port demand: each walk may reach a
        // producer that itself reads a written location, so admit the writers
        // of what this walk demanded and walk again.
        while (true) {
            Map<String, Integer> depthsBefore =
                    new LinkedHashMap<>(demandDepths);
            boolean grown = admittedStateWriters.addAll(admitWritersOfDemands(
                    union.reached, union.demandedInputs, instances,
                    program.regionEdges, demandDepths, targets,
                    caredLocations));
            grown |= transitiveDemands.addAll(transitiveSharedLocationDemand(
                    union.reached, union.demandedInputs, instances,
                    program.regionEdges, demandDepths, caredLocations));
            // A round that only shortened a demand chain still restates the
            // hop counts the rows publish.  Depths never rise and the
            // occurrence set is finite, so answering that round terminates.
            grown |= !depthsBefore.equals(demandDepths);
            if (!grown) break;
            union = walkFailureClosure(targets, instances, demands,
                    predecessors, targetInteractionInputs,
                    requestFlowPrefixInputs, admittedStateWriters,
                    transitiveDemands);
        }
        return union;
    }

    /**
     * Retains an explicit fault decision only when its exact request
     * transaction already supplies a response value used by the selected
     * failure closure.  The resulting edge is scheduling evidence; it states
     * no value equality and therefore carries no IN/OUT value ports.
     */
    private static List<Map<String, Object>> retainExactRequestFaultControls(
            StaticProgram program, ClosureWalk walk,
            Collection<Map<String, Object>> occurrenceLinks) {
        List<Map<String, Object>> controls = exactRequestFaultControlEdges(
                program, walk.retainedEdges, occurrenceLinks);
        for (Map<String, Object> control : controls) {
            String from = text(control.get("fromOccurrenceId"));
            String to = text(control.get("toOccurrenceId"));
            String edgeId = text(control.get("edgeId"));
            String portId = text(control.get("faultPortId"));
            if (!from.isEmpty()) walk.reached.add(from);
            if (!to.isEmpty()) walk.reached.add(to);
            if (!edgeId.isEmpty()) walk.retainedEdges.add(edgeId);
            if (!from.isEmpty() && !portId.isEmpty()) {
                walk.demandedInputs.add(portDemandKey(from, portId));
            }
        }
        return controls;
    }

    /** Package-visible proof constructor used by the focused contract test. */
    static List<Map<String, Object>> exactRequestFaultControlEdges(
            StaticProgram program, Collection<String> retainedEdgeIds,
            Collection<Map<String, Object>> occurrenceLinks) {
        Set<String> retained = new LinkedHashSet<>(retainedEdgeIds == null
                ? Collections.<String>emptyList() : retainedEdgeIds);
        Set<String> targetInputProducerSources =
                targetRequestProducerSources(program, retained);
        Set<String> fatalSharedLocationWriters =
                fatalSharedLocationWriters(program, retained);
        if (targetInputProducerSources.isEmpty()
                && fatalSharedLocationWriters.isEmpty()) {
            return Collections.emptyList();
        }
        Map<String, Map<String, Object>> activationsById =
                program.activationsByActivationId();
        Map<String, Map<String, Object>> regions = program.regionsById();
        List<Map<String, Object>> requestLinks = new ArrayList<>();
        for (Map<String, Object> link : occurrenceLinks == null
                ? Collections.<Map<String, Object>>emptyList()
                : occurrenceLinks) {
            if ("RECORDED_EXCHANGE_OCCURRENCE_LINK_V1".equals(
                    text(link.get("authority")))
                    && "REQUEST".equals(
                    text(link.get("direction")).toUpperCase())
                    && !exchangeTransaction(link.get("exchangeLeg"))
                    .isEmpty()) {
                requestLinks.add(link);
            }
        }

        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (Map<String, Object> response : program.regionEdges) {
            if (!retained.contains(text(response.get("edgeId")))
                    || !"RUNTIME_PROTOCOL_FLOW".equals(
                    text(response.get("kind")))
                    || !"RESPONSE".equals(
                    text(response.get("direction")).toUpperCase())) {
                continue;
            }
            String transaction = exchangeTransaction(
                    response.get("exchangeLeg"));
            String requestKey = text(response.get("requestKey"));
            String consumerOccurrence = text(
                    response.get("toOccurrenceId"));
            Map<String, Object> consumer = program.activations.get(
                    consumerOccurrence);
            if (transaction.isEmpty() || requestKey.isEmpty()
                    || consumer == null) {
                continue;
            }
            String consumerSource = activationSourceKey(consumer);
            long responseSend = longNumber(
                    response.get("senderEventSeq"), -1L);
            long responseReceive = longNumber(
                    response.get("receiverEventSeq"), -1L);
            if (consumerSource.isEmpty()
                    || OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(
                    consumerSource) || responseSend < 0L
                    || responseReceive <= responseSend) {
                continue;
            }
            for (Map<String, Object> link : requestLinks) {
                if (!transaction.equals(exchangeTransaction(
                        link.get("exchangeLeg")))
                        || !requestKey.equals(text(link.get("requestKey")))
                        || !sameOptionalValue(link, "requestApi",
                        response, "requestApi")
                        || !sameOptionalValue(link, "transport",
                        response, "transportKind")
                        || !sameOptionalValue(link, "attemptId",
                        response, "attemptId")) {
                    continue;
                }
                Map<String, Object> fault = activationsById.get(
                        text(link.get("fromActivationId")));
                if (fault == null
                        || !"EXPLICIT_FAULT_ENTRY".equals(
                        text(fault.get("rootAuthority")))
                        || !consumerSource.equals(
                        activationSourceKey(fault))) {
                    continue;
                }
                // Two admission rules, either of which states a control on
                // the observed failure.  The first is the upstream one: the
                // failed request's node produced the value the target
                // checked.  The second is the target's own side: the failed
                // request's response is what writes -- through the recorded
                // heap chain -- a shared location the fatal read depends on,
                // so idling it leaves that location at the arm the recording
                // wrote before the request.  The same-node test above holds
                // for both: a request is only failable where it is sent.
                if (!targetInputProducerSources.contains(
                        activationSourceKey(fault))
                        && !fatalSharedLocationWriters.contains(
                        consumerOccurrence)) {
                    continue;
                }
                String faultOccurrence = occurrenceKey(
                        fault.get("occurrenceId"));
                Map<String, Object> faultRegion = regions.get(
                        text(fault.get("regionId")));
                long requestSend = longNumber(
                        link.get("senderEventSeq"), -1L);
                long requestReceive = longNumber(
                        link.get("receiverEventSeq"), -1L);
                if (faultOccurrence.isEmpty() || faultRegion == null
                        || requestSend < 0L
                        || requestReceive <= requestSend
                        || requestReceive >= responseSend) {
                    continue;
                }
                for (Map<String, Object> port : rows(
                        faultRegion.get("symbolicInputs"))) {
                    long faultEvent = longNumber(port.get("eventSeq"), -1L);
                    String portOccurrence = occurrenceKey(
                            port.get("occurrenceId"));
                    if (!EXPLICIT_SYMBOLIC_FAULT.equals(
                            text(port.get("sourceKind")))
                            || !faultOccurrence.equals(portOccurrence)
                            || faultEvent <= requestSend
                            || faultEvent >= requestReceive) {
                        continue;
                    }
                    Map<String, Object> edge = requestFaultControlEdge(
                            fault, consumer, port, link, response,
                            transaction, consumerSource, faultEvent,
                            requestSend, requestReceive, responseSend,
                            responseReceive);
                    unique.putIfAbsent(text(edge.get("edgeId")), edge);
                }
            }
        }
        return new ArrayList<>(unique.values());
    }

    /**
     * Sources that supplied a demanded request value directly to an observed
     * failure target.  This is the first of the two request-control admission
     * rules: a fault on one of these nodes controls the upstream value the
     * target is checking.
     *
     * <p>It is not the only way a request failure controls the failure.  A
     * target predicate that compares an incoming value against target-local
     * state has that state as its other operand, and the target's own
     * state-maintenance traffic is what writes it.  That case is admitted by
     * {@link #fatalSharedLocationWriters} instead, so neither rule has to
     * admit every successful request that happened to touch the target.</p>
     */
    private static Set<String> targetRequestProducerSources(
            StaticProgram program, Set<String> retainedEdgeIds) {
        Set<String> result = new LinkedHashSet<>();
        for (Map<String, Object> edge : program.regionEdges) {
            if (!retainedEdgeIds.contains(text(edge.get("edgeId")))
                    || !"RUNTIME_PROTOCOL_FLOW".equals(
                    text(edge.get("kind")))
                    || !"REQUEST".equals(
                    text(edge.get("direction")).toUpperCase())
                    || !DependencyRole.valueFrontier(
                    edge.get("dependencyRole"))) {
                continue;
            }
            Map<String, Object> target = program.activations.get(
                    text(edge.get("toOccurrenceId")));
            Map<String, Object> producer = program.activations.get(
                    text(edge.get("fromOccurrenceId")));
            if (target == null || producer == null
                    || !text(target.get("selection"))
                    .startsWith("EXCEPTION")
                    || rows(target.get("observedFatalTargets")).isEmpty()) {
                continue;
            }
            String sourceKey = activationSourceKey(producer);
            if (!sourceKey.isEmpty()
                    && !OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(
                    sourceKey)) {
                result.add(sourceKey);
            }
        }
        return result;
    }

    /**
     * Occurrences whose recorded delivery lands on the write chain the fatal
     * read depends on.
     *
     * <p>Walks the retained heap flow backwards from the observed failure
     * target.  Every {@code RUNTIME_FIELD_FLOW} edge the closure kept names
     * one shared location the reader demanded and one occurrence that wrote
     * it, so the transitive closure of those edges is exactly the recorded
     * write chain behind the fatal read, and nothing else on the node.</p>
     *
     * <p>A response delivered into a member of this set maintains the other
     * operand of the failure's own predicate -- a membership test such as
     * {@code allKeys.get(id) == null} reads the container the delivery
     * fills.  Idling that delivery therefore leaves the location at the arm
     * the recording wrote before the request, which is a control on the
     * failure in the same sense as controlling the checked value is.  The
     * demand is read off the recording, so a request whose response writes
     * nothing the fatal read depends on stays out.</p>
     */
    private static Set<String> fatalSharedLocationWriters(
            StaticProgram program, Set<String> retainedEdgeIds) {
        Map<String, Set<String>> writersByReader = new LinkedHashMap<>();
        for (Map<String, Object> edge : program.regionEdges) {
            if (!retainedEdgeIds.contains(text(edge.get("edgeId")))
                    || !"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))
                    || text(edge.get(SharedFieldFlow.EDGE_LOCATION))
                    .isEmpty()) {
                continue;
            }
            String reader = text(edge.get("toOccurrenceId"));
            String writer = text(edge.get("fromOccurrenceId"));
            if (reader.isEmpty() || writer.isEmpty()
                    || reader.equals(writer)) {
                continue;
            }
            writersByReader.computeIfAbsent(reader,
                    ignored -> new LinkedHashSet<>()).add(writer);
        }
        Deque<String> pending = new ArrayDeque<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : program.activations.entrySet()) {
            Map<String, Object> activation = entry.getValue();
            if (!text(activation.get("selection")).startsWith("EXCEPTION")
                    || rows(activation.get("observedFatalTargets"))
                    .isEmpty()) {
                continue;
            }
            pending.addLast(entry.getKey());
        }
        Set<String> writers = new LinkedHashSet<>();
        while (!pending.isEmpty()) {
            for (String writer : writersByReader.getOrDefault(
                    pending.removeFirst(),
                    Collections.<String>emptySet())) {
                if (writers.add(writer)) pending.addLast(writer);
            }
        }
        return writers;
    }

    private static Map<String, Object> requestFaultControlEdge(
            Map<String, Object> fault, Map<String, Object> consumer,
            Map<String, Object> port, Map<String, Object> request,
            Map<String, Object> response, String transaction,
            String sourceKey, long faultEvent, long requestSend,
            long requestReceive, long responseSend, long responseReceive) {
        // The response edge already names this exchange from content, and it
        // names it more exactly than the wire transaction does: one logical
        // request can be retried on several transactions and each attempt has
        // its own response edge.  The transaction itself is the workload's
        // per-run IPC id, so it is evidence on the edge and not part of its
        // name.
        String identity = occurrenceKey(fault.get("occurrenceId")) + "\n"
                + text(port.get("portId")) + "\n"
                + occurrenceKey(consumer.get("occurrenceId")) + "\n"
                + text(response.get("edgeId"));
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind",
                AutomaticRegionEdge.RUNTIME_REQUEST_CONTROL_EDGE_KIND);
        edge.put("edgeId", CausynthStaticFacts.nameId("CTRL.", identity));
        edge.put("fromRegion", fault.get("regionId"));
        edge.put("toRegion", consumer.get("regionId"));
        edge.put("fromOccurrenceId", fault.get("occurrenceId"));
        edge.put("toOccurrenceId", consumer.get("occurrenceId"));
        edge.put("fromRootCallId", fault.get("rootCallId"));
        edge.put("toRootCallId", consumer.get("rootCallId"));
        edge.put("faultPortId", port.get("portId"));
        edge.put("symbolicName", port.get("symbolicName"));
        edge.put("sourceKey", sourceKey);
        edge.put("consumerSourceKey", sourceKey);
        edge.put("requestKey", request.get("requestKey"));
        edge.put("requestApi", request.get("requestApi"));
        edge.put("transportKind", request.get("transport"));
        edge.put("attemptId", request.get("attemptId"));
        edge.put("exchangeTransaction", transaction);
        edge.put("faultEventSeq", faultEvent);
        edge.put("requestSenderEventSeq", requestSend);
        edge.put("requestReceiverEventSeq", requestReceive);
        edge.put("responseSenderEventSeq", responseSend);
        edge.put("responseReceiverEventSeq", responseReceive);
        edge.put("controlledResponseEdgeId", response.get("edgeId"));
        edge.put("dependencyRole",
                DependencyRole.CONCRETE_STRUCTURE_CARRIER);
        edge.put("correlationAuthority",
                AutomaticRegionEdge.EXACT_REQUEST_FAULT_CONTROL_AUTHORITY);
        edge.put("authority",
                AutomaticRegionEdge.EXACT_REQUEST_FAULT_CONTROL_AUTHORITY);
        return edge;
    }

    private static boolean sameOptionalValue(
            Map<String, Object> left, String leftField,
            Map<String, Object> right, String rightField) {
        String leftValue = text(left.get(leftField));
        String rightValue = text(right.get(rightField));
        return leftValue.isEmpty() || rightValue.isEmpty()
                || leftValue.equals(rightValue);
    }

    /** Correlation plus attempt, with the REQUEST/RESPONSE half removed. */
    private static String exchangeTransaction(Object encoded) {
        String leg = text(encoded);
        for (String half : Arrays.asList("REQUEST", "RESPONSE")) {
            String suffix = "\n" + half;
            if (leg.endsWith(suffix)) {
                return leg.substring(0, leg.length() - suffix.length());
            }
        }
        return "";
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

    /** Admits every observed writer linked to a demanded shared location. */
    private static Set<String> admitSharedLocationWriters(
            Set<String> targets,
            Map<String, Map<String, Object>> instances,
            RegionDemandIndex demands,
            List<Map<String, Object>> regionEdges,
            Map<String, Integer> demandDepths) throws IOException {
        Set<String> fatalInputs = new LinkedHashSet<>();
        for (String target : targets) {
            fatalInputs.addAll(demands.targetInputs(instances.get(target)));
        }
        return admitWritersOfDemands(targets, fatalInputs, instances,
                regionEdges, demandDepths, targets, null);
    }

    /**
     * The hop count of one admitted occurrence.  A target is the origin.  An
     * occurrence the closure reached on its own authority -- a fault entry, a
     * communication entry, a protocol producer -- is a demand origin of the
     * same standing as the target's own reads, and counts as one hop rather
     * than zero.
     */
    private static int demandDepth(Map<String, Integer> demandDepths,
                                   String occurrenceId) {
        Integer known = demandDepths.get(occurrenceId);
        return known == null ? 1 : known;
    }

    /** Records the shortest demand chain that reached one admission. */
    private static void recordDemandDepth(
            Map<String, Integer> demandDepths, String occurrenceId,
            int depth) {
        Integer known = demandDepths.get(occurrenceId);
        if (known == null || depth < known) {
            demandDepths.put(occurrenceId, depth);
        }
    }

    /**
     * The shared locations this failure cares about.
     *
     * <p>Transitive demand may only travel through a location whose value
     * can still differ in a way the target can observe.  Two conditions
     * decide that, both read off the one runtime-refined graph this
     * finalization already holds:</p>
     *
     * <ol>
     *   <li>the location lies on the backward slice from the fatal target,
     *   i.e. it appears as a declared field of some refined edge; and</li>
     *   <li>it is forward-reachable from a symbolic root -- the explicit
     *   fault symbol, a declared {@code CausynthSymbolicSource} field, an
     *   {@code EXTERNAL_CALL_RETURN} value, or a wire attach point -- so
     *   some symbolic choice can still change it.</li>
     * </ol>
     *
     * <p>A location on the slice that no symbolic root reaches is a constant
     * for this failure: every replay arm writes the value the recording
     * observed, so admitting its writers buys no new behaviour and only
     * grows the campaign.  Heartbeat timestamps, report counters and
     * test-harness setters fall out here.</p>
     */
    static Set<String> caredSharedLocations(
            List<Map<String, Object>> refinedGraph) {
        List<Map<String, Object>> rows = refinedGraph == null
                ? Collections.<Map<String, Object>>emptyList() : refinedGraph;
        Map<String, Set<String>> forward = new LinkedHashMap<>();
        Set<String> roots = new LinkedHashSet<>();
        for (Map<String, Object> edge : rows) {
            String from = text(edge.get("fromCell"));
            String to = text(edge.get("toCell"));
            if (from.isEmpty() || to.isEmpty()) continue;
            forward.computeIfAbsent(from,
                    ignored -> new LinkedHashSet<>()).add(to);
            if (symbolicRootEdge(edge)) {
                // Both ends: the fault edge names the symbol it introduces
                // on one side and the cell that carries it on the other.
                roots.add(from);
                roots.add(to);
            }
        }
        Set<String> reachable = new LinkedHashSet<>(roots);
        Deque<String> pending = new ArrayDeque<>(roots);
        while (!pending.isEmpty()) {
            for (String next : forward.getOrDefault(pending.removeFirst(),
                    Collections.<String>emptySet())) {
                if (reachable.add(next)) pending.addLast(next);
            }
        }
        Set<String> cared = new LinkedHashSet<>();
        for (Map<String, Object> edge : rows) {
            if (!reachable.contains(text(edge.get("fromCell")))
                    && !reachable.contains(text(edge.get("toCell")))) {
                continue;
            }
            cared.addAll(declaredFieldLocations(edge));
        }
        return cared;
    }

    /** A refined edge that introduces a symbolic value of its own. */
    private static boolean symbolicRootEdge(Map<String, Object> edge) {
        String kind = text(edge.get("kind"));
        return Boolean.TRUE.equals(booleanValue(
                edge.get("explicitSymbolicFault")))
                || !text(edge.get("symbolicName")).isEmpty()
                || "wire_handoff".equals(kind)
                || "wire_capture_argument".equals(kind)
                || EXTERNAL_CALL_RETURN.equals(text(edge.get("sourceKind")));
    }

    /** Every {@code owner#field} address one refined edge names. */
    private static Set<String> declaredFieldLocations(
            Map<String, Object> edge) {
        Set<String> located = new LinkedHashSet<>();
        List<String> declarations = new ArrayList<>(
                strings(edge.get("fieldPathDeclarations")));
        declarations.add(text(edge.get("declaredFieldSignature")));
        for (String declaration : declarations) {
            FieldPathSpec.DeclaredField field =
                    FieldPathSpec.declaredField(declaration);
            if (field == null) continue;
            String key = SharedFieldFlow.fieldKey(field.owner(),
                    field.name());
            if (!key.isEmpty()) located.add(key);
        }
        return located;
    }

    /**
     * Second-order shared-location demand: the read ports an already admitted
     * occurrence holds for a location some other recorded activation of the
     * same node and epoch wrote.
     *
     * <p>The first-order rule only follows a read the failure closure had
     * already demanded through a port, which is the read of a value the
     * failure consumed directly.  A region admitted to supply that value
     * reads shared state of its own, and such a read is ordinarily neither a
     * target input nor an explored branch operand, so no port demand ever
     * reaches it: replay then pins it to the one INITIAL arm its recording
     * observed.  Returning the port here seeds it into the next closure walk,
     * which retains the recorded field flows into it and therefore hands the
     * first-order rule the writers to admit -- under
     * {@code SHARED_LOCATION_DEMAND_V1}, with the hop count this demand
     * travelled.</p>
     *
     * <p>Evidence is the same pass-2 field and accessor binding the
     * first-order rule reads: one recorded {@code RUNTIME_FIELD_FLOW} per
     * observed writer of the exact receiver and leaf.  A hop is opened only
     * by a writer inside the reader's own semantic source, because a heap
     * location is private to the node and epoch that holds the object; once
     * the read is demanded, every recorded writer of that receiver and leaf
     * is a replay arm of it, which is the first-order rule's standing
     * contract and not this rule's to narrow.</p>
     */
    static Set<String> transitiveSharedLocationDemand(
            Collection<String> admitted,
            Set<String> demandedInputs,
            Map<String, Map<String, Object>> instances,
            List<Map<String, Object>> regionEdges,
            Map<String, Integer> demandDepths,
            Set<String> caredLocations) {
        Set<String> reached = new LinkedHashSet<>(admitted);
        Set<String> seeds = new LinkedHashSet<>();
        for (Map<String, Object> edge : regionEdges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                continue;
            }
            String consumer = text(edge.get("toOccurrenceId"));
            String writer = text(edge.get("fromOccurrenceId"));
            String toPort = text(edge.get("toPort"));
            if (!reached.contains(consumer) || writer.equals(consumer)
                    || toPort.isEmpty()
                    || text(edge.get(SharedFieldFlow.EDGE_LOCATION))
                    .isEmpty()
                    || !instances.containsKey(writer)
                    || !instances.containsKey(consumer)) {
                continue;
            }
            String demand = portDemandKey(consumer, toPort);
            if (demandedInputs.contains(demand)) {
                // Already first-order demand; its writers are admitted by
                // the rule above and this hop would only recount them.
                continue;
            }
            if (!activationSourceKey(instances.get(consumer)).equals(
                    activationSourceKey(instances.get(writer)))) {
                continue;
            }
            String location = text(edge.get(SharedFieldFlow.EDGE_LOCATION));
            if (caredLocations != null
                    && !caredLocations.contains(location)) {
                // Outside the care set this location is a constant for the
                // failure, so the hop stops here.
                continue;
            }
            recordDemandDepth(demandDepths, writer,
                    demandDepth(demandDepths, consumer) + 1);
            seeds.add(demand);
        }
        return seeds;
    }

    /** Admits the observed writers of locations read by the demand set. */
    static Set<String> admitWritersOfDemands(
            Collection<String> demanding,
            Set<String> demandedInputs,
            Map<String, Map<String, Object>> instances,
            List<Map<String, Object>> regionEdges,
            Map<String, Integer> demandDepths,
            Collection<String> fatalTargets,
            Set<String> caredLocations)
            throws IOException {
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
            String location = text(edge.get(SharedFieldFlow.EDGE_LOCATION));
            if (location.isEmpty()) {
                continue;
            }
            // The fatal target's own reads are demanded whatever they are:
            // they are the failure's direct inputs.  Every other consumer is
            // here because it was itself admitted to supply a location, so
            // its reads are second-order demand and travel only through the
            // care set.
            if (caredLocations != null
                    && (fatalTargets == null
                    || !fatalTargets.contains(consumer))
                    && !caredLocations.contains(location)) {
                continue;
            }
            locationsByWriter.computeIfAbsent(writer,
                    ignored -> new LinkedHashSet<>()).add(location);
            targetRegionsByWriter.computeIfAbsent(writer,
                    ignored -> new TreeSet<>()).add(text(
                    instances.get(consumer).get("regionId")));
            recordDemandDepth(demandDepths, writer,
                    demandDepth(demandDepths, consumer) + 1);
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
            // Which regions demanded this writer, and which locations they
            // demanded it for, were the stitcher's join columns: it merged
            // replays and had to re-derive who wanted each write.  The
            // admission basis and the depth stay -- the scheduler reads both.
            activation.put(ADMISSION_BASIS,
                    SHARED_LOCATION_DEMAND_ADMISSION);
            activation.put(DEMAND_DEPTH,
                    demandDepth(demandDepths, writer));
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
            Set<String> admittedStateWriters,
            Collection<String> transitiveSharedDemands)
            throws IOException {
        Set<String> reached = new LinkedHashSet<>(targets);
        Set<String> retainedEdges = new LinkedHashSet<>();
        Set<String> demandedInputs = new LinkedHashSet<>();
        Set<String> demandedOutputs = new LinkedHashSet<>();
        Set<String> expandedOutputOccurrences = new LinkedHashSet<>();
        Set<String> expandedRegionPathOccurrences = new LinkedHashSet<>();
        List<String> seeds = new ArrayList<>();
        for (String target : targets) {
            Map<String, Object> instance = instances.get(target);
            seeds.addAll(demands.targetInputs(instance));
        }
        for (String input : targetInteractionInputs) {
            seeds.add(input);
        }
        seeds.addAll(requestFlowPrefixInputs.keySet());
        // Second-order shared-location demand, in the order the recorded
        // field flows exposed it.  A read seeded here is demanded exactly the
        // way a target input is, so the walk retains its recorded writers'
        // flows and output versions and the read becomes a multi-writer
        // GuardedRead instead of its one recorded INITIAL arm.
        seeds.addAll(transitiveSharedDemands);
        // A selected writer is retained even when nothing demands one of its
        // outputs yet: the bounded NN heartbeat predecessors stay in the
        // closure without any of them becoming a read-from arm before replay
        // records a write/version.
        for (String writer : admittedStateWriters) {
            Map<String, Object> instance = instances.get(writer);
            if (instance == null) continue;
            reached.add(writer);
            addRegionPathInputs(seeds, writer, targets,
                    expandedRegionPathOccurrences, demands);
        }
        // Communication is represented by exact occurrence-owned IN/OUT
        // ports in predecessors, so the walk crosses a call the same way it
        // crosses any other edge: from the demanded input port to the output
        // port some other occurrence declared for it. Writer choice stays in
        // the VM expression; this walk only selects linked replay members.
        List<IOException> refused = new ArrayList<>();
        StaticProgram.closure(seeds, demanded -> {
            demandedInputs.add(demanded);
            List<String> next = new ArrayList<>();
            for (Map<String, Object> edge : predecessors.getOrDefault(
                    demanded, Collections.<Map<String, Object>>emptyList())) {
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
                addRegionPathInputs(next, fromOccurrence, targets,
                        expandedRegionPathOccurrences, demands);
                String toOccurrence = text(edge.get("toOccurrenceId"));
                reached.add(toOccurrence);
                addRegionPathInputs(next, toOccurrence, targets,
                        expandedRegionPathOccurrences, demands);
                String outputDemand = portDemandKey(fromOccurrence,
                        text(edge.get("fromPort")));
                demandedOutputs.add(outputDemand);
                if (expandedOutputOccurrences.add(outputDemand)) {
                    next.addAll(demands.inputsForOutput(fromOccurrence,
                            text(edge.get("fromPort"))));
                    next.addAll(demands.communicationInputs(
                            fromOccurrence));
                }
            }
            return next;
        });
        if (!refused.isEmpty()) throw refused.get(0);
        return new ClosureWalk(reached, retainedEdges, demandedInputs,
                demandedOutputs);
    }

    /**
     * A retained non-target activation becomes a REGION_PATH_CLOSURE task.
     * Keep the exact local inputs of every semantic branch that task may
     * reopen, even when the activation was admitted before one of its output
     * versions was selected by the causal closure.
     */
    private static void addRegionPathInputs(
            Collection<String> work, String occurrenceId,
            Collection<String> targets, Set<String> expanded,
            RegionDemandIndex demands) {
        if (occurrenceId.isEmpty() || targets.contains(occurrenceId)
                || !expanded.add(occurrenceId)) {
            return;
        }
        work.addAll(demands.exploredBranchInputs(occurrenceId));
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
                    fatalPrefixCutoffs, program.planGaps));
            region.put("outputs", filterPorts(
                    rows(region.get("outputs")),
                    occurrences, true, walk.demandedOutputs,
                    fatalPrefixCutoffs, program.planGaps));
        }
    }

    private static List<Map<String, Object>> filterPorts(
            List<Map<String, Object>> ports, Set<String> occurrences,
            boolean output,
            Set<String> demandedPorts,
            Map<String, Long> fatalPrefixCutoffs,
            List<Map<String, Object>> gaps)
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
            retainRuntimeAccesses(selected, demand, gaps);
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

    /** Keeps the bounded occurrence-local accesses of one retained port. */
    private static void retainRuntimeAccesses(
            Map<String, Object> port, String demand,
            List<Map<String, Object>> gaps) throws IOException {
        if (!"HEAP".equals(text(port.get("transportKind")))) return;
        List<Map<String, Object>> accesses = boundedRuntimeAccesses(port,
                NO_ACCESS_DEMAND, gaps);
        if (accesses.isEmpty()) {
            throw new IOException("demanded heap port has no runtime access: "
                    + demand);
        }
        sortByEventSeq(accesses);
        port.put("runtimeAccesses", accesses);
        if (accesses.size() == 1) {
            copyRuntimeOccurrence(accesses.get(0), port);
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
    private static String recordedRootCallKey(String regionId,
                                              long rootCallId) {
        return regionId + "\n" + rootCallId;
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
                "mutatorDeclaredCallee"}) {
            access.put(key, binding.get(key));
        }
        access.put("staticAccessSiteId", firstNonEmpty(
                text(binding.get("siteId")), staticAccessSiteId(edge)));
        accesses.add(access);
    }

    private static String staticAccessSiteId(Map<String, Object> edge) {
        String site = text(edge.get("siteId"));
        if (!site.isEmpty()) return site;
        String method = text(edge.get("method"));
        int unit = number(edge.get("unitIndex"), -1);
        if (!method.isEmpty() && unit >= 0) return SiteId.of(method, unit);
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
            String field = firstNonEmpty(text(edge.get("declaredFieldSignature")),
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
                // A port id is published identity, so it has to be spelled
                // from content.  The recorder's callId is a global per-run
                // event counter (CausynthTraceRecorder's EVENT_COUNTER), so
                // keying on it renamed the same field root in every run.
                // accessorOccurrence is already counted per activation per
                // (method, siteId, declaredCallee), which is what makes this
                // spelling both run-stable and exact.
                String key = occurrenceId + "\n" + text(edge.get("id"))
                        + "\n" + SiteId.of(caller, unitIndex)
                        + "\n" + declaredCallee + "\n" + occurrence;
                if (unique.containsKey(key)) continue;
                // The root can be a long-lived service loop.
                String stream = occurrenceId + "\n" + callId
                        + "\nACCESSOR_RETURN\n"
                        + SiteId.of(caller, unitIndex) + "\n" + field + "\n"
                        + declaredCallee + "\n" + implementation;
                int retained = retainedByActivationStream.getOrDefault(
                        stream, 0);
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
    static List<Map<String, Object>> externalCallReturnPorts(
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
            for (Long callId : MapFields.longValues(
                    activation.getValue().get("callIds"))) {
                occurrencesByCall.computeIfAbsent(callId,
                        ignored -> new ArrayList<>()).add(activation.getKey());
            }
        }
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Integer> ordinals = new LinkedHashMap<>();
        Set<String> exactAccessorReturns = exactAccessorReturnEvents(
                program, regionId);
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
                long eventSeq = longNumber(observation.get("eventSeq"), -1L);
                // An exact accessor binding already names the field value at
                // this very return event.  The VM propagates that field
                // expression through the getter, so minting another symbol
                // for the call result would give one value two authorities.
                if (exactAccessorReturns.contains(returnEventKey(regionId,
                        site, callee, callId, eventSeq))) {
                    continue;
                }
                for (String occurrenceId : occurrenceIds) {
                    // Same reason as the accessor ports above: the
                    // ordinal has to count return events per occurrence and
                    // site, not per per-run callId, or the port id it names
                    // differs between two runs of one obligation.
                    String stream = occurrenceId + "\n" + site;
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

    /** Exact accessor-field observations that already define a call result. */
    private static Set<String> exactAccessorReturnEvents(
            StaticProgram program, String regionId) {
        Set<String> result = new LinkedHashSet<>();
        for (Map<String, Object> edge : program.regionGraph(regionId)) {
            if (!"accessor_field_return".equals(text(edge.get("kind")))
                    || !Boolean.TRUE.equals(booleanValue(
                    edge.get("runtimeObserved")))) {
                continue;
            }
            String edgeSite = staticAccessSiteId(edge);
            String edgeCallee = text(edge.get("invoke"));
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeAccessorBindings"))) {
                if (!regionId.equals(text(binding.get("regionId")))
                        || !"EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1"
                        .equals(text(binding.get("authority")))) {
                    continue;
                }
                String site = firstNonEmpty(text(binding.get("siteId")), edgeSite);
                String callee = firstNonEmpty(
                        text(binding.get("declaredCallee")), edgeCallee);
                long callId = longNumber(binding.get("callId"), -1L);
                long eventSeq = longNumber(binding.get("eventSeq"), -1L);
                if (site.isEmpty() || callee.isEmpty()
                        || callId < 0L || eventSeq < 0L) {
                    continue;
                }
                result.add(returnEventKey(regionId, site, callee,
                        callId, eventSeq));
            }
        }
        return result;
    }

    private static String returnEventKey(
            String regionId, String site, String callee,
            long callId, long eventSeq) {
        return regionId + "\n" + site + "\n" + callee + "\n"
                + callId + "\n" + eventSeq;
    }

    /** Exact external primitive definitions reached by explored guards. */
    private static Set<String> semanticExternalCallReturnEdges(
            StaticProgram program, String regionId,
            List<Map<String, Object>> branchPolicies) {
        List<String> seeds = new ArrayList<>();
        for (Map<String, Object> branch : branchPolicies) {
            seeds.addAll(strings(branch.get("operandCells")));
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
                String key = occurrenceId + "\n"
                        + SiteId.of(caller, unitIndex)
                        + "\n" + occurrence;
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
                port.put("siteId", SiteId.of(caller, unitIndex));
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
     * The region's branch catalog: which conditional sites the slice reaches
     * and which cells decide them.
     *
     * <p>No policy and no guard set.  Every decision whose term has a
     * symbolic operand is recorded (LEAN section 1), so a branch the slice
     * names is a branch the replay records; and the guard set of a site is
     * {@code static_scope_map}'s, computed once by
     * {@link SiteControlDependence}.  This used to classify each site
     * EXPLORE or PATH_ASSUMPTION from a second, may-reach control-dependence
     * relation carried on the graph, and to re-derive the fatal polarity
     * from it.</p>
     */
    private static List<Map<String, Object>> branches(
            StaticProgram program, String regionId) {
        Map<String, List<Map<String, Object>>> bySite = guardsBySite(
                program.regionGraph(regionId), edge -> true);
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
            String site = firstNonEmpty(text(edge.get("guardSiteId")),
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

    private static boolean exactLocalPass(Map<String, Object> edge) {
        return "local_def_use".equals(text(edge.get("kind")))
                && ("VALUE_PASS".equals(text(edge.get("transferKind")))
                || !text(edge.get("valueFlowAuthority")).isEmpty());
    }

    /** Every writer the trace observed for each demanded shared-field read. */
    static List<Map<String, Object>> fieldFlows(
            List<Map<String, Object>> regions,
            Set<String> demandedFields,
            List<Map<String, Object>> gaps) throws IOException {
        // Reads state the location demand. Every bounded write to that exact
        // receiver and leaf remains a replay candidate; concrete trace order
        // never chooses a writer for the symbolic read.
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(reads, text(region.get("regionId")),
                    rows(region.get("symbolicInputs")), NO_ACCESS_DEMAND,
                    gaps);
        }
        reads.removeIf(port -> !demandedFields.contains(
                port.leafDeclaration()));
        RuntimeAccessDemand demand = leafReceiverDemand(reads);
        List<BoundPort> writes = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(writes, text(region.get("regionId")),
                    rows(region.get("outputs")), demand, gaps);
        }
        Map<String, List<BoundPort>> writesByReceiverAndField =
                new LinkedHashMap<>();
        for (BoundPort write : writes) {
            if (write.receiver == 0 || !demandedFields.contains(
                    write.leafDeclaration())) {
                continue;
            }
            writesByReceiverAndField.computeIfAbsent(
                    write.receiver + "\n" + write.leafDeclaration(),
                    ignored -> new ArrayList<>()).add(write);
        }
        List<Map<String, Object>> flows = new ArrayList<>();
        for (BoundPort read : reads) {
            for (BoundPort write : writesByReceiverAndField.getOrDefault(
                    read.receiver + "\n" + read.leafDeclaration(),
                    Collections.<BoundPort>emptyList())) {
                // A self edge adds no replay member. The VM still records all
                // writes made inside that activation in the same version set.
                if (write.occurrenceId.equals(read.occurrenceId)) continue;
                flows.add(fieldFlowEdge(write, read));
            }
        }
        return flows;
    }

    /** Renders one shared-location pair as linked-replay topology. */
    private static Map<String, Object> fieldFlowEdge(
            BoundPort write, BoundPort read) {
        String alternative = write.occurrenceId + "\n" + write.port
                + "\n" + write.site
                + "\n" + write.occurrence + "\n" + read.occurrenceId
                + "\n" + read.port
                + "\n" + read.site + "\n" + read.occurrence;
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind", "RUNTIME_FIELD_FLOW");
        edge.put("transportKind", "HEAP");
        edge.put("authority", SharedFieldFlow.LOCATION_MATCH_AUTHORITY);
        edge.put("edgeId", CausynthStaticFacts.nameId("SF.",
                alternative));
        edge.put("fromRegion", write.region);
        edge.put("toRegion", read.region);
        edge.put("fromPort", write.port);
        edge.put("toPort", read.port);
        edge.put("fromOccurrenceId", write.occurrenceId);
        edge.put("toOccurrenceId", read.occurrenceId);
        // Root calls identify the two recorded occurrences for diagnostics.
        edge.put("fromRootCallId", write.rootCallId);
        edge.put("toRootCallId", read.rootCallId);
        edge.put("dependencyRole", read.dependencyRole);
        edge.put("fieldPathDeclarations", Collections.singletonList(
                write.leafDeclaration()));
        // This is a scheduling address, the read leaf named by its owner
        // and its name.  The value itself is the VM's GuardedRead expression
        // and is never reconstructed from this edge.
        DeclaredFieldCell leaf = DeclaredFieldCell.parse(
                read.leafDeclaration());
        edge.put(SharedFieldFlow.EDGE_LOCATION, leaf == null ? ""
                : SharedFieldFlow.fieldKey(leaf.owner, leaf.name));
        return edge;
    }

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
                String atomicValue = SharedFieldFlow.atomicValueField(field,
                        firstNonEmpty(text(edge.get("mutatorDeclaredCallee")),
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

    /** Ports that read or write one declared field of one observed object. */
    private static boolean causalHeapPort(Map<String, Object> port) {
        if ("HEAP".equals(text(port.get("transportKind")))) return true;
        return "ACCESSOR_RETURN".equals(text(port.get("sourceKind")))
                && number(port.get("fieldReceiverObjectId"), 0) > 0
                && !strings(port.get("fieldPathDeclarations")).isEmpty();
    }

    private static void collectPorts(List<BoundPort> target, String region,
                                     List<Map<String, Object>> ports,
                                     RuntimeAccessDemand demand,
                                     List<Map<String, Object>> gaps)
            throws IOException {
        for (Map<String, Object> port : ports) {
            if (!causalHeapPort(port)) {
                continue;
            }
            List<Map<String, Object>> accesses = boundedRuntimeAccesses(
                    port, demand, gaps);
            if (accesses.isEmpty()) {
                accesses = Collections.singletonList(port);
            }
            for (Map<String, Object> access : accesses) {
                SemanticHeapAddress address = semanticHeapAddress(
                        port, access);
                target.add(new BoundPort(region, text(port.get("portId")),
                        firstNonEmpty(text(access.get("occurrenceId")),
                                text(port.get("occurrenceId"))),
                        longNumber(access.get("rootCallId"),
                                longNumber(port.get("rootCallId"), 0L)),
                        address.receiver,
                        address.declarations,
                        DependencyRole.normalize(
                                port.get("dependencyRole")),
                        firstNonEmpty(text(access.get("staticAccessSiteId")),
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
        String bindingKind = firstNonEmpty(text(access.get("bindingKind")),
                text(port.get("bindingKind")));
        String declaredCallee = firstNonEmpty(
                text(access.get("mutatorDeclaredCallee")),
                text(port.get("mutatorDeclaredCallee")));
        String atomicValue = "CONTAINER_MUTATION".equals(bindingKind)
                && !declarations.isEmpty()
                ? SharedFieldFlow.atomicValueField(
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
                        semanticDeclarations);
            }
        }
        return new SemanticHeapAddress(receiver, declarations);
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
    /**
     * Records one finalizer gap, once per (kind, subject), stating its own
     * class exactly like a {@link
     * edu.uva.liftlab.graphchecker.contract.GapRow}.
     *
     * <p>{@code gaps} may be null where a caller builds ports outside a
     * finalize pass; the truncation below runs inside one.</p>
     */
    private static void planGap(List<Map<String, Object>> gaps, GapKind kind,
                                GapClass cls, String subject, String detail) {
        if (gaps == null) return;
        for (Map<String, Object> existing : gaps) {
            if (kind.name().equals(text(existing.get("kind")))
                    && subject.equals(text(existing.get("subject")))) {
                return;
            }
        }
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 1);
        row.put("kind", kind.name());
        row.put("cls", cls.name());
        row.put("subject", subject);
        row.put("detail", detail);
        gaps.add(row);
    }

    private static List<Map<String, Object>> boundedRuntimeAccesses(
            Map<String, Object> port, RuntimeAccessDemand demand,
            List<Map<String, Object>> gaps)
            throws IOException {
        List<Map<String, Object>> accesses = new ArrayList<>(
                rows(port.get("runtimeAccesses")));
        sortByEventSeq(accesses);
        Map<String, Integer> occurrences = new LinkedHashMap<>();
        Map<String, Integer> retained = new LinkedHashMap<>();
        List<Map<String, Object>> bounded = new ArrayList<>();
        List<Map<String, Object>> resourceDefault = new ArrayList<>();
        // The same number the campaign declared for an inherited loop
        // bound: one activation-local access per body execution.
        int accessDefault = LoopBoundPolicy.declaredDefault();
        String refusal = "";
        for (Map<String, Object> access : accesses) {
            String site = firstNonEmpty(text(access.get("staticAccessSiteId")),
                    text(port.get("portId")));
            int occurrence = occurrences.getOrDefault(site, 0) + 1;
            occurrences.put(site, occurrence);
            access.put("staticAccessSiteId", site);
            access.put("activationLocalStaticSiteOccurrence", occurrence);
            boolean withinDefault =
                    occurrence <= accessDefault;
            if (withinDefault) resourceDefault.add(access);
            if (!withinDefault && !demand.required(port, access)) continue;
            int kept = retained.getOrDefault(site, 0) + 1;
            retained.put(site, kept);
            if (kept > MAX_RETAINED_SITE_ACCESSES) {
                if (refusal.isEmpty()) {
                    refusal = "static site " + site
                            + " demands more than " + MAX_RETAINED_SITE_ACCESSES
                            + " activation-local accesses, so this port keeps"
                            + " only the "
                            + accessDefault
                            + "-access resource default and the accesses"
                            + " above it are invisible to every later stage";
                    planGap(gaps, GapKind.BOUND_INSUFFICIENT,
                            GapClass.BLOCKING,
                            text(port.get("portId")) + "\n" + site, refusal);
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
        for (BoundPort read : reads) {
            if (read.receiver != 0 && !read.leafDeclaration().isEmpty()) {
                demanded.add(read.receiver + "\n"
                        + read.leafDeclaration());
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
            return demanded.contains(location);
        };
    }

    /** Recorded rows in observed order; unstamped rows sort last. */
    private static void sortByEventSeq(List<Map<String, Object>> rows) {
        rows.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
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
        /** Operands of semantic branches reopened by REGION_PATH_CLOSURE. */
        private final Map<String, List<String>> exploredSeeds =
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
                    if (!site.isEmpty()) {
                        for (String operand : strings(
                                branch.get("operandCells"))) {
                            addUnique(exploredSeeds, regionId, operand);
                        }
                    }
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

        /** Communication inputs that make this occurrence a linked replay. */
        private List<String> communicationInputs(String occurrenceId) {
            return instanceInputs(occurrenceId, port ->
                    COMMUNICATION_SITE_PORT.equals(
                            text(port.get("sourceKind"))));
        }

        /** Every propagated value consumed by one whole-state writer. */
        private List<String> valueInputs(String occurrenceId) {
            return instanceInputs(occurrenceId, port ->
                    DependencyRole.valueFrontier(
                            port.get("dependencyRole")));
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

        /** Exact occurrence-owned boundary inputs of its EXPLORE branches. */
        private List<String> exploredBranchInputs(String occurrenceId) {
            String regionId = regionByOccurrence.getOrDefault(
                    occurrenceId, "");
            return backwardInputs(occurrenceId,
                    exploredSeeds.getOrDefault(regionId,
                            Collections.<String>emptyList()));
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
                    // The fatal occurrence of this activation is the FIRST
                    // decision the recording made at that site in it.  It
                    // used to be the first occurrence whose observed outcome
                    // equalled a required one -- an election over recorded
                    // evidence that this tree spelled out three times.
                    int selectedIndex = 0;
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
            String sourceKind = text(port.get("sourceKind"));
            if ("ACCESSOR_RETURN".equals(sourceKind)
                    || COMMUNICATION_SITE_PORT.equals(sourceKind)
                    || EXPLICIT_SYMBOLIC_FAULT.equals(sourceKind)
                    || EXTERNAL_CALL_RETURN.equals(sourceKind)) {
                long event = longNumber(port.get("eventSeq"), -1L);
                if (event < 0L) return 0;
                return event <= fatalEventSeq ? 1 : -1;
            }
            return 0;
        }

        private List<String> inputsForOutput(String occurrenceId,
                                             String portId) {
            String demand = portDemandKey(occurrenceId, portId);
            List<String> cached = inputsForOutputCache.get(demand);
            if (cached != null) {
                return cached;
            }
            List<String> computed = computeInputsForOutput(occurrenceId,
                    portId);
            inputsForOutputCache.put(demand, computed);
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
                // A whole-state version summarizes every container mutation
                // in this activation. The receiver cell alone cannot name
                // the keys and values consumed by those mutations, so retain
                // every observed value boundary of the writer occurrence.
                result.addAll(valueInputs(occurrenceId));
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
        /** Activation identity; the only activation discriminator here. */
        private final String occurrenceId;
        /** Recorded trace evidence republished on the emitted edge. */
        private final long rootCallId;
        private final int receiver;
        private final List<String> declarations;
        private final String dependencyRole;
        private final String site;
        private final int occurrence;

        private BoundPort(String region, String port,
                          String occurrenceId,
                          long rootCallId, int receiver,
                          List<String> declarations,
                          String dependencyRole, String site,
                          int occurrence) {
            this.region = region;
            this.port = port;
            this.occurrenceId = occurrenceId;
            this.rootCallId = rootCallId;
            this.receiver = receiver;
            this.declarations = declarations;
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

        private SemanticHeapAddress(int receiver,
                                    List<String> declarations) {
            this.receiver = receiver;
            this.declarations = declarations;
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
        /**
         * Gaps this pass raised about its own ports: every one of them
         * says a recorded access or a recorded container observation was
         * dropped, which no later stage can see, so they travel into the
         * runtime plan artifact stating their own kind and class.
         */
        public final List<Map<String, Object>> gaps;
        private Result(List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges,
                       List<Map<String, Object>> gaps) {
            this.regions = regions;
            this.regionEdges = regionEdges;
            this.gaps = gaps;
        }
    }
}
