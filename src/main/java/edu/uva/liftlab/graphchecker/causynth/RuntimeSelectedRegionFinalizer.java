package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.DoorsOnlyRoots;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.RuntimeWorkflowDiscovery;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder;
import edu.uva.liftlab.graphchecker.runtime.RuntimeRegionPlanner;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Consumer;
import java.util.function.Function;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.booleanValue;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.strings;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

public final class RuntimeSelectedRegionFinalizer {
    private static final org.slf4j.Logger LOG = org.slf4j.LoggerFactory
            .getLogger(RuntimeSelectedRegionFinalizer.class);
    private static final String REFINED_KIND = "RUNTIME_REFINED_DATAFLOW";

    public static final String EXPLICIT_SYMBOLIC_FAULT =
            "EXPLICIT_SYMBOLIC_FAULT";
    public static final String EXTERNAL_CALL_RETURN =
            "EXTERNAL_CALL_RETURN";

    public static final String ADMISSION_BASIS = "admissionBasis";
    private static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    public static final String DEMAND_DEPTH = "demandDepth";
    private static final int TARGET_DEMAND_DEPTH = 0;
    private static final String ROOT_RELEVANT_ADMISSION = "ROOT_RELEVANT_V1";
    private static final String CONTROL_PRODUCER_ADMISSION =
            "CONTROL_PRODUCER_V1";
    public static final String DOORS_ONLY = "doorsOnly";
    public static final String DOORS_ONLY_DECLARED = "doorsOnlyDeclared";
    private static final String WIRE_PRODUCER_ADMISSION = "WIRE_PRODUCER_V1";
    private static final String STORE_WRITER_ADMISSION = "STORE_WRITER_V1";
    private static final String STORE_ITEM_PRODUCER_ADMISSION =
            "STORE_ITEM_PRODUCER_V1";
    private static final String STORE_FETCH_ADMISSION = "STORE_FETCH_V1";
    public static final String STORE_FETCHES = "storeFetches";
    static final String PROVENANCE_FETCH = "PROVENANCE";
    public static final String FIELD_OWNERS = "fieldOwners";
    public static final String RECEIVER_HOLDERS = "receiverHolders";
    public static final String FIELD_REFERENTS = "fieldReferents";
    public static final String SIGNATURE = "signature";
    public static final String FIRST_SEQ = "firstSeq";
    public static final String LAST_SEQ = "lastSeq";
    public static final String NAMED_OBJECTS = "namedObjects";
    public static final String CONFINED_WRITERS = "confinedWriters";
    public static final String ESCAPED_WRITERS = "escapedWriters";
    public static final String DECIDER_CLASS = "deciderClass";
    public static final String COMMUNICATION_PORTS = "communicationPorts";

    public static final String REGION_PORT_SIDE = "regionPortSide";
    public static final String COMMUNICATION_SITE_PORT =
            "COMMUNICATION_SITE_PORT";
    public static final String OBSERVED_COMMUNICATION_CAPTURES =
            "observedCommunicationCaptures";
    public static final String SENT_EXCHANGE_LEGS = "sentExchangeLegs";
    public static final String RETAINED_LOOPS = "retainedLoops";
    public static final int REGION_SCHEMA_VERSION = 3;
    public static final String SKELETON_KIND = "REGION_SKELETON";
    public static final String SHARED_ADDRESS_ROOT_CALLS =
            "sharedAddressRootCallIds";
    public static final String FOLDED_REGION_IDS = "foldedRegionIds";
    public static final String FOLDED_ENTRY_CALLERS = "foldedEntryCallers";
    public static final String FAILURE_TARGET_OCCURRENCE =
            "failureTargetOccurrence";
    public static final String DECLARED_OCCURRENCE = "declaredOccurrence";
    public static final String CONTEXT_SHAPE = "contextShape";
    public static final String RECORDED_BESIDE = "recordedBeside";

    private RuntimeSelectedRegionFinalizer() {
    }

    public static Result finalizeRegions(
            List<Map<String, Object>> graph,
            List<StaticProgram.RegionRow> selectedSkeletons,
            String skeletonSource, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> branchObservations,
            StaticScopeMap scopeMap, String declaredOccurrence,
            Collection<ScheduleEvent> recordedSchedule, RecordedStore store,
            RecordedAccesses accesses, RecordedHeap heap)
            throws IOException {
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }
        StaticProgram program = new StaticProgram();
        program.graph = graph;
        for (StaticProgram.RegionRow skeleton : selectedSkeletons) {
            program.skeletons.put(skeleton.regionId, skeleton);
        }

        List<Map<String, Object>> branchOrder = orderedBranchObservations(
                branchObservations);
        List<Map<String, Object>> sharedAddresses = new ArrayList<>();
        readOccurrences(program, runtimeInstances, skeletonSource,
                sharedAddresses);
        Map<String, List<String>> foldedIntoRegion = new LinkedHashMap<>();
        for (Map<String, Object> activation : program.activations.values()) {
            List<String> held = foldedIntoRegion.computeIfAbsent(
                    text(activation.get("regionId")),
                    ignored -> new ArrayList<String>());
            for (String folded : strings(activation.get(FOLDED_REGION_IDS))) {
                if (!held.contains(folded)) held.add(folded);
            }
        }

        for (Map.Entry<String, StaticProgram.RegionRow> entry
                : program.skeletons.entrySet()) {
            String regionId = entry.getKey();
            StaticProgram.RegionRow skeleton = entry.getValue();
            if (!selectedRegion(skeleton, observed)) {
                continue;
            }
            Map<String, Object> region = new LinkedHashMap<>();
            region.put("schemaVersion", REGION_SCHEMA_VERSION);
            region.put("kind", "SYMBOLIC_REGION");
            region.put("graphKind", REFINED_KIND);
            region.put("regionId", regionId);
            region.put("rootMethod", skeleton.rootMethod);
            if (!skeleton.rootAuthority.isEmpty()) {
                region.put("rootAuthority", skeleton.rootAuthority);
            }
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
            List<String> foldedHere = foldedIntoRegion.getOrDefault(regionId,
                    Collections.<String>emptyList());
            region.put("methods", foldedUnion(program, skeleton, foldedHere,
                    row -> row.methods));
            for (String carried : new String[]{RETAINED_LOOPS,
                    StaticSymbolicSourceDeclaration.FIELD,
                    ConfiguredSourcePhaseContract.DECLARATION_FIELD}) {
                List<Map<String, Object>> declared = foldedUnion(program,
                        skeleton, foldedHere, row -> rows(row.json.get(
                                carried)));
                if (!declared.isEmpty()) region.put(carried, declared);
            }

            region.put("symbolicInputs", new ArrayList<Map<String, Object>>());
            region.put("outputs", new ArrayList<Map<String, Object>>());
            region.put("branchPolicies", branches(foldedUnion(program,
                    skeleton, foldedHere,
                    row -> program.regionGraph(row.regionId))));
            program.regions.add(region);
        }
        bindObservedFatalTargets(program.regions, runtimeInstances,
                branchOrder);
        Map<String, List<CutPort>> cutPorts = declaredCutPorts(program);
        declareCommunicationPorts(program, cutPorts, foldedIntoRegion);
        RegionDemandIndex demands = new RegionDemandIndex(program, scopeMap,
                branchOrder);
        applyClosure(program, failureDirectedClosure(program, demands,
                skeletonSource, scopeMap, cutPorts, declaredOccurrence,
                new RecordedMessages(recordedSchedule), store, accesses,
                heap));
        stateSharedAddressClasses(program, sharedAddresses);
        declareCommunicationPorts(program, cutPorts, foldedIntoRegion);
        return new Result(program.regions, program.planGaps,
                ZkChain.of(program.zkChain));
    }

    private static final class CutPort {
        private final String side;
        private final Map<String, Object> row;
        private final Set<String> cells = new LinkedHashSet<>();

        private CutPort(String side, Map<String, Object> row,
                        List<Map<String, Object>> regionGraph) {
            this.side = side;
            this.row = row;
            if ("IN".equals(side) && CommunicationCatalogContract
                    .CAPTURE_CALL_RETURN.equals(text(row.get(
                            CommunicationCatalogContract
                                    .PORT_OUTPUT_CAPTURE_KIND)))) {
                cells.addAll(callReturnValueCells(regionGraph, row));
            } else {
                cells.add(declaredCutPortCell(row));
            }
            cells.remove("");
        }
    }

    private static Map<String, List<CutPort>> declaredCutPorts(
            StaticProgram program) {
        Map<String, List<CutPort>> byRegion = new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : program.skeletons.values()) {
            List<CutPort> ports = new ArrayList<>();
            List<Map<String, Object>> regionGraph = program.regionGraph(
                    skeleton.regionId);
            for (Map.Entry<String, List<Map<String, Object>>> side
                    : cutPortRows(skeleton, regionGraph).entrySet()) {
                for (Map<String, Object> row : side.getValue()) {
                    ports.add(new CutPort(side.getKey(), row, regionGraph));
                }
            }
            if (!ports.isEmpty()) byRegion.put(skeleton.regionId, ports);
        }
        return byRegion;
    }

    public static Map<String, List<Map<String, Object>>> cutPortRows(
            StaticProgram.RegionRow skeleton,
            List<Map<String, Object>> regionGraph) {
        Map<String, List<Map<String, Object>>> bySide = new LinkedHashMap<>();
        bySide.put("IN", new ArrayList<>());
        bySide.put("OUT", new ArrayList<>());
        for (Map<String, Object> port : skeleton.communicationPorts) {
            String portId = text(port.get("portId"));
            String side = text(port.get(REGION_PORT_SIDE));
            if (portId.isEmpty() || !bySide.containsKey(side)) {
                continue;
            }
            Map<String, Object> row = new LinkedHashMap<>(port);
            row.remove(REGION_PORT_SIDE);
            Set<String> cells = callReturnValueCells(regionGraph, row);
            if (cells.size() == 1) {
                row.put("dependencyCells", new ArrayList<>(cells));
            }
            bySide.get(side).add(row);
        }
        return bySide;
    }

    private static void declareCommunicationPorts(StaticProgram program,
            Map<String, List<CutPort>> declaredByRegion,
            Map<String, List<String>> foldedIntoRegion) {
        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            List<CutPort> declared = new ArrayList<>();
            for (String performed : performedRegionIds(regionId,
                    foldedIntoRegion.getOrDefault(regionId,
                            Collections.<String>emptyList()))) {
                List<CutPort> held = declaredByRegion.get(performed);
                if (held != null) declared.addAll(held);
            }
            if (declared.isEmpty()) {
                continue;
            }
            List<Map<String, Object>> inputs = rows(
                    region.get("symbolicInputs"));
            List<Map<String, Object>> outputs = rows(region.get("outputs"));
            Set<String> held = declaredCaptures(inputs, "IN");
            held.addAll(declaredCaptures(outputs, "OUT"));
            for (CutPort port : declared) {
                if (!held.add(CommunicationCatalogContract.captureKey(
                        port.side, port.row))) {
                    continue;
                }
                ("IN".equals(port.side) ? inputs : outputs).add(
                        new LinkedHashMap<>(port.row));
            }
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
        }
    }

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
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return callee.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : callee + ".param" + argumentIndex + ":" + javaType;
        }
        return "";
    }

    public static Map<String, String> fieldAccessingCalls(
            Collection<Map<String, Object>> graph, StaticScopeMap scopeMap) {
        Map<String, String> sites = new HashMap<>();
        for (Map<String, Object> edge : graph) {
            if ("accessor_field_return".equals(text(edge.get("kind")))) {
                sites.put(text(edge.get("siteId")),
                        text(edge.get("fromCell")));
            }
        }
        for (List<StaticScopeMap.Site> stores
                : scopeMap.writeSitesByCell().values()) {
            for (StaticScopeMap.Site store : stores) {
                if (!store.declaredCallee.isEmpty()
                        && !store.cell.equals(store.carrier)) {
                    sites.put(store.siteId, store.cell);
                }
            }
        }
        sites.putAll(scopeMap.provenanceCalls());
        return sites;
    }

    public static Map<String, Map<String, Boolean>> receiverReads(
            Collection<Map<String, Object>> graph) {
        Map<String, Map<String, Boolean>> reads = new HashMap<>();
        for (Map<String, Object> edge : graph) {
            if (!"field_read".equals(text(edge.get("kind")))) continue;
            boolean onReceiver = Boolean.TRUE.equals(edge.get(
                    SeedBackwardStaticAnalyzer.ON_RECEIVER));
            reads.computeIfAbsent(text(edge.get("method")),
                    ignored -> new HashMap<>())
                    .merge(text(edge.get("fromCell")), onReceiver,
                            Boolean::logicalAnd);
        }
        return reads;
    }

    public static Map<String, String> storingCalls(StaticScopeMap scopeMap) {
        Map<String, String> sites = new HashMap<>();
        for (List<StaticScopeMap.Site> stores
                : scopeMap.writeSitesByCell().values()) {
            for (StaticScopeMap.Site store : stores) {
                if (!store.declaredCallee.isEmpty()) {
                    sites.put(store.siteId, store.cell);
                }
            }
        }
        return sites;
    }

    private static Set<String> declaredCaptures(
            List<Map<String, Object>> ports, String side) {
        Set<String> captures = new LinkedHashSet<>();
        for (Map<String, Object> port : ports) {
            if (!text(port.get("occurrenceId")).isEmpty()
                    || text(port.get("portId")).isEmpty()) {
                continue;
            }
            captures.add(CommunicationCatalogContract.captureKey(side, port));
        }
        return captures;
    }

    private static void readOccurrences(
            StaticProgram program,
            Collection<Map<String, Object>> runtimeInstances,
            String source,
            List<Map<String, Object>> sharedAddresses) throws IOException {
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
            rootCallsByAddress.computeIfAbsent(occurrenceId,
                    ignored -> new ArrayList<>()).add(rootCallId);
            program.activations.putIfAbsent(occurrenceId, instance);
        }
        for (Map.Entry<String, List<Long>> entry
                : rootCallsByAddress.entrySet()) {
            if (entry.getValue().size() < 2) continue;
            Map<String, Object> activation =
                    program.activations.get(entry.getKey());
            activation.put(SHARED_ADDRESS_ROOT_CALLS, entry.getValue());
            Map<String, Object> shared = new LinkedHashMap<>();
            shared.put("occurrenceId", entry.getKey());
            shared.put("regionId", text(activation.get("regionId")));
            shared.put(SHARED_ADDRESS_ROOT_CALLS, entry.getValue());
            sharedAddresses.add(shared);
        }
    }

    private static void stateSharedAddressClasses(StaticProgram program,
            List<Map<String, Object>> sharedAddresses) {
        Set<String> kept = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            kept.addAll(strings(region.get("runtimeOccurrenceIds")));
        }
        for (Map<String, Object> shared : sharedAddresses) {
            String regionId = text(shared.get("regionId"));
            boolean member = kept.contains(text(shared.get("occurrenceId")));
            Object rootCalls = shared.get(SHARED_ADDRESS_ROOT_CALLS);
            int count = rootCalls instanceof Collection
                    ? ((Collection<?>) rootCalls).size() : 0;
            planGap(program.planGaps, GapKind.OCCURRENCE_ADDRESS_SHARED,
                    member ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                    text(shared.get("occurrenceId")),
                    count + " activations of this region share one address: "
                            + "nothing the address names distinguishes them "
                            + "(same node, causal context and execution "
                            + "index); recorded root calls " + rootCalls
                            + "; one occurrence is one plan row, so only the "
                            + "first is published"
                            + (member
                            ? "; BLOCKING: the closure this plan publishes "
                            + "retains this occurrence of " + regionId
                            + ", so a task addresses it and no claim may be "
                            + "made over it"
                            : "; DIAGNOSTIC: the closure this plan publishes "
                            + "does not retain this occurrence of " + regionId
                            + " (no rule plans a shared address), so no plan "
                            + "row, no task and no session row names it and "
                            + "no composition can rest on it"));
        }
    }

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
            Map<String, Object> previous = byRecordedActivation.putIfAbsent(
                    regionId + "\n" + rootCallId, instance);
            if (previous != null && !previous.equals(instance)) {
                throw new IOException("conflicting runtime region activation "
                        + "payload: " + regionId + "\n" + rootCallId);
            }
        }
        return new ArrayList<>(byRecordedActivation.values());
    }

    private static boolean selectedRegion(StaticProgram.RegionRow skeleton,
                                          Set<String> observed) {
        return !skeleton.methods.isEmpty()
                && (observed.isEmpty()
                || !Collections.disjoint(skeleton.methods, observed));
    }

    public static final String FAILURE_TARGET_CELLS = "failureTargetCells";

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
            Map<String, Map<String, Object>> regionTargets =
                    new LinkedHashMap<>();
            for (String regionId : performedRegionIds(instance)) {
                Map<String, Map<String, Object>> held = targets.get(regionId);
                if (held != null) regionTargets.putAll(held);
            }
            if (regionTargets.isEmpty()) continue;

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

    private static List<String> performedRegionIds(
            String own, Collection<String> folded) {
        List<String> performed = new ArrayList<>();
        if (!own.isEmpty()) performed.add(own);
        for (String regionId : folded) {
            if (!regionId.isEmpty() && !performed.contains(regionId)) {
                performed.add(regionId);
            }
        }
        return performed;
    }

    private static List<String> performedRegionIds(
            Map<String, Object> activation) {
        return performedRegionIds(text(activation.get("regionId")),
                strings(activation.get(FOLDED_REGION_IDS)));
    }

    private static Set<String> failureDirectedClosure(
            StaticProgram program, RegionDemandIndex demands, String source,
            StaticScopeMap scopeMap, Map<String, List<CutPort>> cutPorts,
            String declaredOccurrence, RecordedMessages messages,
            RecordedStore store, RecordedAccesses accesses,
            RecordedHeap heap)
            throws IOException {
        Map<String, Map<String, Object>> instances = program.activations;
        if (instances.isEmpty()) {
            throw new IOException("NO_REGION_ACTIVATION: runtime failure "
                    + "closure requires concrete region activations: "
                    + source);
        }
        Set<String> contexts = new LinkedHashSet<>();
        Set<String> targets = new LinkedHashSet<>();
        Set<String> policylessRegions = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : program.activations.entrySet()) {
            String context = exceptionContextRegion(program,
                    entry.getValue());
            if (context.isEmpty()) {
                continue;
            }
            contexts.add(entry.getKey());
            if (!demands.declaresExplicitFatalTarget(entry.getValue())) {
                policylessRegions.add(context);
            } else if (demands.observedExplicitFatalTarget(
                    entry.getValue())) {
                targets.add(entry.getKey());
            }
        }
        if (contexts.isEmpty()) {
            throw new IOException("FATAL_TARGET_NOT_IN_WINDOW: runtime "
                    + "failure closure found no observed exception-context "
                    + "activation: " + source);
        }
        if (targets.isEmpty() && !policylessRegions.isEmpty()) {
            throw new IOException("FATAL_TARGET_POLICY_ABSENT: "
                    + "exception-context region declares no failure target "
                    + "site to bind the target to: " + policylessRegions
                    + " " + source);
        }
        if (targets.isEmpty()) {
            throw new IOException("FATAL_TARGET_OBSERVATION_GAP: no "
                    + "exception-context activation observed its explicit "
                    + "fatal target branch: " + source);
        }
        Map<CausalContext, List<String>> shapes = new HashMap<>();
        String declared = RuntimeWorkflowDiscovery.declaredOccurrence(
                new ArrayList<>(targets), declaredOccurrence.isEmpty()
                        ? RuntimeWorkflowDiscovery.FIRST : declaredOccurrence,
                target -> shapes.computeIfAbsent(
                        OccurrenceAddress.parse(target).context(),
                        messages::shape));
        OccurrenceAddress question = OccurrenceAddress.parse(declared);
        Set<String> otherTargets = new LinkedHashSet<>();
        for (String target : targets) {
            if (!ContextShape.sameQuestion(OccurrenceAddress.parse(target),
                    question, context -> shapes.computeIfAbsent(context,
                            messages::shape))) {
                otherTargets.add(target);
            }
        }
        targets.removeAll(otherTargets);
        instances.get(declared).put(DECLARED_OCCURRENCE, true);
        try {
            if (demands.recordedFatal(instances.get(declared), scopeMap)) {
                planGap(program.planGaps,
                        GapKind.TARGET_FATAL_IN_RECORDING, GapClass.BLOCKING,
                        declared, "the recording took the fatal arm at the "
                                + "declared occurrence: the case declares an "
                                + "occurrence that throws as recorded, so no "
                                + "counterfactual is asked of it; declare one "
                                + "the recording ran healthy");
            }
        } catch (StaticScopeMap.AmbiguousFatalArm ambiguous) {
            planGap(program.planGaps, GapKind.AMBIGUOUS_FATAL_ARM,
                    GapClass.BLOCKING, declared, ambiguous.getMessage()
                            + ", so no arm the recording took there is the "
                            + "fatal one by the scope map: the declaration "
                            + "names no question; declare the throw one "
                            + "guard arm reaches");
        }
        Set<String> unplannable = new LinkedHashSet<>(otherTargets);
        for (Map.Entry<String, Map<String, Object>> held
                : instances.entrySet()) {
            if (held.getValue().containsKey(SHARED_ADDRESS_ROOT_CALLS)
                    && !targets.contains(held.getKey())) {
                unplannable.add(held.getKey());
            }
        }
        DemandWalk walk = new DemandWalk(program, demands, scopeMap,
                cutPorts, unplannable, heap);
        walk.zk = ZkCausalGraph.of(store);
        walk.chain = zkChain(program, scopeMap, messages, store, walk.zk,
                targets);
        program.zkChain.addAll(walk.chain.rows());
        program.zkChain.addAll(contentKeys(program, store, walk.zk,
                walk.chain, targets));
        List<Demand> seeds = new ArrayList<>();
        for (String target : targets) {
            instances.get(target).put(FAILURE_TARGET_OCCURRENCE, true);
            walk.admit(target, TARGET_DEMAND_DEPTH);
            for (String cell : demands.targetSeedCells(instances.get(target))) {
                seeds.add(new Demand(target, cell));
            }
        }
        walk.walk(seeds);
        crossStore(program, walk, scopeMap, messages, store, targets);
        admitRelevantRoots(program, walk, scopeMap, messages);
        walk.stateOffChain(program.planGaps);
        walk.stateConfinedWriters(program.planGaps);
        walk.stateUnpairedWires(program.planGaps);
        walk.stateFixedDeciders(program.planGaps);
        walk.classDeciders(accesses, context -> shapes.computeIfAbsent(
                context, messages::shape));
        for (String occurrence : walk.reached) {
            Map<String, Object> activation = instances.get(occurrence);
            if (activation.containsKey(ADMISSION_BASIS)) {
                activation.put(DEMAND_DEPTH, walk.depth(occurrence));
            }
        }
        stateShapes(instances, walk.reached, context -> shapes.computeIfAbsent(
                context, messages::shape));
        LOG.info("PLAN {}", dataFlowDoors(program, walk.reached, scopeMap));
        LOG.info("PLAN doors-only: {} of the {} planned occurrence(s)"
                + " (control producers and store fetches) run paused but for"
                + " their doors",
                stateDoorsOnly(instances, walk.reached, regionId -> {
                    StaticProgram.RegionRow skeleton =
                            program.skeletons.get(regionId);
                    return skeleton == null ? "" : skeleton.rootMethod;
                }, DoorsOnlyRoots.current()), walk.reached.size());
        return walk.reached;
    }

    static int stateDoorsOnly(Map<String, Map<String, Object>> instances,
                              Collection<String> planned,
                              Function<String, String> rootOf,
                              DoorsOnlyRoots declared) {
        int doorsOnly = 0;
        for (String occurrence : planned) {
            Map<String, Object> activation = instances.get(occurrence);
            boolean heavy = !activation.containsKey(FAILURE_TARGET_OCCURRENCE)
                    && declared.holds(rootOf.apply(
                            text(activation.get("regionId"))));
            if (heavy) activation.put(DOORS_ONLY_DECLARED, true);
            if (heavy || doorBasis(text(activation.get(ADMISSION_BASIS)))) {
                activation.put(DOORS_ONLY, true);
                doorsOnly++;
            }
        }
        return doorsOnly;
    }

    static boolean doorBasis(String basis) {
        return CONTROL_PRODUCER_ADMISSION.equals(basis)
                || STORE_FETCH_ADMISSION.equals(basis);
    }

    static void stateShapes(Map<String, Map<String, Object>> instances,
                            Collection<String> planned,
                            Function<CausalContext, List<String>> shapes) {
        Map<String, List<OccurrenceAddress>> recorded = new HashMap<>();
        for (String activation : instances.keySet()) {
            OccurrenceAddress address = OccurrenceAddress.parse(activation);
            recorded.computeIfAbsent(address.regionId() + "|"
                    + address.node().render(), key -> new ArrayList<>())
                    .add(address);
        }
        for (String occurrence : planned) {
            OccurrenceAddress address = OccurrenceAddress.parse(occurrence);
            List<String> shape = shapes.apply(address.context());
            List<String> beside = new ArrayList<>();
            for (OccurrenceAddress other : recorded.get(address.regionId()
                    + "|" + address.node().render())) {
                if (!other.id().equals(address.id())
                        && shapes.apply(other.context()).equals(shape)) {
                    beside.add(other.id());
                }
            }
            instances.get(occurrence).put(CONTEXT_SHAPE, shape);
            instances.get(occurrence).put(RECORDED_BESIDE, beside);
        }
    }

    private static final class RootRead {
        private final String dependencyCell;
        private final boolean fault;

        private RootRead(StaticScopeMap.Site site) {
            this.dependencyCell = site.declared.dependencyCell;
            this.fault = StaticScopeMap.FAULT_INPUT.equals(
                    site.declared.inputKind);
        }
    }

    private static final class Attach {
        private final String port;
        private final String leg;
        private final long seq;

        private Attach(String port, String leg, long seq) {
            this.port = port;
            this.leg = leg;
            this.seq = seq;
        }
    }

    private static List<RootRead> rootReads(Map<String, Object> activation,
                                            StaticScopeMap scopeMap) {
        List<RootRead> reads = new ArrayList<>();
        for (Map<String, Object> capture
                : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
            for (StaticScopeMap.Site site : scopeMap.declaredSitesAt(
                    text(capture.get(SiteId.MEMBER)),
                    text(capture.get(DeclaredSiteCapture.DECLARED_CALLEE)))) {
                String kind = site.declared.inputKind;
                if (StaticScopeMap.FAULT_INPUT.equals(kind)
                        && LibraryCatalog.dataFlowMarker(site.declared.marker)) {
                    continue;
                }
                if (StaticScopeMap.CLOCK_INPUT.equals(kind)
                        || StaticScopeMap.FAULT_INPUT.equals(kind)
                        || StaticScopeMap.CONFIG_INPUT.equals(kind)) {
                    reads.add(new RootRead(site));
                }
            }
        }
        return reads;
    }

    private static ZkCausalGraph.Chain zkChain(StaticProgram program,
                                               StaticScopeMap scopeMap,
                                               RecordedMessages messages,
                                               RecordedStore store,
                                               ZkCausalGraph zk,
                                               Collection<String> targets) {
        Map<String, String> byId = new HashMap<>();
        for (String occurrence : program.activations.keySet()) {
            byId.put(OccurrenceAddress.parse(occurrence).id(), occurrence);
        }
        Map<String, Long> seeds = new LinkedHashMap<>();
        for (String target : targets) {
            Set<Integer> objects = new HashSet<>();
            for (String cell : scopeMap.provenanceCells()) {
                objects.addAll(objectsOf(program.activations.get(target),
                        cell, false));
            }
            for (Map.Entry<String, Long> read
                    : store.versionsOf(objects).entrySet()) {
                seeds.merge(read.getKey(), read.getValue(), Math::max);
            }
        }
        return zk.chain(targets, seeds, occurrence -> {
            List<String> senders = new ArrayList<>();
            for (String sender : messages.sendersOf(
                    OccurrenceAddress.parse(occurrence))) {
                String held = byId.get(sender);
                if (held != null) senders.add(held);
            }
            return senders;
        });
    }

    private static List<JsonObject> contentKeys(
            StaticProgram program, RecordedStore store, ZkCausalGraph zk,
            ZkCausalGraph.Chain chain, Collection<String> targets) {
        Set<Integer> seeds = new HashSet<>();
        Set<Integer> owners = new HashSet<>();
        for (String target : targets) {
            Map<String, Object> activation = program.activations.get(target);
            owners.addAll(allObjects(activation, FIELD_OWNERS));
            seeds.addAll(owners);
            seeds.addAll(allObjects(activation, FIELD_REFERENTS));
        }
        List<JsonObject> rows = new ArrayList<>();
        Set<Map<String, Object>> union = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Set<String>>> held : zk.keys(
                chain, seeds, store.versionsOf(owners).keySet()).entrySet()) {
            List<Map<String, Object>> stated = new ArrayList<>();
            for (Map.Entry<String, Set<String>> location
                    : held.getValue().entrySet()) {
                int cut = location.getKey().indexOf('\n');
                String path = location.getKey().substring(cut + 1);
                String slot = chain.paths.get(location.getKey());
                JsonObject row = new JsonObject();
                row.addProperty("schemaVersion", 1);
                row.addProperty("kind", ZkChain.KEYS);
                row.addProperty("occurrenceId", held.getKey());
                row.addProperty("location", path);
                row.addProperty("slot", slot);
                JsonArray pointers = new JsonArray();
                for (String pointer : location.getValue()) pointers.add(pointer);
                row.add("pointers", pointers);
                rows.add(row);
                for (String pointer : location.getValue()) {
                    Map<String, Object> key = new LinkedHashMap<>();
                    key.put("location", path);
                    key.put("slot", slot);
                    key.put("pointer", pointer);
                    stated.add(key);
                }
            }
            Map<String, Object> activation = program.activations.get(
                    held.getKey());
            if (activation != null) {
                activation.put(ZkChain.CONTENT_KEYS, stated);
            }
            union.addAll(stated);
        }
        Map<String, JsonObject> byLocation = new LinkedHashMap<>();
        for (Map<String, Object> key : union) {
            String location = (String) key.get("location");
            String slot = (String) key.get("slot");
            JsonObject row = byLocation.computeIfAbsent(location + "\n"
                    + slot, ignored -> {
                JsonObject keys = new JsonObject();
                keys.addProperty("schemaVersion", 1);
                keys.addProperty("kind", ZkChain.KEYS);
                keys.addProperty("location", location);
                keys.addProperty("slot", slot);
                keys.add("pointers", new JsonArray());
                return keys;
            });
            row.getAsJsonArray("pointers").add((String) key.get("pointer"));
        }
        for (String target : targets) {
            Map<String, Object> activation = program.activations.get(target);
            if (activation == null || union.isEmpty()) continue;
            activation.put(ZkChain.CONTENT_KEYS, new ArrayList<>(union));
            rows.removeIf(row -> target.equals(
                    row.get("occurrenceId").getAsString()));
            for (JsonObject keys : byLocation.values()) {
                JsonObject row = keys.deepCopy();
                row.addProperty("occurrenceId", target);
                rows.add(row);
            }
        }
        return rows;
    }

    @SuppressWarnings("unchecked")
    private static Set<Integer> allObjects(Map<String, Object> activation,
                                           String member) {
        Set<Integer> objects = new HashSet<>();
        Object byField = activation == null ? null : activation.get(member);
        if (!(byField instanceof Map)) return objects;
        for (Object held : ((Map<String, Object>) byField).values()) {
            if (held instanceof Set) objects.addAll((Set<Integer>) held);
        }
        return objects;
    }

    private static void crossStore(StaticProgram program, DemandWalk walk,
                                   StaticScopeMap scopeMap,
                                   RecordedMessages messages,
                                   RecordedStore store,
                                   Collection<String> targets) {
        Set<String> cells = scopeMap.provenanceCells();
        if (store.isEmpty() || cells.isEmpty()) return;
        Map<String, String> byId = new HashMap<>();
        for (String occurrence : program.activations.keySet()) {
            byId.put(OccurrenceAddress.parse(occurrence).id(), occurrence);
        }
        Set<String> crossed = new LinkedHashSet<>();
        for (String target : targets) {
            Map<String, Object> activation = program.activations.get(target);
            Set<Integer> objects = new HashSet<>();
            for (String cell : cells) {
                objects.addAll(objectsOf(activation, cell, false));
            }
            int depth = walk.depth(target) + 1;
            askFetches(program, walk, scopeMap, store, byId, target, objects,
                    depth);
            for (Map.Entry<String, Long> version
                    : store.versionsOf(objects).entrySet()) {
                for (String writer : store.writersUpTo(version.getKey(),
                        version.getValue())) {
                    if (!crossed.add(writer)) continue;
                    if (program.activations.containsKey(writer)
                            && !walk.excluded.contains(writer)) {
                        walk.admitValue(writer, depth, STORE_WRITER_ADMISSION);
                    }
                    for (String sender : messages.sendersOf(
                            OccurrenceAddress.parse(writer))) {
                        String held = byId.get(sender);
                        if (held != null && !walk.excluded.contains(held)) {
                            walk.admitValue(held, depth + 1,
                                    STORE_ITEM_PRODUCER_ADMISSION);
                        }
                    }
                    for (String door : doorsOf(messages, program,
                            OccurrenceAddress.parse(writer))) {
                        String held = byId.get(door);
                        if (held == null || walk.reached.contains(held)
                                || walk.excluded.contains(held)
                                || !readsAFault(rootReads(
                                program.activations.get(held), scopeMap))) {
                            continue;
                        }
                        walk.admit(held, depth + 1,
                                CONTROL_PRODUCER_ADMISSION);
                    }
                }
            }
        }
    }

    private static void askFetches(StaticProgram program, DemandWalk walk,
                                   StaticScopeMap scopeMap,
                                   RecordedStore store,
                                   Map<String, String> byId, String target,
                                   Set<Integer> objects, int depth) {
        for (Map.Entry<RecordedStore.Fetch, String> fetch : dataFlowFetches(
                store, objects).entrySet()) {
            admitFetch(program, walk, scopeMap, byId, fetch.getKey(),
                    fetch.getValue(), depth);
        }
    }

    static Map<RecordedStore.Fetch, String> dataFlowFetches(
            RecordedStore store, Collection<Integer> objects) {
        Map<RecordedStore.Fetch, String> fetches = new LinkedHashMap<>();
        for (RecordedStore.Fetch fetch : store.fetchesOf(objects)) {
            fetches.putIfAbsent(fetch, PROVENANCE_FETCH);
        }
        return fetches;
    }

    @SuppressWarnings("unchecked")
    private static void admitFetch(StaticProgram program, DemandWalk walk,
                                   StaticScopeMap scopeMap,
                                   Map<String, String> byId,
                                   RecordedStore.Fetch fetch, String why,
                                   int depth) {
        String held = byId.get(OccurrenceAddress.parse(fetch.occurrence)
                .id());
        if (held == null) return;
        Map<String, Object> activation = program.activations.get(held);
        List<Map<String, Object>> door = fetchDoor(activation, scopeMap,
                fetch.since, fetch.seq);
        if (door.isEmpty()) return;
        List<Map<String, Object>> stated = (List<Map<String, Object>>)
                activation.computeIfAbsent(STORE_FETCHES,
                        ignored -> new ArrayList<Map<String, Object>>());
        for (Map<String, Object> capture : door) {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put(SiteId.MEMBER, capture.get(SiteId.MEMBER));
            row.put(DeclaredSiteCapture.ORDINAL,
                    capture.get(DeclaredSiteCapture.ORDINAL));
            row.put("fetch", why);
            row.put("location", fetch.location.replace('\n', ':'));
            row.put("version", fetch.version);
            boolean known = false;
            for (Map<String, Object> each : stated) {
                known |= each.get(SiteId.MEMBER).equals(row.get(
                        SiteId.MEMBER)) && each.get(DeclaredSiteCapture
                        .ORDINAL).equals(row.get(DeclaredSiteCapture.ORDINAL));
            }
            if (!known) stated.add(row);
        }
        if (!walk.reached.contains(held) && !walk.excluded.contains(held)) {
            walk.admit(held, depth, STORE_FETCH_ADMISSION);
        }
    }

    static List<Map<String, Object>> fetchDoor(
            Map<String, Object> activation, StaticScopeMap scopeMap,
            long since, long seq) {
        Map<String, Map<String, Object>> latest = new LinkedHashMap<>();
        Map<String, Object> last = null;
        for (Map<String, Object> capture
                : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
            long at = longNumber(capture.get(DeclaredSiteCapture.EVENT_SEQ), 0L);
            if (at <= since || at >= seq
                    || !dataFlowCapture(capture, scopeMap)) {
                continue;
            }
            String site = text(capture.get(SiteId.MEMBER));
            Map<String, Object> held = latest.get(site);
            if (held == null || longNumber(held.get(
                    DeclaredSiteCapture.EVENT_SEQ), 0L) < at) {
                latest.put(site, capture);
            }
            if (last == null || longNumber(last.get(
                    DeclaredSiteCapture.EVENT_SEQ), 0L) < at) {
                last = capture;
            }
        }
        List<Map<String, Object>> door = new ArrayList<>();
        if (last == null) return door;
        String method = SiteId.methodOf(text(last.get(SiteId.MEMBER)));
        for (Map.Entry<String, Map<String, Object>> site : latest.entrySet()) {
            if (SiteId.methodOf(site.getKey()).equals(method)) {
                door.add(site.getValue());
            }
        }
        return door;
    }

    static boolean dataFlowCapture(Map<String, Object> capture,
                                   StaticScopeMap scopeMap) {
        for (StaticScopeMap.Site site : scopeMap.declaredSitesAt(
                text(capture.get(SiteId.MEMBER)),
                text(capture.get(DeclaredSiteCapture.DECLARED_CALLEE)))) {
            if (StaticScopeMap.FAULT_INPUT.equals(site.declared.inputKind)
                    && LibraryCatalog.dataFlowMarker(site.declared.marker)) {
                return true;
            }
        }
        return false;
    }

    static String dataFlowDoors(StaticProgram program, Collection<String> planned,
                                StaticScopeMap scopeMap) {
        int calls = 0;
        int fetching = 0;
        int admitted = 0;
        Map<String, Integer> asked = new TreeMap<>();
        for (String occurrence : planned) {
            Map<String, Object> activation = program.activations.get(
                    occurrence);
            if (activation.containsKey(STORE_FETCHES)) {
                fetching++;
                if (STORE_FETCH_ADMISSION.equals(text(activation.get(
                        ADMISSION_BASIS)))) {
                    admitted++;
                }
            }
            Set<String> doors = new HashSet<>();
            for (Map<String, Object> capture : rows(activation.get(
                    DeclaredSiteCapture.PLAN_FIELD))) {
                if (dataFlowCapture(capture, scopeMap)) {
                    doors.add(SiteId.methodOf(text(capture.get(
                            SiteId.MEMBER))) + "@" + number(capture.get(
                            DeclaredSiteCapture.ORDINAL), -1));
                }
            }
            calls += doors.size();
            Set<String> fetched = new HashSet<>();
            for (Map<String, Object> row : rows(activation.get(
                    STORE_FETCHES))) {
                if (fetched.add(SiteId.methodOf(text(row.get(SiteId.MEMBER)))
                        + "@" + number(row.get(DeclaredSiteCapture.ORDINAL), -1))) {
                    asked.merge(text(row.get("fetch")), 1, Integer::sum);
                }
            }
        }
        int total = 0;
        for (int each : asked.values()) total += each;
        return "data-flow doors: " + calls + " store read(s) in the "
                + planned.size() + " planned occurrence(s), " + total
                + " asked " + asked + ", " + (calls - total)
                + " woven but never asked; " + fetching + " fetching"
                + " occurrence(s), " + admitted + " admitted only as such";
    }

    private static void admitRelevantRoots(StaticProgram program,
            DemandWalk walk, StaticScopeMap scopeMap,
            RecordedMessages messages) throws IOException {
        Map<String, List<RootRead>> reading = new LinkedHashMap<>();
        Map<String, String> occurrenceById = new LinkedHashMap<>();
        Map<String, List<String>> readers = new LinkedHashMap<>();
        Map<String, List<String>> methodsByRegion = new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : program.skeletons.values()) {
            methodsByRegion.put(skeleton.regionId, skeleton.methods);
        }
        for (Map.Entry<String, Map<String, Object>> entry
                : program.activations.entrySet()) {
            OccurrenceAddress address = OccurrenceAddress.parse(entry.getKey());
            occurrenceById.put(address.id(), entry.getKey());
            if (address.context() instanceof CausalContext.Anchor) {
                readers.computeIfAbsent(((CausalContext.Anchor)
                        address.context()).producerEndpointId(),
                        ignored -> new ArrayList<>()).add(address.id());
            }
            List<RootRead> reads = rootReads(entry.getValue(), scopeMap);
            if (!reads.isEmpty()) reading.put(entry.getKey(), reads);
        }
        RootRelevance relevance = new RootRelevance(program.graph,
                walk.writeSites.keySet(), methodsByRegion);
        Set<String> served = new HashSet<>();
        Set<String> crossed = new HashSet<>();
        boolean progressed;
        do {
            progressed = false;
            List<Demand> seeds = new ArrayList<>();
            for (Map.Entry<String, List<RootRead>> entry
                    : reading.entrySet()) {
                String occurrence = entry.getKey();
                if (walk.excluded.contains(occurrence)) continue;
                List<String> regions = performedRegionIds(
                        program.activations.get(occurrence));
                Set<String> through = new LinkedHashSet<>();
                for (RootRead read : entry.getValue()) {
                    RootRelevance.Influence influence = relevance.influence(
                            regions, read.dependencyCell);
                    through.addAll(influence.through(
                            walk.demandedOf(occurrence, influence)));
                }
                if (through.isEmpty()) continue;
                progressed |= walk.admitValue(occurrence, 1,
                        ROOT_RELEVANT_ADMISSION);
                for (String cell : through) {
                    Demand demand = new Demand(occurrence, cell);
                    if (!walk.visited.contains(demand)) seeds.add(demand);
                }
            }
            for (String occurrence : new ArrayList<>(walk.reached)) {
                List<String> regions = performedRegionIds(
                        program.activations.get(occurrence));
                for (Attach attach : walk.attaches(occurrence)) {
                    String key = occurrence + "\n" + attach.port + "\n"
                            + attach.leg;
                    if (crossed.contains(key)) continue;
                    Set<String> through = new LinkedHashSet<>();
                    for (String cell : walk.attachCells.getOrDefault(
                            attach.port, Collections.<String>emptySet())) {
                        RootRelevance.Influence influence =
                                relevance.influence(regions, cell);
                        through.addAll(influence.through(
                                walk.demandedOf(occurrence, influence)));
                    }
                    if (through.isEmpty()) continue;
                    crossed.add(key);
                    progressed |= walk.admitValue(occurrence, 1,
                            ROOT_RELEVANT_ADMISSION);
                    walk.crossMessage(occurrence, attach, seeds::add);
                    for (String cell : through) {
                        Demand demand = new Demand(occurrence, cell);
                        if (!walk.visited.contains(demand)) seeds.add(demand);
                    }
                }
            }
            for (String occurrence : new ArrayList<>(walk.reached)) {
                if (served.contains(occurrence)) continue;
                if (doorBasis(text(program.activations.get(occurrence)
                        .get(ADMISSION_BASIS)))) {
                    if (!messages.doorsOf(OccurrenceAddress.parse(occurrence))
                            .isEmpty()) {
                        planGap(program.planGaps, GapKind.ADMISSION_GAP,
                                GapClass.DIAGNOSTIC, occurrence
                                        + " door occurrence", "a control"
                                        + " producer or a store fetch"
                                        + " contributes no value: the doors"
                                        + " of the message that started it"
                                        + " are not asked");
                    }
                    continue;
                }
                served.add(occurrence);
                Set<String> doors = doorsOf(messages, program,
                        OccurrenceAddress.parse(occurrence));
                doors.addAll(messages.replyLegsOf(
                        OccurrenceAddress.parse(occurrence), readers));
                for (String door : doors) {
                    String held = occurrenceById.get(door);
                    if (held == null || walk.reached.contains(held)
                            || walk.excluded.contains(held)
                            || !readsAFault(reading.get(held))) {
                        continue;
                    }
                    walk.admit(held, walk.depth(occurrence) + 1,
                            CONTROL_PRODUCER_ADMISSION);
                    progressed = true;
                }
            }
            progressed |= !seeds.isEmpty();
            walk.walk(seeds);
        } while (progressed);
    }

    private static Set<String> doorsOf(RecordedMessages messages,
                                       StaticProgram program,
                                       OccurrenceAddress occurrence) {
        Set<String> doors = new LinkedHashSet<>(messages.doorsOf(occurrence));
        Set<String> stances = messages.doorStancesOf(occurrence);
        Set<String> handlers = messages.handlerStancesOf(occurrence);
        if (stances.isEmpty() && handlers.isEmpty()) return doors;
        String own = ContextShape.Stance.of(occurrence).render();
        int ownTurn = 0;
        int handling = 0;
        Map<String, List<String>> byStance = program.activationsByStance();
        Set<String> asked = new LinkedHashSet<>(stances);
        asked.addAll(handlers);
        for (String stance : asked) {
            for (String activation : byStance.getOrDefault(stance,
                    Collections.<String>emptyList())) {
                String id = OccurrenceAddress.parse(activation).id();
                if (id.equals(occurrence.id())) continue;
                if (stances.contains(stance) && !stance.equals(own)) {
                    doors.add(id);
                } else if (stances.contains(stance)) {
                    ownTurn++;
                } else {
                    handling++;
                }
            }
        }
        if (ownTurn > 0) {
            planGap(program.planGaps, GapKind.ADMISSION_GAP,
                    GapClass.DIAGNOSTIC, occurrence.id() + " own turn",
                    ownTurn + " other occurrence(s) of this occurrence's own"
                            + " turn hold no door of the message that started"
                            + " it: they are what it started too");
        }
        if (handling > 0) {
            planGap(program.planGaps, GapKind.ADMISSION_GAP,
                    GapClass.DIAGNOSTIC, occurrence.id() + " handlers",
                    handling + " occurrence(s) of turns standing on the"
                            + " message that started this occurrence (its"
                            + " handlers) hold no door of it: it started"
                            + " them");
        }
        return doors;
    }

    private static boolean readsAFault(List<RootRead> reads) {
        if (reads == null) return false;
        for (RootRead read : reads) {
            if (read.fault) return true;
        }
        return false;
    }

    private static Set<Integer> objectsOf(Map<String, Object> activation,
                                          String cell, boolean referents) {
        Set<Integer> objects = new HashSet<>(field(activation, FIELD_OWNERS,
                cell));
        if (referents) {
            objects.addAll(field(activation, FIELD_REFERENTS, cell));
        }
        return objects;
    }

    @SuppressWarnings("unchecked")
    private static Set<Integer> field(Map<String, Object> activation,
                                      String member, String cell) {
        Object byField = activation.get(member);
        if (!(byField instanceof Map)) return Collections.emptySet();
        Object held = ((Map<String, Object>) byField).get(cell);
        return held instanceof Set ? (Set<Integer>) held
                : Collections.<Integer>emptySet();
    }

    private enum Scope {
        CONTEXT(CONFINED_WRITERS),
        ESCAPED(ESCAPED_WRITERS),
        REACHED("");

        private final String member;

        Scope(String member) {
            this.member = member;
        }

        private Scope wider(Scope other) {
            return other.ordinal() > ordinal() ? other : this;
        }
    }

    private static final int CONFINED_FIRST = 3;

    public static String ownerClass(String cell) {
        int colon = cell.indexOf(':');
        return cell.startsWith("<") && colon > 1 ? cell.substring(1, colon)
                : cell;
    }

    private static int[] namedObjects(Map<String, Object> activation) {
        Object named = activation.get(NAMED_OBJECTS);
        return named instanceof int[] ? (int[]) named : new int[0];
    }

    private static final class Demanded {
        private final Set<Integer> objects = new HashSet<>();
        private boolean any;

        private void add(Set<Integer> owners) {
            if (owners.isEmpty()) {
                any = true;
            } else {
                objects.addAll(owners);
            }
        }

        private boolean heldBy(Map<String, Object> activation, String cell) {
            Set<Integer> held = objectsOf(activation, cell, true);
            return any || held.isEmpty()
                    || !Collections.disjoint(held, objects);
        }
    }

    static boolean pairs(String readerNode, String writerNode,
                         boolean readerClient, boolean writerClient) {
        return readerClient || writerClient || readerNode.equals(writerNode);
    }

    private static final class DemandWalk {
        private final StaticProgram program;
        private final StaticScopeMap scopeMap;
        private final RegionDemandIndex demands;
        private final Map<String, List<StaticScopeMap.Site>> writeSites;
        private final Set<String> wireConsumers = new HashSet<>();
        private final Map<String, String> nodes = new HashMap<>();
        private final Set<String> reached = new LinkedHashSet<>();
        private final Set<String> excluded;
        private final Map<String, Integer> depths = new HashMap<>();
        private final Set<Demand> visited = new HashSet<>();
        private final Set<Demand> writersCrossed = new HashSet<>();
        private final Map<StaticScopeMap.Site, SiteWriters> siteWriters =
                new IdentityHashMap<>();
        private final Map<String, Map<String, Demanded>> carriers =
                new HashMap<>();
        private final Set<String> consumers = new HashSet<>();
        private final Map<String, List<CutPort>> cutPorts;
        private final Map<String, Set<String>> attachCells = new HashMap<>();
        private final Map<String, Set<String>> exportCells = new HashMap<>();
        private final Map<String, List<String>> exporters = new HashMap<>();
        private final Map<String, Map<String, Long>> senders =
                new HashMap<>();
        private final Map<String, Set<String>> unpaired =
                new LinkedHashMap<>();
        private final Set<String> sources = new HashSet<>();
        private final Set<String> fixedDeciders = new LinkedHashSet<>();
        private ZkCausalGraph zk;
        private ZkCausalGraph.Chain chain;
        private final Set<String> offChain = new LinkedHashSet<>();
        private final Set<String> storeWriters = new HashSet<>();
        private final Set<String> heldApart = new HashSet<>();
        private final RecordedHeap heap;
        private final Map<String, Set<Integer>> reachable = new HashMap<>();
        private final Map<String, Map<Scope, Map<String, Set<String>>>>
                notCrossed = new LinkedHashMap<>();

        private DemandWalk(StaticProgram program, RegionDemandIndex demands,
                           StaticScopeMap scopeMap,
                           Map<String, List<CutPort>> cutPorts,
                           Set<String> excluded, RecordedHeap heap) {
            this.program = program;
            this.heap = heap;
            this.scopeMap = scopeMap;
            this.demands = demands;
            this.cutPorts = cutPorts;
            this.excluded = excluded;
            this.writeSites = scopeMap.writeSitesByCell();
            sources.addAll(scopeMap.trackedCells());
            for (StaticScopeMap.Site declared : scopeMap.declaredSites()) {
                if (!declared.declared.inputKind.isEmpty()) {
                    sources.add(declared.declared.dependencyCell);
                }
            }
            for (Map<String, Object> edge : program.graph) {
                if ("wire_handoff".equals(text(edge.get("kind")))) {
                    wireConsumers.add(text(edge.get("toCell")));
                }
            }
            for (List<CutPort> ports : cutPorts.values()) {
                for (CutPort port : ports) {
                    String portId = text(port.row.get("portId"));
                    if (!"IN".equals(port.side)) {
                        exportCells.computeIfAbsent(portId,
                                ignored -> new LinkedHashSet<>())
                                .addAll(port.cells);
                        continue;
                    }
                    attachCells.computeIfAbsent(portId,
                            ignored -> new LinkedHashSet<>())
                            .addAll(port.cells);
                    sources.addAll(port.cells);
                }
            }
            for (Map.Entry<String, Map<String, Object>> entry
                    : program.activations.entrySet()) {
                nodes.put(entry.getKey(), OccurrenceAddress.parse(
                        entry.getKey()).node().render());
                for (Map<String, Object> sent : rows(entry.getValue().get(
                        SENT_EXCHANGE_LEGS))) {
                    senders.computeIfAbsent(text(sent.get("exchangeLeg")),
                            ignored -> new LinkedHashMap<>())
                            .put(entry.getKey(), longNumber(sent.get(
                                    "transportEventSeq"), -1L));
                }
                for (Map<String, Object> capture : rows(entry.getValue().get(
                        OBSERVED_COMMUNICATION_CAPTURES))) {
                    String leg = text(capture.get("exchangeLeg"));
                    if ("OUT".equals(text(capture.get("side")))
                            && !leg.isEmpty()) {
                        exporters.computeIfAbsent(wireKey(text(capture.get(
                                "portId")), leg), ignored -> new ArrayList<>())
                                .add(entry.getKey());
                    }
                }
            }
        }

        private static String wireKey(String portId, String leg) {
            return portId + "\n" + leg;
        }

        private void admit(String occurrence, int depth, String basis) {
            admit(occurrence, depth);
            program.activations.get(occurrence).put(ADMISSION_BASIS, basis);
        }

        private void admit(String occurrence, int depth) {
            reached.add(occurrence);
            heldApart.add(occurrence);
            recordDepth(occurrence, depth);
        }

        private boolean admitValue(String occurrence, int depth,
                                   String basis) {
            if (!reached.contains(occurrence)) {
                admit(occurrence, depth, basis);
                return true;
            }
            Map<String, Object> activation = program.activations.get(
                    occurrence);
            if (!doorBasis(text(activation.get(ADMISSION_BASIS)))) {
                return false;
            }
            activation.put(ADMISSION_BASIS, basis);
            recordDepth(occurrence, depth);
            return true;
        }

        private void reach(String occurrence, int depth, String basis)
                throws IOException {
            recordDepth(occurrence, depth);
            Map<String, Object> activation = program.activations.get(
                    occurrence);
            if (!reached.add(occurrence)) {
                if (doorBasis(text(activation.get(ADMISSION_BASIS)))) {
                    activation.put(ADMISSION_BASIS, basis);
                }
                return;
            }
            String held = text(activation.get(ADMISSION_BASIS));
            if (!held.isEmpty()) {
                throw new IOException("conflicting runtime activation "
                        + "admission basis for " + occurrence + ": " + held);
            }
            activation.put(ADMISSION_BASIS, basis);
        }

        private int depth(String occurrence) {
            Integer known = depths.get(occurrence);
            return known == null ? 1 : known;
        }

        private void recordDepth(String occurrence, int depth) {
            Integer known = depths.get(occurrence);
            if (known == null || depth < known) depths.put(occurrence, depth);
        }

        private Set<String> demandedOf(String occurrence,
                                       RootRelevance.Influence influence) {
            Map<String, Object> activation = program.activations.get(
                    occurrence);
            Map<String, Demanded> onNode = carriers.getOrDefault(
                    nodes.get(occurrence),
                    Collections.<String, Demanded>emptyMap());
            Set<String> ends = new LinkedHashSet<>();
            for (String carrier : influence.carriers) {
                Demanded demanded = onNode.get(carrier);
                if (demanded != null && demanded.heldBy(activation, carrier)) {
                    ends.add(carrier);
                }
            }
            for (String consumer : influence.consumers) {
                if (consumers.contains(consumer)) ends.add(consumer);
            }
            return ends;
        }

        private void walk(Collection<Demand> seeds) throws IOException {
            Map<String, Map<String, Object>> instances = program.activations;
            Deque<Demand> work = new ArrayDeque<>();
            Consumer<Demand> queue = demand -> {
                if (visited.add(demand)) work.add(demand);
            };
            seeds.forEach(queue);
            while (!work.isEmpty()) {
                Demand demand = work.removeFirst();
                String occurrenceId = demand.occurrence;
                String cell = demand.cell;
                if (wireConsumers.contains(cell)) consumers.add(cell);
                crossWire(occurrenceId, cell, queue);
                List<StaticScopeMap.Site> writers = writeSites.get(cell);
                if (writers == null || writers.isEmpty()) {
                    for (String from
                            : demands.incomingCells(occurrenceId, cell)) {
                        queue.accept(new Demand(occurrenceId, from));
                    }
                    continue;
                }
                String node = nodes.get(occurrenceId);
                Map<String, Object> reader = instances.get(occurrenceId);
                Set<Integer> readObjects = objectsOf(reader, cell, true);
                carriers.computeIfAbsent(node, ignored -> new HashMap<>())
                        .computeIfAbsent(cell, ignored -> new Demanded())
                        .add(readObjects);
                boolean stored = zk.decoded(readObjects);
                for (StaticScopeMap.Site site : writers) {
                    SiteWriters held = siteWriters.computeIfAbsent(site,
                            SiteWriters::new);
                    for (String writerOccurrence : held.candidates) {
                        if (writerOccurrence.equals(occurrenceId)
                                || excluded.contains(writerOccurrence)
                                || !pairs(node, nodes.get(writerOccurrence),
                                        client(occurrenceId),
                                        client(writerOccurrence))
                                || holdsOthersOnly(writerOccurrence,
                                        occurrenceId, cell, site)) {
                            continue;
                        }
                        if ((stored || zk.zkCarried(writerOccurrence))
                                && !chain.holds(writerOccurrence)) {
                            offChain.add(writerOccurrence);
                            continue;
                        }
                        if (!held.storers.contains(writerOccurrence)
                                && !held.movable(writerOccurrence)) {
                            fixedDeciders.add(writerOccurrence);
                            continue;
                        }
                        storeWriters.add(writerOccurrence);
                        reach(writerOccurrence, depth(occurrenceId) + 1,
                                SHARED_LOCATION_DEMAND_ADMISSION);
                        if (!writersCrossed.add(new Demand(writerOccurrence,
                                cell))) {
                            continue;
                        }
                        for (String guard : demands.guardCells(
                                writerOccurrence, cell)) {
                            queue.accept(new Demand(writerOccurrence, guard));
                        }
                    }
                }
                for (String guard : demands.guardCells(occurrenceId, cell)) {
                    queue.accept(new Demand(occurrenceId, guard));
                }
            }
        }

        private final class SiteWriters {
            private final Set<String> storers;
            private final Map<String, List<String>> deciders;
            private final List<String> candidates;
            private final Map<String, Boolean> movable = new HashMap<>();

            private SiteWriters(StaticScopeMap.Site site) {
                List<String> stored = demands.storers(site);
                storers = new HashSet<>(stored);
                deciders = demands.deciders(site);
                Set<String> all = new LinkedHashSet<>(stored);
                all.addAll(deciders.keySet());
                candidates = new ArrayList<>(all);
            }

            private boolean movable(String decider) {
                return movable.computeIfAbsent(decider, ignored ->
                        DemandWalk.this.movable(decider,
                                deciders.get(decider)));
            }
        }

        private boolean client(String occurrence) {
            return CausynthTraceRecorder.WORKLOAD_KIND.equals(text(
                    program.activations.get(occurrence).get(
                            RuntimeRegionPlanner.SOURCE_KIND)));
        }

        private boolean holdsOthersOnly(String writerOccurrence,
                                        String readerOccurrence,
                                        String cell,
                                        StaticScopeMap.Site site) {
            Map<String, Object> writer =
                    program.activations.get(writerOccurrence);
            Map<String, Object> reader =
                    program.activations.get(readerOccurrence);
            boolean mutation = !site.declaredCallee.isEmpty();
            Set<Integer> wroteOn = field(writer, FIELD_OWNERS, cell);
            Set<Integer> readOn = field(reader, FIELD_OWNERS, cell);
            Set<Integer> receivers = field(reader, RECEIVER_HOLDERS, cell);
            if (!receivers.isEmpty()) {
                readOn = new HashSet<>(readOn);
                readOn.addAll(receivers);
            }
            Set<Integer> wroteHeld = mutation
                    ? field(writer, FIELD_REFERENTS, cell)
                    : Collections.<Integer>emptySet();
            Set<Integer> readHeld = mutation
                    ? field(reader, FIELD_REFERENTS, cell)
                    : Collections.<Integer>emptySet();
            if (wroteOn.isEmpty() && wroteHeld.isEmpty()) return false;
            if (readOn.isEmpty() && readHeld.isEmpty()) {
                Set<Integer> reach = reachable.computeIfAbsent(
                        readerOccurrence, ignored -> heap.reachable(
                                namedObjects(reader)));
                long readerContext = heap.contextOfRoot(longNumber(
                        reader.get("rootCallId"), -1L));
                Scope scope = Scope.CONTEXT;
                for (Set<Integer> objects : Arrays.asList(wroteOn,
                        wroteHeld)) {
                    for (int object : objects) {
                        scope = scope.wider(scopeOf(object, reach,
                                readerContext));
                    }
                }
                if (scope == Scope.REACHED) return false;
                notCrossed.computeIfAbsent(readerOccurrence,
                        ignored -> new TreeMap<>())
                        .computeIfAbsent(scope, ignored -> new TreeMap<>())
                        .computeIfAbsent(cell, ignored -> new TreeSet<>())
                        .add(writerOccurrence);
                return scope == Scope.CONTEXT;
            }
            return Collections.disjoint(wroteOn, readOn)
                    && Collections.disjoint(wroteOn, readHeld)
                    && Collections.disjoint(wroteHeld, readOn)
                    && Collections.disjoint(wroteHeld, readHeld);
        }

        private Scope scopeOf(int object, Set<Integer> reach,
                              long readerContext) {
            if (object == 0 || reach.contains(object)) return Scope.REACHED;
            long context = heap.confinement(object);
            return context != RecordedHeap.NOWHERE
                    && readerContext != RecordedHeap.NOWHERE
                    && context != readerContext
                    ? Scope.CONTEXT : Scope.ESCAPED;
        }

        private void stateConfinedWriters(List<Map<String, Object>> gaps) {
            for (Map.Entry<String, Map<Scope, Map<String, Set<String>>>>
                    reader : notCrossed.entrySet()) {
                Map<String, Object> activation =
                        program.activations.get(reader.getKey());
                for (Map.Entry<Scope, Map<String, Set<String>>> scope
                        : reader.getValue().entrySet()) {
                    Map<String, Integer> counts = new TreeMap<>();
                    for (Map.Entry<String, Set<String>> field
                            : scope.getValue().entrySet()) {
                        counts.put(field.getKey(), field.getValue().size());
                        if (scope.getKey() == Scope.CONTEXT) {
                            confinedGap(gaps, reader.getKey(),
                                    scope.getKey(), field.getKey(),
                                    field.getValue());
                        }
                    }
                    activation.put(scope.getKey().member, counts);
                }
            }
        }

        private void confinedGap(List<Map<String, Object>> gaps,
                                 String reader, Scope scope, String cell,
                                 Set<String> writers) {
            List<String> first = new ArrayList<>(writers).subList(0,
                    Math.min(CONFINED_FIRST, writers.size()));
            Map<String, Object> row = planGap(gaps,
                    GapKind.CLOSURE_CONFINED, GapClass.DIAGNOSTIC,
                    scope.name() + " " + cell + " @ " + reader,
                    writers.size() + " writer(s) of " + cell + " were not"
                            + " crossed to for this reader, which never"
                            + " touched the field in the recording: each"
                            + " wrote it only on objects that, with every"
                            + " recorded holder above them, the recorded"
                            + " events mention under one causal context,"
                            + " not the reader's; untraced code between"
                            + " two contexts may have handed them over"
                            + " (first: " + String.join(", ", first) + ")");
            row.put("scope", scope.name());
            row.put("ownerClass", ownerClass(cell));
            row.put("field", cell);
            row.put("reader", reader);
            row.put("writers", writers.size());
            row.put("first", first);
        }

        private void crossWire(String occurrence, String cell,
                               Consumer<Demand> work) throws IOException {
            Set<String> ports = new LinkedHashSet<>();
            for (String regionId : performedRegionIds(
                    program.activations.get(occurrence))) {
                for (CutPort port : cutPorts.getOrDefault(regionId,
                        Collections.<CutPort>emptyList())) {
                    if ("IN".equals(port.side) && port.cells.contains(cell)) {
                        ports.add(text(port.row.get("portId")));
                    }
                }
            }
            if (ports.isEmpty()) return;
            boolean paired = false;
            for (Attach attach : attaches(occurrence)) {
                if (ports.contains(attach.port)) {
                    paired |= crossMessage(occurrence, attach, work)
                            || crossRelay(occurrence, attach, work);
                }
            }
            if (!paired) {
                unpaired.computeIfAbsent(cell,
                        ignored -> new LinkedHashSet<>()).addAll(ports);
            }
        }

        private List<Attach> attaches(String occurrence) {
            List<Attach> held = new ArrayList<>();
            for (Map<String, Object> capture : rows(program.activations.get(
                    occurrence).get(OBSERVED_COMMUNICATION_CAPTURES))) {
                String leg = text(capture.get("exchangeLeg"));
                if ("IN".equals(text(capture.get("side")))
                        && !leg.isEmpty()) {
                    held.add(new Attach(text(capture.get("portId")), leg,
                            longNumber(capture.get("eventSeq"), -1L)));
                }
            }
            return held;
        }

        private boolean crossMessage(String occurrence, Attach attach,
                                     Consumer<Demand> work)
                throws IOException {
            return crossExports(occurrence, attach, depth(occurrence) + 1,
                    work);
        }

        private boolean crossRelay(String occurrence, Attach attach,
                                   Consumer<Demand> work)
                throws IOException {
            boolean paired = false;
            for (Map.Entry<String, Long> sender : senders.getOrDefault(
                    attach.leg, Collections.<String, Long>emptyMap())
                    .entrySet()) {
                if (sender.getKey().equals(occurrence)
                        || excluded.contains(sender.getKey())) {
                    continue;
                }
                for (Attach received : attaches(sender.getKey())) {
                    if (received.port.equals(attach.port)
                            && !received.leg.equals(attach.leg)
                            && received.seq < sender.getValue()) {
                        paired |= crossExports(sender.getKey(), received,
                                depth(occurrence) + 1, work);
                    }
                }
            }
            return paired;
        }

        private boolean crossExports(String holder, Attach attach, int depth,
                                     Consumer<Demand> work)
                throws IOException {
            boolean paired = false;
            for (String producer : exporters.getOrDefault(wireKey(
                    attach.port, attach.leg),
                    Collections.<String>emptyList())) {
                if (producer.equals(holder) || excluded.contains(producer)) {
                    continue;
                }
                paired = true;
                heldApart.add(producer);
                reach(producer, depth, WIRE_PRODUCER_ADMISSION);
                for (String handed : exportCells.getOrDefault(attach.port,
                        Collections.<String>emptySet())) {
                    work.accept(new Demand(producer, handed));
                }
            }
            return paired;
        }

        private boolean movable(String occurrence, List<String> guards) {
            Set<String> seen = new HashSet<>();
            Deque<String> work = new ArrayDeque<>();
            for (String guard : guards) work.addAll(demands.operandsOf(guard));
            if (work.isEmpty()) return true;
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!seen.add(cell)) continue;
                if (sources.contains(cell)) return true;
                work.addAll(demands.incomingCells(occurrence, cell));
            }
            return false;
        }

        private void classDeciders(RecordedAccesses accesses,
                Function<CausalContext, List<String>> shapes) {
            Map<String, List<String>> groups = new LinkedHashMap<>();
            for (String occurrence : reached) {
                Map<String, Object> activation = program.activations.get(
                        occurrence);
                String signature = text(activation.get(SIGNATURE));
                if (!storeWriters.contains(occurrence)
                        || heldApart.contains(occurrence)
                        || signature.isEmpty()
                        || mintsRoot(activation)
                        || !rows(activation.get(
                                OBSERVED_COMMUNICATION_CAPTURES)).isEmpty()
                        || accesses.stored(demandedOn(occurrence),
                                seq(occurrence, FIRST_SEQ),
                                seq(occurrence, LAST_SEQ),
                                callsOf(occurrence))) {
                    continue;
                }
                OccurrenceAddress address = OccurrenceAddress.parse(
                        occurrence);
                List<String> path = new ArrayList<>();
                for (Frame frame : address.index().frames()) {
                    path.add(frame.callSite());
                }
                groups.computeIfAbsent(nodes.get(occurrence) + "\n"
                        + address.regionId() + "\n"
                        + shapes.apply(address.context()) + "\n" + path
                        + "\n" + signature, ignored -> new ArrayList<>())
                        .add(occurrence);
            }
            for (List<String> group : groups.values()) {
                if (group.size() < 2) continue;
                group.sort(Comparator.comparingLong(occurrence -> seq(
                        occurrence, FIRST_SEQ)));
                Set<String> cells = demandedOn(group.get(0));
                List<String> members = new ArrayList<>();
                for (String occurrence : group) {
                    if (!members.isEmpty()) {
                        String previous = members.get(members.size() - 1);
                        Set<Long> own = callsOf(previous);
                        own.addAll(callsOf(occurrence));
                        if (accesses.touched(cells, seq(previous, FIRST_SEQ),
                                seq(occurrence, LAST_SEQ), own)) {
                            planOnce(members);
                            members = new ArrayList<>();
                        }
                    }
                    members.add(occurrence);
                }
                planOnce(members);
            }
        }

        private boolean mintsRoot(Map<String, Object> activation) {
            for (Map<String, Object> capture
                    : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
                for (StaticScopeMap.Site site : scopeMap.declaredSitesAt(
                        text(capture.get(SiteId.MEMBER)),
                        text(capture.get(
                                DeclaredSiteCapture.DECLARED_CALLEE)))) {
                    if (!site.declared.inputKind.isEmpty()) return true;
                }
            }
            return false;
        }

        private Set<String> demandedOn(String occurrence) {
            return carriers.getOrDefault(nodes.get(occurrence),
                    Collections.<String, Demanded>emptyMap()).keySet();
        }

        private Set<Long> callsOf(String occurrence) {
            return new HashSet<>(MapFields.longValues(program.activations
                    .get(occurrence).get("callIds")));
        }

        private long seq(String occurrence, String member) {
            return longNumber(program.activations.get(occurrence).get(member),
                    -1L);
        }

        private void planOnce(List<String> members) {
            if (members.size() < 2) return;
            String first = members.get(0);
            for (String member : members.subList(1, members.size())) {
                recordDepth(first, depth(member));
                reached.remove(member);
                program.activations.get(member).remove(ADMISSION_BASIS);
            }
            Map<String, Object> deciderClass = new LinkedHashMap<>();
            deciderClass.put("members", members.size());
            deciderClass.put("first", first);
            deciderClass.put("last", members.get(members.size() - 1));
            program.activations.get(first).put(DECIDER_CLASS, deciderClass);
        }

        private void stateOffChain(List<Map<String, Object>> gaps) {
            if (offChain.isEmpty()) return;
            planGap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "ZooKeeper causal chain", offChain.size() + " writer(s)"
                            + " of a demanded cell read, decoded or were"
                            + " called back on a store location off the"
                            + " targets' chain (" + chain.paths.size()
                            + " location(s), " + chain.occurrences.size()
                            + " occurrence(s)) and are not planned, e.g. "
                            + offChain.iterator().next());
        }

        private void stateFixedDeciders(List<Map<String, Object>> gaps) {
            Map<String, Integer> byRegion = new LinkedHashMap<>();
            for (String occurrence : fixedDeciders) {
                if (reached.contains(occurrence)) continue;
                byRegion.merge(text(program.activations.get(occurrence)
                        .get("regionId")), 1, Integer::sum);
            }
            for (Map.Entry<String, Integer> region : byRegion.entrySet()) {
                planGap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        region.getKey(), region.getValue() + " occurrence(s)"
                                + " of this region took the arm of a guard of"
                                + " a demanded store away from it, at a"
                                + " decision no root, tracked read or"
                                + " attach reaches there, so no world the"
                                + " engine expresses makes them store: none"
                                + " is planned as its writer");
            }
        }

        private void stateUnpairedWires(List<Map<String, Object>> gaps) {
            for (Map.Entry<String, Set<String>> entry : unpaired.entrySet()) {
                planGap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        entry.getKey(), "the failure's demand reached this "
                                + "consumer cell of ports " + entry.getValue()
                                + " where the recording bound no capture of "
                                + "them to a message an export of them was "
                                + "bound to, so no producer of the value is "
                                + "planned and it stays the value the "
                                + "recording attached");
            }
        }
    }

    private static <T> List<T> foldedUnion(
            StaticProgram program, StaticProgram.RegionRow skeleton,
            List<String> foldedRegionIds,
            Function<StaticProgram.RegionRow, Collection<T>> catalog) {
        List<T> union = new ArrayList<>(catalog.apply(skeleton));
        Set<T> held = new HashSet<>(union);
        for (String folded : foldedRegionIds) {
            StaticProgram.RegionRow row = program.skeletons.get(folded);
            if (row == null) continue;
            for (T item : catalog.apply(row)) {
                if (held.add(item)) union.add(item);
            }
        }
        return union;
    }

    private static String exceptionContextRegion(
            StaticProgram program, Map<String, Object> activation) {
        if (text(activation.get("selection")).startsWith("EXCEPTION")) {
            return text(activation.get("regionId"));
        }
        for (String regionId : strings(activation.get(FOLDED_REGION_IDS))) {
            StaticProgram.RegionRow folded = program.skeletons.get(regionId);
            if (folded != null && folded.selection.startsWith("EXCEPTION")) {
                return regionId;
            }
        }
        return "";
    }

    private static final class Demand {
        private final String occurrence;
        private final String cell;
        private final int hash;

        private Demand(String occurrence, String cell) {
            this.occurrence = occurrence;
            this.cell = cell;
            this.hash = 31 * occurrence.hashCode() + cell.hashCode();
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Demand)) return false;
            Demand that = (Demand) other;
            return hash == that.hash && occurrence.equals(that.occurrence)
                    && cell.equals(that.cell);
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    private static void applyClosure(StaticProgram program,
                                     Set<String> reached) {
        Set<String> retainedRegions = new LinkedHashSet<>();
        for (String key : reached) {
            retainedRegions.add(text(program.activations.get(key).get(
                    "regionId")));
        }
        program.regions.removeIf(region -> !retainedRegions.contains(
                text(region.get("regionId"))));
        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            Set<String> occurrences = new LinkedHashSet<>();
            for (String key : reached) {
                Map<String, Object> instance = program.activations.get(key);
                if (!regionId.equals(text(instance.get("regionId")))) {
                    continue;
                }
                occurrences.add(key);
            }
            region.put("runtimeOccurrenceIds",
                    new ArrayList<>(occurrences));
            region.put("symbolicInputs", new ArrayList<Map<String, Object>>());
            region.put("outputs", new ArrayList<Map<String, Object>>());
        }
    }

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

    private static List<Map<String, Object>> branches(
            List<Map<String, Object>> edges) {
        Map<String, List<Map<String, Object>>> bySite = guardsBySite(edges);
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

    private static Map<String, List<Map<String, Object>>> guardsBySite(
            Collection<Map<String, Object>> edges) {
        Map<String, List<Map<String, Object>>> bySite = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) continue;
            String site = text(edge.get("siteId"));
            if (site.isEmpty()) continue;
            bySite.computeIfAbsent(site, ignored -> new ArrayList<>())
                    .add(edge);
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

    private static String contextKey(String region, String cell) {
        return region + "\n" + cell;
    }

    public static Map<String, Object> planGap(
            List<Map<String, Object>> gaps, GapKind kind, GapClass cls,
            String subject, String detail) {
        for (Map<String, Object> existing : gaps) {
            if (kind.name().equals(text(existing.get("kind")))
                    && subject.equals(text(existing.get("subject")))) {
                return existing;
            }
        }
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 1);
        row.put("kind", kind.name());
        row.put("cls", cls.name());
        row.put("subject", subject);
        row.put("detail", detail);
        gaps.add(row);
        return row;
    }

    private static void sortByEventSeq(List<Map<String, Object>> rows) {
        rows.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
    }

    private static final class RegionDemandIndex {
        private final Map<String, List<String>> regionsByOccurrence =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> methodsByOccurrence =
                new HashMap<>();
        private final Map<String, List<String>> occurrencesByMethod =
                new HashMap<>();
        private final Map<String, Set<String>> occurrencesByDecision =
                new HashMap<>();
        private final Map<String, Set<String>> guardOperands =
                new HashMap<>();
        private final Map<String, Map<String, Set<String>>> localIncoming =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Set<String>>> guardIncoming =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                explicitFatalSeedsBySite = new LinkedHashMap<>();
        private final Set<String> pathSites = new LinkedHashSet<>();

        private RegionDemandIndex(StaticProgram program,
                                  StaticScopeMap scopeMap,
                                  List<Map<String, Object>> branches) {
            for (StaticScopeMap.Site target : scopeMap.targetSites()) {
                pathSites.addAll(target.pathSites());
            }
            Map<Long, List<String>> occurrencesByCall = new HashMap<>();
            for (Map.Entry<String, Map<String, Object>> entry
                    : program.activations.entrySet()) {
                regionsByOccurrence.put(entry.getKey(),
                        performedRegionIds(entry.getValue()));
                methodsByOccurrence.put(entry.getKey(), new HashSet<>(
                        strings(entry.getValue().get("observedMethods"))));
                for (String method : methodsByOccurrence.get(entry.getKey())) {
                    occurrencesByMethod.computeIfAbsent(method,
                            ignored -> new ArrayList<>()).add(entry.getKey());
                }
                for (Long call : MapFields.longValues(
                        entry.getValue().get("callIds"))) {
                    occurrencesByCall.computeIfAbsent(call,
                            ignored -> new ArrayList<>()).add(entry.getKey());
                }
            }
            for (Map<String, Object> branch : branches) {
                String site = text(branch.get("siteId"));
                Object outcome = branch.get("outcome");
                for (String occurrence : occurrencesByCall.getOrDefault(
                        longNumber(branch.get("callId"), -1L),
                        Collections.<String>emptyList())) {
                    for (String key : new String[] {decision(site, null),
                            decision(site, outcome instanceof Boolean
                                    ? (Boolean) outcome : null)}) {
                        occurrencesByDecision.computeIfAbsent(key,
                                ignored -> new LinkedHashSet<>())
                                .add(occurrence);
                    }
                }
            }
            Set<String> selectedRegions = new LinkedHashSet<>();
            for (Map<String, Object> region : program.regions) {
                String regionId = text(region.get("regionId"));
                selectedRegions.add(regionId);
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
            for (Map<String, Object> edge : program.graph) {
                String from = text(edge.get("fromCell"));
                String to = text(edge.get("toCell"));
                String method = text(edge.get("method"));
                if (from.isEmpty() || to.isEmpty()) continue;
                if ("GUARD".equals(text(edge.get("transferKind")))
                        && to.equals(text(edge.get("siteId")))) {
                    guardOperands.computeIfAbsent(to,
                            ignored -> new LinkedHashSet<>()).add(from);
                }
                for (String regionId
                        : program.skeletonRegionsHolding(method)) {
                    if (!selectedRegions.contains(regionId)) continue;
                    add(localIncoming, contextKey(regionId, to), from,
                            method);
                    if ("GUARD".equals(text(edge.get("transferKind")))) {
                        add(guardIncoming, contextKey(regionId, to), from,
                                method);
                    }
                }
            }
        }

        private Map<String, List<Map<String, Object>>> observedFatalEvidence(
                Map<String, Object> instance) {
            Map<String, List<Map<String, Object>>> evidenceBySite =
                    new LinkedHashMap<>();
            Map<String, List<String>> explicit =
                    explicitFatalSeeds(instance);
            if (explicit.isEmpty()) {
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
                if (explicit.containsKey(site)
                        && pathSites.contains(site)) {
                    evidenceBySite.computeIfAbsent(site,
                            ignored -> new ArrayList<>()).add(evidence);
                }
            }
            return evidenceBySite;
        }

        private boolean recordedFatal(Map<String, Object> instance,
                                      StaticScopeMap scopeMap) {
            for (Map.Entry<String, List<Map<String, Object>>> site
                    : observedFatalEvidence(instance).entrySet()) {
                Boolean arm = scopeMap.fatalArm(site.getKey());
                if (arm == null) continue;
                for (Map<String, Object> evidence : site.getValue()) {
                    if (arm.equals(evidence.get("observedOutcome"))) {
                        return true;
                    }
                }
            }
            return false;
        }

        private boolean observedExplicitFatalTarget(
                Map<String, Object> instance) {
            return !observedFatalEvidence(instance).isEmpty();
        }

        private boolean declaresExplicitFatalTarget(
                Map<String, Object> instance) {
            return !explicitFatalSeeds(instance).isEmpty();
        }

        private Map<String, List<String>> explicitFatalSeeds(
                Map<String, Object> instance) {
            Map<String, List<String>> explicit = new LinkedHashMap<>();
            for (String regionId : performedRegionIds(instance)) {
                Map<String, List<String>> held =
                        explicitFatalSeedsBySite.get(regionId);
                if (held != null) explicit.putAll(held);
            }
            return explicit;
        }

        private List<String> targetSeedCells(Map<String, Object> instance)
                throws IOException {
            String occurrenceId = text(instance.get("occurrenceId"));
            Map<String, List<String>> explicit =
                    explicitFatalSeeds(instance);
            List<String> cells = new ArrayList<>();
            for (Map.Entry<String, List<Map<String, Object>>> entry
                    : observedFatalEvidence(instance).entrySet()) {
                List<Map<String, Object>> occurrences = entry.getValue();
                sortByEventSeq(occurrences);
                if (longNumber(occurrences.get(0).get("eventSeq"), -1L) < 0L) {
                    throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: "
                            + "observed fatal target has no eventSeq: "
                            + occurrenceId + " " + entry.getKey());
                }
                for (String cell : explicit.getOrDefault(entry.getKey(),
                        Collections.<String>emptyList())) {
                    if (!cells.contains(cell)) cells.add(cell);
                }
            }
            return cells;
        }

        private List<String> storers(StaticScopeMap.Site site) {
            return occurrencesByMethod.getOrDefault(SiteId.methodOf(
                    site.siteId), Collections.<String>emptyList());
        }

        private Map<String, List<String>> deciders(StaticScopeMap.Site site) {
            Map<String, List<String>> found = new LinkedHashMap<>();
            for (int index = 0; index < site.guards.size(); index++) {
                String guard = site.guards.get(index);
                Boolean toward = site.guardOutcomes == null
                        || index >= site.guardOutcomes.size() ? null
                        : site.guardOutcomes.get(index);
                for (String occurrence : occurrencesByDecision.getOrDefault(
                        decision(guard, toward == null ? null : !toward),
                        Collections.<String>emptySet())) {
                    found.computeIfAbsent(occurrence,
                            ignored -> new ArrayList<>()).add(guard);
                }
            }
            return found;
        }

        private Set<String> operandsOf(String site) {
            return guardOperands.getOrDefault(site,
                    Collections.<String>emptySet());
        }

        private static String decision(String site, Boolean outcome) {
            return site + "\n" + (outcome == null ? "any" : outcome);
        }

        private List<String> incomingCells(String occurrenceId, String cell) {
            return edgesInto(localIncoming, occurrenceId, cell);
        }

        private List<String> guardCells(String occurrenceId, String cell) {
            return edgesInto(guardIncoming, occurrenceId, cell);
        }

        private List<String> edgesInto(
                Map<String, Map<String, Set<String>>> edges,
                String occurrenceId, String cell) {
            Set<String> ran = methodsByOccurrence.getOrDefault(occurrenceId,
                    Collections.<String>emptySet());
            List<String> incoming = new ArrayList<>();
            for (String regionId : regionsByOccurrence.getOrDefault(
                    occurrenceId, Collections.<String>emptyList())) {
                for (Map.Entry<String, Set<String>> from : edges.getOrDefault(
                        contextKey(regionId, cell),
                        Collections.<String, Set<String>>emptyMap())
                        .entrySet()) {
                    if (!incoming.contains(from.getKey())
                            && !Collections.disjoint(from.getValue(), ran)) {
                        incoming.add(from.getKey());
                    }
                }
            }
            return incoming;
        }

        private static void add(Map<String, Map<String, Set<String>>> target,
                                String key, String from, String method) {
            target.computeIfAbsent(key, ignored -> new LinkedHashMap<>())
                    .computeIfAbsent(from, ignored -> new HashSet<>())
                    .add(method);
        }
    }

    public static final class Result {
        public final List<Map<String, Object>> regions;
        public final List<Map<String, Object>> gaps;
        public final ZkChain zkChain;
        private Result(List<Map<String, Object>> regions,
                       List<Map<String, Object>> gaps,
                       ZkChain zkChain) {
            this.regions = regions;
            this.gaps = gaps;
            this.zkChain = zkChain;
        }
    }
}
