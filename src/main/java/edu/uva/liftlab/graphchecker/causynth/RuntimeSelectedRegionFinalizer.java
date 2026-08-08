package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.ArrayList;
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
import java.util.UUID;
import java.util.zip.GZIPInputStream;

/** Builds executable region state exclusively from a runtime-refined graph. */
public final class RuntimeSelectedRegionFinalizer {
    private static final Type ROW =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final String REFINED_KIND = "RUNTIME_REFINED_DATAFLOW";

    /**
     * Equality that stands on a declared reply reconstruction rather than on
     * the mapping alone.  It is a strictly weaker claim than
     * {@code TRUSTED_CONFIGURED_RPC_MAPPING_V1} and is named separately so a
     * composer or an audit can see which relations rest on the declaration.
     */
    private static final String DECLARED_CARRIER_AUTHORITY =
            "TRUSTED_DECLARED_CARRIER_PROJECTION_V1";

    private static final String DECLARED_CARRIER_SELECTION =
            "DECLARED_CARRIER_PATH_PROJECTION_V1";
    /**
     * Skeleton field naming the methods reached from the anchors that admitted
     * the region.  Absent or empty means "not decided": every guard in the
     * region stays explorable.
     */
    public static final String DEMAND_SCOPE = "demandScopeMethods";

    private RuntimeSelectedRegionFinalizer() {
    }

    public static Result finalizeRegions(
            File refinedGraph, File selectedSkeletons, File regions,
            File regionEdges, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances)
            throws IOException {
        return finalizeRegions(refinedGraph, selectedSkeletons, regions,
                regionEdges, observedMethods, runtimeInstances,
                Collections.<Map<String, Object>>emptyList());
    }

    /**
     * Finalizes regions using exact branch observations from the same runtime
     * trace that produced {@code runtimeInstances}.  The compact observations
     * keep a fatal target activation tied to the static predicate it actually
     * reached; an exception-context template is not itself runtime evidence
     * that every failure site in that template was reached.
     */
    public static Result finalizeRegions(
            File refinedGraph, File selectedSkeletons, File regions,
            File regionEdges, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations)
            throws IOException {
        return finalizeRegions(read(refinedGraph), refinedGraph,
                selectedSkeletons, regions, regionEdges, observedMethods,
                runtimeInstances, runtimeBranchObservations);
    }

    /**
     * In-memory entry point for an already parsed refined graph.  The rows
     * must be in the exact JSONL value domain (integral numbers as Long),
     * which {@code RuntimeRefinedGraphBuilder} guarantees for the rows it
     * returns; behavior is identical to re-reading {@code refinedGraph}.
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph, File refinedGraph,
            File selectedSkeletons, File regions,
            File regionEdges, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations)
            throws IOException {
        List<Map<String, Object>> skeletons = read(selectedSkeletons);
        requireRefinedGraph(graph, refinedGraph);
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }

        StaticProgram program = new StaticProgram();
        Map<String, Map<String, Object>> skeletonById = new LinkedHashMap<>();
        Map<String, List<Map<String, Object>>> edgesByRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> skeleton : skeletons) {
            requireSkeleton(skeleton, selectedSkeletons);
            skeletonById.put(text(skeleton.get("regionId")), skeleton);
        }
        for (Map<String, Object> edge : graph) {
            for (String region : strings(edge.get("regionIds"))) {
                edgesByRegion.computeIfAbsent(region,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        for (Map.Entry<String, Map<String, Object>> entry
                : skeletonById.entrySet()) {
            String regionId = entry.getKey();
            Map<String, Object> skeleton = entry.getValue();
            List<String> methods = strings(skeleton.get("methods"));
            if (methods.isEmpty()
                    || !observed.isEmpty()
                    && Collections.disjoint(methods, observed)) {
                continue;
            }
            Map<String, Object> region = new LinkedHashMap<>();
            region.put("schemaVersion", 3);
            region.put("kind", "SYMBOLIC_REGION");
            region.put("graphKind", REFINED_KIND);
            region.put("regionId", regionId);
            region.put("rootMethod", skeleton.get("rootMethod"));
            region.put("anchorMethod", skeleton.get("anchorMethod"));
            if (skeleton.containsKey("anchorMethods")) {
                region.put("anchorMethods", skeleton.get("anchorMethods"));
            }
            region.put("selection", skeleton.get("selection"));
            region.put("methods", methods);

            List<Map<String, Object>> regionGraph = edgesByRegion.getOrDefault(
                    regionId, Collections.emptyList());
            List<Map<String, Object>> outputs = statePorts(regionId,
                    regionGraph, "HEAP_WRITE", "OUT");
            outputs.addAll(protocolPorts(regionId, regionGraph, "OUT"));
            List<Map<String, Object>> branchPolicies = branches(regionGraph,
                    demandScope(skeleton, outputs));
            List<Map<String, Object>> inputs = statePorts(regionId,
                    regionGraph, "HEAP_READ", "IN");
            inputs.addAll(accessorPorts(regionId, regionGraph,
                    branchPolicies));
            inputs.addAll(protocolPorts(regionId, regionGraph, "IN"));
            markLoopControlOnlyInputs(inputs, regionGraph, branchPolicies);
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
            region.put("branchPolicies", branchPolicies);
            program.regions.add(region);
        }
        bindObservedFatalTargets(program.regions, graph, runtimeInstances,
                runtimeBranchObservations);
        Set<String> demandedFields = failureRelevantFields(
                program.regions, graph);
        Map<String, Long> laneByInstance = laneIds(runtimeInstances);
        List<Map<String, Object>> runtimeFieldFlows = fieldFlows(
                program.regions, demandedFields, laneByInstance);
        program.regionEdges.addAll(runtimeFieldFlows);
        program.regionEdges.addAll(protocolFlows(graph));
        addTrustedRpcDescendantProjections(program, graph);
        program.regionEdges.addAll(demandedLeafProducerFlows(
                program.regions, program.regionEdges, laneByInstance));
        annotateFlowContexts(program.regionEdges, runtimeInstances);
        markBoundedContainerStateChains(program.regions,
                runtimeFieldFlows);
        markBoundedMutationStateFrontiers(program.regions, graph);
        markUnclosedReferenceLeavesConcrete(program.regions,
                program.regionEdges, graph);
        RuntimeClosure closure = failureDirectedClosure(program, graph,
                runtimeInstances, selectedSkeletons);
        applyClosure(program, closure);
        // Member leaves are a property of the exact target-first program,
        // not of the initial over-approximate region set.  Project only after
        // closure filtering, and recompute field relevance against those
        // retained definitions so a discarded target/producer cannot widen a
        // bounded member relation.
        projectFailureRelevantContainerMembers(program.regions, graph,
                laneByInstance);
        CausynthArtifactWriter.writeRegions(regions.toPath(),
                regionEdges.toPath(), program);
        return new Result(closure.instanceCount, closure.reached.size(),
                closure.targetCount, program.regions,
                program.regionEdges, closure.targetClosures);
    }

    /**
     * Adds activation-local fatal-target evidence by intersecting exact
     * runtime BRANCH sites with static {@code failureTarget} branch policies.
     * The concrete outcome is evidence for replay; it need not already equal
     * the failure outcome because concolic execution is expected to flip it.
     */
    private static void bindObservedFatalTargets(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> graph,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations) {
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

        Map<String, List<String>> targetCellsByRegionSite =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : graph) {
            if (!"GUARD".equals(text(edge.get("transferKind")))
                    || !isExceptionTargetEdge(edge)) {
                continue;
            }
            String site = first(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            String targetCell = text(edge.get("toCell"));
            for (String regionId : strings(edge.get("regionIds"))) {
                if (targets.getOrDefault(regionId,
                        Collections.<String, Map<String, Object>>emptyMap())
                        .containsKey(site)) {
                    List<String> cells = targetCellsByRegionSite
                            .computeIfAbsent(contextKey(regionId, site),
                                    ignored -> new ArrayList<>());
                    if (!targetCell.isEmpty()
                            && !cells.contains(targetCell)) {
                        cells.add(targetCell);
                    }
                }
            }
        }

        List<Map<String, Object>> observations = runtimeBranchObservations
                == null ? Collections.<Map<String, Object>>emptyList()
                : new ArrayList<>(runtimeBranchObservations);
        observations.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
        for (Map<String, Object> instance : runtimeInstances) {
            String regionId = text(instance.get("regionId"));
            Map<String, Map<String, Object>> regionTargets = targets.get(
                    regionId);
            if (regionTargets == null || regionTargets.isEmpty()) continue;

            Set<Long> calls = longValues(instance.get("callIds"));
            List<Map<String, Object>> bound = rows(
                    instance.get("observedFatalTargets"));
            for (Map<String, Object> observation : observations) {
                if (!"BRANCH".equals(text(observation.get("kind")))) {
                    continue;
                }
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
                evidence.put("targetCells",
                        targetCellsByRegionSite.getOrDefault(
                                contextKey(regionId, site),
                                Collections.<String>emptyList()));
                evidence.put("requiredOutcome", target.get(
                        "requiredOutcome"));
                evidence.put("observedOutcome", observation.get("outcome"));
                evidence.put("eventSeq", observation.get("eventSeq"));
                evidence.put("callId", callId);
                bound.add(evidence);
            }
            if (!bound.isEmpty()) {
                bound.sort(Comparator.comparingLong(value ->
                        longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
                instance.put("observedFatalTargets", bound);
            }
        }
    }

    private static boolean isExceptionTargetEdge(Map<String, Object> edge) {
        return "exception_guard".equals(text(edge.get("kind")))
                || text(edge.get("toCell")).contains("#exception:");
    }

    private static Set<Long> longValues(Object value) {
        Set<Long> result = new LinkedHashSet<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Number) {
                    result.add(((Number) item).longValue());
                }
            }
        }
        return result;
    }

    /**
     * Retains the concrete producer activations and ports that can reach an
     * observed exception through confirmed heap or protocol flow.  The work
     * list is a demanded input port, not merely a region activation: after a
     * cross-region edge is selected, the producer output is sliced backward
     * to the exact producer inputs on which that output depends.  Multiple
     * demanded outputs of one producer are unioned in the same transition.
     */
    private static RuntimeClosure failureDirectedClosure(
            StaticProgram program,
            List<Map<String, Object>> graph,
            Collection<Map<String, Object>> runtimeInstances,
            File source) throws IOException {
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        Set<String> targets = new LinkedHashSet<>();
        for (Map<String, Object> instance : runtimeInstances == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeInstances) {
            if (!"RUNTIME_REGION_ACTIVATION".equals(
                    text(instance.get("kind")))) {
                throw new IOException("invalid runtime region activation: "
                        + source);
            }
            String region = text(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            if (region.isEmpty() || rootCallId < 0L) {
                throw new IOException("runtime region activation requires "
                        + "regionId and rootCallId: " + source);
            }
            String key = instanceKey(region, rootCallId);
            if (instances.putIfAbsent(key, instance) != null) {
                throw new IOException("duplicate runtime region activation: "
                        + key);
            }
            if (text(instance.get("selection")).startsWith("EXCEPTION")) {
                targets.add(key);
            }
        }
        if (instances.isEmpty()) {
            throw new IOException("runtime failure closure requires concrete "
                    + "region activations: " + source);
        }
        if (targets.isEmpty()) {
            throw new IOException("runtime failure closure found no observed "
                    + "exception-context activation: " + source);
        }

        RegionDemandIndex demands = new RegionDemandIndex(
                program.regions, graph);
        Map<String, List<Map<String, Object>>> predecessors =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : program.regionEdges) {
            if (!causalRegionRetentionEdge(edge)) {
                continue;
            }
            String from = instanceKey(text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L));
            String to = instanceKey(text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L));
            if (!instances.containsKey(from) || !instances.containsKey(to)) {
                throw new IOException("runtime causal edge references an "
                        + "unselected activation: "
                        + text(edge.get("edgeId")));
            }
            String toPort = text(edge.get("toPort"));
            String fromPort = text(edge.get("fromPort"));
            if (toPort.isEmpty() || fromPort.isEmpty()
                    || !demands.hasInput(text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L), toPort)
                    || !demands.hasOutput(text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L),
                    fromPort)) {
                throw new IOException("runtime causal edge references an "
                        + "unknown exact port: " + text(edge.get("edgeId")));
            }
            predecessors.computeIfAbsent(portDemandKey(
                    text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L), toPort),
                    ignored -> new ArrayList<>()).add(edge);
        }

        ClosureWalk union = walkFailureClosure(targets, instances,
                demands, predecessors);
        List<Map<String, Object>> targetClosures = new ArrayList<>();
        for (String target : targets) {
            ClosureWalk single = walkFailureClosure(
                    Collections.singleton(target), instances,
                    demands, predecessors);
            Map<String, Object> targetInstance = instances.get(target);
            Set<String> regionDefinitions = new LinkedHashSet<>();
            for (String reached : single.reached) {
                regionDefinitions.add(text(instances.get(reached).get(
                        "regionId")));
            }
            Map<String, Object> metadata = new LinkedHashMap<>();
            metadata.put("scope", "SINGLE_TARGET_CLOSURE");
            metadata.put("targetRegionId",
                    targetInstance.get("regionId"));
            metadata.put("targetRootCallId",
                    targetInstance.get("rootCallId"));
            metadata.put("retainedRegionInstanceCount",
                    single.reached.size());
            metadata.put("retainedRegionDefinitionCount",
                    regionDefinitions.size());
            metadata.put("retainedCausalEdgeCount",
                    single.retainedEdges.size());
            targetClosures.add(metadata);
        }
        return new RuntimeClosure(instances, union.reached, targets.size(),
                union.retainedEdges, union.demandedInputs,
                union.demandedOutputs, targetClosures);
    }

    private static ClosureWalk walkFailureClosure(
            Collection<String> targets,
            Map<String, Map<String, Object>> instances,
            RegionDemandIndex demands,
            Map<String, List<Map<String, Object>>> predecessors)
            throws IOException {
        Set<String> reached = new LinkedHashSet<>(targets);
        Set<String> retainedEdges = new LinkedHashSet<>();
        Set<String> demandedInputs = new LinkedHashSet<>();
        Set<String> demandedOutputs = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        for (String target : targets) {
            Map<String, Object> instance = instances.get(target);
            work.addAll(demands.targetInputs(instance));
        }
        while (!work.isEmpty()) {
            String inputDemand = work.removeFirst();
            if (!demandedInputs.add(inputDemand)) continue;
            for (Map<String, Object> edge : predecessors.getOrDefault(
                    inputDemand,
                    Collections.<Map<String, Object>>emptyList())) {
                String edgeId = text(edge.get("edgeId"));
                if (edgeId.isEmpty()) {
                    throw new IOException("runtime causal edge has no "
                            + "identity");
                }
                retainedEdges.add(edgeId);
                String fromRegion = text(edge.get("fromRegion"));
                long fromRootCallId = longNumber(
                        edge.get("fromRootCallId"), -1L);
                reached.add(instanceKey(fromRegion, fromRootCallId));
                String outputDemand = portDemandKey(fromRegion,
                        fromRootCallId, text(edge.get("fromPort")));
                if (demandedOutputs.add(outputDemand)) {
                    work.addAll(demands.inputsForOutput(fromRegion,
                            fromRootCallId,
                            text(edge.get("fromPort"))));
                }
            }
        }
        return new ClosureWalk(reached, retainedEdges, demandedInputs,
                demandedOutputs);
    }

    /**
     * Region retention needs an executable channel, not a same-declaration
     * hint. Exact heap identity and configured runtime RPC lineage are the two
     * channel authorities emitted by this finalizer.
     */
    private static boolean causalRegionRetentionEdge(
            Map<String, Object> edge) {
        String kind = text(edge.get("kind"));
        return "RUNTIME_FIELD_FLOW".equals(kind)
                || "RUNTIME_PROTOCOL_FLOW".equals(kind);
    }

    private static void applyClosure(StaticProgram program,
                                     RuntimeClosure closure)
            throws IOException {
        Set<String> retainedRegions = new LinkedHashSet<>();
        for (String key : closure.reached) {
            retainedRegions.add(text(closure.instances.get(key).get(
                    "regionId")));
        }
        program.regionEdges.removeIf(edge -> !closure.retainedEdges.contains(
                text(edge.get("edgeId"))));
        program.regions.removeIf(region -> !retainedRegions.contains(
                text(region.get("regionId"))));
        Map<String, Set<Long>> demandedAccesses =
                demandedRuntimeAccesses(program.regionEdges);
        Map<String, Long> fatalPrefixCutoffs = new LinkedHashMap<>();
        Map<String, List<Map<String, Object>>> fatalPrefixContexts =
                new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : closure.instances.entrySet()) {
            List<Map<String, Object>> contexts = rows(
                    entry.getValue().get("fatalPrefixContexts"));
            if (!contexts.isEmpty()) {
                fatalPrefixContexts.put(entry.getKey(), contexts);
            }
            long cutoff = longNumber(entry.getValue().get(
                    "fatalPrefixEventSeq"), -1L);
            if (cutoff >= 0L) fatalPrefixCutoffs.put(entry.getKey(), cutoff);
        }

        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            Set<Long> rootCalls = new LinkedHashSet<>();
            Set<String> methods = new LinkedHashSet<>();
            for (String key : closure.reached) {
                Map<String, Object> instance = closure.instances.get(key);
                if (!regionId.equals(text(instance.get("regionId")))) {
                    continue;
                }
                rootCalls.add(longNumber(instance.get("rootCallId"), -1L));
                methods.addAll(strings(instance.get("observedMethods")));
            }
            List<Long> orderedCalls = new ArrayList<>(rootCalls);
            Collections.sort(orderedCalls);
            region.put("runtimeRootCallIds", orderedCalls);
            region.put("runtimeInstanceCount", orderedCalls.size());
            List<String> observedMethods = new ArrayList<>(methods);
            Collections.sort(observedMethods);
            region.put("runtimeObservedMethods", observedMethods);
            region.put("symbolicInputs", filterPorts(
                    rows(region.get("symbolicInputs")), regionId,
                    rootCalls, false, closure.demandedInputs,
                    demandedAccesses, fatalPrefixCutoffs,
                    fatalPrefixContexts));
            region.put("outputs", filterPorts(
                    rows(region.get("outputs")), regionId,
                    rootCalls, true, closure.demandedOutputs,
                    demandedAccesses, fatalPrefixCutoffs,
                    fatalPrefixContexts));
        }
    }

    private static List<Map<String, Object>> filterPorts(
            List<Map<String, Object>> ports, String regionId,
            Set<Long> rootCalls, boolean output,
            Set<String> demandedPorts,
            Map<String, Set<Long>> demandedAccesses,
            Map<String, Long> fatalPrefixCutoffs,
            Map<String, List<Map<String, Object>>> fatalPrefixContexts)
            throws IOException {
        List<Map<String, Object>> retained = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            long rootCallId = portRootCallId(port, output);
            String demand = portDemandKey(regionId, rootCallId,
                    text(port.get("portId")));
            if (!regionId.equals(protocolRegion(port, output, regionId))
                    || !rootCalls.contains(rootCallId)
                    || !demandedPorts.contains(demand)) {
                continue;
            }
            // Region definitions are shared by all observed target
            // occurrences.  Every retained occurrence gets its own shallow
            // port row so one fatal cutoff cannot trim another occurrence's
            // canonical runtime-access catalog.
            Map<String, Object> selected = new LinkedHashMap<>(port);
            String instance = instanceKey(regionId, rootCallId);
            List<Map<String, Object>> contexts = output
                    ? Collections.<Map<String, Object>>emptyList()
                    : fatalPrefixContexts.getOrDefault(instance,
                    Collections.<Map<String, Object>>emptyList());
            List<Map<String, Object>> portContexts =
                    fatalPrefixContextsForPort(contexts,
                            text(port.get("portId")));
            if (!portContexts.isEmpty()) {
                selected.put("fatalPrefixContexts", portContexts);
            }
            Long cutoff = output ? null : fatalPrefixCutoffs.get(instance);
            if (cutoff != null && DependencyRole.valueFrontier(
                    selected.get("dependencyRole"))) {
                trimFatalPrefixAccesses(selected, cutoff);
            }
            retainExactRuntimeAccesses(selected, demand, output,
                    demandedAccesses.getOrDefault(demand,
                            Collections.<Long>emptySet()));
            retained.add(selected);
        }
        return retained;
    }

    private static List<Map<String, Object>> fatalPrefixContextsForPort(
            List<Map<String, Object>> contexts, String portId) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> context : contexts) {
            if (!strings(context.get("inputPorts")).contains(portId)) {
                continue;
            }
            Map<String, Object> compact = new LinkedHashMap<>(context);
            compact.remove("inputPorts");
            result.add(compact);
        }
        return result;
    }

    private static void trimFatalPrefixAccesses(
            Map<String, Object> port, long cutoff) {
        List<Map<String, Object>> accesses = rows(
                port.get("runtimeAccesses"));
        if (!accesses.isEmpty()) {
            List<Map<String, Object>> prefix = new ArrayList<>();
            for (Map<String, Object> access : accesses) {
                long event = longNumber(access.get("eventSeq"), -1L);
                if (event >= 0L && event <= cutoff) prefix.add(access);
            }
            port.put("runtimeAccesses", prefix);
            port.put("fatalPrefixAuthority",
                    "EXACT_RUNTIME_ACCESS_PREFIX_V1");
        } else if ("PROTOCOL_INPUT".equals(
                text(port.get("sourceKind")))) {
            port.put("fatalPrefixAuthority",
                    "TRUSTED_PROTOCOL_RECEIVE_PREFIX_V1");
        } else if ("ACCESSOR_RETURN".equals(
                text(port.get("sourceKind")))) {
            port.put("fatalPrefixAuthority",
                    "EXACT_RUNTIME_ACCESSOR_PREFIX_V1");
        }
        port.put("fatalPrefixEventSeq", cutoff);
    }

    /** Keeps only concrete accesses selected by retained causal edges. */
    private static Map<String, Set<Long>> demandedRuntimeAccesses(
            Collection<Map<String, Object>> edges) {
        Map<String, Set<Long>> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                continue;
            }
            addDemandedAccess(result, text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L),
                    text(edge.get("fromPort")),
                    longNumber(edge.get("writerEventSeq"), -1L));
            addDemandedAccess(result, text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L),
                    text(edge.get("toPort")),
                    longNumber(edge.get("readerEventSeq"), -1L));
        }
        return result;
    }

    private static void addDemandedAccess(
            Map<String, Set<Long>> target, String region, long rootCallId,
            String port, long eventSeq) {
        if (region.isEmpty() || rootCallId < 0L || port.isEmpty()
                || eventSeq < 0L) {
            return;
        }
        target.computeIfAbsent(portDemandKey(region, rootCallId, port),
                ignored -> new LinkedHashSet<>()).add(eventSeq);
    }

    private static void retainExactRuntimeAccesses(
            Map<String, Object> port, String demand, boolean output,
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
        accesses.sort(Comparator.comparingLong(access ->
                longNumber(access.get("eventSeq"), Long.MAX_VALUE)));
        List<Map<String, Object>> exact = new ArrayList<>();
        if (!eventSeqs.isEmpty()) {
            for (Map<String, Object> access : accesses) {
                if (eventSeqs.contains(longNumber(
                        access.get("eventSeq"), -1L))) {
                    exact.add(access);
                }
            }
        } else {
            // No edge selected an individual occurrence. Keep the bounded
            // static-site alternatives; never leak an unbounded long-lived
            // loop's aggregate access array into one concolic task.
            exact.addAll(accesses);
        }
        if (exact.isEmpty()) {
            throw new IOException("causal edge occurrence is absent from "
                    + "demanded heap port: " + demand + " events="
                    + eventSeqs);
        }
        port.put("runtimeAccesses", exact);
    }

    private static long portRootCallId(Map<String, Object> port,
                                       boolean output) {
        if ("PROTOCOL_INPUT".equals(text(port.get("sourceKind")))) {
            return longNumber(port.get(output
                    ? "fromRootCallId" : "toRootCallId"), -1L);
        }
        return longNumber(port.get("rootCallId"), -1L);
    }

    private static String protocolRegion(Map<String, Object> port,
                                         boolean output,
                                         String fallback) {
        String region = text(port.get(output
                ? "fromRegionId" : "toRegionId"));
        return region.isEmpty() ? fallback : region;
    }

    private static String instanceKey(String region, long rootCallId) {
        return region + "\n" + rootCallId;
    }

    private static String portDemandKey(String region, long rootCallId,
                                        String portId) {
        return instanceKey(region, rootCallId) + "\n" + portId;
    }

    private static Map<String, Long> laneIds(
            Collection<Map<String, Object>> runtimeInstances) {
        Map<String, Long> result = new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeInstances) {
            long laneId = longNumber(instance.get("laneId"), -1L);
            if (laneId > 0L) {
                result.put(instanceKey(text(instance.get("regionId")),
                        longNumber(instance.get("rootCallId"), -1L)),
                        laneId);
            }
        }
        return result;
    }

    private static void annotateFlowContexts(
            List<Map<String, Object>> edges,
            Collection<Map<String, Object>> runtimeInstances) {
        Map<String, Map<String, Object>> byInstance = new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeInstances) {
            byInstance.put(instanceKey(text(instance.get("regionId")),
                    longNumber(instance.get("rootCallId"), -1L)), instance);
        }
        for (Map<String, Object> edge : edges) {
            Map<String, Object> from = byInstance.get(instanceKey(
                    text(edge.get("fromRegion")), longNumber(
                            edge.get("fromRootCallId"), -1L)));
            Map<String, Object> to = byInstance.get(instanceKey(
                    text(edge.get("toRegion")), longNumber(
                            edge.get("toRootCallId"), -1L)));
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

    /**
     * Promotes only an exact, failure-directed container read-from relation
     * to symbolic state.  A container reference is otherwise a concrete
     * structure carrier: seeing a {@code Map} field is not by itself a reason
     * to symbolize it.
     *
     * <p>The runtime mutation edge proves the post-state and the downstream
     * read of the same declared field on the same concrete owner.  The
     * producer must additionally have one unambiguous live-in port for that
     * field, with a read before the selected mutation.  The planner later
     * narrows that port to the earliest read in the exact definition
     * invocation; this pass deliberately does not use a long-lived root-call
     * ordinal as replay identity.</p>
     */
    private static void markBoundedContainerStateChains(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> fieldEdges) {
        Map<String, Map<String, Object>> regionsById =
                new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            regionsById.put(text(region.get("regionId")), region);
        }
        for (Map<String, Object> edge : fieldEdges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))
                    || !"CONTAINER_MUTATION".equals(
                    text(edge.get("bindingKind")))) {
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
            long fromRoot = longNumber(edge.get("fromRootCallId"), -1L);
            long toRoot = longNumber(edge.get("toRootCallId"), -1L);
            Map<String, Object> producerRegion = regionsById.get(fromRegion);
            Map<String, Object> consumerRegion = regionsById.get(toRegion);
            Map<String, Object> output = exactRegionPort(producerRegion,
                    "outputs", text(edge.get("fromPort")), fromRoot, true);
            Map<String, Object> consumer = exactRegionPort(consumerRegion,
                    "symbolicInputs", text(edge.get("toPort")), toRoot,
                    false);
            Map<String, Object> outputAccess = exactPortAccess(output,
                    longNumber(edge.get("writerEventSeq"), -1L));
            Map<String, Object> consumerAccess = exactPortAccess(consumer,
                    longNumber(edge.get("readerEventSeq"), -1L));
            if (!exactContainerAccess(outputAccess, declarations,
                    number(edge.get("receiverObjectId"), 0))
                    || !exactContainerAccess(consumerAccess, declarations,
                    number(edge.get("receiverObjectId"), 0))) {
                blockContainerStateChain(edge,
                        "MISSING_EXACT_CONTAINER_ENDPOINT");
                continue;
            }

            markBoundedContainerPort(output, leaf.type,
                    "MUTATION_POST_STATE");
            markBoundedContainerPort(consumer, leaf.type,
                    "DOWNSTREAM_CONTAINER_READ");
            // The downstream lookup result is semantic state, even when the
            // static classifier originally labelled its receiver as a
            // structure carrier.
            consumer.put("dependencyRole", DependencyRole.VALUE_FRONTIER);

            long upperBound = firstPositive(
                    longNumber(edge.get("writerFieldReadSeq"), -1L),
                    longNumber(edge.get("mutatorEnterSeq"), -1L),
                    longNumber(edge.get("writerEventSeq"), -1L));
            int owner = number(edge.get("receiverObjectId"), 0);
            int container = number(outputAccess.get("valueObjectId"), 0);
            Map<String, Object> preState = uniqueContainerPreStatePort(
                    producerRegion, fromRoot, declarations, owner, container,
                    upperBound, strings(output.get("fieldPath")));
            if (preState == null) {
                blockContainerStateChain(edge,
                        "MISSING_OR_AMBIGUOUS_CONTAINER_PRE_STATE");
                output.put("boundedContainerStateAdmission", "BLOCKED");
                output.put("boundedContainerStateBlocker",
                        "MISSING_OR_AMBIGUOUS_CONTAINER_PRE_STATE");
                continue;
            }
            markBoundedContainerPort(preState, leaf.type,
                    "MUTATION_PRE_STATE");
            preState.put("boundedContainerPreStateCandidate", true);
            preState.put("boundedContainerPreStateUpperBoundSeq",
                    upperBound);
            addUniqueValue(output, "boundedContainerPreStatePorts",
                    text(preState.get("portId")));
            output.put("boundedContainerStateAdmission", "PROVED");
            edge.put("boundedContainerStateAdmission", "PROVED");
            edge.put("boundedContainerStateAuthority",
                    "EXACT_RUNTIME_CONTAINER_MUTATION_STATE_CHAIN_V1");
            edge.put("containerJavaType", leaf.type);
            edge.put("containerCapacity", LoopBoundPolicy
                    .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
            edge.put("producerPreStatePort", preState.get("portId"));
        }
    }

    private static Map<String, Object> exactRegionPort(
            Map<String, Object> region, String field, String portId,
            long rootCallId, boolean output) {
        if (region == null || portId.isEmpty() || rootCallId < 0L) {
            return null;
        }
        Map<String, Object> selected = null;
        for (Map<String, Object> port : rows(region.get(field))) {
            if (!portId.equals(text(port.get("portId")))
                    || portRootCallId(port, output) != rootCallId) {
                continue;
            }
            if (selected != null) return null;
            selected = port;
        }
        return selected;
    }

    private static Map<String, Object> exactPortAccess(
            Map<String, Object> port, long eventSeq) {
        if (port == null || eventSeq < 0L) return null;
        Map<String, Object> selected = null;
        for (Map<String, Object> access : rows(port.get("runtimeAccesses"))) {
            if (longNumber(access.get("eventSeq"), -1L) != eventSeq) {
                continue;
            }
            if (selected != null) return null;
            selected = access;
        }
        return selected;
    }

    private static boolean exactContainerAccess(
            Map<String, Object> access, List<String> declarations,
            int owner) {
        return access != null && owner > 0
                && number(access.get("fieldReceiverObjectId"), 0) == owner
                && sameDeclaredLeaf(declarations, strings(
                access.get("fieldPathDeclarations")));
    }

    private static Map<String, Object> uniqueContainerPreStatePort(
            Map<String, Object> region, long rootCallId,
            List<String> declarations, int owner, int container,
            long upperBound, List<String> outputPath) {
        if (region == null || rootCallId < 0L || owner <= 0
                || upperBound < 0L) {
            return null;
        }
        List<Map<String, Object>> candidates = new ArrayList<>();
        for (Map<String, Object> input
                : rows(region.get("symbolicInputs"))) {
            if (portRootCallId(input, false) != rootCallId
                    || !sameDeclaredLeaf(declarations, strings(
                    input.get("fieldPathDeclarations")))) {
                continue;
            }
            boolean preceding = false;
            for (Map<String, Object> access
                    : rows(input.get("runtimeAccesses"))) {
                int observedContainer = number(
                        access.get("valueObjectId"), 0);
                if (number(access.get("fieldReceiverObjectId"), 0) == owner
                        && (container <= 0 || observedContainer == container)
                        && longNumber(access.get("eventSeq"), -1L) >= 0L
                        && longNumber(access.get("eventSeq"), -1L)
                        < upperBound) {
                    preceding = true;
                    break;
                }
            }
            if (preceding) candidates.add(input);
        }
        if (candidates.size() > 1 && !outputPath.isEmpty()) {
            candidates.removeIf(candidate -> !outputPath.equals(
                    strings(candidate.get("fieldPath"))));
        }
        return candidates.size() == 1 ? candidates.get(0) : null;
    }

    /**
     * Runtime read-from edges identify the concrete field endpoint.  Their
     * declaration list is intentionally reduced to that leaf, while a port
     * may retain the full static root-to-leaf path used to reach it.  Compare
     * the declared leaf here; exact root activation, receiver identity and
     * event sequence are checked by the surrounding corridor matching.
     */
    private static boolean sameDeclaredLeaf(List<String> left,
                                            List<String> right) {
        return !left.isEmpty() && !right.isEmpty()
                && left.get(left.size() - 1).equals(
                right.get(right.size() - 1));
    }

    private static void markBoundedContainerPort(
            Map<String, Object> port, String javaType, String role) {
        if (port == null) return;
        port.put("javaType", javaType);
        port.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        port.put("containerCapacity", LoopBoundPolicy
                .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
        port.put("boundedContainerStateRole", role);
        port.put("boundedContainerStateAuthority",
                "EXACT_RUNTIME_CONTAINER_MUTATION_STATE_CHAIN_V1");
    }

    private static void blockContainerStateChain(
            Map<String, Object> edge, String blocker) {
        edge.put("boundedContainerStateAdmission", "BLOCKED");
        edge.put("boundedContainerStateBlocker", blocker);
    }

    /**
     * Carries demanded scalar leaves across a bounded container timeline by
     * the exact mutation that introduced the member.  The token is trace
     * local and comes from {@code Map.put} provenance; neither a concrete key
     * value nor an iteration slot participates in its identity.
     */
    static void projectDemandedContainerMembers(
            List<Map<String, Object>> regions, Set<String> demandedFields,
            Map<String, Long> laneByInstance) {
        Map<String, Set<Long>> writerLanes = new LinkedHashMap<>();
        Set<String> incompleteWriters = new LinkedHashSet<>();
        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            for (Map<String, Object> output : rows(region.get("outputs"))) {
                for (Map<String, Object> access
                        : rows(output.get("runtimeAccesses"))) {
                    if (!JavaContainerTypes.associativePut(text(
                            access.get("mutatorDeclaredCallee")))) {
                        continue;
                    }
                    String token = text(access.get("containerMemberToken"));
                    int container = number(access.get("containerObjectId"),
                            0);
                    long root = longNumber(access.get("rootCallId"), -1L);
                    Long lane = laneByInstance.get(instanceKey(regionId,
                            root));
                    String containerKey = memberContainerKey(access,
                            container);
                    if (!token.isEmpty() && container > 0 && lane != null) {
                        writerLanes.computeIfAbsent(containerKey,
                                ignored -> new LinkedHashSet<>()).add(lane);
                    } else if (container > 0) {
                        incompleteWriters.add(containerKey);
                    }
                }
            }
        }

        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            Map<String, Map<String, Object>> inputsById =
                    new LinkedHashMap<>();
            for (Map<String, Object> input
                    : rows(region.get("symbolicInputs"))) {
                inputsById.put(text(input.get("portId")), input);
            }
            for (Map<String, Object> output : rows(region.get("outputs"))) {
                if (!"MUTATION_POST_STATE".equals(text(output.get(
                        "boundedContainerStateRole")))) {
                    continue;
                }
                for (Map<String, Object> access
                        : rows(output.get("runtimeAccesses"))) {
                    if (!JavaContainerTypes.associativePut(text(
                            access.get("mutatorDeclaredCallee")))) {
                        continue;
                    }
                    String token = text(access.get("containerMemberToken"));
                    int container = number(access.get("containerObjectId"),
                            0);
                    long root = longNumber(access.get("rootCallId"), -1L);
                    Long lane = laneByInstance.get(instanceKey(regionId,
                            root));
                    String containerKey = memberContainerKey(access,
                            container);
                    Set<Long> lanes = writerLanes.getOrDefault(
                            containerKey,
                            Collections.<Long>emptySet());
                    if (container <= 0) {
                        markMemberProjectionBlocked(output,
                                "MISSING_EXACT_CONTAINER_IDENTITY");
                        continue;
                    }
                    if (token.isEmpty() || lane == null
                            || lanes.size() != 1
                            || incompleteWriters.contains(containerKey)) {
                        markMemberProjectionBlocked(output,
                                "MISSING_OR_MULTIPLE_MUTATION_WRITER_LANES");
                        continue;
                    }
                    Map<String, Object> projection = memberProjection(
                            access, demandedFields, lane);
                    if (projection == null) continue;
                    addMemberProjection(output, access, projection,
                            "POST_STATE");
                    for (String preStatePort : strings(output.get(
                            "boundedContainerPreStatePorts"))) {
                        Map<String, Object> input = inputsById.get(
                                preStatePort);
                        if (input != null && portRootCallId(input, false)
                                == root) {
                            addMemberProjection(input, null, projection,
                                    "PRE_STATE");
                        }
                    }
                }
            }
        }
    }

    /** Recomputes leaf relevance over the already closure-filtered program. */
    static void projectFailureRelevantContainerMembers(
            List<Map<String, Object>> retainedRegions,
            List<Map<String, Object>> graph,
            Map<String, Long> laneByInstance) {
        projectDemandedContainerMembers(retainedRegions,
                failureRelevantFields(retainedRegions, graph),
                laneByInstance);
    }

    private static String memberContainerKey(Map<String, Object> access,
                                             int container) {
        return text(access.get("process")) + "\n" + container;
    }

    private static Map<String, Object> memberProjection(
            Map<String, Object> access, Set<String> demandedFields,
            long writerLane) {
        if (!"EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1".equals(
                text(access.get("containerMemberIdentityAuthority")))) {
            return null;
        }
        List<Map<String, Object>> leaves = new ArrayList<>();
        leaves.add(memberLeaf("PRESENT", "boolean", ""));
        for (Map<String, Object> binding
                : rows(access.get("containerMemberFieldBindings"))) {
            String declaration = text(binding.get("field"));
            DeclaredFieldCell field = DeclaredFieldCell.parse(declaration);
            if (field == null || !field.primitive()
                    || !demandedFields.contains(declaration)) {
                continue;
            }
            Map<String, Object> leaf = memberLeaf(
                    "VALUE_FIELD", field.type, declaration);
            leaf.put("fieldEventSeq", binding.get("eventSeq"));
            leaves.add(leaf);
        }
        Map<String, Object> projection = new LinkedHashMap<>();
        projection.put("memberToken", access.get("containerMemberToken"));
        projection.put("identityAuthority",
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1");
        projection.put("containerObjectId",
                access.get("containerObjectId"));
        projection.put("keyObjectId", access.get("containerKeyObjectId"));
        projection.put("valueObjectId",
                access.get("containerValueObjectId"));
        projection.put("mutationInvocationId",
                access.get("mutationInvocationId"));
        projection.put("writerLaneId", writerLane);
        projection.put("leaves", leaves);
        return projection;
    }

    private static Map<String, Object> memberLeaf(
            String kind, String javaType, String declaration) {
        Map<String, Object> leaf = new LinkedHashMap<>();
        leaf.put("kind", kind);
        leaf.put("javaType", javaType);
        if (!declaration.isEmpty()) leaf.put("field", declaration);
        return leaf;
    }

    private static void addMemberProjection(
            Map<String, Object> port, Map<String, Object> exactAccess,
            Map<String, Object> projection, String stateRole) {
        Map<String, Object> copy = new LinkedHashMap<>(projection);
        copy.put("stateRole", stateRole);
        addUniqueMap(port, "boundedContainerMemberProjections", copy,
                "memberToken");
        if (exactAccess != null) {
            exactAccess.put("boundedContainerMemberProjection", copy);
        }
        port.put("boundedContainerMemberProjectionAdmission", "PROVED");
        port.put("boundedContainerMemberProjectionAuthority",
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1");
        port.put("containerTimelineWriterPolicy",
                "SINGLE_WRITER_REQUIRED");
    }

    private static void markMemberProjectionBlocked(
            Map<String, Object> port, String blocker) {
        port.put("boundedContainerMemberProjectionAdmission", "BLOCKED");
        port.put("boundedContainerMemberProjectionBlocker", blocker);
        port.put("containerTimelineWriterPolicy",
                "SINGLE_WRITER_REQUIRED");
    }

    @SuppressWarnings("unchecked")
    private static void addUniqueMap(Map<String, Object> target, String key,
                                     Map<String, Object> value,
                                     String identityKey) {
        List<Map<String, Object>> values;
        Object existing = target.get(key);
        if (existing instanceof List<?>) {
            values = (List<Map<String, Object>>) existing;
        } else {
            values = new ArrayList<>();
            target.put(key, values);
        }
        String identity = text(value.get(identityKey));
        for (Map<String, Object> candidate : values) {
            if (identity.equals(text(candidate.get(identityKey)))) return;
        }
        values.add(value);
    }

    private static long firstPositive(long... values) {
        for (long value : values) {
            if (value >= 0L) return value;
        }
        return -1L;
    }

    /**
     * Marks primitive element fields that are part of a demanded container
     * transition rather than unrelated leaves of a transported reference.
     *
     * <p>The proof is deliberately narrow and name agnostic: an observed
     * primitive accessor must flow to an explorable, non-loop branch, and the
     * same branch must guard a mutation of the container output.  Only then
     * is the accessor retained as a bounded symbolic state frontier.  The
     * exact runtime output corridor later chooses which helper activation and
     * at most {@link LoopBoundPolicy#SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY}
     * element occurrences belong to the task.</p>
     */
    private static void markBoundedMutationStateFrontiers(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> refinedGraph) {
        Map<String, List<Map<String, Object>>> edgesByRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : refinedGraph) {
            for (String regionId : strings(edge.get("regionIds"))) {
                edgesByRegion.computeIfAbsent(regionId,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            List<Map<String, Object>> edges = edgesByRegion.getOrDefault(
                    regionId, Collections.<Map<String, Object>>emptyList());
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
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
                String to = text(edge.get("toCell"));
                if (!to.isEmpty()) {
                    incoming.computeIfAbsent(to,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
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
                if (!"CONTAINER_MUTATION".equals(
                        text(output.get("bindingKind")))) {
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
                        markPrimitiveAccessorFrontiers(
                                text(guard.get("fromCell")), incoming,
                                inputBoundaries, outputCell, outputPort,
                                guardSite);
                    }
                }
            }
        }
    }

    private static void markPrimitiveAccessorFrontiers(
            String start,
            Map<String, List<Map<String, Object>>> incoming,
            Map<String, List<Map<String, Object>>> inputBoundaries,
            String outputCell, String outputPort, String guardSite) {
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        if (!start.isEmpty()) work.add(start);
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            boolean foundAccessor = false;
            for (Map<String, Object> input : inputBoundaries.getOrDefault(
                    cell, Collections.<Map<String, Object>>emptyList())) {
                if (!"ACCESSOR_RETURN".equals(text(input.get("sourceKind")))
                        || !primitiveLeaf(input)) {
                    continue;
                }
                foundAccessor = true;
                input.put("symbolicDemand", "BOUNDED_STATE_FRONTIER");
                input.put("boundedStateFrontierAuthority",
                        "STATIC_ACCESSOR_SEMANTIC_MUTATION_GUARD_V1");
                addUniqueValue(input, "boundedMutationOutputCells",
                        outputCell);
                addUniqueValue(input, "boundedMutationOutputPorts",
                        outputPort);
                addUniqueValue(input, "boundedMutationGuardSites",
                        guardSite);
            }
            if (foundAccessor) continue;
            for (Map<String, Object> edge : incoming.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                // Loop/path guards are control context, not value sources for
                // the semantic mutation predicate.
                if ("GUARD".equals(text(edge.get("transferKind")))) {
                    continue;
                }
                String from = text(edge.get("fromCell"));
                if (!from.isEmpty()) work.addLast(from);
            }
        }
    }

    private static void addUniqueValue(Map<String, Object> row, String key,
                                       String value) {
        if (value.isEmpty()) return;
        List<String> values = strings(row.get(key));
        if (!values.contains(value)) values.add(value);
        row.put(key, values);
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
     *
     * <p>The runtime object id is used only inside this trace to prove that a
     * primitive receiver descends from the exact reference delivered to this
     * activation.  If an exact region edge already writes that primitive
     * input, the normal symbolic relation is retained.  Otherwise replaying
     * the observed primitive is a deliberate under-approximation: it is more
     * precise than inventing a fresh solver leaf with no producer.</p>
     */
    private static void markUnclosedReferenceLeavesConcrete(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges,
            List<Map<String, Object>> refinedGraph) {
        Map<String, Set<Integer>> boundaryObjects = new LinkedHashMap<>();
        Set<String> closedInputs = new LinkedHashSet<>();
        for (Map<String, Object> edge : regionEdges) {
            String toRegion = text(edge.get("toRegion"));
            long toRootCallId = longNumber(edge.get("toRootCallId"), -1L);
            String toPort = text(edge.get("toPort"));
            if (!toRegion.isEmpty() && toRootCallId >= 0L
                    && !toPort.isEmpty()) {
                closedInputs.add(portDemandKey(toRegion, toRootCallId,
                        toPort));
            }
            int deliveredObject = 0;
            if ("RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                deliveredObject = number(edge.get("valueObjectId"), 0);
            } else if ("RUNTIME_PROTOCOL_FLOW".equals(
                    text(edge.get("kind")))
                    && "RESPONSE".equals(text(edge.get(
                    "protocolDirection")))) {
                deliveredObject = number(edge.get(
                        "callerResultObjectId"), 0);
            }
            if (deliveredObject > 0 && !toRegion.isEmpty()
                    && toRootCallId >= 0L) {
                boundaryObjects.computeIfAbsent(instanceKey(toRegion,
                        toRootCallId), ignored -> new LinkedHashSet<>())
                        .add(deliveredObject);
            }
        }
        if (boundaryObjects.isEmpty()) return;

        Map<String, Map<Integer, Set<Integer>>> objectLinks =
                referenceObjectLinks(refinedGraph);
        for (Map.Entry<String, Set<Integer>> entry
                : boundaryObjects.entrySet()) {
            Set<Integer> reachable = entry.getValue();
            Deque<Integer> work = new ArrayDeque<>(reachable);
            Map<Integer, Set<Integer>> links = objectLinks.getOrDefault(
                    entry.getKey(), Collections.<Integer, Set<Integer>>emptyMap());
            while (!work.isEmpty()) {
                for (Integer child : links.getOrDefault(work.removeFirst(),
                        Collections.<Integer>emptySet())) {
                    if (child != null && child > 0
                            && reachable.add(child)) {
                        work.addLast(child);
                    }
                }
            }
        }

        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            for (Map<String, Object> port
                    : rows(region.get("symbolicInputs"))) {
                long rootCallId = portRootCallId(port, false);
                String demand = portDemandKey(regionId, rootCallId,
                        text(port.get("portId")));
                if (closedInputs.contains(demand)
                        || "BOUNDED_STATE_FRONTIER".equals(
                        text(port.get("symbolicDemand")))
                        || !primitiveLeaf(port)) {
                    continue;
                }
                Set<Integer> reachable = boundaryObjects.get(instanceKey(
                        regionId, rootCallId));
                if (reachable == null || reachable.isEmpty()
                        || Collections.disjoint(reachable,
                        receiverObjects(port))) {
                    continue;
                }
                port.put("referenceBoundaryLeaf", true);
                port.put("symbolicDemand",
                        "CONCRETE_REFERENCE_BOUNDARY_REPLAY");
                port.put("replayAuthority",
                        "EXACT_TRACE_REFERENCE_LEAF_UNDER_APPROX_V1");
            }
        }
    }

    private static Map<String, Map<Integer, Set<Integer>>>
            referenceObjectLinks(List<Map<String, Object>> graph) {
        Map<String, Map<Integer, Set<Integer>>> result =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : graph) {
            List<Map<String, Object>> bindings = new ArrayList<>();
            bindings.addAll(rows(edge.get("runtimeAccessorBindings")));
            if ("HEAP_READ".equals(text(edge.get("transferKind")))) {
                bindings.addAll(rows(edge.get("runtimeFieldBindings")));
            }
            for (Map<String, Object> binding : bindings) {
                int receiver = number(binding.containsKey("receiverObjectId")
                        ? binding.get("receiverObjectId")
                        : binding.get("fieldReceiverObjectId"), 0);
                int value = number(binding.get("valueObjectId"), 0);
                String region = text(binding.get("regionId"));
                long rootCallId = longNumber(binding.get("rootCallId"), -1L);
                if (receiver <= 0 || value <= 0 || region.isEmpty()
                        || rootCallId < 0L) {
                    continue;
                }
                result.computeIfAbsent(instanceKey(region, rootCallId),
                        ignored -> new LinkedHashMap<>())
                        .computeIfAbsent(receiver,
                                ignored -> new LinkedHashSet<>()).add(value);
            }
        }
        return result;
    }

    private static boolean primitiveLeaf(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        String declaration = declarations.isEmpty()
                ? text(port.get("cell"))
                : declarations.get(declarations.size() - 1);
        DeclaredFieldCell field = DeclaredFieldCell.parse(declaration);
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
        putIfMissing(edge, prefix + "OwnerId", instance.get("ownerId"));
        putIfMissing(edge, prefix + "LaneId", instance.get("laneId"));
        putIfMissing(edge, prefix + "SpanId", instance.get("spanId"));
        putIfMissing(edge, prefix + "LogicalRegionId",
                instance.get("logicalRegionId"));
    }

    private static void putIfMissing(Map<String, Object> target, String key,
                                     Object value) {
        if (!target.containsKey(key) && value != null
                && !text(value).isEmpty()) {
            target.put(key, value);
        }
    }

    private static void copyIfPresent(Map<String, Object> target,
                                      Map<String, Object> source,
                                      String key) {
        if (source.containsKey(key) && source.get(key) != null) {
            target.put(key, source.get(key));
        }
    }

    private static List<Map<String, Object>> protocolPorts(
            String regionId, List<Map<String, Object>> edges,
            String direction) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"PROTOCOL_TRANSFER".equals(
                    text(edge.get("transferKind")))) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeProtocolBindings"))) {
                String boundRegion = "OUT".equals(direction)
                        ? text(binding.get("fromRegionId"))
                        : text(binding.get("toRegionId"));
                if (!regionId.equals(boundRegion)) {
                    continue;
                }
                String cellKey = "OUT".equals(direction)
                        ? "fromCell" : "toCell";
                String key = text(binding.get("mappingId")) + "\n"
                        + text(binding.get("port")) + "\n"
                        + text(binding.get(cellKey)) + "\n"
                        + text(binding.get("fromRootCallId")) + "\n"
                        + text(binding.get("toRootCallId"));
                Map<String, Object> port = new LinkedHashMap<>(binding);
                port.put("portId", protocolPortId(regionId, direction,
                        binding));
                port.put("cell", binding.get(cellKey));
                port.put("sourceKind", "PROTOCOL_INPUT");
                port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
                port.put("transportKind", binding.get("transport"));
                port.put("protocolDirection", binding.get("direction"));
                if ("IN".equals(direction)
                        && "REQUEST".equals(text(binding.get("direction")))) {
                    port.put("argumentIndex",
                            edge.get("protocolServerParameter"));
                }
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    private static String protocolPortId(String regionId, String direction,
                                         Map<String, Object> binding) {
        String identity = regionId + "\n" + direction + "\n"
                + text(binding.get("mappingId")) + "\n"
                + text(binding.get("port")) + "\n"
                + text(binding.get("fromRootCallId")) + "\n"
                + text(binding.get("toRootCallId"));
        return regionId + ("IN".equals(direction) ? ".in." : ".out.")
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8));
    }

    private static List<Map<String, Object>> protocolFlows(
            List<Map<String, Object>> graph) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> edge : graph) {
            if (!"PROTOCOL_TRANSFER".equals(
                    text(edge.get("transferKind")))) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeProtocolBindings"))) {
                String fromRegion = text(binding.get("fromRegionId"));
                String toRegion = text(binding.get("toRegionId"));
                if (fromRegion.isEmpty() || toRegion.isEmpty()) {
                    continue;
                }
                String identity = text(binding.get("mappingId")) + "\n"
                        + text(binding.get("port")) + "\n"
                        + text(binding.get("fromCell")) + "\n"
                        + text(binding.get("toCell")) + "\n"
                        + text(binding.get("fromRootCallId")) + "\n"
                        + text(binding.get("toRootCallId"));
                Map<String, Object> flow = new LinkedHashMap<>(binding);
                flow.put("schemaVersion", 3);
                flow.put("kind", "RUNTIME_PROTOCOL_FLOW");
                flow.put("transportKind", binding.get("transport"));
                flow.put("edgeId", "RP." + UUID.nameUUIDFromBytes(
                        identity.getBytes(StandardCharsets.UTF_8)));
                flow.put("fromRegion", fromRegion);
                flow.put("toRegion", toRegion);
                flow.put("fromPort", protocolPortId(fromRegion, "OUT",
                        binding));
                flow.put("toPort", protocolPortId(toRegion, "IN", binding));
                flow.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
                result.add(flow);
            }
        }
        return result;
    }

    /**
     * Projects a demanded value leaf carried below a trusted RPC response.
     *
     * <p>The configured response mapping is the sole cross-process
     * authority.  Static value flow only selects the exact leaf written into
     * the producer response and the matching leaf read after the consumer
     * receives it.  A leaf is either a bounded container or a semantic scalar
     * ({@code int}, {@code boolean}, {@code java.lang.String}, ...); the
     * carrier objects between them stay concrete.  In particular, this does
     * not equate a producer state input (for example a {@code Map}) with the
     * response: the VM must capture the derived output after the producer's
     * actual conversion code has run.</p>
     *
     * <p>The producer is selected uniquely inside the exact server receive
     * to normal-return window.  On the consumer, runtime object ids reject
     * reads outside the concrete received-response descendant tree.  Object
     * ids are deliberately absent from the projected edge and its
     * deterministic identity.</p>
     */
    private static void addTrustedRpcDescendantProjections(
            StaticProgram program, List<Map<String, Object>> graph)
            throws IOException {
        Map<String, String> carrierProjections =
                ConfiguredProtocolStubs.declaredCarrierProjections();
        RpcDescendantProjectionIndex index =
                new RpcDescendantProjectionIndex(program.regions, graph);
        List<Map<String, Object>> wholeFlows = new ArrayList<>(
                program.regionEdges);
        Set<String> emittedEdges = new LinkedHashSet<>();
        for (Map<String, Object> edge : program.regionEdges) {
            emittedEdges.add(text(edge.get("edgeId")));
        }

        for (Map<String, Object> whole : wholeFlows) {
            if (!trustedResponseFlow(whole)) continue;
            String fromRegion = text(whole.get("fromRegion"));
            String toRegion = text(whole.get("toRegion"));
            long fromRoot = longNumber(whole.get("fromRootCallId"), -1L);
            long toRoot = longNumber(whole.get("toRootCallId"), -1L);
            long producerLowerSeq = longNumber(whole.get(
                    "receiveEventSeq"), -1L);
            long producerUpperSeq = longNumber(whole.get(
                    "producerResultEventSeq"), -1L);
            long consumerLowerSeq = longNumber(whole.get(
                    "callerResultEventSeq"), -1L);
            long consumerUpperSeq = nextTrustedResponseCallerSite(
                    wholeFlows, whole);
            if (fromRegion.isEmpty() || toRegion.isEmpty()
                    || fromRoot < 0L || toRoot < 0L) {
                continue;
            }

            Map<String, List<RpcDescendantCandidate>> producers =
                    candidatesByDeclaration(index.candidates(fromRegion,
                            fromRoot, "HEAP_WRITE"), candidate ->
                            producerLowerSeq >= 0L
                                    && producerUpperSeq >= producerLowerSeq
                                    && candidate.eventSeq >= producerLowerSeq
                                    && candidate.eventSeq
                                    <= producerUpperSeq);
            Map<String, List<RpcDescendantCandidate>> consumers =
                    candidatesByDeclaration(index.candidates(toRegion,
                            toRoot, "HEAP_READ"), candidate ->
                            consumerLowerSeq >= 0L
                                    && candidate.eventSeq >= consumerLowerSeq
                                    && candidate.eventSeq
                                    < consumerUpperSeq);

            for (String declaration : consumers.keySet()) {
                DeclaredFieldCell leaf = DeclaredFieldCell.parse(declaration);
                if (leaf == null || rpcProjectionKind(leaf.type).isEmpty()) {
                    // A carrier spine field is not a value endpoint.  Only a
                    // declared carrier reconstruction can say anything about
                    // it, and that runs below.
                    continue;
                }
                List<RpcDescendantCandidate> sourceCandidates = producers
                        .getOrDefault(declaration,
                                Collections.<RpcDescendantCandidate>
                                        emptyList());
                List<RpcDescendantCandidate> targetCandidates =
                        consumers.get(declaration);
                if (sourceCandidates.size() != 1
                        || targetCandidates.size() != 1) {
                    markRpcProjectionBlocked(index, targetCandidates,
                            "MISSING_OR_AMBIGUOUS_RPC_DESCENDANT_PROJECTION",
                            -1);
                    continue;
                }
                RpcDescendantCandidate source = sourceCandidates.get(0);
                RpcDescendantCandidate target = targetCandidates.get(0);
                ExactPort sourceState = index.exactPort(source, true);
                ExactPort targetInput = index.exactInputPort(target);
                if (sourceState == null || targetInput == null) {
                    markRpcProjectionBlocked(index, targetCandidates,
                            "MISSING_EXACT_RPC_DESCENDANT_PORT", -1);
                    continue;
                }
                boolean container = rpcProjectableContainerType(target.type);
                int width = Math.max(source.observedWidth,
                        target.observedWidth);
                if (container && width > LoopBoundPolicy
                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
                    markRpcProjectionBlocked(index, targetCandidates,
                            "BOUND_INSUFFICIENT", width);
                    continue;
                }

                if (!publishRpcDescendantProjection(program, index, whole,
                        source, target, sourceState, targetInput,
                        emittedEdges,
                        "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                        rpcProjectionSelectionAuthority(source.type))) {
                    continue;
                }
                if (container) {
                    markProducerContainerDependencies(index, whole, source);
                }
            }
            addDeclaredCarrierProjections(program, index, whole,
                    carrierProjections.get(text(whole.get("mappingId"))),
                    consumerUpperSeq, emittedEdges);
        }
        markProtocolCarrierReconstructions(program, index);
    }

    /**
     * Publishes one producer output, one consumer input and the equality
     * between them.  Returns false when the producer region is unknown.
     */
    private static boolean publishRpcDescendantProjection(
            StaticProgram program, RpcDescendantProjectionIndex index,
            Map<String, Object> whole, RpcDescendantCandidate source,
            RpcDescendantCandidate target, ExactPort sourceState,
            ExactPort targetInput, Set<String> emittedEdges,
            String authority, String selection) {
        Map<String, Object> outputRegion = index.region(source.region);
        if (outputRegion == null) return false;
        Map<String, Object> derivedOutput = derivedRpcDescendantOutput(
                whole, source, sourceState, authority, selection);
        Map<String, Object> member = index.exactContainerMember(source);
        copyContainerMemberIdentity(member, derivedOutput, false);
        List<Map<String, Object>> outputs = rows(
                outputRegion.get("outputs"));
        addPortIfAbsent(outputs, derivedOutput);
        outputRegion.put("outputs", outputs);

        markProjectedDescendantInput(targetInput.port, whole,
                source.declaration, target.type, false, authority,
                selection);
        copyContainerMemberIdentity(member, targetInput.port, true);
        targetInput.port.put("runtimeAccesses",
                Collections.singletonList(targetInput.access));

        Map<String, Object> projection = projectedRpcDescendantFlow(whole,
                source, target, text(derivedOutput.get("portId")),
                text(targetInput.port.get("portId")), authority, selection);
        copyContainerMemberIdentity(member, projection, false);
        if (emittedEdges.add(text(projection.get("edgeId")))) {
            program.regionEdges.add(projection);
        }
        return true;
    }

    private static void copyContainerMemberIdentity(
            Map<String, Object> member, Map<String, Object> target,
            boolean sourcePrefix) {
        if (member == null || target == null) return;
        String prefix = sourcePrefix ? "rpcSource" : "";
        for (String field : new String[]{"containerMemberToken",
                "containerMemberIdentityAuthority"}) {
            Object value = member.get(field);
            if (value == null) continue;
            String name = sourcePrefix
                    ? prefix + Character.toUpperCase(field.charAt(0))
                    + field.substring(1) : field;
            target.put(name, value);
        }
    }

    /**
     * Projects the declared fields of a reply carrier the mapping states is
     * rebuilt field by field.
     *
     * <p>A trusted mapping alone equates the whole reply object, which leaves
     * every leaf below it unproven.  A mapping that additionally declares
     * {@code DECLARED_FIELDS_AND_ELEMENT_ORDER} states a structural property
     * of the transport: the reply is reconstructed as the same declared
     * types, so the same declared field of the same declared type holds the
     * same value on both sides.  That is a declared path match between two
     * byte-identical declarations, never an inference from a name.</p>
     *
     * <p>The descent is seeded by the exact server-result and caller-result
     * objects recorded on the trusted response edge.  From that corresponding
     * carrier pair it continues into every declared field <em>both sides
     * actually recorded</em>: a scalar leaf becomes an equality, another
     * spine field becomes the next pair.  Nothing is projected where one side
     * has no recorded access, and no port is invented for a field that was
     * never observed.</p>
     *
     * <p>A reference-array field descends only when both sides record the
     * exact array object, index, and element identity and the configured
     * transport declares element-order preservation.  Lists/maps and arrays
     * with missing, conflicting, or over-bound evidence keep a named gap.
     * The whole descent is bounded by
     * {@link LoopBoundPolicy#SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY}
     * corresponding pairs.</p>
     */
    private static void addDeclaredCarrierProjections(
            StaticProgram program, RpcDescendantProjectionIndex index,
            Map<String, Object> whole, String carrierProjection,
            long consumerUpperSeq, Set<String> emittedEdges) {
        if (!ProtocolCarrierProjection.DECLARED_FIELDS_AND_ELEMENT_ORDER
                .equals(text(carrierProjection))) {
            return;
        }
        String fromRegion = text(whole.get("fromRegion"));
        String toRegion = text(whole.get("toRegion"));
        long fromRoot = longNumber(whole.get("fromRootCallId"), -1L);
        long toRoot = longNumber(whole.get("toRootCallId"), -1L);
        long sendSeq = longNumber(whole.get("sendEventSeq"), -1L);
        long producerLowerSeq = longNumber(whole.get("receiveEventSeq"), -1L);
        long consumerLowerSeq = longNumber(whole.get(
                "callerResultEventSeq"), -1L);
        // The server method result starts response transport; it does not
        // finish it.  Hadoop IPC (like many RPC stacks) reads the returned
        // carrier in a serializer after the server stub has returned.  The
        // caller-result event is the first recorded fence that proves that
        // serialization and reconstruction have completed.  Exact producer
        // region/root/object filtering below keeps this wider transaction
        // window from admitting consumer or unrelated-object accesses.
        long producerUpperSeq = responseProjectionUpperSeq(whole);
        if (sendSeq < 0L || producerLowerSeq < 0L
                || producerUpperSeq < producerLowerSeq
                || consumerLowerSeq < 0L) {
            return;
        }

        Deque<int[]> work = new ArrayDeque<>();
        Set<String> visited = new LinkedHashSet<>();
        int[] carrierPair = exactDeclaredCarrierRootPair(whole);
        if (carrierPair == null) return;
        work.addLast(carrierPair);
        while (!work.isEmpty() && visited.size()
                < LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
            int[] pair = work.removeFirst();
            if (!visited.add(pair[0] + "\n" + pair[1])) continue;

            Map<String, RpcDescendantCandidate> producerFields =
                    lastDefinitionsOn(index, pair[0], producerUpperSeq);
            for (Map.Entry<String, RpcDescendantCandidate> entry
                    : producerFields.entrySet()) {
                DeclaredFieldCell field = DeclaredFieldCell.parse(
                        entry.getKey());
                if (field == null) continue;
                RpcDescendantCandidate source = entry.getValue();
                List<RpcDescendantCandidate> reads =
                        reconstructedReadsOn(index, pair[1], entry.getKey(),
                                toRegion, toRoot, sendSeq, consumerLowerSeq,
                                consumerUpperSeq);
                if (reads.isEmpty()) continue;
                if (rpcProjectableContainerType(field.type)) {
                    // Lists/maps retain their existing bounded-container
                    // algebra.  This recorder package proves only JVM
                    // reference-array element identity.
                    if (!rpcProjectableReferenceArrayType(field.type)) {
                        continue;
                    }
                    int rebuiltArray = uniqueValueObject(reads);
                    ArrayElementProjection elements =
                            exactDeclaredArrayElementPairs(
                                    rows(source.binding.get(
                                            "runtimeArrayElementBindings")),
                                    source.valueObjectId,
                                    combinedArrayElementBindings(reads),
                                    rebuiltArray,
                                    source.eventSeq,
                                    consumerLowerSeq,
                                    sendSeq,
                                    consumerLowerSeq);
                    if (!elements.proved()) {
                        markRpcProjectionBlocked(index, reads,
                                elements.blocker, elements.width);
                        continue;
                    }
                    for (int[] elementPair : elements.pairs) {
                        work.addLast(elementPair);
                    }
                    markArrayElementProjectionProved(index, reads,
                            elements.width);
                    continue;
                }
                if (rpcCarrierReferenceType(field.type)) {
                    int next = uniqueValueObject(reads);
                    if (next != 0 && source.valueObjectId != 0) {
                        work.addLast(new int[]{source.valueObjectId, next});
                    }
                    continue;
                }
                ExactPort sourceState = index.exactPort(source, true);
                if (sourceState == null) continue;
                for (RpcDescendantCandidate target : reads) {
                    ExactPort targetInput = index.exactInputPort(target);
                    if (targetInput == null) continue;
                    publishRpcDescendantProjection(program, index, whole,
                            source, target, sourceState, targetInput,
                            emittedEdges, DECLARED_CARRIER_AUTHORITY,
                            DECLARED_CARRIER_SELECTION);
                }
            }
        }
    }

    /**
     * End fence for reading a returned response carrier.
     *
     * <p>A server-stub method exit only publishes the carrier to the RPC
     * stack. Serialization may read that object afterwards. The matching
     * caller-result event is the first recorded event that proves the
     * response transfer, including serialization, has completed.</p>
     */
    static long responseProjectionUpperSeq(Map<String, Object> flow) {
        long producerResult = longNumber(flow.get(
                "producerResultEventSeq"), -1L);
        long callerResult = longNumber(flow.get(
                "callerResultEventSeq"), -1L);
        return producerResult >= 0L && callerResult >= producerResult
                ? callerResult : -1L;
    }

    /**
     * Exact carrier roots recorded at the two ends of one trusted response.
     * A descendant value is deliberately not used as a seed: doing so would
     * start the walk at (for example) two arrays and skip the declared field
     * that establishes what those arrays mean.  Missing result identity is a
     * hard stop, never an invitation to pair by a value or occurrence.
     */
    static int[] exactDeclaredCarrierRootPair(Map<String, Object> flow) {
        if (!"EXACT_RUNTIME_PROTOCOL_CALLSITE_RESULT_V1".equals(
                text(flow.get("callsiteAuthority")))) {
            return null;
        }
        int producer = number(flow.get("producerResultObjectId"), 0);
        int consumer = number(flow.get("callerResultObjectId"), 0);
        return producer == 0 || consumer == 0
                ? null : new int[]{producer, consumer};
    }

    /**
     * The last recorded definition of each declared field of one producer
     * object before the reply was sent.  A later write cannot be what the
     * reply carried.
     */
    private static Map<String, RpcDescendantCandidate> lastDefinitionsOn(
            RpcDescendantProjectionIndex index, int object,
            long producerResultSeq) {
        Map<String, RpcDescendantCandidate> result = new LinkedHashMap<>();
        for (RpcDescendantCandidate candidate
                : index.onReceiver("HEAP_WRITE", object)) {
            if (candidate.eventSeq >= producerResultSeq) continue;
            RpcDescendantCandidate prior = result.get(candidate.declaration);
            if (prior == null || prior.eventSeq < candidate.eventSeq) {
                result.put(candidate.declaration, candidate);
            }
        }
        return result;
    }

    /**
     * Consumer reads of one declared field of a reconstructed object whose
     * observed value this reply defined: the read is preceded by a write in
     * this reply's decode window and by no later one.  A read that observes a
     * value written after the decode is not this reply's value.
     */
    private static List<RpcDescendantCandidate> reconstructedReadsOn(
            RpcDescendantProjectionIndex index, int object,
            String declaration, String toRegion, long toRoot, long sendSeq,
            long consumerLowerSeq, long consumerUpperSeq) {
        List<RpcDescendantCandidate> result = new ArrayList<>();
        for (RpcDescendantCandidate read
                : index.onReceiver("HEAP_READ", object)) {
            if (!declaration.equals(read.declaration)
                    || !toRegion.equals(read.region)
                    || read.rootCallId != toRoot
                    || read.eventSeq >= consumerUpperSeq) {
                continue;
            }
            long latest = -1L;
            for (RpcDescendantCandidate write
                    : index.onReceiver("HEAP_WRITE", object)) {
                if (!declaration.equals(write.declaration)
                        || write.eventSeq >= read.eventSeq) {
                    continue;
                }
                latest = Math.max(latest, write.eventSeq);
            }
            if (latest > sendSeq && latest <= consumerLowerSeq) {
                result.add(read);
            }
        }
        return result;
    }

    private static int uniqueValueObject(
            List<RpcDescendantCandidate> candidates) {
        Set<Integer> values = new LinkedHashSet<>();
        for (RpcDescendantCandidate candidate : candidates) {
            if (candidate.valueObjectId != 0) {
                values.add(candidate.valueObjectId);
            }
        }
        return values.size() == 1 ? values.iterator().next() : 0;
    }

    private static List<Map<String, Object>> combinedArrayElementBindings(
            List<RpcDescendantCandidate> candidates) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (RpcDescendantCandidate candidate : candidates) {
            for (Map<String, Object> access : rows(candidate.binding.get(
                    "runtimeArrayElementBindings"))) {
                unique.put(CausynthJson.write(access), access);
            }
        }
        return new ArrayList<>(unique.values());
    }

    /**
     * Pairs two reconstructed reference arrays solely by exact object id and
     * the order-preserving index declared by the configured transport.
     */
    static ArrayElementProjection exactDeclaredArrayElementPairs(
            List<Map<String, Object>> producerAccesses, int producerArray,
            List<Map<String, Object>> consumerAccesses, int consumerArray,
            long producerLowerExclusive, long producerUpperExclusive,
            long consumerLowerExclusive, long consumerUpperExclusive) {
        if (producerArray == 0 || consumerArray == 0) {
            return ArrayElementProjection.blocked(
                    "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY", -1);
        }
        // A declared carrier contract relates the two logical result
        // objects, not their serializers.  Prefer the exact array snapshot
        // recorded when each result field was published.  Older traces may
        // still prove the same fact through concrete construction writes or
        // a complete read traversal, in that order.
        ArrayElementIndex producer = ArrayElementIndex.buildLogicalResult(
                producerAccesses, producerArray,
                producerLowerExclusive, producerUpperExclusive,
                "ARRAY_WRITE", "ARRAY_READ");
        ArrayElementIndex consumer = ArrayElementIndex.buildLogicalResult(
                consumerAccesses, consumerArray,
                consumerLowerExclusive, consumerUpperExclusive,
                "ARRAY_WRITE", "ARRAY_READ");
        int width = Math.max(producer.width, consumer.width);
        if (!producer.blocker.isEmpty()) {
            return ArrayElementProjection.blocked(producer.blocker, width);
        }
        if (!consumer.blocker.isEmpty()) {
            return ArrayElementProjection.blocked(consumer.blocker, width);
        }
        if (width > LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
            return ArrayElementProjection.blocked("BOUND_INSUFFICIENT",
                    width);
        }
        if ((!producer.exactSnapshot && producer.elements.isEmpty())
                || (!consumer.exactSnapshot && consumer.elements.isEmpty())
                || !producer.elements.keySet().equals(
                consumer.elements.keySet())) {
            return ArrayElementProjection.blocked(
                    "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY", width);
        }
        List<int[]> pairs = new ArrayList<>();
        for (int index = 0; index < width; index++) {
            Integer left = producer.elements.get(index);
            Integer right = consumer.elements.get(index);
            if (left == null || right == null || left == 0 || right == 0) {
                return ArrayElementProjection.blocked(
                        "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY", width);
            }
            pairs.add(new int[]{left, right});
        }
        return ArrayElementProjection.proved(pairs, width);
    }

    private static void markArrayElementProjectionProved(
            RpcDescendantProjectionIndex index,
            List<RpcDescendantCandidate> candidates, int width) {
        for (RpcDescendantCandidate candidate : candidates) {
            ExactPort port = index.exactInputPort(candidate);
            if (port == null) continue;
            port.port.put("rpcArrayElementProjectionAdmission", "PROVED");
            port.port.put("rpcArrayElementProjectionAuthority",
                    "EXACT_RUNTIME_REFERENCE_ARRAY_ELEMENT_ORDER_V1");
            port.port.put("observedContainerWidth", width);
        }
    }

    static final class ArrayElementProjection {
        final List<int[]> pairs;
        final String blocker;
        final int width;

        private ArrayElementProjection(List<int[]> pairs, String blocker,
                                       int width) {
            this.pairs = pairs;
            this.blocker = blocker;
            this.width = width;
        }

        private static ArrayElementProjection proved(List<int[]> pairs,
                                                      int width) {
            return new ArrayElementProjection(pairs, "", width);
        }

        private static ArrayElementProjection blocked(String blocker,
                                                       int width) {
            return new ArrayElementProjection(
                    Collections.<int[]>emptyList(), blocker, width);
        }

        boolean proved() {
            return blocker.isEmpty();
        }
    }

    private static final class ArrayElementIndex {
        private final Map<Integer, Integer> elements =
                new LinkedHashMap<>();
        private String blocker = "";
        private int width;
        private boolean exactSnapshot;

        private static ArrayElementIndex buildLogicalResult(
                List<Map<String, Object>> accesses, int array,
                long lowerExclusive, long upperExclusive,
                String... fallbacks) {
            ArrayElementIndex snapshot = latestSnapshot(accesses, array,
                    lowerExclusive, upperExclusive);
            if (snapshot != null) return snapshot;
            for (String kind : fallbacks) {
                ArrayElementIndex candidate = build(accesses, kind, array,
                        lowerExclusive, upperExclusive);
                if (!candidate.blocker.isEmpty()
                        || !candidate.elements.isEmpty()) {
                    return candidate;
                }
            }
            return new ArrayElementIndex();
        }

        /** Latest exact FIELD_WRITE-bound snapshot in the result window. */
        private static ArrayElementIndex latestSnapshot(
                List<Map<String, Object>> accesses, int array,
                long lowerExclusive, long upperExclusive) {
            long latestBoundary = -1L;
            for (Map<String, Object> access : accesses) {
                if (!"ARRAY_SNAPSHOT".equals(text(access.get("kind")))
                        || array != number(access.get("arrayObjectId"), 0)) {
                    continue;
                }
                long boundary = longNumber(
                        access.get("snapshotBoundarySeq"), -1L);
                if (boundary < lowerExclusive
                        || boundary >= upperExclusive) {
                    continue;
                }
                latestBoundary = Math.max(latestBoundary, boundary);
            }
            if (latestBoundary < 0L) return null;

            ArrayElementIndex result = new ArrayElementIndex();
            result.exactSnapshot = true;
            int declaredLength = -1;
            long snapshotLastEvent = -1L;
            for (Map<String, Object> access : accesses) {
                if (!"ARRAY_SNAPSHOT".equals(text(access.get("kind")))
                        || array != number(access.get("arrayObjectId"), 0)
                        || latestBoundary != longNumber(
                        access.get("snapshotBoundarySeq"), -1L)) {
                    continue;
                }
                if (!"EXACT_RUNTIME_REFERENCE_ARRAY_SNAPSHOT_V1".equals(
                        text(access.get("authority")))) {
                    result.blocker =
                            "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
                int length = number(access.get("arrayLength"), -1);
                if (length < 0 || declaredLength >= 0
                        && declaredLength != length) {
                    result.blocker =
                            "AMBIGUOUS_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
                declaredLength = length;
                result.width = length;
                snapshotLastEvent = Math.max(snapshotLastEvent,
                        longNumber(access.get("eventSeq"), -1L));
                if (length == 0) continue;
                int index = number(access.get("arrayIndex"), -1);
                int element = number(access.get("elementObjectId"), 0);
                if (index < 0 || index >= length || element == 0) {
                    result.blocker =
                            "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
                Integer prior = result.elements.putIfAbsent(index, element);
                if (prior != null && prior != element) {
                    result.blocker =
                            "AMBIGUOUS_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
            }
            if (declaredLength < 0) {
                result.blocker = "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
                return result;
            }
            if (declaredLength > LoopBoundPolicy
                    .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
                result.blocker = "BOUND_INSUFFICIENT";
                return result;
            }
            // The field write publishes the initial logical value.  Exact
            // program writes after that snapshot but before the result fence
            // update the same array state; take the latest write per index.
            Map<Integer, Long> latestWrite = new LinkedHashMap<>();
            for (Map<String, Object> access : accesses) {
                long event = longNumber(access.get("eventSeq"), -1L);
                if (!"ARRAY_WRITE".equals(text(access.get("kind")))
                        || array != number(access.get("arrayObjectId"), 0)
                        || event <= snapshotLastEvent
                        || event >= upperExclusive) {
                    continue;
                }
                if (!"EXACT_RUNTIME_REFERENCE_ARRAY_ELEMENT_V1".equals(
                        text(access.get("authority")))) {
                    result.blocker =
                            "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
                int index = number(access.get("arrayIndex"), -1);
                int element = number(access.get("elementObjectId"), 0);
                if (index < 0 || index >= declaredLength || element == 0) {
                    result.blocker =
                            "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
                if (event > latestWrite.getOrDefault(index, -1L)) {
                    latestWrite.put(index, event);
                    result.elements.put(index, element);
                }
            }
            if (declaredLength != result.elements.size()) {
                result.blocker = "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
            }
            return result;
        }

        private static ArrayElementIndex build(
                List<Map<String, Object>> accesses, String kind, int array,
                long lowerExclusive, long upperExclusive) {
            ArrayElementIndex result = new ArrayElementIndex();
            for (Map<String, Object> access : accesses) {
                long event = longNumber(access.get("eventSeq"), -1L);
                if (!kind.equals(text(access.get("kind")))
                        || array != number(access.get("arrayObjectId"), 0)
                        || event <= lowerExclusive
                        || event >= upperExclusive) {
                    continue;
                }
                if (!"EXACT_RUNTIME_REFERENCE_ARRAY_ELEMENT_V1".equals(
                        text(access.get("authority")))) {
                    result.blocker =
                            "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
                int index = number(access.get("arrayIndex"), -1);
                int element = number(access.get("elementObjectId"), 0);
                if (index < 0 || element == 0) {
                    result.blocker =
                            "MISSING_EXACT_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
                result.width = Math.max(result.width, index + 1);
                Integer prior = "ARRAY_WRITE".equals(kind)
                        ? result.elements.put(index, element)
                        : result.elements.putIfAbsent(index, element);
                if (!"ARRAY_WRITE".equals(kind)
                        && prior != null && prior != element) {
                    result.blocker =
                            "AMBIGUOUS_ARRAY_ELEMENT_IDENTITY";
                    return result;
                }
            }
            return result;
        }
    }

    /**
     * Stops the demand closure from treating a rebuilt protocol carrier as
     * the authoritative producer of the value it carries.
     *
     * <p>A write recorded between a configured request send and its own
     * caller result is reply decoding, and a later read of a field that such
     * a write last defined observes a decoded value.  Both penetrate to the
     * configured response port instead of ending the chain, so the demand
     * continues into the server region.  A carrier without an exact declared
     * descendant projection keeps a named gap rather than an implicit
     * equality.</p>
     */
    private static void markProtocolCarrierReconstructions(
            StaticProgram program, RpcDescendantProjectionIndex index) {
        for (Map<String, Object> region : program.regions) {
            List<Map<String, Object>> inputs = rows(
                    region.get("symbolicInputs"));
            ProtocolCarrierReconstruction decode =
                    ProtocolCarrierReconstruction.of(inputs);
            if (decode.isEmpty()) continue;
            String regionId = text(region.get("regionId"));
            for (Map<String, Object> output : rows(region.get("outputs"))) {
                if ("PROTOCOL_INPUT".equals(
                        text(output.get("sourceKind")))) {
                    continue;
                }
                long rootCallId = portRootCallId(output, true);
                ProtocolCarrierReconstruction.Window window =
                        decode.reconstructionOf(rootCallId,
                                longNumber(output.get("eventSeq"), -1L));
                if (window != null) {
                    ProtocolCarrierReconstruction.mark(output, window,
                            Boolean.TRUE.equals(booleanValue(output.get(
                                    "rpcDescendantProjectionOutput"))));
                }
            }
            for (Map<String, Object> input : inputs) {
                if ("PROTOCOL_INPUT".equals(text(input.get("sourceKind")))) {
                    continue;
                }
                long rootCallId = portRootCallId(input, false);
                ProtocolCarrierReconstruction.Window window =
                        decode.reconstructionOf(rootCallId,
                                carrierDefinitionSeq(index, regionId,
                                        rootCallId, input));
                if (window != null) {
                    ProtocolCarrierReconstruction.mark(input, window,
                            Boolean.TRUE.equals(booleanValue(input.get(
                                    "rpcDescendantProjectionInput"))));
                }
            }
        }
    }

    /**
     * Returns the event that last defined the exact field value one input
     * port observes, or {@code -1} when no write to that receiver and
     * declaration precedes the read inside the same activation.
     */
    private static long carrierDefinitionSeq(
            RpcDescendantProjectionIndex index, String regionId,
            long rootCallId, Map<String, Object> input) {
        List<String> declarations = strings(
                input.get("fieldPathDeclarations"));
        if (declarations.isEmpty() || rootCallId < 0L) return -1L;
        String declaration = declarations.get(declarations.size() - 1);
        DeclaredFieldCell leaf = DeclaredFieldCell.parse(declaration);
        if (leaf == null || rpcProjectionKind(leaf.type).isEmpty()) {
            // A carrier spine field holds an object, not a value; a rebuilt
            // reference is not evidence about anything the demand asked for.
            return -1L;
        }
        long readSeq = longNumber(input.get("eventSeq"), -1L);
        int receiver = number(input.get("fieldReceiverObjectId"), 0);
        if (readSeq < 0L || receiver == 0) return -1L;
        long latest = -1L;
        for (RpcDescendantCandidate candidate : index.candidates(regionId,
                rootCallId, "HEAP_WRITE")) {
            if (candidate.receiverObjectId != receiver
                    || !declaration.equals(candidate.declaration)
                    || candidate.eventSeq >= readSeq
                    || candidate.eventSeq <= latest) {
                continue;
            }
            latest = candidate.eventSeq;
        }
        return latest;
    }

    private interface RpcCandidatePredicate {
        boolean test(RpcDescendantCandidate candidate);
    }

    private static Map<String, List<RpcDescendantCandidate>>
            candidatesByDeclaration(
            List<RpcDescendantCandidate> candidates,
            RpcCandidatePredicate predicate) {
        Map<String, Map<String, RpcDescendantCandidate>> unique =
                new LinkedHashMap<>();
        for (RpcDescendantCandidate candidate : candidates) {
            if (!predicate.test(candidate)) continue;
            String occurrence = candidate.staticSite + "\n"
                    + candidate.eventSeq + "\n" + candidate.declaration;
            unique.computeIfAbsent(candidate.declaration,
                    ignored -> new LinkedHashMap<>()).putIfAbsent(
                    occurrence, candidate);
        }
        Map<String, List<RpcDescendantCandidate>> result =
                new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, RpcDescendantCandidate>> entry
                : unique.entrySet()) {
            result.put(entry.getKey(), new ArrayList<>(
                    entry.getValue().values()));
        }
        return result;
    }

    private static boolean trustedResponseFlow(Map<String, Object> flow) {
        long caller = longNumber(flow.get("callerSiteEventSeq"), -1L);
        long send = longNumber(flow.get("sendEventSeq"), -1L);
        long receive = longNumber(flow.get("receiveEventSeq"), -1L);
        return "RUNTIME_PROTOCOL_FLOW".equals(text(flow.get("kind")))
                && "RESPONSE".equals(first(text(flow.get("direction")),
                text(flow.get("protocolDirection"))))
                && "TRUSTED_CONFIGURED_RPC_MAPPING_V1".equals(
                text(flow.get("authority")))
                && !text(flow.get("mappingId")).isEmpty()
                && caller >= 0L && caller < send && send < receive;
    }

    /**
     * Returns the next trusted RPC call boundary in the same consumer
     * activation.  A response-derived read belongs to the half-open corridor
     * beginning at this response's concrete caller result and ending when the
     * next RPC starts.  This keeps repeated service-loop iterations separate
     * without depending on replay-unstable object identities or invocation
     * ordinals.
     */
    private static long nextTrustedResponseCallerSite(
            List<Map<String, Object>> flows, Map<String, Object> current) {
        String region = text(current.get("toRegion"));
        long rootCallId = longNumber(current.get("toRootCallId"), -1L);
        long caller = longNumber(current.get("callerSiteEventSeq"), -1L);
        long next = Long.MAX_VALUE;
        for (Map<String, Object> candidate : flows) {
            if (!trustedResponseFlow(candidate)
                    || !region.equals(text(candidate.get("toRegion")))
                    || rootCallId != longNumber(
                    candidate.get("toRootCallId"), -1L)) {
                continue;
            }
            long candidateCaller = longNumber(
                    candidate.get("callerSiteEventSeq"), -1L);
            if (candidateCaller > caller && candidateCaller < next) {
                next = candidateCaller;
            }
        }
        return next;
    }

    private static Map<String, Object> derivedRpcDescendantOutput(
            Map<String, Object> whole, RpcDescendantCandidate source,
            ExactPort exact, String authority, String selection) {
        Map<String, Object> output = new LinkedHashMap<>(exact.port);
        String identity = source.region + "\n" + source.rootCallId + "\n"
                + text(whole.get("mappingId")) + "\n"
                + source.staticSite + "\n" + source.declaration;
        output.put("portId", source.region + ".out."
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8)));
        output.put("runtimeAccesses",
                Collections.singletonList(exact.access));
        output.put("javaType", source.type);
        output.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        if (rpcProjectableContainerType(source.type)) {
            output.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        } else {
            output.remove("symbolicDemand");
        }
        output.put("rpcDescendantProjectionOutput", true);
        output.put("rpcProjectionAuthority", authority);
        output.put("rpcProjectionSelectionAuthority", selection);
        output.put("rpcProjectionMappingId", whole.get("mappingId"));
        output.put("rpcProjectionFieldDeclaration", source.declaration);
        output.put("rpcProjectionValueCell", source.valueCell());
        output.put("rpcProjectionWholeOutputCell", whole.get("fromCell"));
        output.put("rpcProjectionWholeOutputPort", whole.get("fromPort"));
        output.put("rpcProjectionStaticAccessSiteId", source.staticSite);
        return output;
    }

    private static Map<String, Object> projectedRpcDescendantFlow(
            Map<String, Object> whole, RpcDescendantCandidate source,
            RpcDescendantCandidate target, String fromPort, String toPort,
            String authority, String selection) {
        String identity = text(whole.get("edgeId")) + "\n"
                + source.declaration + "\n" + fromPort + "\n" + toPort;
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("schemaVersion", 3);
        result.put("kind", "RUNTIME_PROTOCOL_FLOW");
        result.put("edgeId", "RP.PROJECTION."
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8)));
        result.put("fromRegion", source.region);
        result.put("toRegion", target.region);
        result.put("fromRootCallId", source.rootCallId);
        result.put("toRootCallId", target.rootCallId);
        result.put("fromPort", fromPort);
        result.put("toPort", toPort);
        result.put("fromCell", source.valueCell());
        result.put("toCell", target.resultCell());
        result.put("transportKind", whole.get("transportKind"));
        result.put("direction", "RESPONSE");
        result.put("protocolDirection", "RESPONSE");
        result.put("mappingId", whole.get("mappingId"));
        result.put("port", whole.get("port"));
        result.put("authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        result.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        result.put("projectionKind", rpcProjectionKind(source.type));
        result.put("rpcDescendantProjection", true);
        result.put("rpcProjectionAuthority", authority);
        result.put("projectionSelectionAuthority", selection);
        result.put("projectionOfEdgeId", whole.get("edgeId"));
        result.put("projectionOfFromPort", whole.get("fromPort"));
        result.put("projectionOfToPort", whole.get("toPort"));
        result.put("javaType", source.type);
        result.put("fieldPathDeclarations",
                Collections.singletonList(source.declaration));
        result.put("producerProjectionSiteId", source.staticSite);
        result.put("consumerProjectionSiteId", target.staticSite);
        for (String field : new String[]{
                "callerSiteEventSeq", "sendEventSeq", "receiveEventSeq",
                "callerResultEventSeq", "callerMethod", "callerSiteId",
                "callerUnitIndex", "callerInvocationId",
                "callerDeclaredCallee", "clientCallId", "serverThreadId",
                "fromOwnerId", "fromLaneId", "fromSpanId",
                "fromLogicalRegionId", "toOwnerId", "toLaneId",
                "toSpanId", "toLogicalRegionId",
                "receiveRemoteParentSpanId"}) {
            copyIfPresent(result, whole, field);
        }
        return result;
    }

    private static void markProjectedDescendantInput(
            Map<String, Object> input, Map<String, Object> whole,
            String declaration, String javaType, boolean producerDependency,
            String authority, String selection) {
        input.put("javaType", javaType);
        input.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        input.put("rpcDescendantProjectionInput", !producerDependency);
        input.put("rpcDescendantProjectionDependency", producerDependency);
        input.put("rpcProjectionAuthority", authority);
        input.put("rpcProjectionSelectionAuthority", selection);
        // A projection answers the very question an earlier blocker asked.
        input.remove("rpcProjectionAdmission");
        input.remove("rpcProjectionBlocker");
        input.put("rpcProjectionMappingId", whole.get("mappingId"));
        input.put("rpcProjectionFieldDeclaration", declaration);
        if (rpcProjectableContainerType(javaType)) {
            input.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
            input.put("containerCapacity", LoopBoundPolicy
                    .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
        } else {
            // A scalar leaf carried below the wire object is an ordinary
            // symbolic value once its exact producer definition is bound.
            // The carrier object itself keeps no demand and stays concrete.
            input.remove("symbolicDemand");
            input.remove("containerCapacity");
        }
    }

    private static void markProducerContainerDependencies(
            RpcDescendantProjectionIndex index, Map<String, Object> whole,
            RpcDescendantCandidate source) {
        Map<String, Object> region = index.region(
                text(whole.get("fromRegion")));
        if (region == null) return;
        long rootCallId = longNumber(whole.get("fromRootCallId"), -1L);
        for (Map<String, Object> input
                : rows(region.get("symbolicInputs"))) {
            if (portRootCallId(input, false) != rootCallId) continue;
            String type = projectableContainerType(input);
            if (type.isEmpty()) continue;
            boolean reaches = false;
            for (String boundary : RegionDemandIndex.boundaryCells(input)) {
                if (index.valueFlow.reaches(text(whole.get("fromRegion")),
                        boundary, source.valueCell())) {
                    reaches = true;
                    break;
                }
            }
            if (reaches) {
                markProjectedDescendantInput(input, whole,
                        source.declaration, type, true,
                        "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                        rpcProjectionSelectionAuthority(type));
            }
        }
    }

    private static void markRpcProjectionBlocked(
            RpcDescendantProjectionIndex index,
            List<RpcDescendantCandidate> candidates, String blocker,
            int observedWidth) {
        for (RpcDescendantCandidate candidate : candidates) {
            ExactPort port = index.exactInputPort(candidate);
            if (port == null) continue;
            port.port.put("symbolicDemand", "BOUND_INSUFFICIENT".equals(
                    blocker) ? "CONCRETE_BOUND_INSUFFICIENT"
                    : "CONCRETE_RPC_DESCENDANT_REPLAY");
            port.port.put("rpcProjectionAdmission", "BLOCKED");
            port.port.put("rpcProjectionBlocker", blocker);
            if (rpcProjectableContainerType(candidate.type)) {
                port.port.put("containerCapacity", LoopBoundPolicy
                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
                if (observedWidth >= 0) {
                    port.port.put("observedContainerWidth", observedWidth);
                }
            }
        }
    }

    private static void addPortIfAbsent(List<Map<String, Object>> ports,
                                        Map<String, Object> port) {
        String id = text(port.get("portId"));
        for (Map<String, Object> prior : ports) {
            if (id.equals(text(prior.get("portId")))) return;
        }
        ports.add(port);
    }

    private static String projectableContainerType(
            Map<String, Object> port) {
        String type = text(port.get("javaType"));
        if (rpcProjectableContainerType(type)) return type;
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        if (!declarations.isEmpty()) {
            DeclaredFieldCell leaf = DeclaredFieldCell.parse(
                    declarations.get(declarations.size() - 1));
            if (leaf != null && rpcProjectableContainerType(leaf.type)) {
                return leaf.type;
            }
        }
        return "";
    }

    private static boolean rpcProjectableContainerType(String type) {
        String value = text(type).trim();
        if (value.startsWith("[") || value.endsWith("[]")) return true;
        return "java.util.Map".equals(value)
                || "java.util.HashMap".equals(value)
                || "java.util.LinkedHashMap".equals(value)
                || "java.util.List".equals(value)
                || "java.util.AbstractList".equals(value)
                || "java.util.ArrayList".equals(value);
    }

    private static boolean rpcProjectableReferenceArrayType(String type) {
        String value = text(type).trim();
        if (value.startsWith("[")) {
            return value.startsWith("[L") || value.startsWith("[[");
        }
        if (!value.endsWith("[]")) return false;
        String component = value.substring(0, value.length() - 2).trim();
        if (component.endsWith("[]")) return true;
        return !("boolean".equals(component) || "byte".equals(component)
                || "char".equals(component) || "short".equals(component)
                || "int".equals(component) || "long".equals(component)
                || "float".equals(component) || "double".equals(component));
    }

    /**
     * Semantic value leaves the current VM/SMT contract can represent
     * directly.  A carrier object below a boundary is never one of them, so
     * the demanded slice keeps descending until it reaches such a leaf.
     */
    private static boolean rpcProjectableScalarLeafType(String type) {
        String value = text(type).trim();
        return "boolean".equals(value) || "byte".equals(value)
                || "char".equals(value) || "short".equals(value)
                || "int".equals(value) || "long".equals(value)
                || "float".equals(value) || "double".equals(value)
                || "java.lang.String".equals(value);
    }

    /**
     * A declared field whose type is neither a container nor a semantic
     * scalar carries further declared fields rather than a value.  Such a
     * field is the spine of a transferred object graph: it is never itself
     * an equality endpoint, but a declared carrier reconstruction makes the
     * object it holds correspond, which is what lets the demanded descent
     * continue to a leaf that lives on that object.
     */
    private static boolean rpcCarrierReferenceType(String type) {
        String value = text(type).trim();
        return !value.isEmpty() && !rpcProjectableContainerType(value)
                && !rpcProjectableScalarLeafType(value)
                && value.indexOf('.') > 0;
    }

    /** Empty when the declared type is neither a projectable leaf shape. */
    private static String rpcProjectionKind(String type) {
        if (rpcProjectableContainerType(type)) {
            return "BOUNDED_CONTAINER_STATE";
        }
        return rpcProjectableScalarLeafType(type) ? "SCALAR_LEAF_VALUE" : "";
    }

    private static String rpcProjectionSelectionAuthority(String type) {
        return rpcProjectableContainerType(type)
                ? "STATIC_DEF_USE_CONTAINER_PROJECTION_V1"
                : "STATIC_DEF_USE_SCALAR_LEAF_PROJECTION_V1";
    }

    private static int observedContainerWidth(Map<String, Object> edge,
                                              Map<String, Object> binding) {
        for (String field : new String[]{"observedContainerWidth",
                "observedContainerSize", "containerSize",
                "containerLength", "arrayLength", "boundedWidth"}) {
            int value = number(binding.get(field), -1);
            if (value < 0) value = number(edge.get(field), -1);
            if (value >= 0) return value;
        }
        return -1;
    }

    private static List<Map<String, Object>> statePorts(
            String regionId, List<Map<String, Object>> edges,
            String transfer, String prefix) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Set<String>> seenAccesses = new LinkedHashMap<>();
        DependencyRoleClassifier roles = new DependencyRoleClassifier(edges);
        for (Map<String, Object> edge : edges) {
            if (!transfer.equals(text(edge.get("transferKind")))) {
                continue;
            }
            String dependencyRole = "HEAP_READ".equals(transfer)
                    ? roles.heapReadRole(edge)
                    : DependencyRole.VALUE_FRONTIER;
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeFieldBindings"))) {
                if (!regionId.equals(text(binding.get("regionId")))) {
                    continue;
                }
                String key = text(binding.get("rootCallId")) + "\n"
                        + text(binding.get("rootCell")) + "\n"
                        + strings(binding.get("fieldPath"));
                Map<String, Object> port = unique.get(key);
                if (port == null) {
                    port = new LinkedHashMap<>(binding);
                    String direction = "IN".equals(prefix)
                            ? ".in." : ".out.";
                    port.put("portId", regionId + direction
                            + UUID.nameUUIDFromBytes(
                            (regionId + "\n" + key).getBytes(
                                    StandardCharsets.UTF_8)));
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
                addRuntimeAccess(port, binding, edge,
                        seenAccesses.computeIfAbsent(key,
                                ignored -> new LinkedHashSet<>()));
                addUniqueString(port, "dependencyCells",
                        text(edge.get("fromCell")));
            }
        }
        return new ArrayList<>(unique.values());
    }

    @SuppressWarnings("unchecked")
    private static void addRuntimeAccess(Map<String, Object> port,
                                         Map<String, Object> binding,
                                         Map<String, Object> edge,
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
        access.put("process", binding.get("process"));
        access.put("rootCallId", binding.get("rootCallId"));
        access.put("fieldReceiverObjectId",
                binding.get("fieldReceiverObjectId"));
        access.put("valueObjectId", binding.get("valueObjectId"));
        access.put("primitiveValue", binding.get("primitiveValue"));
        access.put("fieldPathDeclarations",
                binding.get("fieldPathDeclarations"));
        access.put("bindingKind", binding.get("bindingKind"));
        access.put("writerFieldReadSeq", binding.get("writerFieldReadSeq"));
        access.put("mutatorEnterSeq", binding.get("mutatorEnterSeq"));
        access.put("mutationCompletionSeq",
                binding.get("mutationCompletionSeq"));
        access.put("mutationInvocationId",
                binding.get("mutationInvocationId"));
        access.put("mutatorDeclaredCallee",
                binding.get("mutatorDeclaredCallee"));
        access.put("containerMemberToken",
                binding.get("containerMemberToken"));
        access.put("containerMemberIdentityAuthority",
                binding.get("containerMemberIdentityAuthority"));
        access.put("containerObjectId", binding.get("containerObjectId"));
        access.put("containerKeyObjectId",
                binding.get("containerKeyObjectId"));
        access.put("containerValueObjectId",
                binding.get("containerValueObjectId"));
        access.put("containerMemberFieldBindings",
                binding.get("containerMemberFieldBindings"));
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
            String regionId, List<Map<String, Object>> edges,
            List<Map<String, Object>> branchPolicies) {
        Set<String> demandedEdges = semanticAccessorEdges(edges,
                branchPolicies);
        if (demandedEdges.isEmpty()) return Collections.emptyList();
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Integer> retainedByActivationStream =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!demandedEdges.contains(text(edge.get("id")))) continue;
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
                long rootCallId = longNumber(binding.get("rootCallId"), -1L);
                long callId = longNumber(binding.get("callId"), -1L);
                if (occurrence < 1 || rootCallId < 0L || callId < 0L) {
                    continue;
                }
                String key = rootCallId + "\n" + text(edge.get("id"))
                        + "\n" + callId + "\n" + occurrence;
                if (unique.containsKey(key)) continue;
                // The root can be a long-lived service loop.  Capacity is a
                // bound on one concrete helper activation, not on every use
                // of this accessor during the lifetime of the root thread.
                // Keep the trace call id only as discovery evidence; runtime
                // planning later selects the exact output-invocation corridor
                // and emits the replay-stable accessor occurrence.
                String stream = rootCallId + "\n" + callId
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
                port.put("portId", regionId + ".in."
                        + UUID.nameUUIDFromBytes((regionId + "\n" + key)
                        .getBytes(StandardCharsets.UTF_8)));
                port.put("cell", field);
                port.put("sourceKind", "ACCESSOR_RETURN");
                // An accessor port is emitted only after the exact primitive
                // field return reaches a semantic branch operand.  Declare
                // that leaf explicitly; DependencyRole intentionally rejects
                // missing roles instead of turning owners into symbolic data.
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
                port.put("dependencyCells",
                        Collections.singletonList(text(edge.get("fromCell"))));
                port.put("replayOccurrence", occurrence);
                port.put("helperActivationBoundedOccurrence", retained + 1);
                port.put("materialization", MaterializationSpec.accessorReturn(
                        declaration.type, field,
                        Collections.singletonList(declaration.name), caller,
                        unitIndex, declaredCallee, implementation).toMap());
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    private static Set<String> semanticAccessorEdges(
            List<Map<String, Object>> edges,
            List<Map<String, Object>> branchPolicies) {
        Map<String, List<Map<String, Object>>> incoming = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            String to = text(edge.get("toCell"));
            if (!to.isEmpty()) {
                incoming.computeIfAbsent(to,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }
        Deque<String> work = new ArrayDeque<>();
        for (Map<String, Object> branch : branchPolicies) {
            if ("EXPLORE".equals(text(branch.get("policy")))) {
                work.addAll(strings(branch.get("operandCells")));
            }
        }
        Set<String> visited = new LinkedHashSet<>();
        Set<String> selected = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            List<Map<String, Object>> predecessors = incoming.getOrDefault(
                    cell, Collections.emptyList());
            boolean accessorLeaf = false;
            for (Map<String, Object> edge : predecessors) {
                if (!"accessor_field_return".equals(text(edge.get("kind")))
                        || !Boolean.TRUE.equals(booleanValue(
                        edge.get("runtimeObserved")))) {
                    continue;
                }
                String id = text(edge.get("id"));
                if (!id.isEmpty()) selected.add(id);
                accessorLeaf = true;
            }
            // An observed structural getter is the exact symbolic boundary.
            // Following its receiver/container history would pull unrelated
            // writers and Map keys into the symbolic input set.
            if (accessorLeaf) continue;
            for (Map<String, Object> edge : predecessors) {
                if ("GUARD".equals(text(edge.get("transferKind")))) continue;
                String from = text(edge.get("fromCell"));
                if (!from.isEmpty()) work.addLast(from);
            }
        }
        return selected;
    }

    /**
     * A live-in used only to replay a bounded loop's continuation decision is
     * retained in the task, but must not become a symbolic search dimension.
     * Any flow to a non-loop branch wins and keeps the value symbolic.
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
            if (reachesAny(starts, loopOperands, outgoing)
                    && !reachesAny(starts, semanticOperands, outgoing)) {
                input.put("loopControlOnly", true);
                input.put("symbolicDemand", "CONCRETE_LOOP_CONTROL");
            }
        }
    }

    private static boolean reachesAny(
            Collection<String> starts, Set<String> targets,
            Map<String, List<String>> outgoing) {
        if (targets.isEmpty()) return false;
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>(starts);
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            if (targets.contains(cell)) return true;
            work.addAll(outgoing.getOrDefault(cell,
                    Collections.<String>emptyList()));
        }
        return false;
    }

    private static void addUniqueString(Map<String, Object> row,
                                        String field, String value) {
        if (value.isEmpty()) return;
        List<String> values = strings(row.get(field));
        if (!values.contains(value)) values.add(value);
        row.put(field, values);
    }

    /**
     * The methods whose guards decide the region's demanded behaviour: what the
     * admitting anchors reach, widened by the methods that define this
     * region's own outputs.  A region can carry more than one demand, and a
     * guard inside an output definition is about how that output comes about
     * whichever anchor admitted the region.  An unknown scope stays unknown.
     */
    private static Set<String> demandScope(
            Map<String, Object> skeleton,
            List<Map<String, Object>> outputs) {
        Set<String> result = new LinkedHashSet<>(
                strings(skeleton.get(DEMAND_SCOPE)));
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

    /**
     * Builds the region's branch policies.  {@code demandScope} names the
     * methods reached from the anchors that admitted the region; a guard
     * outside it decides something the execution context does for its own
     * reasons, not how this region's outputs come about, so it is replayed as
     * observed instead of explored.  An empty scope decides nothing and leaves
     * every guard explorable, and a guard that dominates the failure target is
     * never demoted -- that one is the goal.
     */
    private static List<Map<String, Object>> branches(
            List<Map<String, Object>> edges, Set<String> demandScope) {
        Map<String, List<Map<String, Object>>> bySite =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) {
                continue;
            }
            String site = first(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            if (!site.isEmpty()) {
                bySite.computeIfAbsent(site,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        BranchPolicyClassifier classifier =
                new BranchPolicyClassifier(edges);
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
                if ("exception_guard".equals(text(guard.get("kind")))
                        || text(guard.get("toCell")).contains(
                        "#exception:")) {
                    failureGuards.add(guard);
                }
            }
            Collection<Map<String, Object>> decisiveGuards =
                    failureGuards.isEmpty() ? guards : failureGuards;
            branch.put("failureTarget", !failureGuards.isEmpty());
            branch.put("operandCells", operandCells(decisiveGuards));
            Boolean required = consistentRequiredOutcome(decisiveGuards);
            branch.put("requiredOutcome", required);
            branch.put("guardedSiteOutcomes", guardedSiteOutcomes(guards));

            boolean conflicting = required == null
                    && hasConflictingRequiredOutcomes(decisiveGuards);
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
            branch.put("policy", conflicting || loopStructure
                    || carrierStructure || outsideDemand
                    ? "PATH_ASSUMPTION" : "EXPLORE");
            branch.put("policyReason", conflicting
                    ? "CONFLICTING_REQUIRED_OUTCOMES"
                    : loopStructure ? "BOUND_LOOP_CONTROL_GUARD"
                    : carrierStructure ? "STRUCTURE_CARRIER_GUARD"
                    : outsideDemand ? "OUTSIDE_DEMANDED_SCOPE"
                    : "FAILURE_DIRECTED_SEMANTIC_GUARD");
            result.add(branch);
        }
        return result;
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
     * proved is required to reach that site.  The analyzer already ran the
     * CFG reachability; keeping only the aggregate answer threw away which
     * site each answer was about, which is the part a consumer needs to ask
     * whether one exact position survives a flip.  A site two rows disagree
     * about, or that no row proves an outcome for, is left out: a reader may
     * conclude unreachability only from a proof.
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
        Boolean selected = null;
        for (Map<String, Object> guard : guards) {
            Boolean value = booleanValue(guard.get("requiredOutcome"));
            if (value == null) continue;
            if (selected != null && !selected.equals(value)) return null;
            selected = value;
        }
        return selected;
    }

    private static boolean hasConflictingRequiredOutcomes(
            Collection<Map<String, Object>> guards) {
        Set<Boolean> values = new LinkedHashSet<>();
        for (Map<String, Object> guard : guards) {
            Boolean value = booleanValue(guard.get("requiredOutcome"));
            if (value != null) values.add(value);
        }
        return values.size() > 1;
    }

    private static Boolean booleanValue(Object value) {
        if (value instanceof Boolean) return (Boolean) value;
        if ("true".equalsIgnoreCase(text(value))) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(text(value))) return Boolean.FALSE;
        return null;
    }

    /**
     * Classifies only positively proven structural traversal guards.  The
     * runtime-refined graph is already failure-directed, so every remaining
     * ambiguous guard stays explorable instead of being discarded by a name
     * heuristic.  A size/isEmpty/array-length value is structural only when
     * the same guard also has loop recurrence evidence; semantic cardinality
     * checks outside a loop remain explorable.
     */
    private static final class BranchPolicyClassifier {
        private final Map<String, List<Map<String, Object>>> incoming =
                new LinkedHashMap<>();

        private BranchPolicyClassifier(
                Collection<Map<String, Object>> edges) {
            for (Map<String, Object> edge : edges) {
                String target = text(edge.get("toCell"));
                if (!target.isEmpty()) {
                    incoming.computeIfAbsent(target,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
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
                if (nearestContainerRole(operand).equals(
                        DependencyRole.CONCRETE_STRUCTURE_CARRIER)) {
                    return true;
                }
            }
            return false;
        }

        private String nearestContainerRole(String start) {
            Set<String> visited = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(start);
            boolean carrier = false;
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!visited.add(cell)) continue;
                for (Map<String, Object> edge : incoming.getOrDefault(
                        cell, Collections.<Map<String, Object>>emptyList())) {
                    if ("container_receiver".equals(text(edge.get("kind")))) {
                        String role = DependencyRole.normalize(
                                edge.get("dependencyRole"));
                        if (DependencyRole.VALUE_FRONTIER.equals(role)) {
                            return DependencyRole.VALUE_FRONTIER;
                        }
                        carrier = true;
                        continue;
                    }
                    if (exactLocalPass(edge)) {
                        String predecessor = text(edge.get("fromCell"));
                        if (!predecessor.isEmpty()) work.addLast(predecessor);
                    }
                }
            }
            return carrier ? DependencyRole.CONCRETE_STRUCTURE_CARRIER
                    : DependencyRole.VALUE_FRONTIER;
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
            Set<String> visitedCells = new LinkedHashSet<>();
            Set<String> visitedEdges = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(start);
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!visitedCells.add(cell)) continue;
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
                            || text(edge.get("unit")).contains("lengthof")) {
                        return true;
                    }
                    String predecessor = text(edge.get("fromCell"));
                    if (!predecessor.isEmpty()) work.addLast(predecessor);
                }
            }
            return false;
        }
    }

    /** Projects a proved lookup-result role back to its exact heap port. */
    private static final class DependencyRoleClassifier {
        private final Map<String, List<Map<String, Object>>> outgoing =
                new LinkedHashMap<>();

        private DependencyRoleClassifier(
                Collection<Map<String, Object>> edges) {
            for (Map<String, Object> edge : edges) {
                String source = text(edge.get("fromCell"));
                if (!source.isEmpty()) {
                    outgoing.computeIfAbsent(source,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
        }

        private String heapReadRole(Map<String, Object> heapRead) {
            String start = text(heapRead.get("toCell"));
            if (start.isEmpty()) return DependencyRole.VALUE_FRONTIER;
            Set<String> visited = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(start);
            boolean carrier = false;
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!visited.add(cell)) continue;
                for (Map<String, Object> edge : outgoing.getOrDefault(
                        cell, Collections.<Map<String, Object>>emptyList())) {
                    if ("container_receiver".equals(text(edge.get("kind")))) {
                        String role = DependencyRole.normalize(
                                edge.get("dependencyRole"));
                        if (DependencyRole.VALUE_FRONTIER.equals(role)) {
                            return DependencyRole.VALUE_FRONTIER;
                        }
                        carrier = true;
                        continue;
                    }
                    if (exactLocalPass(edge)) {
                        String next = text(edge.get("toCell"));
                        if (!next.isEmpty()) work.addLast(next);
                    }
                }
            }
            return carrier ? DependencyRole.CONCRETE_STRUCTURE_CARRIER
                    : DependencyRole.VALUE_FRONTIER;
        }
    }

    private static boolean exactLocalPass(Map<String, Object> edge) {
        return "local_def_use".equals(text(edge.get("kind")))
                && ("VALUE_PASS".equals(text(edge.get("transferKind")))
                || !text(edge.get("valueFlowAuthority")).isEmpty());
    }

    private static List<Map<String, Object>> fieldFlows(
            List<Map<String, Object>> regions,
            Set<String> demandedFields,
            Map<String, Long> laneByInstance) throws IOException {
        // Reads state the demand, so they are collected first under the plain
        // resource default; the writes that could answer them are then kept
        // however late the trace recorded them.
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(reads, text(region.get("regionId")),
                    rows(region.get("symbolicInputs")), NO_ACCESS_DEMAND);
        }
        reads.removeIf(port -> !demandedFields.contains(
                port.leafDeclaration()));
        RuntimeAccessDemand demand = leafReceiverDemand(reads);
        List<BoundPort> writes = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(writes, text(region.get("regionId")),
                    rows(region.get("outputs")), demand);
        }
        writes.removeIf(port -> !demandedFields.contains(
                port.leafDeclaration()));
        List<Map<String, Object>> result = new ArrayList<>();
        for (BoundPort read : reads) {
            String readField = read.leafDeclaration();
            Map<String, BoundPort> selectedByPort =
                    new LinkedHashMap<>();
            for (BoundPort write : writes) {
                String writeField = write.leafDeclaration();
                if (sameInstance(write, read)
                        || !write.process.equals(read.process)
                        || write.receiver == 0
                        || write.receiver != read.receiver
                        || !writeField.equals(readField)
                        || sameLane(write, read, laneByInstance)
                        && write.seq >= read.seq
                        || DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(
                        read.dependencyRole)
                        && !"CONTAINER_MUTATION".equals(
                        write.bindingKind)) {
                    continue;
                }
                String writerPort = portDemandKey(write.region,
                        write.rootCallId, write.port);
                BoundPort selected = selectedByPort.get(writerPort);
                if (selected == null || write.seq > selected.seq) {
                    selectedByPort.put(writerPort, write);
                }
            }
            for (BoundPort write : selectedByPort.values()) {
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
                    edge.put("readerValueObjectId", read.valueObject);
                }
                result.add(edge);
            }
        }
        return result;
    }

    /**
     * Binds a still-unclosed demanded leaf to the region that actually wrote
     * it.
     *
     * <p>A leaf reached through a reference another region handed over is
     * demanded on the reading side, but the write that produced it is
     * activation-local to the producer: the object is built there and only
     * later escapes through a carrier field.  The failure-relevant field set
     * is stated over carriers, so the ordinary field flow never pairs the two
     * and the leaf is left to be replayed as a concrete observation.</p>
     *
     * <p>Runtime object identity settles it exactly.  A write to the same
     * object and the same declaration, in another activation, before this
     * read, is that read's producer.  Only an unambiguous writer counts: if
     * several distinct writer ports could have produced the value, the leaf
     * keeps its concrete under-approximation rather than inventing a
     * relation the trace does not prove.</p>
     */
    static List<Map<String, Object>> demandedLeafProducerFlows(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges,
            Map<String, Long> laneByInstance) throws IOException {
        Set<String> closedInputs = new LinkedHashSet<>();
        for (Map<String, Object> edge : regionEdges) {
            String toRegion = text(edge.get("toRegion"));
            long toRootCallId = longNumber(edge.get("toRootCallId"), -1L);
            String toPort = text(edge.get("toPort"));
            if (!toRegion.isEmpty() && toRootCallId >= 0L
                    && !toPort.isEmpty()) {
                closedInputs.add(portDemandKey(toRegion, toRootCallId,
                        toPort));
            }
        }
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            // Only a semantic scalar leaf is at stake here.  A carrier read
            // is answered by the ordinary field flow over demanded fields,
            // and widening this pass to carriers would invent relations the
            // failure never asked for.
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
                || closedInputs.contains(portDemandKey(read.region,
                read.rootCallId, read.port)));
        // The producing write is activation-local to a long-lived root, so
        // the trace may record it far past the resource default; demanding it
        // by receiver and leaf is what keeps it visible here.
        RuntimeAccessDemand demand = leafReceiverDemand(reads);
        List<BoundPort> writes = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(writes, text(region.get("regionId")),
                    rows(region.get("outputs")), demand);
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (BoundPort read : reads) {
            String readField = read.leafDeclaration();
            Map<String, BoundPort> byWriterPort = new LinkedHashMap<>();
            for (BoundPort write : writes) {
                if (sameInstance(write, read)
                        || !write.process.equals(read.process)
                        || write.receiver == 0
                        || write.receiver != read.receiver
                        || !write.leafDeclaration().equals(readField)
                        || sameLane(write, read, laneByInstance)
                        && write.seq >= read.seq) {
                    continue;
                }
                String writerPort = portDemandKey(write.region,
                        write.rootCallId, write.port);
                BoundPort selected = byWriterPort.get(writerPort);
                if (selected == null || write.seq > selected.seq) {
                    byWriterPort.put(writerPort, write);
                }
            }
            if (byWriterPort.size() != 1) continue;
            BoundPort write = byWriterPort.values().iterator().next();
            result.add(fieldFlowEdge(write, read, LEAF_PRODUCER_AUTHORITY,
                    "RF.LEAF."));
        }
        return result;
    }

    /**
     * Renders one write/read pair as a runtime field-flow edge.
     *
     * <p>Both field-flow rules publish the same edge schema; only the
     * authority that admitted the pair and the edge-id prefix differ.  A
     * field added to one rule and not the other would silently make the two
     * kinds of edge un-mergeable downstream.</p>
     */
    private static Map<String, Object> fieldFlowEdge(
            BoundPort write, BoundPort read, String authority,
            String edgeIdPrefix) {
        String alternative = write.region + "\n" + write.port
                + "\n" + write.rootCallId + "\n" + write.site
                + "\n" + write.occurrence + "\n" + read.region
                + "\n" + read.port + "\n" + read.rootCallId
                + "\n" + read.site + "\n" + read.occurrence;
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind", "RUNTIME_FIELD_FLOW");
        edge.put("transportKind", "HEAP");
        if (!authority.isEmpty()) {
            edge.put("authority", authority);
        }
        edge.put("edgeId", edgeIdPrefix + UUID.nameUUIDFromBytes(
                alternative.getBytes(StandardCharsets.UTF_8)));
        edge.put("causalAlternativeId", "FIELD_OCCURRENCE."
                + UUID.nameUUIDFromBytes(alternative.getBytes(
                StandardCharsets.UTF_8)));
        edge.put("fromRegion", write.region);
        edge.put("toRegion", read.region);
        edge.put("fromPort", write.port);
        edge.put("toPort", read.port);
        edge.put("fromRootCallId", write.rootCallId);
        edge.put("toRootCallId", read.rootCallId);
        edge.put("receiverObjectId", write.receiver);
        edge.put("valueObjectId", write.valueObject);
        edge.put("primitiveValue", write.primitiveValue);
        edge.put("writerEventSeq", write.seq);
        edge.put("readerEventSeq", read.seq);
        edge.put("writerStaticSiteId", write.site);
        edge.put("readerStaticSiteId", read.site);
        edge.put("writerOccurrence", write.occurrence);
        edge.put("readerOccurrence", read.occurrence);
        edge.put("bindingKind", write.bindingKind);
        edge.put("dependencyRole", read.dependencyRole);
        edge.put("fieldPathDeclarations", Collections.singletonList(
                write.leafDeclaration()));
        edge.put("writerFieldPathDeclarations", write.declarations);
        edge.put("readerFieldPathDeclarations", read.declarations);
        return edge;
    }

    /** Names the leaf-producer binding for downstream manifest tracing. */
    static final String LEAF_PRODUCER_AUTHORITY =
            "RUNTIME_FIELD_FLOW_LEAF_PRODUCER_V1";

    private static Set<String> failureRelevantFields(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> graph) {
        Set<String> targetRegions = new LinkedHashSet<>();
        Set<String> selectedRegions = new LinkedHashSet<>();
        for (Map<String, Object> region : regions) {
            selectedRegions.add(text(region.get("regionId")));
            if (text(region.get("selection")).startsWith("EXCEPTION")) {
                targetRegions.add(text(region.get("regionId")));
            }
        }
        Map<String, List<Map<String, Object>>> localIncoming =
                new LinkedHashMap<>();
        Map<String, List<ContextCell>> protocolIncoming =
                new LinkedHashMap<>();
        Deque<ContextCell> work = new ArrayDeque<>();
        for (Map<String, Object> edge : graph) {
            if ("PROTOCOL_TRANSFER".equals(
                    text(edge.get("transferKind")))) {
                // A protocol boundary may connect unrelated implementations
                // with coincidentally compatible types.  Cross it only for a
                // concrete runtime-correlated transfer, never from the static
                // mapping alone.
                for (Map<String, Object> binding
                        : rows(edge.get("runtimeProtocolBindings"))) {
                    String fromRegion = text(binding.get("fromRegionId"));
                    String toRegion = text(binding.get("toRegionId"));
                    String fromCell = text(binding.get("fromCell"));
                    String toCell = text(binding.get("toCell"));
                    if (!selectedRegions.contains(fromRegion)
                            || !selectedRegions.contains(toRegion)
                            || fromCell.isEmpty() || toCell.isEmpty()) {
                        continue;
                    }
                    protocolIncoming.computeIfAbsent(
                            contextKey(toRegion, toCell),
                            ignored -> new ArrayList<>()).add(
                            new ContextCell(fromRegion, fromCell));
                }
                continue;
            }
            String to = text(edge.get("toCell"));
            if (to.isEmpty()) continue;
            for (String region : strings(edge.get("regionIds"))) {
                if (!selectedRegions.contains(region)) continue;
                localIncoming.computeIfAbsent(contextKey(region, to),
                        ignored -> new ArrayList<>()).add(edge);
                if (targetRegions.contains(region)
                        && to.contains("#exception:")) {
                    work.add(new ContextCell(region, to));
                }
            }
        }
        Set<String> visited = new LinkedHashSet<>();
        Set<String> fields = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            ContextCell current = work.removeFirst();
            String key = contextKey(current.region, current.cell);
            if (!visited.add(key)) continue;
            for (Map<String, Object> edge : localIncoming.getOrDefault(key,
                    Collections.emptyList())) {
                String from = text(edge.get("fromCell"));
                if ("HEAP_READ".equals(text(edge.get("transferKind")))
                        && declaredField(from)) {
                    fields.add(from);
                }
                if (!from.isEmpty()) {
                    work.addLast(new ContextCell(current.region, from));
                }
            }
            for (ContextCell predecessor : protocolIncoming.getOrDefault(
                    key, Collections.<ContextCell>emptyList())) {
                work.addLast(predecessor);
            }
        }
        Set<String> dynamicallyDefined = new LinkedHashSet<>();
        for (Map<String, Object> edge : graph) {
            String field = text(edge.get("toCell"));
            if ("HEAP_WRITE".equals(text(edge.get("transferKind")))
                    && declaredField(field)) {
                // Constructor writes are ordinary definitions of the
                // constructed object's scalar leaves.  They become a region
                // boundary only when the failure-directed slice demands that
                // exact field and runtime evidence later reads the same
                // receiver in another activation.  Keeping them here does
                // not turn constructors into regions or expand arbitrary
                // objects; fieldFlows performs the exact receiver/leaf join.
                dynamicallyDefined.add(field);
            }
        }
        fields.retainAll(dynamicallyDefined);
        return fields;
    }

    private static String contextKey(String region, String cell) {
        return region + "\n" + cell;
    }

    private static boolean declaredField(String cell) {
        return cell.startsWith("<") && cell.endsWith(">")
                && cell.contains(":") && !cell.contains("(");
    }

    private static boolean sameInstance(BoundPort left, BoundPort right) {
        return left.region.equals(right.region)
                && left.rootCallId == right.rootCallId;
    }

    private static boolean sameLane(BoundPort left, BoundPort right,
                                    Map<String, Long> laneByInstance) {
        Long leftLane = laneByInstance.get(instanceKey(left.region,
                left.rootCallId));
        Long rightLane = laneByInstance.get(instanceKey(right.region,
                right.rootCallId));
        return leftLane != null && leftLane.equals(rightLane);
    }

    /**
     * Ports that read or write one declared field of one observed object.
     *
     * <p>An exact accessor return is such a read: it names the same declared
     * leaf and the same receiver object as a direct {@code getfield}.  Only
     * its transport label differs, so excluding it would leave a demanded
     * scalar leaf below a shared reference carrier without any producer even
     * though the exact writer is present in this trace.</p>
     */
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
                target.add(new BoundPort(region, text(port.get("portId")),
                        first(text(access.get("process")),
                                text(port.get("process"))),
                        longNumber(access.get("rootCallId"),
                                longNumber(port.get("rootCallId"), 0L)),
                        number(access.get("fieldReceiverObjectId"),
                                number(port.get("fieldReceiverObjectId"), 0)),
                        longNumber(access.get("eventSeq"),
                                longNumber(port.get("eventSeq"), 0L)),
                        strings(access.containsKey("fieldPathDeclarations")
                                ? access.get("fieldPathDeclarations")
                                : port.get("fieldPathDeclarations")),
                        number(access.get("valueObjectId"),
                                number(port.get("valueObjectId"), 0)),
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
     * Assigns a replay-stable occurrence within one activation and static
     * access site. Raw trace sequence numbers remain evidence only; the
     * bounded occurrence is the cross-run identity used by causal edges.
     */
    /**
     * Decides whether the closure names one recorded access exactly, so that
     * the per-site resource cap must not drop it.
     */
    private interface RuntimeAccessDemand {
        boolean required(Map<String, Object> port, Map<String, Object> access);
    }

    /** Nothing is demanded yet; only the resource default applies. */
    private static final RuntimeAccessDemand NO_ACCESS_DEMAND =
            (port, access) -> false;

    /**
     * Resource ceiling on the accesses one static site may contribute to one
     * port.  Unlike the loop bound this states no execution semantics: it
     * exists so that a long-lived thread root cannot materialise an unbounded
     * access array, and a port that cannot be served within it says so on the
     * port rather than silently keeping an arbitrary subset.
     */
    static final int MAX_RETAINED_SITE_ACCESSES = 64;

    /** Names a port whose demand exceeded the retained-access ceiling. */
    static final String DEMAND_RETENTION_REFUSAL = "demandRetentionRefusal";

    /**
     * Keeps a bounded, demand-aware view of one port's recorded accesses.
     *
     * <p>The occurrence index counts every activation-local execution of the
     * site, including the ones nested calls contribute; it is not a loop body
     * counter.  Capping it is therefore a resource default, never the loop
     * bound, and an access the closure names exactly is retained however late
     * in the activation the trace recorded it.</p>
     *
     * <p>A site whose demand exceeds the resource ceiling cannot be served
     * honestly: keeping some arbitrary 64 of its demanded accesses would be
     * the silent truncation this pass exists to remove.  Such a port keeps
     * only the plain resource default and carries the refusal by name, so the
     * leaves below it stay under-approximated and the reason travels with the
     * artifact instead of ending the whole refinement over one hot site.</p>
     */
    private static List<Map<String, Object>> boundedRuntimeAccesses(
            Map<String, Object> port, RuntimeAccessDemand demand)
            throws IOException {
        List<Map<String, Object>> accesses = new ArrayList<>(
                rows(port.get("runtimeAccesses")));
        accesses.sort(Comparator.comparingLong(access ->
                longNumber(access.get("eventSeq"), Long.MAX_VALUE)));
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
        if (!refusal.isEmpty()) {
            port.put(DEMAND_RETENTION_REFUSAL, refusal);
            return resourceDefault;
        }
        return bounded;
    }

    /**
     * Demands exactly the writes that could answer a collected read: the same
     * receiver object and the same declared leaf.  That is a necessary
     * condition of every pairing below, so a write this excludes could never
     * have been chosen, while a write it admits survives the resource cap.
     */
    private static RuntimeAccessDemand leafReceiverDemand(
            List<BoundPort> reads) {
        Set<String> demanded = new LinkedHashSet<>();
        for (BoundPort read : reads) {
            if (read.receiver != 0 && !read.leafDeclaration().isEmpty()) {
                demanded.add(read.receiver + "\n" + read.leafDeclaration());
            }
        }
        return (port, access) -> {
            int receiver = number(access.get("fieldReceiverObjectId"),
                    number(port.get("fieldReceiverObjectId"), 0));
            List<String> declarations = strings(
                    access.containsKey("fieldPathDeclarations")
                            ? access.get("fieldPathDeclarations")
                            : port.get("fieldPathDeclarations"));
            return receiver != 0 && !declarations.isEmpty()
                    && demanded.contains(receiver + "\n"
                    + declarations.get(declarations.size() - 1));
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

    private static void requireSkeleton(Map<String, Object> row, File source)
            throws IOException {
        if (number(row.get("schemaVersion"), -1) != 3
                || !"REGION_SKELETON".equals(text(row.get("kind")))) {
            throw new IOException("invalid selected skeleton: " + source);
        }
    }

    private static List<Map<String, Object>> read(File file)
            throws IOException {
        List<Map<String, Object>> result = new ArrayList<>();
        try (BufferedReader reader = reader(file)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (!line.trim().isEmpty()) {
                    Map<String, Object> row = GSON.fromJson(line, ROW);
                    if (row == null) {
                        throw new IOException("null row in " + file);
                    }
                    result.add(row);
                }
            }
        }
        return result;
    }

    private static BufferedReader reader(File file) throws IOException {
        InputStream input = Files.newInputStream(file.toPath());
        if (file.getName().endsWith(".gz")) {
            input = new GZIPInputStream(input);
        }
        return new BufferedReader(new InputStreamReader(input,
                StandardCharsets.UTF_8));
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Map<?, ?>) {
                    result.add((Map<String, Object>) item);
                }
            }
        }
        return result;
    }

    private static List<String> strings(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                String text = text(item);
                if (!text.isEmpty()) {
                    result.add(text);
                }
            }
        }
        return result;
    }

    private static int number(Object value, int fallback) {
        return value instanceof Number ? ((Number) value).intValue()
                : fallback;
    }

    private static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue()
                : fallback;
    }

    private static String first(String left, String right) {
        return left.isEmpty() ? right : left;
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    /**
     * Activation-local backward slices from demanded outputs (or a fatal
     * branch) to exact boundary input ports.  Static cells establish the
     * dependency relation; runtime root call ids select the concrete port
     * occurrence to which that relation applies.
     */
    private static final class RegionDemandIndex {
        private final Map<String, Map<String, Object>> inputs =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Object>> outputs =
                new LinkedHashMap<>();
        private final Map<String, List<String>> inputsByInstance =
                new LinkedHashMap<>();
        private final Map<String, List<String>> inputsByBoundary =
                new LinkedHashMap<>();
        private final Map<String, List<String>>
                boundedMutationFrontiersByOutput = new LinkedHashMap<>();
        private final Map<String, List<String>> localIncoming =
                new LinkedHashMap<>();
        /** Demand a rebuilt protocol carrier penetrates to. */
        private final Map<String, String> carrierDemands =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                explicitFatalSeedsBySite = new LinkedHashMap<>();
        private final Map<String, List<String>> fatalSeeds =
                new LinkedHashMap<>();
        /**
         * inputsForOutput is a pure function of the frozen index; the union
         * walk and every per-target closure walk repeat the same demands, so
         * each backward walk is computed once.  Cached lists are read-only
         * by contract of the callers.
         */
        private final Map<String, List<String>> inputsForOutputCache =
                new LinkedHashMap<>();
        private final Map<Map<String, Object>, List<String>>
                targetInputsCache = new java.util.IdentityHashMap<>();

        private RegionDemandIndex(List<Map<String, Object>> regions,
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
                    if (Boolean.TRUE.equals(booleanValue(
                            branch.get("failureTarget")))) {
                        String site = text(branch.get("siteId"));
                        if (!site.isEmpty()) {
                            Map<String, List<String>> bySite =
                                    explicitFatalSeedsBySite.computeIfAbsent(
                                            regionId,
                                            ignored -> new LinkedHashMap<>());
                            List<String> seeds = bySite.computeIfAbsent(site,
                                    ignored -> new ArrayList<>());
                            for (String operand : strings(
                                    branch.get("operandCells"))) {
                                if (!seeds.contains(operand)) {
                                    seeds.add(operand);
                                }
                            }
                        }
                    }
                }
            }
            for (Map<String, Object> edge : graph) {
                if ("PROTOCOL_TRANSFER".equals(
                        text(edge.get("transferKind")))) {
                    continue;
                }
                String from = text(edge.get("fromCell"));
                String to = text(edge.get("toCell"));
                if (from.isEmpty() || to.isEmpty()) continue;
                for (String regionId : strings(edge.get("regionIds"))) {
                    if (!selectedRegions.contains(regionId)) continue;
                    addUnique(localIncoming, contextKey(regionId, to),
                            from);
                    // A generic exception cell is only a fallback for a
                    // region without an explicit failureTarget policy.  Once
                    // a target predicate is known, adding every exception in
                    // the template recreates the whole-region union that the
                    // runtime fatal-site evidence is meant to eliminate.
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
            long rootCallId = portRootCallId(port, output);
            String portId = text(port.get("portId"));
            if (rootCallId < 0L || portId.isEmpty()) return;
            String demand = portDemandKey(regionId, rootCallId, portId);
            (output ? outputs : inputs).put(demand, port);
            String carrier = ProtocolCarrierReconstruction.responsePort(port);
            if (!carrier.isEmpty()) {
                carrierDemands.put(demand, portDemandKey(regionId,
                        rootCallId, carrier));
            }
            if (output) return;
            addUnique(inputsByInstance,
                    instanceKey(regionId, rootCallId), demand);
            for (String cell : boundaryCells(port)) {
                addUnique(inputsByBoundary,
                        instanceCellKey(regionId, rootCallId, cell),
                        demand);
            }
            for (String outputCell : strings(
                    port.get("boundedMutationOutputCells"))) {
                addUnique(boundedMutationFrontiersByOutput,
                        instanceCellKey(regionId, rootCallId, outputCell),
                        demand);
            }
        }

        private boolean hasInput(String regionId, long rootCallId,
                                 String portId) {
            return inputs.containsKey(portDemandKey(regionId, rootCallId,
                    portId));
        }

        private boolean hasOutput(String regionId, long rootCallId,
                                  String portId) {
            return outputs.containsKey(portDemandKey(regionId, rootCallId,
                    portId));
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

        private List<String> computeTargetInputs(
                Map<String, Object> instance) throws IOException {
            String regionId = text(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            Map<String, List<String>> explicit =
                    explicitFatalSeedsBySite.get(regionId);
            if (explicit != null && !explicit.isEmpty()) {
                Set<String> observedSites = new LinkedHashSet<>();
                Map<String, List<Map<String, Object>>> evidenceBySite =
                        new LinkedHashMap<>();
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
                    List<String> siteSeeds = explicit.get(site);
                    if (siteSeeds != null) {
                        observedSites.add(site);
                        evidenceBySite.computeIfAbsent(site,
                                ignored -> new ArrayList<>()).add(evidence);
                    }
                }
                if (evidenceBySite.isEmpty()) {
                    throw new IOException("exception-context activation did "
                            + "not observe its explicit fatal target branch: "
                            + instanceKey(regionId, rootCallId));
                }
                instance.put("observedFatalTargetSites",
                        new ArrayList<>(observedSites));

                Set<String> retained = new LinkedHashSet<>();
                List<Map<String, Object>> contexts = new ArrayList<>();
                for (Map.Entry<String, List<Map<String, Object>>> entry
                        : evidenceBySite.entrySet()) {
                    List<Map<String, Object>> occurrences = entry.getValue();
                    occurrences.sort(Comparator.comparingLong(value ->
                            longNumber(value.get("eventSeq"),
                                    Long.MAX_VALUE)));
                    int selectedIndex = selectedFatalOccurrence(occurrences);
                    Map<String, Object> selected = occurrences.get(
                            selectedIndex);
                    long cutoff = longNumber(selected.get("eventSeq"), -1L);
                    if (cutoff < 0L) {
                        throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: "
                                + "observed fatal target has no eventSeq: "
                                + instanceKey(regionId, rootCallId) + " "
                                + entry.getKey());
                    }
                    List<String> inputs = retainFatalPrefixInputs(instance,
                            backwardInputs(regionId, rootCallId,
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
                // Preserve the compact legacy field only when it is
                // unambiguous.  Multi-site activations are projected by site
                // later in Scheduler and must never share one max cutoff.
                if (contexts.size() == 1) {
                    instance.put("fatalPrefixEventSeq",
                            contexts.get(0).get("eventSeq"));
                } else {
                    instance.remove("fatalPrefixEventSeq");
                }
                return new ArrayList<>(retained);
            }
            List<String> seeds = fatalSeeds.getOrDefault(regionId,
                    Collections.<String>emptyList());
            if (seeds.isEmpty()) {
                // Small fixtures and locally terminal failures may not have
                // an explicit exception edge.  In that case the target is
                // still the analysis seed, so preserve its observed inputs.
                return new ArrayList<>(inputsByInstance.getOrDefault(
                        instanceKey(regionId, rootCallId),
                        Collections.<String>emptyList()));
            }
            return backwardInputs(regionId, rootCallId, seeds);
        }

        /** Same occurrence rule as Scheduler.TargetBranch.select. */
        private int selectedFatalOccurrence(
                List<Map<String, Object>> occurrences) {
            int fallback = 0;
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
            return fallback;
        }

        /**
         * A static backward slice says which boundary ports may feed the
         * fatal predicate; the exact trace says which of those ports existed
         * when that predicate was reached.  A value observed only after the
         * fatal branch cannot be one of its inputs and is therefore removed.
         * Missing ordering evidence is different: admitting that port would
         * create a free symbolic leaf, so it is a named, fail-closed gap.
         */
        private List<String> retainFatalPrefixInputs(
                Map<String, Object> instance, List<String> candidates,
                long fatalEventSeq) throws IOException {
            List<String> retained = new ArrayList<>();
            List<String> rejectedAfterFatal = new ArrayList<>();
            List<String> missingEvidence = new ArrayList<>();
            for (String demand : candidates) {
                Map<String, Object> port = inputs.get(demand);
                if (port == null) continue;
                // Structural owners remain concrete replay support.  They do
                // not become causal/symbolic leaves merely because their
                // construction has no independently timestamped value.
                if (!DependencyRole.valueFrontier(
                        port.get("dependencyRole"))) {
                    retained.add(demand);
                    continue;
                }
                FatalPrefixEvidence evidence = fatalPrefixEvidence(
                        port, fatalEventSeq);
                if (evidence.atOrBefore) {
                    retained.add(demand);
                } else if (evidence.observedAfter) {
                    rejectedAfterFatal.add(text(port.get("portId")));
                } else {
                    missingEvidence.add(text(port.get("portId")));
                }
            }
            if (!rejectedAfterFatal.isEmpty()) {
                instance.put("postFatalInputPorts",
                        rejectedAfterFatal);
            }
            if (!missingEvidence.isEmpty()) {
                throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: target "
                        + instanceKey(text(instance.get("regionId")),
                        longNumber(instance.get("rootCallId"), -1L))
                        + " has demanded ports without exact runtime order: "
                        + missingEvidence);
            }
            return retained;
        }

        private FatalPrefixEvidence fatalPrefixEvidence(
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
                if (!prefix.isEmpty()) {
                    return FatalPrefixEvidence.before();
                }
                if (observed && after) {
                    return FatalPrefixEvidence.after();
                }
                return FatalPrefixEvidence.missing();
            }

            if ("PROTOCOL_INPUT".equals(text(port.get("sourceKind")))) {
                if (!"TRUSTED_CONFIGURED_RPC_MAPPING_V1".equals(
                        text(port.get("authority")))) {
                    return FatalPrefixEvidence.missing();
                }
                String direction = text(port.get("protocolDirection"));
                long event = "RESPONSE".equals(direction)
                        ? longNumber(port.get("callerResultEventSeq"), -1L)
                        : "REQUEST".equals(direction)
                        ? longNumber(port.get("receiveEventSeq"), -1L)
                        : -1L;
                if (event < 0L) return FatalPrefixEvidence.missing();
                return event <= fatalEventSeq
                        ? FatalPrefixEvidence.before()
                        : FatalPrefixEvidence.after();
            }

            // Accessor-return ports are emitted only from an exact runtime
            // binding and carry that occurrence directly on the port.
            if ("ACCESSOR_RETURN".equals(text(port.get("sourceKind")))) {
                long event = longNumber(port.get("eventSeq"), -1L);
                if (event < 0L) return FatalPrefixEvidence.missing();
                return event <= fatalEventSeq
                        ? FatalPrefixEvidence.before()
                        : FatalPrefixEvidence.after();
            }
            return FatalPrefixEvidence.missing();
        }

        private List<String> inputsForOutput(String regionId,
                                             long rootCallId,
                                             String portId) {
            String demand = portDemandKey(regionId, rootCallId, portId);
            List<String> cached = inputsForOutputCache.get(demand);
            if (cached != null) {
                return cached;
            }
            List<String> computed = computeInputsForOutput(regionId,
                    rootCallId, portId);
            inputsForOutputCache.put(demand, computed);
            return computed;
        }

        private List<String> computeInputsForOutput(String regionId,
                                             long rootCallId,
                                             String portId) {
            String demand = portDemandKey(regionId, rootCallId, portId);
            Map<String, Object> output = outputs.get(demand);
            if (output == null) return Collections.emptyList();
            String carrier = carrierDemands.get(demand);
            if (carrier != null) {
                // The write only rebuilt the transferred carrier, so its
                // decode-path operands are not the producer of this value.
                return Collections.singletonList(requireCarrier(carrier));
            }
            Set<String> result = new LinkedHashSet<>(backwardInputs(
                    regionId, rootCallId, boundaryCells(output)));
            if ("CONTAINER_MUTATION".equals(
                    text(output.get("bindingKind")))) {
                for (String preStatePort : strings(
                        output.get("boundedContainerPreStatePorts"))) {
                    String preState = portDemandKey(regionId, rootCallId,
                            preStatePort);
                    if (inputs.containsKey(preState)) result.add(preState);
                }
                for (String cell : mutationOutputCells(output)) {
                    result.addAll(boundedMutationFrontiersByOutput
                            .getOrDefault(instanceCellKey(regionId,
                                            rootCallId, cell),
                                    Collections.<String>emptyList()));
                }
            }
            return new ArrayList<>(result);
        }

        private List<String> backwardInputs(String regionId,
                                            long rootCallId,
                                            Collection<String> seeds) {
            Set<String> result = new LinkedHashSet<>();
            Set<String> visited = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>(seeds);
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (cell.isEmpty() || !visited.add(cell)) continue;
                List<String> boundary = inputsByBoundary.getOrDefault(
                        instanceCellKey(regionId, rootCallId, cell),
                        Collections.<String>emptyList());
                if (!boundary.isEmpty()) {
                    result.addAll(boundary);
                    // A region input is the boundary.  Following another
                    // write to the same declared field would re-introduce a
                    // cross-activation alias through the local slice.
                    for (String input : boundary) {
                        String carrier = carrierDemands.get(input);
                        if (carrier != null) result.add(requireCarrier(carrier));
                    }
                    continue;
                }
                work.addAll(localIncoming.getOrDefault(
                        contextKey(regionId, cell),
                        Collections.<String>emptyList()));
            }
            return new ArrayList<>(result);
        }

        /** Fails closed when a declared correspondence has no exact port. */
        private String requireCarrier(String demand) {
            if (!inputs.containsKey(demand)) {
                throw new IllegalStateException("protocol carrier "
                        + "reconstruction has no configured response port: "
                        + demand);
            }
            return demand;
        }

        private static List<String> boundaryCells(
                Map<String, Object> port) {
            List<String> result = strings(port.get("dependencyCells"));
            if (result.isEmpty()) {
                String cell = text(port.get("cell"));
                if (!cell.isEmpty()) result.add(cell);
            }
            return result;
        }

        private static String instanceCellKey(String regionId,
                                              long rootCallId,
                                              String cell) {
            return instanceKey(regionId, rootCallId) + "\nCELL\n" + cell;
        }

        private static void addUnique(Map<String, List<String>> target,
                                      String key, String value) {
            if (value.isEmpty()) return;
            List<String> values = target.computeIfAbsent(key,
                    ignored -> new ArrayList<>());
            if (!values.contains(value)) values.add(value);
        }

        private static final class FatalPrefixEvidence {
            private final boolean atOrBefore;
            private final boolean observedAfter;

            private FatalPrefixEvidence(boolean atOrBefore,
                                        boolean observedAfter) {
                this.atOrBefore = atOrBefore;
                this.observedAfter = observedAfter;
            }

            private static FatalPrefixEvidence before() {
                return new FatalPrefixEvidence(true, false);
            }

            private static FatalPrefixEvidence after() {
                return new FatalPrefixEvidence(false, true);
            }

            private static FatalPrefixEvidence missing() {
                return new FatalPrefixEvidence(false, false);
            }
        }
    }

    private static final class ContextCell {
        private final String region;
        private final String cell;

        private ContextCell(String region, String cell) {
            this.region = region;
            this.cell = cell;
        }
    }

    private static final class RpcDescendantProjectionIndex {
        private final Map<String, Map<String, Object>> regions =
                new LinkedHashMap<>();
        private final Map<String, List<RpcDescendantCandidate>> candidates =
                new LinkedHashMap<>();
        private final Map<String, List<ExactPort>> ports =
                new LinkedHashMap<>();
        private final Map<String, List<RpcDescendantCandidate>> byReceiver =
                new LinkedHashMap<>();
        private final Map<String, List<Map<String, Object>>> membersByValue =
                new LinkedHashMap<>();
        private final StaticValueFlowIndex valueFlow;

        private RpcDescendantProjectionIndex(
                List<Map<String, Object>> regionRows,
                List<Map<String, Object>> graph) {
            for (Map<String, Object> region : regionRows) {
                String regionId = text(region.get("regionId"));
                if (!regionId.isEmpty()) regions.put(regionId, region);
                indexPorts(regionId, rows(region.get("symbolicInputs")),
                        false);
                indexPorts(regionId, rows(region.get("outputs")), true);
            }
            for (Map<String, Object> edge : graph) {
                for (Map<String, Object> binding
                        : rows(edge.get("runtimeFieldBindings"))) {
                    indexContainerMember(binding);
                }
                String transfer = text(edge.get("transferKind"));
                if (!"HEAP_READ".equals(transfer)
                        && !"HEAP_WRITE".equals(transfer)) {
                    continue;
                }
                for (Map<String, Object> binding
                        : rows(edge.get("runtimeFieldBindings"))) {
                    indexCandidate(edge, binding, transfer, false);
                }
                if ("HEAP_READ".equals(transfer)) {
                    for (Map<String, Object> binding
                            : rows(edge.get("runtimeAccessorBindings"))) {
                        indexCandidate(edge, binding, transfer, true);
                    }
                }
            }
            valueFlow = new StaticValueFlowIndex(graph);
        }

        private void indexContainerMember(Map<String, Object> binding) {
            String token = text(binding.get("containerMemberToken"));
            String authority = text(binding.get(
                    "containerMemberIdentityAuthority"));
            String process = text(binding.get("process"));
            int value = number(binding.get("containerValueObjectId"), 0);
            if (token.isEmpty() || process.isEmpty() || value == 0
                    || !"EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1".equals(
                    authority)) {
                return;
            }
            membersByValue.computeIfAbsent(process + "\n" + value,
                    ignored -> new ArrayList<>()).add(binding);
        }

        private Map<String, Object> exactContainerMember(
                RpcDescendantCandidate candidate) {
            String process = text(candidate.binding.get("process"));
            if (process.isEmpty() || candidate.receiverObjectId == 0) {
                return null;
            }
            Map<String, Map<String, Object>> byToken =
                    new LinkedHashMap<>();
            for (Map<String, Object> member : membersByValue.getOrDefault(
                    process + "\n" + candidate.receiverObjectId,
                    Collections.<Map<String, Object>>emptyList())) {
                byToken.put(text(member.get("containerMemberToken")), member);
            }
            return byToken.size() == 1
                    ? byToken.values().iterator().next() : null;
        }

        private void indexCandidate(Map<String, Object> edge,
                                    Map<String, Object> binding,
                                    String transfer, boolean accessor) {
            List<String> declarations = strings(
                    binding.get("fieldPathDeclarations"));
            String declaration = declarations.isEmpty()
                    ? first(text(binding.get("declaredFieldSignature")),
                    first(text(edge.get("declaredFieldSignature")),
                            text(edge.get("HEAP_READ".equals(transfer)
                                    ? "fromCell" : "toCell"))))
                    : declarations.get(declarations.size() - 1);
            DeclaredFieldCell field = DeclaredFieldCell.parse(declaration);
            String region = text(binding.get("regionId"));
            long rootCallId = longNumber(binding.get("rootCallId"), -1L);
            long eventSeq = longNumber(binding.get("eventSeq"), -1L);
            if (field == null || region.isEmpty() || rootCallId < 0L
                    || eventSeq < 0L
                    || rpcProjectionKind(field.type).isEmpty()
                    && !rpcCarrierReferenceType(field.type)) {
                return;
            }
            int receiver = number(binding.get(accessor ? "receiverObjectId"
                    : "fieldReceiverObjectId"), 0);
            RpcDescendantCandidate candidate = new RpcDescendantCandidate(
                    region, rootCallId, transfer, declaration, field.type,
                    staticAccessSiteId(edge), eventSeq, receiver,
                    number(binding.get("valueObjectId"), 0),
                    observedContainerWidth(edge, binding), edge, binding,
                    accessor);
            String key = endpointKey(region, rootCallId, transfer);
            candidates.computeIfAbsent(key,
                    ignored -> new ArrayList<>()).add(candidate);
            if (receiver != 0) {
                byReceiver.computeIfAbsent(transfer + "\n" + receiver,
                        ignored -> new ArrayList<>()).add(candidate);
            }
        }

        /** Recorded accesses whose receiver is one concrete object. */
        private List<RpcDescendantCandidate> onReceiver(String transfer,
                                                        int receiver) {
            return byReceiver.getOrDefault(transfer + "\n" + receiver,
                    Collections.<RpcDescendantCandidate>emptyList());
        }

        private void indexPorts(String region,
                                List<Map<String, Object>> rows,
                                boolean output) {
            for (Map<String, Object> port : rows) {
                long rootCallId = portRootCallId(port, output);
                if (rootCallId < 0L) continue;
                List<Map<String, Object>> accesses = rows(
                        port.get("runtimeAccesses"));
                if (accesses.isEmpty()) {
                    // A port without a separate access row records its own
                    // exact access inline.  Snapshot it instead of aliasing
                    // the port: a projection publishes the selected access
                    // back under the port's own "runtimeAccesses", and an
                    // alias would make the port contain itself.
                    accesses = Collections.<Map<String, Object>>singletonList(
                            new LinkedHashMap<String, Object>(port));
                }
                for (Map<String, Object> access : accesses) {
                    List<String> declarations = strings(
                            access.containsKey("fieldPathDeclarations")
                                    ? access.get("fieldPathDeclarations")
                                    : port.get("fieldPathDeclarations"));
                    if (declarations.isEmpty()) continue;
                    String declaration = declarations.get(
                            declarations.size() - 1);
                    long eventSeq = longNumber(access.get("eventSeq"),
                            longNumber(port.get("eventSeq"), -1L));
                    if (eventSeq < 0L) continue;
                    String key = exactPortKey(region, rootCallId, output,
                            declaration, eventSeq);
                    ports.computeIfAbsent(key,
                            ignored -> new ArrayList<>()).add(
                            new ExactPort(port, access));
                }
            }
        }

        private Map<String, Object> region(String regionId) {
            return regions.get(regionId);
        }

        private List<RpcDescendantCandidate> candidates(
                String region, long rootCallId, String transfer) {
            return candidates.getOrDefault(endpointKey(region, rootCallId,
                    transfer), Collections.<RpcDescendantCandidate>emptyList());
        }

        private ExactPort exactPort(RpcDescendantCandidate candidate,
                                    boolean output) {
            List<ExactPort> matches = ports.getOrDefault(exactPortKey(
                    candidate.region, candidate.rootCallId, output,
                    candidate.declaration, candidate.eventSeq),
                    Collections.<ExactPort>emptyList());
            return matches.size() == 1 ? matches.get(0) : null;
        }

        private ExactPort exactInputPort(
                RpcDescendantCandidate candidate) {
            ExactPort exact = exactPort(candidate, false);
            if (exact != null || !candidate.accessor) return exact;
            Map<String, Object> region = region(candidate.region);
            if (region == null) return null;
            DeclaredFieldCell field = DeclaredFieldCell.parse(
                    candidate.declaration);
            String caller = text(candidate.edge.get("method"));
            int unitIndex = number(candidate.edge.get("unitIndex"), -1);
            String declaredCallee = text(candidate.edge.get("invoke"));
            String implementation = text(candidate.edge.get(
                    "accessorImplementationMethod"));
            if (field == null || caller.isEmpty() || unitIndex < 0
                    || declaredCallee.isEmpty()
                    || implementation.isEmpty()) {
                return null;
            }

            Map<String, Object> access = new LinkedHashMap<>(
                    candidate.binding);
            access.put("fieldReceiverObjectId",
                    candidate.receiverObjectId);
            access.put("fieldPathDeclarations",
                    Collections.singletonList(candidate.declaration));
            access.put("staticAccessSiteId", candidate.staticSite);

            String identity = candidate.region + "\n"
                    + candidate.rootCallId + "\n"
                    + text(candidate.edge.get("id")) + "\n"
                    + candidate.eventSeq + "\n" + candidate.declaration;
            Map<String, Object> port = new LinkedHashMap<>(
                    candidate.binding);
            port.put("portId", candidate.region + ".in."
                    + UUID.nameUUIDFromBytes(identity.getBytes(
                    StandardCharsets.UTF_8)));
            port.put("cell", candidate.declaration);
            port.put("sourceKind", "ACCESSOR_RETURN");
            port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
            port.put("transportKind", "ACTIVATION_LOCAL");
            port.put("rootKind", "OBSERVED_FIELD_RECEIVER");
            port.put("rootObjectId", candidate.receiverObjectId);
            port.put("fieldReceiverObjectId",
                    candidate.receiverObjectId);
            port.put("fieldPath", Collections.singletonList(field.name));
            port.put("fieldPathDeclarations",
                    Collections.singletonList(candidate.declaration));
            port.put("javaType", candidate.type);
            port.put("dependencyCells", Collections.singletonList(
                    text(candidate.edge.get("fromCell"))));
            int occurrence = number(candidate.binding.get(
                    "accessorOccurrence"), -1);
            if (occurrence > 0) {
                port.put("replayOccurrence", occurrence);
                port.put("helperActivationBoundedOccurrence", occurrence);
            }
            port.put("materialization", MaterializationSpec.accessorReturn(
                    candidate.type, candidate.declaration,
                    Collections.singletonList(field.name), caller, unitIndex,
                    declaredCallee, implementation).toMap());
            port.put("runtimeAccesses", Collections.singletonList(access));

            List<Map<String, Object>> inputs = rows(
                    region.get("symbolicInputs"));
            addPortIfAbsent(inputs, port);
            region.put("symbolicInputs", inputs);
            ExactPort created = new ExactPort(port, access);
            ports.computeIfAbsent(exactPortKey(candidate.region,
                    candidate.rootCallId, false, candidate.declaration,
                    candidate.eventSeq), ignored -> new ArrayList<>())
                    .add(created);
            return created;
        }

        private static String endpointKey(String region, long rootCallId,
                                          String transfer) {
            return region + "\n" + rootCallId + "\n" + transfer;
        }

        private static String exactPortKey(String region, long rootCallId,
                                           boolean output,
                                           String declaration,
                                           long eventSeq) {
            return region + "\n" + rootCallId + "\n"
                    + (output ? "OUT" : "IN") + "\n" + declaration
                    + "\n" + eventSeq;
        }
    }

    private static final class RpcDescendantCandidate {
        private final String region;
        private final long rootCallId;
        private final String transfer;
        private final String declaration;
        private final String type;
        private final String staticSite;
        private final long eventSeq;
        private final int receiverObjectId;
        private final int valueObjectId;
        private final int observedWidth;
        private final Map<String, Object> edge;
        private final Map<String, Object> binding;
        private final boolean accessor;

        private RpcDescendantCandidate(
                String region, long rootCallId, String transfer,
                String declaration, String type, String staticSite,
                long eventSeq, int receiverObjectId, int valueObjectId,
                int observedWidth,
                Map<String, Object> edge, Map<String, Object> binding,
                boolean accessor) {
            this.region = region;
            this.rootCallId = rootCallId;
            this.transfer = transfer;
            this.declaration = declaration;
            this.type = type;
            this.staticSite = staticSite;
            this.eventSeq = eventSeq;
            this.receiverObjectId = receiverObjectId;
            this.valueObjectId = valueObjectId;
            this.observedWidth = observedWidth;
            this.edge = edge;
            this.binding = binding;
            this.accessor = accessor;
        }

        private String valueCell() {
            return text(edge.get("fromCell"));
        }

        private String resultCell() {
            return text(edge.get("toCell"));
        }
    }

    private static final class ExactPort {
        private final Map<String, Object> port;
        private final Map<String, Object> access;

        private ExactPort(Map<String, Object> port,
                          Map<String, Object> access) {
            this.port = port;
            this.access = access;
        }
    }

    private static final class StaticValueFlowIndex {
        private final Map<String, List<String>> outgoing =
                new LinkedHashMap<>();
        private final Map<String, Boolean> reachability =
                new LinkedHashMap<>();

        private StaticValueFlowIndex(List<Map<String, Object>> graph) {
            for (Map<String, Object> edge : graph) {
                String transfer = text(edge.get("transferKind"));
                if ("GUARD".equals(transfer)
                        || "PROTOCOL_TRANSFER".equals(transfer)
                        || "EXCEPTION".equals(transfer)
                        || "UNKNOWN".equals(transfer)) {
                    continue;
                }
                String from = text(edge.get("fromCell"));
                String to = text(edge.get("toCell"));
                if (from.isEmpty() || to.isEmpty()) continue;
                for (String region : strings(edge.get("regionIds"))) {
                    String key = contextKey(region, from);
                    List<String> values = outgoing.computeIfAbsent(key,
                            ignored -> new ArrayList<>());
                    if (!values.contains(to)) values.add(to);
                }
            }
        }

        private boolean reaches(String region, String from, String to) {
            if (region.isEmpty() || from.isEmpty() || to.isEmpty()) {
                return false;
            }
            if (from.equals(to)) return true;
            String cacheKey = region + "\n" + from + "\n" + to;
            Boolean cached = reachability.get(cacheKey);
            if (cached != null) return cached;
            Set<String> visited = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(from);
            while (!work.isEmpty()) {
                String current = work.removeFirst();
                if (!visited.add(current)) continue;
                for (String next : outgoing.getOrDefault(
                        contextKey(region, current),
                        Collections.<String>emptyList())) {
                    if (to.equals(next)) {
                        reachability.put(cacheKey, true);
                        return true;
                    }
                    if (!visited.contains(next)) work.addLast(next);
                }
            }
            reachability.put(cacheKey, false);
            return false;
        }
    }

    private static final class BoundPort {
        private final String region;
        private final String port;
        private final String process;
        private final long rootCallId;
        private final int receiver;
        private final long seq;
        private final List<String> declarations;
        private final int valueObject;
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

        private BoundPort(String region, String port, String process,
                          long rootCallId, int receiver, long seq,
                          List<String> declarations, int valueObject,
                          String primitiveValue, String bindingKind,
                          long writerFieldReadSeq, long mutatorEnterSeq,
                          long mutationCompletionSeq,
                          long mutationInvocationId,
                          String mutatorDeclaredCallee,
                          String dependencyRole, String site,
                          int occurrence) {
            this.region = region;
            this.port = port;
            this.process = process;
            this.rootCallId = rootCallId;
            this.receiver = receiver;
            this.seq = seq;
            this.declarations = declarations;
            this.valueObject = valueObject;
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

    private static final class DeclaredFieldCell {
        private static final Set<String> PRIMITIVES = new LinkedHashSet<>(
                java.util.Arrays.asList("boolean", "byte", "short", "char",
                        "int", "long", "float", "double"));
        private final String type;
        private final String name;

        private DeclaredFieldCell(String type, String name) {
            this.type = type;
            this.name = name;
        }

        private boolean primitive() {
            return PRIMITIVES.contains(type);
        }

        private static DeclaredFieldCell parse(String cell) {
            String value = text(cell).trim();
            if (!declaredField(value)) return null;
            int colon = value.indexOf(':');
            int separator = value.lastIndexOf(' ', value.length() - 2);
            if (colon < 1 || separator <= colon + 1) return null;
            String type = value.substring(colon + 1, separator).trim();
            String name = value.substring(separator + 1,
                    value.length() - 1).trim();
            return type.isEmpty() || name.isEmpty() ? null
                    : new DeclaredFieldCell(type, name);
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

    private static final class RuntimeClosure {
        private final Map<String, Map<String, Object>> instances;
        private final Set<String> reached;
        private final int targetCount;
        private final int instanceCount;
        private final Set<String> retainedEdges;
        private final Set<String> demandedInputs;
        private final Set<String> demandedOutputs;
        private final List<Map<String, Object>> targetClosures;

        private RuntimeClosure(
                Map<String, Map<String, Object>> instances,
                Set<String> reached, int targetCount,
                Set<String> retainedEdges,
                Set<String> demandedInputs,
                Set<String> demandedOutputs,
                List<Map<String, Object>> targetClosures) {
            this.instances = instances;
            this.reached = reached;
            this.targetCount = targetCount;
            this.instanceCount = instances.size();
            this.retainedEdges = retainedEdges;
            this.demandedInputs = demandedInputs;
            this.demandedOutputs = demandedOutputs;
            this.targetClosures = targetClosures;
        }
    }

    public static final class Result {
        public final int candidateInstanceCount;
        public final int retainedInstanceCount;
        public final int targetInstanceCount;
        public final int retainedRegionCount;
        public final int retainedEdgeCount;
        public final String regionCatalogScope;
        public final boolean directlySchedulable;
        public final List<Map<String, Object>> targetClosures;
        /** Finalized region rows exactly as written to the artifact. */
        public final List<Map<String, Object>> regions;
        /** Canonicalized region edges exactly as written to the artifact. */
        public final List<Map<String, Object>> regionEdges;

        private Result(int candidateInstanceCount,
                       int retainedInstanceCount,
                       int targetInstanceCount,
                       List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges,
                       List<Map<String, Object>> targetClosures) {
            this.candidateInstanceCount = candidateInstanceCount;
            this.retainedInstanceCount = retainedInstanceCount;
            this.targetInstanceCount = targetInstanceCount;
            this.retainedRegionCount = regions.size();
            this.retainedEdgeCount = regionEdges.size();
            this.regionCatalogScope = targetInstanceCount == 1
                    ? "SINGLE_TARGET_CLOSURE"
                    : "MULTI_TARGET_UNION_CATALOG";
            this.directlySchedulable = targetInstanceCount == 1;
            this.targetClosures = Collections.unmodifiableList(
                    new ArrayList<>(targetClosures));
            this.regions = regions;
            this.regionEdges = regionEdges;
        }
    }
}
