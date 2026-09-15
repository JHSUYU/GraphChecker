package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.d3.smt.JavaContainerTypes;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Predicate;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.asMap;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/**
 * Builds candidate region skeletons around authoritative execution-context
 * entries.
 */
final class SymbolicRegionPlanner {
    /** A demanded shared-state writer no enclosing task region can own. */
    static final String STATE_WRITER_ENTRY = "STATE_WRITER_ENTRY";
    /** An explicit fault call is itself a replayable request boundary. */
    static final String EXPLICIT_FAULT_ENTRY = "EXPLICIT_FAULT_ENTRY";
    private SymbolicRegionPlanner() {
    }

    static void planSelectedSkeleton(
            StaticProgram program, Collection<String> selectedMethods) {
        Set<String> selected = new LinkedHashSet<>();
        if (selectedMethods != null) {
            selected.addAll(selectedMethods);
        }
        selected.remove("");
        Map<String, Set<String>> outgoing = new LinkedHashMap<>();
        Set<String> failureMethods = new LinkedHashSet<>();
        // README Step 1.1: the transport boundary is discovered from the
        // target slice, not declared.
        Set<String> transportBoundaries = new LinkedHashSet<>(
                program.communicationCallSiteCallees);
        // A wire value has two symmetric captures.  Either exact endpoint may
        // own an occurrence; request/response direction only decides which
        // side is IN or OUT.
        Set<String> communicationAnchors = communicationEndpoints(program);
        communicationAnchors.retainAll(selected);
        Set<String> stateAnchors = new LinkedHashSet<>();
        Set<String> demandedState = failureRelevantState(program.edges);
        for (String method : selected) {
            outgoing.put(method, new LinkedHashSet<>());
        }
        for (Map<String, Object> edge : program.edges) {
            String method = text(edge.get("method"));
            String transfer = text(edge.get("transferKind"));
            String target = text(edge.get("toCell"));
            if (target.contains("#exception:") && selected.contains(method)) {
                failureMethods.add(method);
            }
            if (("HEAP_READ".equals(transfer)
                    || "HEAP_WRITE".equals(transfer))
                    && selected.contains(method)
                    && !CausynthStaticFacts.constructor(method)
                    && demandedState.contains(stateDeclaration(edge,
                    transfer))) {
                stateAnchors.add(method);
            }
            String callee = StaticProgram.invocationTarget(edge);
            if (!selected.contains(method) || !selected.contains(callee)
                    || method.equals(callee)) {
                continue;
            }
            outgoing.get(method).add(callee);
        }
        transportBoundaries.remove("");
        String target = text(program.targetResolved.get("method"));
        Map<String, String> regionAuthorities = new LinkedHashMap<>(
                program.executionContextAuthorities);
        for (Map<String, Object> edge : program.edges) {
            String method = text(edge.get("method"));
            if (selected.contains(method) && Boolean.TRUE.equals(
                    edge.get("explicitSymbolicFault"))) {
                regionAuthorities.put(method, EXPLICIT_FAULT_ENTRY);
            }
        }
        if (!target.isEmpty()) {
            regionAuthorities.putIfAbsent(target, "FAILURE_TARGET_ENTRY");
        }

        program.regions.clear();
        program.regionEdges.clear();
        List<String> roots = new ArrayList<>(regionAuthorities.keySet());
        Collections.sort(roots);
        for (String root : roots) {
            if (!selected.contains(root)
                    || CausynthStaticFacts.constructor(root)) {
                continue;
            }
            List<String> methods = forwardClosure(root, outgoing,
                    regionAuthorities);
            String authority = regionAuthorities.get(root);
            boolean admitted = addSkeleton(program, root, authority, methods,
                    failureMethods,
                    communicationAnchors, stateAnchors, outgoing,
                    regionAuthorities, transportBoundaries);
            if (!admitted) {
                addAuthorityEnvelope(program, root, authority, methods);
            }
        }

        List<String> communicationEntries = new ArrayList<>(
                communicationEndpoints(program));
        Collections.sort(communicationEntries);
        Map<String, Map<String, Set<Integer>>> callUnits =
                callUnitsByCallee(program, selected);
        Map<String, List<Map<String, Object>>> loopsByMethod =
                retainedLoopsByMethod(program);
        Set<String> producers = wireProducerEndpoints(program);
        // An endpoint whose region moved up to its loop is held there; a
        // second root at the endpoint itself would re-create the once-per-
        // value activation this rule exists to remove.
        Set<String> rerootedEndpoints = new LinkedHashSet<>();
        for (String endpoint : communicationEntries) {
            if (!selected.contains(endpoint)
                    || CausynthStaticFacts.constructor(endpoint)
                    || !program.regionsHolding(endpoint).isEmpty()) {
                continue;
            }
            String root = producers.contains(endpoint)
                    ? producingLoopRoot(endpoint, selected, callUnits,
                    loopsByMethod, regionAuthorities, transportBoundaries)
                    : endpoint;
            List<String> methods = forwardClosure(root, outgoing,
                    regionAuthorities);
            if (!methods.contains(endpoint)) {
                // The caller's own context owns the endpoint; rooting there
                // would declare a port the region does not hold.
                root = endpoint;
                methods = forwardClosure(root, outgoing, regionAuthorities);
            }
            if (!root.equals(endpoint)) {
                rerootedEndpoints.add(endpoint);
            }
            if (hasSkeletonRoot(program, root)) {
                continue;
            }
            addSkeleton(program, root, "COMMUNICATION_ENTRY", methods,
                    failureMethods, communicationAnchors, stateAnchors,
                    outgoing, regionAuthorities, transportBoundaries);
        }

        List<String> stateEntries = new ArrayList<>(stateAnchors);
        Collections.sort(stateEntries);
        for (String entry : stateEntries) {
            if (!selected.contains(entry)
                    || CausynthStaticFacts.constructor(entry)
                    || rerootedEndpoints.contains(entry)
                    || hasSkeletonRoot(program, entry)) {
                continue;
            }
            addSkeleton(program, entry, STATE_WRITER_ENTRY,
                    forwardClosure(entry, outgoing, regionAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    outgoing, regionAuthorities, transportBoundaries);
        }

        declareCommunicationPorts(program);
        declareRetainedLoops(program);
    }

    /**
     * The method a wire producer's endpoint is rooted at: the nearest
     * selected caller that issues the endpoint's call from inside one of its
     * own retained loops, or the endpoint itself when no caller does.
     *
     * <p>One iteration of such a loop produces one wire value.  A region
     * rooted at the endpoint is entered once per value and its activations
     * can only be told apart by process-wide invocation ordinals, so the
     * consumer's attach binds to whichever of them the ordinal cap left;
     * rooted at the loop's own method the region spans the loop, {@link
     * StaticProgram#loopBodyRoot} names the per-iteration boundary, and each
     * activation exports exactly the element that iteration produced.  That
     * is the shape the consumer half already has whenever the value it
     * builds is also a demanded state anchor, so this makes the two sides of
     * one wire symmetric rather than introducing a new kind of region.</p>
     *
     * <p>The walk stops below any method that already owns an execution
     * context or a transport boundary: above those the endpoint's caller is
     * no longer the frame the value was produced in.</p>
     */
    private static String producingLoopRoot(
            String endpoint, Set<String> selected,
            Map<String, Map<String, Set<Integer>>> callUnits,
            Map<String, List<Map<String, Object>>> loopsByMethod,
            Map<String, String> regionAuthorities,
            Set<String> transportBoundaries) {
        Set<String> visited = new LinkedHashSet<>();
        List<String> frontier = Collections.singletonList(endpoint);
        while (!frontier.isEmpty()) {
            Set<String> next = new TreeSet<>();
            for (String callee : frontier) {
                if (!visited.add(callee)) continue;
                for (Map.Entry<String, Set<Integer>> site
                        : callUnits.getOrDefault(callee,
                        Collections.<String, Set<Integer>>emptyMap())
                        .entrySet()) {
                    String caller = site.getKey();
                    if (!selected.contains(caller)
                            || CausynthStaticFacts.constructor(caller)
                            || transportBoundaries.contains(caller)) {
                        continue;
                    }
                    for (Map<String, Object> loop
                            : loopsByMethod.getOrDefault(caller,
                            Collections.<Map<String, Object>>emptyList())) {
                        for (int unitIndex : site.getValue()) {
                            if (StaticProgram.loopContains(loop, unitIndex)) {
                                return caller;
                            }
                        }
                    }
                    // A caller that already owns an execution context is the
                    // ceiling of this walk, not a step in it.
                    if (!regionAuthorities.containsKey(caller)) {
                        next.add(caller);
                    }
                }
            }
            next.removeAll(visited);
            frontier = new ArrayList<>(next);
        }
        return endpoint;
    }

    /** The endpoint methods that define a declared wire value. */
    private static Set<String> wireProducerEndpoints(StaticProgram program) {
        Set<String> producers = new LinkedHashSet<>();
        for (Map<String, Object> site : program.communicationCallSites) {
            Map<String, Object> capture = asMap(site.get(
                    WireFlowCatalog.PRODUCER));
            if (capture != null) {
                producers.add(text(capture.get(CommunicationCatalogContract
                        .PORT_DEFINITION_METHOD)));
            }
        }
        producers.remove("");
        return producers;
    }

    /** Selected call sites as {@code callee -> caller -> unit indices}. */
    private static Map<String, Map<String, Set<Integer>>> callUnitsByCallee(
            StaticProgram program, Set<String> selected) {
        Map<String, Map<String, Set<Integer>>> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : program.edges) {
            String caller = text(edge.get("method"));
            String callee = StaticProgram.invocationTarget(edge);
            Object unit = edge.get("unitIndex");
            if (callee.isEmpty() || caller.isEmpty() || caller.equals(callee)
                    || !selected.contains(caller)
                    || !(unit instanceof Number)) {
                continue;
            }
            int unitIndex = ((Number) unit).intValue();
            if (unitIndex < 0) continue;
            result.computeIfAbsent(callee,
                    ignored -> new TreeMap<String, Set<Integer>>())
                    .computeIfAbsent(caller,
                            ignored -> new TreeSet<Integer>())
                    .add(unitIndex);
        }
        return result;
    }

    /** The declared retained loops of the slice, by the method that runs them. */
    private static Map<String, List<Map<String, Object>>>
            retainedLoopsByMethod(StaticProgram program) {
        Map<String, List<Map<String, Object>>> result = new LinkedHashMap<>();
        for (Map<String, Object> loop : program.retainedLoops) {
            String method = text(loop.get("enclosingMethod"));
            if (method.isEmpty()) continue;
            result.computeIfAbsent(method,
                    ignored -> new ArrayList<Map<String, Object>>())
                    .add(loop);
        }
        return result;
    }

    /** A method held by another context still needs its own state occurrence. */
    private static boolean hasSkeletonRoot(StaticProgram program,
                                           String method) {
        for (Map<String, Object> region : program.regions) {
            if (method.equals(text(region.get("rootMethod")))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Declares, on each region, the retained loops of the methods it holds.
     */
    private static void declareRetainedLoops(StaticProgram program) {
        if (program.regions.isEmpty() || program.retainedLoops.isEmpty()) {
            return;
        }
        Map<String, List<Map<String, Object>>> byRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> loop : program.retainedLoops) {
            String method = text(loop.get("enclosingMethod"));
            if (method.isEmpty()) continue;
            for (String regionId : program.regionsHolding(method)) {
                byRegion.computeIfAbsent(regionId,
                        ignored -> new ArrayList<Map<String, Object>>())
                        .add(loop);
            }
        }
        for (Map<String, Object> region : program.regions) {
            List<Map<String, Object>> loops = byRegion.get(
                    text(region.get("regionId")));
            if (loops == null || loops.isEmpty()) continue;
            region.put(RuntimeSelectedRegionFinalizer.RETAINED_LOOPS,
                    new ArrayList<>(loops));
        }
    }

    // ------------------------------------------------------------------
    // README section 3 -- the ports of a cut, declared on a region
    // ------------------------------------------------------------------

    /**
     * Declares every port of every discovered cut on the regions that own the
     * two sides of that cut.
     *
     * <p>README section 3 fixes the distributed value-flow shape:</p>
     *
     * <pre>
     * Req = T_C0(Input, Live)
     * Resp = T_S(Req)
     * Target = T_C1(Live, Resp)
     * </pre>
     *
     * <p>The ports identify the producer output and consumer input at each
     * cut.  The VM propagates the producer expression and runtime evidence
     * records the exact endpoints; composition substitutes that expression
     * directly instead of creating a second pair of port values and an
     * equality between them.  Both endpoints must still be declared here so
     * an absent or ambiguous runtime handoff fails closed.</p>
     *
     * <ul>
     *   <li>a REQUEST port is an <b>output</b> of the region holding the
     *       client cut and an <b>input</b> of the region holding the resolved
     *       server entry;</li>
     *   <li>a RESPONSE port is an <b>output</b> of the server region and an
     *       <b>input</b> of the client region;</li>
     * </ul>
     *
     * <p>There is no third kind.  A synchronous call does not split its
     * caller, so a value the client holds across the call stays in one
     * region and needs no port at all.</p>
     *
     */
    private static void declareCommunicationPorts(StaticProgram program) {
        if (program.regions.isEmpty()) {
            return;
        }
        Map<String, Map<String, Map<String, Object>>> byRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> region : program.regions) {
            byRegion.put(text(region.get("regionId")),
                    new LinkedHashMap<String, Map<String, Object>>());
        }
        for (Map<String, Object> site : program.communicationCallSites) {
            declareWirePort(program, site, byRegion);
        }
        for (Map<String, Object> region : program.regions) {
            Map<String, Map<String, Object>> ports = byRegion.get(
                    text(region.get("regionId")));
            if (ports != null && !ports.isEmpty()) {
                region.put(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                        new ArrayList<>(ports.values()));
            }
        }
    }

    /** Declares the producer and consumer of one exact wire value. */
    private static void declareWirePort(
            StaticProgram program, Map<String, Object> site,
            Map<String, Map<String, Map<String, Object>>> byRegion) {
        Map<String, Object> producer = asMap(site.get(WireFlowCatalog.PRODUCER));
        Map<String, Object> consumer = asMap(site.get(WireFlowCatalog.CONSUMER));
        if (producer == null || consumer == null) return;
        String direction = text(site.get(
                CommunicationCatalogContract.PORT_DIRECTION));
        boolean request = CommunicationCatalogContract.DIRECTION_REQUEST
                .equals(direction);
        declareWireEndpoint(program, site, producer, "OUT", request,
                byRegion);
        declareWireEndpoint(program, site, consumer, "IN", !request,
                byRegion);
    }

    private static void declareWireEndpoint(
            StaticProgram program, Map<String, Object> flow,
            Map<String, Object> capture, String side, boolean client,
            Map<String, Map<String, Map<String, Object>>> byRegion) {
        String method = text(capture.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        List<String> regions = program.regionsHolding(method);
        String portId = text(flow.get(CommunicationCatalogContract.PORT_ID));
        for (String regionId : regions) {
            Map<String, Map<String, Object>> ports = byRegion.get(regionId);
            if (ports == null || portId.isEmpty()) continue;
            Map<String, Object> row = new LinkedHashMap<>();
            row.put(CommunicationCatalogContract.PORT_ID, portId);
            row.put(RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, side);
            row.put("sourceKind",
                    RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT);
            row.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
            if (JavaContainerTypes.shape(text(flow.get("javaType")))
                    != JavaContainerTypes.Shape.NONE) {
                row.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
            }
            for (String field : new String[]{
                    CommunicationCatalogContract.PORT_NAME,
                    CommunicationCatalogContract.PORT_JAVA_TYPE,
                    CommunicationCatalogContract.TRANSPORT,
                    CommunicationCatalogContract.PORT_DIRECTION,
                    CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                    CommunicationCatalogContract.CALL_SITE_ID}) {
                row.put(field, flow.get(field));
            }
            row.put(CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                    portId);
            row.put(RuntimeSelectedRegionFinalizer.PORT_ROLE, client
                    ? RuntimeSelectedRegionFinalizer.PORT_ROLE_CLIENT
                    : RuntimeSelectedRegionFinalizer.PORT_ROLE_SERVER);
            row.putAll(capture);
            ports.putIfAbsent(side + "\n" + portId, row);
        }
        if (regions.isEmpty()) {
            program.communicationGaps.add(CommunicationCatalogPlanner.gap(
                    CommunicationCatalogContract.GAP_REQUEST_PORT_UNRESOLVED,
                    "NO_REGION_HOLDS_WIRE_CAPTURE", method,
                    text(flow.get(CommunicationCatalogContract.CALL_SITE_ID)),
                    portId));
        }
    }

    private static boolean addSkeleton(
            StaticProgram program, String root, String authority,
            List<String> methods, Set<String> failureMethods,
            Set<String> communicationAnchors, Set<String> stateAnchors,
            Map<String, Set<String>> outgoing,
            Map<String, String> regionAuthorities,
            Set<String> transportBoundaries) {
        List<String> failure = intersections(methods, failureMethods);
        List<String> communication = intersections(methods,
                communicationAnchors);
        List<String> state = intersections(methods, stateAnchors);
        boolean explicitFault = EXPLICIT_FAULT_ENTRY.equals(authority);
        List<String> fault = explicitFault
                ? Collections.singletonList(root)
                : Collections.<String>emptyList();
        List<String> anchors = union(fault, failure, communication, state);
        if (anchors.isEmpty()) {
            return false;
        }
        // The anchors of the admitting kind are the innermost methods that
        // have to be entered for the demanded behaviour; the root only names
        // the execution context they ran in.
        List<String> demandScope = anchorRootedScope(root,
                explicitFault ? fault
                        : !failure.isEmpty() ? failure
                        : !communication.isEmpty() ? communication : state,
                methods, outgoing, regionAuthorities,
                transportBoundaries);
        Map<String, Object> row = skeletonRow(root, authority);
        row.put("anchorMethod", anchors.get(0));
        row.put("anchorMethods", anchors);
        row.put("methods", methods);
        row.put(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                demandScope);
        row.put("selection", explicitFault
                ? "EXPLICIT_FAULT_CONTEXT"
                : !failure.isEmpty()
                ? "EXCEPTION_CONTEXT"
                : !communication.isEmpty()
                ? "COMMUNICATION_CONTEXT" : "STATE_CONTEXT");
        program.regions.add(row);
        return true;
    }

    private static void addAuthorityEnvelope(
            StaticProgram program, String root, String authority,
            List<String> methods) {
        Map<String, Object> row = skeletonRow(root, authority);
        row.put("anchorMethod", "");
        row.put("anchorMethods", Collections.emptyList());
        row.put("methods", methods);
        row.put("selection", "AUTHORITY_ENVELOPE");
        program.regions.add(row);
    }

    /** The identity and root fields every skeleton row opens with. */
    private static Map<String, Object> skeletonRow(String root,
                                                   String authority) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION);
        row.put("kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND);
        row.put("regionId", CausynthStaticFacts.nameId("REGION.",
                authority + "\n" + root));
        row.put("rootMethod", root);
        row.put("rootAuthority", authority);
        return row;
    }

    private static List<String> intersections(List<String> ordered,
                                              Set<String> candidates) {
        List<String> result = new ArrayList<>();
        for (String value : ordered) {
            if (candidates.contains(value)) {
                result.add(value);
            }
        }
        return result;
    }

    /**
     * Forward closure from every anchor of the admitting kind, kept inside the
     * context closure the root already bounds.
     */
    private static List<String> anchorRootedScope(
            String root, List<String> anchors, List<String> context,
            Map<String, Set<String>> outgoing,
            Map<String, String> authorities,
            Set<String> transportBoundaries) {
        Set<String> sources = new LinkedHashSet<>(anchors);
        Set<String> visited = callClosure(anchors, outgoing,
                candidate -> transportBoundaries.contains(candidate)
                        || !sources.contains(candidate)
                        && authorities.containsKey(candidate));
        visited.retainAll(new LinkedHashSet<>(context));
        visited.add(root);
        List<String> result = new ArrayList<>(visited);
        Collections.sort(result);
        return result;
    }

    /** Every declared producer and consumer capture, without transport roles. */
    private static Set<String> communicationEndpoints(
            StaticProgram program) {
        Set<String> entries = new LinkedHashSet<>();
        for (Map<String, Object> site : program.communicationCallSites) {
            for (String endpoint : new String[]{
                    WireFlowCatalog.PRODUCER, WireFlowCatalog.CONSUMER}) {
                Map<String, Object> capture = asMap(site.get(endpoint));
                if (capture != null) {
                    entries.add(text(capture.get(CommunicationCatalogContract
                            .PORT_DEFINITION_METHOD)));
                }
            }
        }
        entries.remove("");
        return entries;
    }

    private static List<String> forwardClosure(
            String root, Map<String, Set<String>> outgoing,
            Map<String, String> authorities) {
        List<String> result = new ArrayList<>(callClosure(
                Collections.singletonList(root), outgoing,
                candidate -> !root.equals(candidate)
                        && authorities.containsKey(candidate)));
        Collections.sort(result);
        return result;
    }

    /** One FIFO call-graph closure, ordered by signature, never by map. */
    private static Set<String> callClosure(
            Collection<String> seeds, Map<String, Set<String>> outgoing,
            Predicate<String> excluded) {
        return StaticProgram.closure(seeds, method -> {
            List<String> next = new ArrayList<>(outgoing.getOrDefault(method,
                    Collections.emptySet()));
            Collections.sort(next);
            next.removeIf(excluded);
            return next;
        });
    }

    @SafeVarargs
    private static List<String> union(List<String>... groups) {
        Set<String> unique = new LinkedHashSet<>();
        for (List<String> group : groups) {
            unique.addAll(group);
        }
        return new ArrayList<>(unique);
    }

    /**
     * Finds declared state read by the failure slice, then admits only roots
     * that access that state.
     */
    private static Set<String> failureRelevantState(
            Collection<Map<String, Object>> edges) {
        Map<String, List<Map<String, Object>>> incoming =
                new LinkedHashMap<>();
        List<String> seeds = new ArrayList<>();
        for (Map<String, Object> edge : edges) {
            String target = text(edge.get("toCell"));
            if (!target.isEmpty()) {
                incoming.computeIfAbsent(target,
                        ignored -> new ArrayList<>()).add(edge);
            }
            if (target.contains("#exception:")) {
                seeds.add(target);
            }
        }

        Set<String> demanded = new LinkedHashSet<>();
        StaticProgram.closure(seeds, cell -> {
            List<String> next = new ArrayList<>();
            for (Map<String, Object> edge : incoming.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                String transfer = text(edge.get("transferKind"));
                String source = text(edge.get("fromCell"));
                if ("HEAP_READ".equals(transfer)
                        && StaticProgram.declaredField(source)) {
                    demanded.add(source);
                }
                if (!source.isEmpty()) next.add(source);
            }
            return next;
        });
        return demanded;
    }

    private static String stateDeclaration(Map<String, Object> edge,
                                           String transfer) {
        String cell = text(edge.get("HEAP_READ".equals(transfer)
                ? "fromCell" : "toCell"));
        return StaticProgram.declaredField(cell) ? cell : "";
    }
}
