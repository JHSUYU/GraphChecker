package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.asMap;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.strings;
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
    /** {@code rootAuthority} of a region rooted at an object initializer. */
    static final String INITIALIZATION_ENTRY = "INITIALIZATION_ENTRY";
    /** {@code selection} of a region admitted by a demanded state birth. */
    static final String INITIALIZATION_CONTEXT = "INITIALIZATION_CONTEXT";
    /** Region-row member: the demanded fields born under this root. */
    static final String INITIALIZATION_DEMAND = "initializationDemand";
    /** Region-row member: the write sites those fields are born at. */
    static final String INITIALIZATION_WRITE_SITES =
            "initializationWriteSites";

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
        for (String endpoint : communicationEntries) {
            if (!selected.contains(endpoint)
                    || CausynthStaticFacts.constructor(endpoint)
                    || !program.regionsHolding(endpoint).isEmpty()) {
                continue;
            }
            addSkeleton(program, endpoint, "COMMUNICATION_ENTRY",
                    forwardClosure(endpoint, outgoing, regionAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    outgoing, regionAuthorities, transportBoundaries);
        }

        List<String> stateEntries = new ArrayList<>(stateAnchors);
        Collections.sort(stateEntries);
        for (String entry : stateEntries) {
            if (!selected.contains(entry)
                    || CausynthStaticFacts.constructor(entry)
                    || !program.regionsHolding(entry).isEmpty()) {
                continue;
            }
            addSkeleton(program, entry, STATE_WRITER_ENTRY,
                    forwardClosure(entry, outgoing, regionAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    outgoing, regionAuthorities, transportBoundaries);
        }

        planInitializationRegions(program, selected, outgoing,
                regionAuthorities, transportBoundaries);
        declareCommunicationPorts(program);
        declareRetainedLoops(program);
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
     * <p>README section 3 fixes the composition shape:</p>
     *
     * <pre>
     * T_C0(Input, Live_out, Req_out)
     * AND Req_in = Req_out AND T_S(Req_in, Resp_out)
     * AND Resp_in = Resp_out AND Live_in = Live_out
     * AND T_C1(Live_in, Resp_in, Target)
     * </pre>
     *
     * <p>Every one of those equalities is between a port of one region and a
     * port of another, so both endpoints have to appear in a region's port
     * catalog before the composer can state one.  Minting the id at the cut
     * and binding it at runtime is not enough: an equality over a name no
     * catalog declares is an equality between two things the formula knows
     * nothing about, which is why the composer refuses it by name rather than
     * emitting a free variable.  This is where the declaration happens.</p>
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

    /**
     * Plans one candidate region per offered initialization root.
     *
     * <p>An initializer writes state before any service region's activation
     * begins, so the region catalog holds no root that can observe the write
     * and the value it publishes reaches the failure with no symbolic origin.
     * {@link StaticProgram#initializationRootDecisions} decides which
     * initializers may be offered a root of their own -- bounded by the
     * failure-directed demand it is handed, and refused outright whenever a
     * root there would capture the write without the derivation of the value
     * written.  This plans exactly the offers it made.</p>
     *
     * <p>The row is an offer to observe, and nothing more: it names a root,
     * the initializer as its own anchor, the frames the root reaches, and the
     * demanded writes that admitted it.  It states no port, no value and no
     * occurrence, so a write the trace did not record still produces nothing.
     * A run with no decisions -- every static seed pass -- plans none.</p>
     */
    private static void planInitializationRegions(
            StaticProgram program, Set<String> selected,
            Map<String, Set<String>> outgoing,
            Map<String, String> regionAuthorities,
            Set<String> transportBoundaries) {
        Set<String> planned = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            planned.add(text(region.get("regionId")));
        }
        for (Map<String, Object> decision
                : program.initializationDecisions) {
            String root = text(decision.get(
                    StaticProgram.INITIALIZATION_ROOT));
            if (!StaticProgram.INITIALIZATION_OFFERED.equals(text(
                    decision.get(StaticProgram.INITIALIZATION_DECISION)))
                    || !CausynthStaticFacts.constructor(root)
                    || !selected.contains(root)) {
                // Only an offered initializer is planned, and only where the
                // selected slice already holds its frame.
                continue;
            }
            Map<String, Object> row = skeletonRow(root,
                    INITIALIZATION_ENTRY);
            if (!planned.add(text(row.get("regionId")))) {
                continue;
            }
            List<String> methods = forwardClosure(root, outgoing,
                    regionAuthorities);
            row.put("anchorMethod", root);
            row.put("anchorMethods",
                    new ArrayList<>(Collections.singletonList(root)));
            row.put("methods", methods);
            row.put(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                    anchorRootedScope(root,
                            Collections.singletonList(root), methods,
                            outgoing, regionAuthorities,
                            transportBoundaries));
            row.put("selection", INITIALIZATION_CONTEXT);
            row.put(INITIALIZATION_DEMAND, strings(decision.get(
                    StaticProgram.INITIALIZATION_FIELDS)));
            row.put(INITIALIZATION_WRITE_SITES, strings(decision.get(
                    StaticProgram.INITIALIZATION_WRITE_SITES)));
            program.regions.add(row);
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
        List<String> anchors = union(failure, communication, state);
        if (anchors.isEmpty()) {
            return false;
        }
        // The anchors of the admitting kind are the innermost methods that
        // have to be entered for the demanded behaviour; the root only names
        // the execution context they ran in.
        List<String> demandScope = anchorRootedScope(root,
                !failure.isEmpty() ? failure
                        : !communication.isEmpty() ? communication : state,
                methods, outgoing, regionAuthorities,
                transportBoundaries);
        Map<String, Object> row = skeletonRow(root, authority);
        row.put("anchorMethod", anchors.get(0));
        row.put("anchorMethods", anchors);
        row.put("methods", methods);
        row.put(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                demandScope);
        row.put("selection", !failure.isEmpty()
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
