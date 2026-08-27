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
import java.util.TreeSet;
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
        // Implementation, delivery and reply frames are boundaries, not coarse
        // region members.
        selected.removeAll(program.regionEnvelopeExclusions);

        Map<String, Set<String>> outgoing = new LinkedHashMap<>();
        Set<String> failureMethods = new LinkedHashSet<>();
        // README Step 1.1: the transport boundary is discovered from the
        // target slice, not declared.
        Set<String> transportBoundaries = new LinkedHashSet<>(
                program.communicationCallSiteCallees);
        // Communication sites may admit their own coarse occurrence, but they
        // do not widen an occurrence admitted by a different anchor.
        Set<String> communicationAnchors = new LinkedHashSet<>(
                communicationServerEntries(program));
        for (Map<String, Object> site : program.communicationCallSites) {
            String client = text(site.get(
                    CommunicationCatalogContract.CLIENT_METHOD));
            if (!client.isEmpty()) communicationAnchors.add(client);
        }
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

        program.regions.clear();
        program.regionEdges.clear();
        List<String> roots = new ArrayList<>(
                program.executionContextAuthorities.keySet());
        Collections.sort(roots);
        for (String root : roots) {
            if (!selected.contains(root)
                    || CausynthStaticFacts.constructor(root)) {
                continue;
            }
            List<String> methods = forwardClosure(root, outgoing,
                    program.executionContextAuthorities);
            String authority = program.executionContextAuthorities.get(root);
            boolean admitted = addSkeleton(program, root, authority, methods,
                    failureMethods,
                    communicationAnchors, stateAnchors, outgoing,
                    transportBoundaries);
            if (!admitted) {
                addAuthorityEnvelope(program, root, authority, methods);
            }
        }

        List<String> communicationEntries = new ArrayList<>(
                communicationServerEntries(program));
        Collections.sort(communicationEntries);
        for (String endpoint : communicationEntries) {
            if (!selected.contains(endpoint)
                    || CausynthStaticFacts.constructor(endpoint)
                    || !program.regionsHolding(endpoint).isEmpty()) {
                continue;
            }
            addSkeleton(program, endpoint, "COMMUNICATION_ENTRY",
                    forwardClosure(endpoint, outgoing,
                            program.executionContextAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    outgoing, transportBoundaries);
        }

        planTargetActivation(program, selected, failureMethods,
                communicationAnchors, stateAnchors, outgoing,
                transportBoundaries);
        planInitializationRegions(program, selected, outgoing,
                transportBoundaries);
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
     * <p>A side that cannot be resolved is named, never assumed.  A cut whose
     * server entry is ambiguous still declares its client-side ports and
     * reports {@link CommunicationCatalogContract#GAP_SERVER_CUT_UNRESOLVED}
     * for the server half, because one unresolved entry is not a reason to
     * drop the half of the chain that is resolved.</p>
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
        Map<String, Set<String>> callers = program.invocationCallers();
        for (Map<String, Object> site : program.communicationCallSites) {
            declareCutPorts(program, site, byRegion, callers);
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

    /** The request and response ports of one discovered cut. */
    private static void declareCutPorts(
            StaticProgram program, Map<String, Object> site,
            Map<String, Map<String, Map<String, Object>>> byRegion,
            Map<String, Set<String>> callers) {
        String clientMethod = text(site.get(
                CommunicationCatalogContract.CLIENT_METHOD));
        String serverEntry = text(site.get(
                CommunicationCatalogContract.SERVER_ENTRY_METHOD));
        String cutSiteId = text(site.get(
                CommunicationCatalogContract.CALL_SITE_ID));
        String exchangeSiteKey = text(site.get(
                CommunicationCatalogContract.EXCHANGE_SITE_KEY));
        List<Map<String, Object>> request = rows(site.get(
                CommunicationCatalogContract.REQUEST_PORTS));
        Map<String, Object> response = asMap(site.get(
                CommunicationCatalogContract.RESPONSE_PORT));
        List<Map<String, Object>> responseComponents = rows(site.get(
                CommunicationCatalogContract.RESPONSE_COMPONENT_PORTS));
        Set<String> structuredParents = new LinkedHashSet<>();
        List<Map<String, Object>> componentPorts = new ArrayList<>(request);
        componentPorts.addAll(responseComponents);
        for (Map<String, Object> port : componentPorts) {
            String parent = text(port.get(
                    CommunicationCatalogContract.PORT_COMPONENT_OF));
            if (!parent.isEmpty()) structuredParents.add(parent);
        }

        List<String> clientRegions = regionsOwningClientCut(program,
                clientMethod, callers);
        List<String> serverRegions = serverEntry.isEmpty()
                ? Collections.<String>emptyList()
                : program.regionsHolding(serverEntry);
        List<Map<String, Object>> declaredPorts = new ArrayList<>(request);
        if (response != null) declaredPorts.add(response);
        declaredPorts.addAll(responseComponents);
        List<String> serverPortIds = new ArrayList<>();
        for (Map<String, Object> port : declaredPorts) {
            serverPortIds.add(text(port.get(
                    CommunicationCatalogContract.PORT_ID)));
        }

        // One cut, two sides: the request is the client's output and the
        // server's input, the response the reverse, and each side captures
        // the value where its own frame reads it -- Req_out and Resp_in at
        // the cut unit (captureAtCut), Req_in and Resp_out at the server
        // entry (captureAtServerEntry).
        for (boolean client : new boolean[]{true, false}) {
            String role = client
                    ? RuntimeSelectedRegionFinalizer.PORT_ROLE_CLIENT
                    : RuntimeSelectedRegionFinalizer.PORT_ROLE_SERVER;
            String requestSide = client ? "OUT" : "IN";
            String responseSide = client ? "IN" : "OUT";
            for (String regionId : client ? clientRegions : serverRegions) {
                for (Map<String, Object> port : request) {
                    Map<String, Object> declared = declare(byRegion, regionId,
                            requestSide, port, role, exchangeSiteKey,
                            cutSiteId);
                    markStructuredParent(declared, structuredParents);
                    if (client) captureAtCut(declared, site, port);
                    else captureAtServerEntry(declared, port, serverEntry);
                }
                if (response == null) continue;
                Map<String, Object> declared = declare(byRegion, regionId,
                        responseSide, response, role, exchangeSiteKey,
                        cutSiteId);
                markStructuredParent(declared, structuredParents);
                if (client) captureAtCutReturn(declared, site);
                else captureAtServerReturn(declared, serverEntry);
                for (Map<String, Object> component : responseComponents) {
                    Map<String, Object> leaf = declare(byRegion, regionId,
                            responseSide, component, role, exchangeSiteKey,
                            cutSiteId);
                    if (client) captureAtCutReturn(leaf, site);
                    else captureAtServerReturn(leaf, serverEntry);
                }
            }
        }

        if (clientRegions.isEmpty() && !request.isEmpty()) {
            program.communicationGaps.add(CommunicationCatalogPlanner.gap(
                    CommunicationCatalogContract.GAP_REQUEST_PORT_UNRESOLVED,
                    "NO_REGION_HOLDS_CLIENT_CUT_METHOD", clientMethod,
                    cutSiteId, String.join(",", serverPortIds)));
        }
        if (serverPortIds.isEmpty()) {
            return;
        }
        if (serverEntry.isEmpty()) {
            // The two-hop case: both cuts reach two compatible handlers and
            // separating them statically needs allocation-site points-to.
            program.communicationGaps.add(CommunicationCatalogPlanner.gap(
                    CommunicationCatalogContract.GAP_SERVER_CUT_UNRESOLVED,
                    "SERVER_SIDE_PORTS_UNDECLARED", clientMethod, cutSiteId,
                    String.join(",", serverPortIds)));
        } else if (serverRegions.isEmpty()) {
            program.communicationGaps.add(CommunicationCatalogPlanner.gap(
                    CommunicationCatalogContract.GAP_SERVER_CUT_UNRESOLVED,
                    "NO_REGION_HOLDS_SERVER_ENTRY_METHOD", serverEntry,
                    cutSiteId, String.join(",", serverPortIds)));
        }
    }

    /**
     * A wire value with explicitly declared component leaves is the concrete
     * carrier of those leaves, not a second symbolic value.
     */
    private static void markStructuredParent(Map<String, Object> declared,
                                             Set<String> structuredParents) {
        if (declared != null && structuredParents.contains(
                text(declared.get("portId")))) {
            declared.put("dependencyRole",
                    DependencyRole.CONCRETE_STRUCTURE_CARRIER);
        }
    }

    /** Finds the coarse application occurrences that own one client cut. */
    private static List<String> regionsOwningClientCut(
            StaticProgram program, String clientMethod,
            Map<String, Set<String>> callers) {
        List<String> direct = program.regionsHolding(clientMethod);
        if (!direct.isEmpty() || clientMethod.isEmpty()) {
            return direct;
        }
        Set<String> owners = new TreeSet<>();
        StaticProgram.closure(Collections.singletonList(clientMethod),
                callee -> {
            List<String> next = new ArrayList<>();
            for (String caller : callers.getOrDefault(callee,
                    Collections.<String>emptySet())) {
                List<String> held = program.regionsHolding(caller);
                if (!held.isEmpty()) {
                    owners.addAll(held);
                } else if (program.regionEnvelopeExclusions.contains(caller)) {
                    next.add(caller);
                }
            }
            return next;
        });
        return new ArrayList<>(owners);
    }

    /** Files one declaration under {@code side + portId}. */
    private static Map<String, Object> declare(
            Map<String, Map<String, Map<String, Object>>> byRegion,
            String regionId, String side, Map<String, Object> port,
            String portRole, String exchangeSiteKey, String cutSiteId) {
        Map<String, Map<String, Object>> ports = byRegion.get(regionId);
        String portId = text(port.get(
                CommunicationCatalogContract.PORT_ID));
        if (ports == null || portId.isEmpty()) {
            return null;
        }
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("portId", portId);
        row.put(RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, side);
        row.put("sourceKind",
                RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT);
        row.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        row.put("javaType", text(port.get(
                CommunicationCatalogContract.PORT_JAVA_TYPE)));
        row.put(CommunicationCatalogContract.PORT_DIRECTION,
                text(port.get(CommunicationCatalogContract.PORT_DIRECTION)));
        row.put(CommunicationCatalogContract.PORT_NAME,
                text(port.get(CommunicationCatalogContract.PORT_NAME)));
        // A component is a declared leaf carried inside another cut value.
        for (String field : new String[]{
                CommunicationCatalogContract.PORT_COMPONENT_OF,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH}) {
            if (port.containsKey(field)) {
                row.put(field, port.get(field));
            }
        }
        if (port.containsKey(
                CommunicationCatalogContract.PORT_HANDOFF_PATH)) {
            row.put(CommunicationCatalogContract.PORT_HANDOFF_PATH,
                    port.get(CommunicationCatalogContract.PORT_HANDOFF_PATH));
        }
        if (port.containsKey("symbolicDemand")) {
            row.put("symbolicDemand", port.get("symbolicDemand"));
        }
        // A manual carrier is only declared when all three halves are known.
        String[] carrier = side.equals("OUT")
                ? new String[]{
                CommunicationCatalogContract.PORT_EXPORT_CARRIER_CLASS,
                CommunicationCatalogContract.PORT_EXPORT_CARRIER_FIELD,
                CommunicationCatalogContract.PORT_EXPORT_CARRIER_DESCRIPTOR}
                : new String[]{
                CommunicationCatalogContract.PORT_ATTACH_CARRIER_CLASS,
                CommunicationCatalogContract.PORT_ATTACH_CARRIER_FIELD,
                CommunicationCatalogContract.PORT_ATTACH_CARRIER_DESCRIPTOR};
        String[] manual = {
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_CLASS,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_FIELD,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_DESCRIPTOR};
        if (port.containsKey(carrier[0]) && port.containsKey(carrier[1])
                && port.containsKey(carrier[2])) {
            for (int half = 0; half < manual.length; half++) {
                row.put(manual[half], port.get(carrier[half]));
            }
        }
        row.put(RuntimeSelectedRegionFinalizer.PORT_ROLE, portRole);
        row.put(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                exchangeSiteKey);
        row.put(CommunicationCatalogContract.CALL_SITE_ID, cutSiteId);
        Map<String, Object> existing = ports.putIfAbsent(
                side + "\n" + portId, row);
        return existing == null ? row : existing;
    }

    /**
     * States that {@code Req_out} is read at the cut, in the client's frame.
     * That is exactly the merge across a cut README's core invariants forbid.
     */
    private static void captureAtCut(Map<String, Object> declared,
                                     Map<String, Object> site,
                                     Map<String, Object> port) {
        int argument = number(port.get(CommunicationCatalogContract.PORT_CLIENT_ARGUMENT_INDEX), -1);
        if (declared == null || argument < 0) {
            return;
        }
        String clientMethod = text(site.get(
                CommunicationCatalogContract.CLIENT_METHOD));
        int unitIndex = number(site.get(
                CommunicationCatalogContract.CLIENT_UNIT_INDEX), -1);
        if (clientMethod.isEmpty() || unitIndex < 0) {
            return;
        }
        capture(declared, CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT,
                clientMethod);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, unitIndex);
        declared.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                argument);
        declared.put(CommunicationCatalogContract.DECLARED_CALLEE,
                text(site.get(CommunicationCatalogContract.DECLARED_CALLEE)));
        // The compact region-port schema carries callerMethod/unitIndex, so
        // the capture site survives into the published catalog under the
        // names that schema already knows.
        declared.put("callerMethod", clientMethod);
        declared.put("unitIndex", unitIndex);
    }

    /** States that {@code Resp_in} is the value the cut call returned. */
    private static void captureAtCutReturn(Map<String, Object> declared,
                                           Map<String, Object> site) {
        String clientMethod = text(site.get(
                CommunicationCatalogContract.CLIENT_METHOD));
        int unitIndex = number(site.get(
                CommunicationCatalogContract.CLIENT_UNIT_INDEX), -1);
        String callee = text(site.get(
                CommunicationCatalogContract.DECLARED_CALLEE));
        if (declared == null || clientMethod.isEmpty() || unitIndex < 0
                || callee.isEmpty()) {
            return;
        }
        capture(declared, CommunicationCatalogContract.CAPTURE_CALL_RETURN,
                clientMethod);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, unitIndex);
        declared.put(CommunicationCatalogContract.DECLARED_CALLEE, callee);
    }

    /** Every capture states its kind and the method that defines it. */
    private static void capture(Map<String, Object> declared, String kind,
                                String definitionMethod) {
        declared.put(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                kind);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                definitionMethod);
    }

    /**
     * States that {@code Req_in} is the resolved server entry's parameter.
     * README section 3 asks the server relation for {@code T_S(Req_in,
     * Resp_out)}.
     */
    private static void captureAtServerEntry(Map<String, Object> declared,
                                             Map<String, Object> port,
                                             String serverEntry) {
        int parameter = number(port.get(CommunicationCatalogContract.PORT_SERVER_PARAMETER_INDEX), -1);
        if (declared == null || parameter < 0 || serverEntry.isEmpty()) {
            // A component port corresponds to no parameter position on
            // either side; its value crosses inside the port it is a
            // component of, which carries the capture.
            return;
        }
        capture(declared,
                CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER,
                serverEntry);
        declared.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                parameter);
    }

    /** States that {@code Resp_out} is the server entry's returned value. */
    private static void captureAtServerReturn(Map<String, Object> declared,
                                              String serverEntry) {
        if (declared != null && !serverEntry.isEmpty()) {
            capture(declared,
                    CommunicationCatalogContract.CAPTURE_ENTRY_RETURN,
                    serverEntry);
        }
    }

    /**
     * Plans the annotated target's own activation as a region when no other
     * region already demands it.
     */
    private static void planTargetActivation(
            StaticProgram program, Set<String> selected,
            Set<String> failureMethods, Set<String> communicationAnchors,
            Set<String> stateAnchors, Map<String, Set<String>> outgoing,
            Set<String> transportBoundaries) {
        String target = text(program.targetResolved.get("method"));
        if (target.isEmpty() || !selected.contains(target)
                || CausynthStaticFacts.constructor(target)) {
            return;
        }
        for (Map<String, Object> region : program.regions) {
            Object demanded = region.get(
                    RuntimeSelectedRegionFinalizer.DEMAND_SCOPE);
            if (demanded instanceof Collection
                    && ((Collection<?>) demanded).contains(target)) {
                return;
            }
        }
        addSkeleton(program, target, "FAILURE_TARGET_ENTRY",
                forwardClosure(target, outgoing,
                        program.executionContextAuthorities),
                failureMethods, communicationAnchors, stateAnchors,
                outgoing, transportBoundaries);
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
                    program.executionContextAuthorities);
            row.put("anchorMethod", root);
            row.put("anchorMethods",
                    new ArrayList<>(Collections.singletonList(root)));
            row.put("methods", methods);
            row.put(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                    anchorRootedScope(root,
                            Collections.singletonList(root), methods,
                            outgoing, program.executionContextAuthorities,
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
                methods, outgoing, program.executionContextAuthorities,
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

    private static Set<String> communicationServerEntries(
            StaticProgram program) {
        Set<String> entries = new LinkedHashSet<>();
        for (Map<String, Object> site : program.communicationCallSites) {
            entries.addAll(strings(site.get(
                    CommunicationCatalogContract.SERVER_ENTRY_CANDIDATES)));
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
