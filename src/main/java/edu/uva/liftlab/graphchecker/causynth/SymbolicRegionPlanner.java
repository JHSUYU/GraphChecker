package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;

import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.UUID;

/**
 * Builds candidate region skeletons around authoritative execution-context
 * entries.
 *
 * <p>This phase deliberately knows nothing about REGION.IN, REGION.OUT or
 * field paths.  Those facts require a concrete activation and are produced
 * only after the REGION_STATE pass.</p>
 */
final class SymbolicRegionPlanner {
    static final int REGION_SCHEMA_VERSION = 3;
    static final String SKELETON_KIND = "REGION_SKELETON";

    private SymbolicRegionPlanner() {
    }

    static void planSelectedSkeleton(
            StaticProgram program, Collection<String> selectedMethods) {
        Set<String> selected = new LinkedHashSet<>();
        if (selectedMethods != null) {
            selected.addAll(selectedMethods);
        }
        selected.remove("");
        // Implementation, delivery and reply frames are boundaries, not
        // coarse region members. The catalog has already subtracted every
        // real client caller and resolved handler before publishing this
        // in-memory exclusion set.
        selected.removeAll(program.regionEnvelopeExclusions);

        Map<String, Set<String>> outgoing = new LinkedHashMap<>();
        Set<String> failureMethods = new LinkedHashSet<>();
        // README Step 1.1: the transport boundary is discovered from the
        // target slice, not declared.  This is the ONLY source of the cut,
        // so the replaced hand-written rows can no longer decide it.
        Set<String> transportBoundaries = new LinkedHashSet<>(
                program.communicationCallSiteCallees);
        // Communication sites may admit their own coarse occurrence, but they
        // do not widen an occurrence admitted by a different anchor.  In
        // particular, a synchronous call inside one method is an event in that
        // method rather than a second communication-free demand fragment.
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
                    && !constructor(method)
                    && demandedState.contains(stateDeclaration(edge,
                    transfer))) {
                stateAnchors.add(method);
            }
            String callee = invocationTarget(edge);
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
            if (!selected.contains(root) || constructor(root)) {
                continue;
            }
            List<String> methods = forwardClosure(root, outgoing,
                    program.executionContextAuthorities);
            String authority = program.executionContextAuthorities.get(root);
            boolean admitted = addSkeleton(program, root, authority, methods,
                    failureMethods,
                    communicationAnchors, stateAnchors,
                    "STATIC_AUTHORITY_SKELETON", outgoing,
                    program.executionContextAuthorities,
                    transportBoundaries);
            if (!admitted) {
                addAuthorityEnvelope(program, root, authority, methods);
            }
        }

        List<String> communicationEntries = new ArrayList<>(
                communicationServerEntries(program));
        Collections.sort(communicationEntries);
        for (String endpoint : communicationEntries) {
            if (!selected.contains(endpoint) || constructor(endpoint)
                    || regionHolds(program, endpoint)) {
                continue;
            }
            addSkeleton(program, endpoint, "COMMUNICATION_ENTRY",
                    forwardClosure(endpoint, outgoing,
                            program.executionContextAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    "STATIC_COMMUNICATION_ENTRY_SKELETON", outgoing,
                    program.executionContextAuthorities,
                    transportBoundaries);
        }

        planTargetActivation(program, selected, failureMethods,
                communicationAnchors, stateAnchors, outgoing, transportBoundaries,
                program.executionContextAuthorities);
        declareCommunicationPorts(program);
        declareRetainedLoops(program);
    }

    /**
     * Declares, on each region, the retained loops of the methods it holds.
     *
     * <p>Loop discovery is independent of communication and is owned by the
     * static catalog; this only routes each published row to the regions
     * whose selected methods contain it, so the occurrence plan can carry the
     * loop's kind, control sites and {@code K_L} without a later stage
     * re-deriving any of them.</p>
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
            for (String regionId : regionsHolding(program, method)) {
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
        Map<String, Set<String>> callers = invocationCallers(program.edges);
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
        Map<String, Object> response = row(site.get(
                CommunicationCatalogContract.RESPONSE_PORT));
        List<Map<String, Object>> responseComponents = rows(site.get(
                CommunicationCatalogContract.RESPONSE_COMPONENT_PORTS));
        Set<String> structuredParents = new LinkedHashSet<>();
        for (Map<String, Object> port : request) {
            String parent = text(port.get(
                    CommunicationCatalogContract.PORT_COMPONENT_OF));
            if (!parent.isEmpty()) structuredParents.add(parent);
        }
        for (Map<String, Object> port : responseComponents) {
            String parent = text(port.get(
                    CommunicationCatalogContract.PORT_COMPONENT_OF));
            if (!parent.isEmpty()) structuredParents.add(parent);
        }

        List<String> clientRegions = regionsOwningClientCut(program,
                clientMethod, callers);
        List<String> serverRegions = serverEntry.isEmpty()
                ? Collections.<String>emptyList()
                : regionsHolding(program, serverEntry);
        List<String> serverPortIds = new ArrayList<>();
        for (Map<String, Object> port : request) {
            serverPortIds.add(text(port.get(
                    CommunicationCatalogContract.PORT_ID)));
        }
        if (response != null) {
            serverPortIds.add(text(response.get(
                    CommunicationCatalogContract.PORT_ID)));
        }
        for (Map<String, Object> component : responseComponents) {
            serverPortIds.add(text(component.get(
                    CommunicationCatalogContract.PORT_ID)));
        }

        for (String regionId : clientRegions) {
            for (Map<String, Object> port : request) {
                Map<String, Object> declared = declare(byRegion, regionId,
                        "OUT", port,
                        RuntimeSelectedRegionFinalizer.PORT_ROLE_CLIENT,
                        exchangeSiteKey, cutSiteId);
                markStructuredParent(declared, structuredParents);
                // Req_out is the cut argument, read in the client's own
                // frame at the cut unit.  See captureAtCut.
                captureAtCut(declared, site, port);
            }
            if (response != null) {
                // Resp_in is the value the cut call returned, read in the
                // client's own frame at the cut unit.
                Map<String, Object> declared = declare(byRegion, regionId,
                        "IN", response,
                        RuntimeSelectedRegionFinalizer.PORT_ROLE_CLIENT,
                        exchangeSiteKey, cutSiteId);
                markStructuredParent(declared, structuredParents);
                captureAtCutReturn(declared, site);
                for (Map<String, Object> component : responseComponents) {
                    captureAtCutReturn(declare(byRegion, regionId, "IN",
                            component,
                            RuntimeSelectedRegionFinalizer.PORT_ROLE_CLIENT,
                            exchangeSiteKey, cutSiteId), site);
                }
            }
        }
        for (String regionId : serverRegions) {
            for (Map<String, Object> port : request) {
                // Req_in is the server entry's own parameter, one frame
                // above the delivery.  See captureAtServerEntry.
                Map<String, Object> declared = declare(byRegion, regionId,
                        "IN", port,
                        RuntimeSelectedRegionFinalizer.PORT_ROLE_SERVER,
                        exchangeSiteKey, cutSiteId);
                markStructuredParent(declared, structuredParents);
                captureAtServerEntry(declared, site, port, serverEntry);
            }
            if (response != null) {
                Map<String, Object> declared = declare(byRegion, regionId,
                        "OUT", response,
                        RuntimeSelectedRegionFinalizer.PORT_ROLE_SERVER,
                        exchangeSiteKey, cutSiteId);
                markStructuredParent(declared, structuredParents);
                captureAtServerReturn(declared, site, serverEntry);
                for (Map<String, Object> component : responseComponents) {
                    captureAtServerReturn(declare(byRegion, regionId, "OUT",
                            component,
                            RuntimeSelectedRegionFinalizer.PORT_ROLE_SERVER,
                            exchangeSiteKey, cutSiteId), site, serverEntry);
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
            // The client half is still declared above; only the server half
            // is missing, and it is named rather than guessed.
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
     * carrier of those leaves, not a second symbolic value.  Keeping the
     * parent declaration preserves the cut/capture schema used to locate the
     * components; only the component leaves cross as symbolic frontiers.
     */
    private static void markStructuredParent(Map<String, Object> declared,
                                             Set<String> structuredParents) {
        if (declared != null && structuredParents.contains(
                text(declared.get("portId")))) {
            declared.put("dependencyRole",
                    DependencyRole.CONCRETE_STRUCTURE_CARRIER);
        }
    }

    /**
     * Finds the coarse application occurrences that own one client cut.
     *
     * <p>The semantic cut method normally belongs to its enclosing region. A
     * transport adapter may, however, put the cut inside implementation frames
     * that are deliberately absent from the region envelope.  Requiring the
     * cut method itself to become a region in that case recreates per-RPC
     * segmentation.  Instead, walk callers only through the already-proved
     * transport exclusion set and stop at the nearest method an existing
     * coarse region holds.  A non-transport, unowned caller is a real ownership
     * gap and is never crossed.</p>
     */
    private static List<String> regionsOwningClientCut(
            StaticProgram program, String clientMethod,
            Map<String, Set<String>> callers) {
        List<String> direct = regionsHolding(program, clientMethod);
        if (!direct.isEmpty() || clientMethod.isEmpty()) {
            return direct;
        }
        Set<String> owners = new TreeSet<>();
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        work.add(clientMethod);
        while (!work.isEmpty()) {
            String callee = work.removeFirst();
            if (!visited.add(callee)) continue;
            for (String caller : callers.getOrDefault(callee,
                    Collections.<String>emptySet())) {
                List<String> held = regionsHolding(program, caller);
                if (!held.isEmpty()) {
                    owners.addAll(held);
                } else if (program.regionEnvelopeExclusions.contains(caller)) {
                    work.addLast(caller);
                }
            }
        }
        return new ArrayList<>(owners);
    }

    /** Reverse selected invocation index, built once for all client cuts. */
    private static Map<String, Set<String>> invocationCallers(
            Collection<Map<String, Object>> edges) {
        Map<String, Set<String>> callers = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            String caller = text(edge.get("method"));
            String callee = invocationTarget(edge);
            if (!caller.isEmpty() && !callee.isEmpty()
                    && !caller.equals(callee)) {
                callers.computeIfAbsent(callee,
                        ignored -> new TreeSet<String>()).add(caller);
            }
        }
        return callers;
    }

    /**
     * Files one declaration under {@code side + portId}.
     *
     * <p>Repeating one declaration is normal - one cut is reached by more
     * than one path - and it must stay one port, so the first declaration
     * wins and the repeat is dropped rather than duplicated.</p>
     */
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
        // Preserve both halves of that declaration on the region port: the
        // parent says which value contains it and the authority says who
        // asserts the encoding.  Dropping either turns the leaf back into an
        // ordinary unpositioned port and leaves runtime planning no exact
        // alternative to guessing from its name.
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
        String carrierClass = side.equals("OUT")
                ? CommunicationCatalogContract.PORT_EXPORT_CARRIER_CLASS
                : CommunicationCatalogContract.PORT_ATTACH_CARRIER_CLASS;
        String carrierField = side.equals("OUT")
                ? CommunicationCatalogContract.PORT_EXPORT_CARRIER_FIELD
                : CommunicationCatalogContract.PORT_ATTACH_CARRIER_FIELD;
        String carrierDescriptor = side.equals("OUT")
                ? CommunicationCatalogContract.PORT_EXPORT_CARRIER_DESCRIPTOR
                : CommunicationCatalogContract.PORT_ATTACH_CARRIER_DESCRIPTOR;
        if (port.containsKey(carrierClass)
                && port.containsKey(carrierField)
                && port.containsKey(carrierDescriptor)) {
            row.put(CommunicationCatalogContract.PORT_MANUAL_CARRIER_CLASS,
                    port.get(carrierClass));
            row.put(CommunicationCatalogContract.PORT_MANUAL_CARRIER_FIELD,
                    port.get(carrierField));
            row.put(
                    CommunicationCatalogContract.PORT_MANUAL_CARRIER_DESCRIPTOR,
                    port.get(carrierDescriptor));
        }
        row.put(RuntimeSelectedRegionFinalizer.PORT_ROLE, portRole);
        row.put(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                exchangeSiteKey);
        row.put(CommunicationCatalogContract.CALL_SITE_ID, cutSiteId);
        row.put("portAuthority",
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORT_AUTHORITY);
        Map<String, Object> existing = ports.putIfAbsent(
                side + "\n" + portId, row);
        return existing == null ? row : existing;
    }

    /**
     * States that {@code Req_out} is read at the cut, in the client's frame.
     *
     * <p>Without this the only thing a client region has to offer as its
     * request output is the transport's own field write - {@code channel.request
     * = value} inside the callee - and a relation anchored there drags the
     * transport frame into the region's definition scope, because the method
     * that defines the output must be inside the relation.  That is exactly
     * the merge across a cut README's core invariants forbid.</p>
     *
     * <p>The value is the same value either way.  What changes is where it is
     * read: at the cut unit, in the enclosing client method, one frame before
     * the transport is entered.  That site is inside the client region by
     * construction - the cut unit is its export site - so the definition
     * method is local to the region and the closure loses nothing.</p>
     *
     * <p>A component port is skipped: it corresponds to no argument position,
     * so there is no argument to read it at.  Its value crosses inside the
     * port it is a component of, which carries the capture.</p>
     */
    private static void captureAtCut(Map<String, Object> declared,
                                     Map<String, Object> site,
                                     Map<String, Object> port) {
        int argument = integer(port.get(CommunicationCatalogContract.PORT_CLIENT_ARGUMENT_INDEX), -1);
        if (declared == null || argument < 0) {
            return;
        }
        String clientMethod = text(site.get(
                CommunicationCatalogContract.CLIENT_METHOD));
        int unitIndex = integer(site.get(
                CommunicationCatalogContract.CLIENT_UNIT_INDEX), -1);
        if (clientMethod.isEmpty() || unitIndex < 0) {
            return;
        }
        declared.put(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
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

    /**
     * States that {@code Resp_in} is the value the cut call returned.
     *
     * <p>The mirror of {@link #captureAtCut}, and it exists for the same
     * reason: without it the only thing the client region has to offer as
     * its response input is the transport's own field read - {@code value =
     * channel.response} inside the callee - and an input anchored there names
     * a frame the region must not contain.  The value is read at the cut
     * unit, in the enclosing client method, one frame above the transport,
     * which is inside the client region by construction.</p>
     */
    private static void captureAtCutReturn(Map<String, Object> declared,
                                           Map<String, Object> site) {
        String clientMethod = text(site.get(
                CommunicationCatalogContract.CLIENT_METHOD));
        int unitIndex = integer(site.get(
                CommunicationCatalogContract.CLIENT_UNIT_INDEX), -1);
        String callee = text(site.get(
                CommunicationCatalogContract.DECLARED_CALLEE));
        if (declared == null || clientMethod.isEmpty() || unitIndex < 0
                || callee.isEmpty()) {
            return;
        }
        declared.put(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                clientMethod);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, unitIndex);
        declared.put(CommunicationCatalogContract.DECLARED_CALLEE, callee);
    }

    /**
     * States that {@code Req_in} is the resolved server entry's parameter.
     *
     * <p>README section 3 asks the server relation for {@code T_S(Req_in,
     * Resp_out)}.  The declaration alone gives {@code Req_in} a name; this
     * gives it a site, and the site is what decides whether the relation is
     * about the handler at all.  Without it the only thing the server
     * fragment has to offer as its input is the transport's own heap read -
     * {@code channel.request} inside the delivery frame - which is a frame
     * outside the server window, so the relation is either anchored across
     * the cut or has no input at all.  The entry's parameter is one frame
     * above that read and inside the server fragment by construction.</p>
     *
     * <p>{@code argumentIndex} carries the parameter position, the same field
     * the client's call-argument capture uses for the position it is read at,
     * so one field means "the argument position of this port's value inside
     * its definition method" on both sides of the cut and the compact catalog
     * schema needs no second name for the same thing.</p>
     */
    private static void captureAtServerEntry(Map<String, Object> declared,
                                             Map<String, Object> site,
                                             Map<String, Object> port,
                                             String serverEntry) {
        int parameter = integer(port.get(CommunicationCatalogContract.PORT_SERVER_PARAMETER_INDEX), -1);
        if (declared == null || parameter < 0 || serverEntry.isEmpty()) {
            // A component port corresponds to no parameter position on
            // either side; its value crosses inside the port it is a
            // component of, which carries the capture.
            return;
        }
        declared.put(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                serverEntry);
        declared.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                parameter);
    }

    /** States that {@code Resp_out} is the server entry's returned value. */
    private static void captureAtServerReturn(Map<String, Object> declared,
                                              Map<String, Object> site,
                                              String serverEntry) {
        if (declared == null || serverEntry.isEmpty()) {
            return;
        }
        declared.put(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_ENTRY_RETURN);
        declared.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                serverEntry);
    }

    private static int integer(Object value, int fallback) {
        return value instanceof Number ? ((Number) value).intValue()
                : fallback;
    }

    private static List<String> regionsHolding(StaticProgram program,
                                               String method) {
        List<String> result = new ArrayList<>();
        if (method.isEmpty()) {
            return result;
        }
        for (Map<String, Object> region : program.regions) {
            if (stringList(region.get("methods")).contains(method)) {
                result.add(text(region.get("regionId")));
            }
        }
        return result;
    }

    private static boolean regionHolds(StaticProgram program,
                                       String method) {
        return !regionsHolding(program, method).isEmpty();
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

    @SuppressWarnings("unchecked")
    private static Map<String, Object> row(Object value) {
        return value instanceof Map<?, ?> ? (Map<String, Object>) value : null;
    }

    private static List<String> stringList(Object value) {
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

    /**
     * Plans the annotated target's own activation as a region when no other
     * region already demands it.
     *
     * <p>Every other candidate is discovered by walking forward from an
     * execution-context entry, so a target the static call graph cannot reach
     * from any entry gets no region at all: the slice that exists only to
     * explain it would then be planned everywhere except at the site it
     * explains.  A call that leaves Java -- a callback the platform invokes, a
     * reflective dispatch -- is exactly such a gap, and inventing the missing
     * caller edge would be a guess.  Naming the target itself as the root is
     * not a guess: the activation is what the annotation already resolved, and
     * it is the activation the runtime passes have to select.</p>
     *
     * <p>This is a fallback, never an override.  A target an entry does reach
     * keeps the region its enclosing context owns, and this adds nothing.</p>
     */
    private static void planTargetActivation(
            StaticProgram program, Set<String> selected,
            Set<String> failureMethods, Set<String> communicationAnchors,
            Set<String> stateAnchors, Map<String, Set<String>> outgoing,
            Set<String> transportBoundaries,
            Map<String, String> authorities) {
        String target = text(program.targetResolved.get("method"));
        if (target.isEmpty() || !selected.contains(target)
                || constructor(target)) {
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
                "STATIC_TARGET_ACTIVATION_SKELETON", outgoing,
                authorities, transportBoundaries);
    }

    private static boolean addSkeleton(
            StaticProgram program, String root, String authority,
            List<String> methods, Set<String> failureMethods,
            Set<String> communicationAnchors, Set<String> stateAnchors,
            String planningMode, Map<String, Set<String>> outgoing,
            Map<String, String> authorities,
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
        // the execution context they ran in.  What those anchors reach is the
        // demanded scope.  The region still *contains* the whole context --
        // its outputs are produced there -- but a branch outside the demanded
        // scope is the context's own business and is not explored, so the
        // other work the outer frames do buys no path and, by the symbolic
        // leaf rule, no symbol either.
        //
        List<String> demandScope = anchorRootedScope(root,
                !failure.isEmpty() ? failure
                        : !communication.isEmpty() ? communication : state,
                methods, outgoing, authorities, transportBoundaries);
        String identity = authority + "\n" + root;
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", REGION_SCHEMA_VERSION);
        row.put("kind", SKELETON_KIND);
        row.put("regionId", "REGION."
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8)));
        row.put("rootMethod", root);
        row.put("rootAuthority", authority);
        row.put("anchorMethod", anchors.get(0));
        row.put("anchorMethods", anchors);
        row.put("methods", methods);
        row.put(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                demandScope);
        row.put("selection", !failure.isEmpty()
                ? "EXCEPTION_CONTEXT"
                : !communication.isEmpty()
                ? "COMMUNICATION_CONTEXT" : "STATE_CONTEXT");
        row.put("planningMode", planningMode);
        program.regions.add(row);
        return true;
    }

    private static void addAuthorityEnvelope(
            StaticProgram program, String root, String authority,
            List<String> methods) {
        String identity = authority + "\n" + root;
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", REGION_SCHEMA_VERSION);
        row.put("kind", SKELETON_KIND);
        row.put("regionId", "REGION."
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8)));
        row.put("rootMethod", root);
        row.put("rootAuthority", authority);
        row.put("anchorMethod", "");
        row.put("anchorMethods", Collections.emptyList());
        row.put("methods", methods);
        row.put("selection", "AUTHORITY_ENVELOPE");
        row.put("planningMode", "STATIC_AUTHORITY_ENVELOPE");
        program.regions.add(row);
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
     * context closure the root already bounds.  A nested execution-context
     * authority still ends the walk unless it is itself one of the anchors.
     *
     * <p>A discovered communication call site also ends it.  That call is
     * the transport boundary: the demand is carried across by the explicit
     * request/response ports the call site declares, so how
     * the transport reaches the other end is never this region's demand --
     * whether the callee is a proxy that is opaque anyway, or an in-process
     * call tree that would otherwise pull its whole library in.  Only the
     * call edge is cut, so a callee the anchors also reach without crossing
     * a boundary stays demanded.  The region still contains the transport
     * methods; they are simply not what this region has to decide.</p>
     *
     * <p>The boundary set comes from
     * {@link StaticProgram#communicationCallSiteCallees}, which
     * {@link CommunicationCatalogPlanner} discovers inside the target slice.
     * A declared stub row no longer participates in this decision.</p>
     */
    private static List<String> anchorRootedScope(
            String root, List<String> anchors, List<String> context,
            Map<String, Set<String>> outgoing,
            Map<String, String> authorities,
            Set<String> transportBoundaries) {
        Set<String> sources = new LinkedHashSet<>(anchors);
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>(anchors);
        while (!work.isEmpty()) {
            String method = work.removeFirst();
            if (!visited.add(method)) {
                continue;
            }
            List<String> next = new ArrayList<>(outgoing.getOrDefault(method,
                    Collections.emptySet()));
            Collections.sort(next);
            for (String candidate : next) {
                if (transportBoundaries.contains(candidate)
                        || !sources.contains(candidate)
                        && authorities.containsKey(candidate)) {
                    continue;
                }
                work.addLast(candidate);
            }
        }
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
            entries.addAll(stringList(site.get(
                    CommunicationCatalogContract.SERVER_ENTRY_CANDIDATES)));
        }
        entries.remove("");
        return entries;
    }

    private static List<String> forwardClosure(
            String root, Map<String, Set<String>> outgoing,
            Map<String, String> authorities) {
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        work.add(root);
        while (!work.isEmpty()) {
            String method = work.removeFirst();
            if (!visited.add(method)) {
                continue;
            }
            List<String> next = new ArrayList<>(outgoing.getOrDefault(method,
                    Collections.emptySet()));
            Collections.sort(next);
            for (String candidate : next) {
                if (!root.equals(candidate)
                        && authorities.containsKey(candidate)) {
                    continue;
                }
                work.addLast(candidate);
            }
        }
        List<String> result = new ArrayList<>(visited);
        Collections.sort(result);
        return result;
    }

    @SafeVarargs
    private static List<String> union(List<String>... groups) {
        Set<String> unique = new LinkedHashSet<>();
        for (List<String> group : groups) {
            unique.addAll(group);
        }
        return new ArrayList<>(unique);
    }

    private static boolean constructor(String method) {
        return method != null && (method.contains(" <init>(")
                || method.contains(" <clinit>("));
    }

    private static String invocationTarget(Map<String, Object> edge) {
        if ("DYNAMIC_DISPATCH".equals(text(edge.get("transferKind")))
                && "dispatch_activation".equals(text(edge.get("kind")))) {
            String activation = text(edge.get("toCell"));
            if (activation.endsWith(".activation")) {
                return activation.substring(0,
                        activation.length() - ".activation".length());
            }
        }
        return text(edge.get("invoke"));
    }

    /**
     * Finds declared state read by the failure slice, then admits only roots
     * that access that state.  The old rule treated every selected heap access
     * as a region anchor, which turned broad call-graph scaffolding into
     * hundreds of unrelated region candidates.
     */
    private static Set<String> failureRelevantState(
            Collection<Map<String, Object>> edges) {
        Map<String, List<Map<String, Object>>> incoming =
                new LinkedHashMap<>();
        Deque<String> work = new ArrayDeque<>();
        for (Map<String, Object> edge : edges) {
            String target = text(edge.get("toCell"));
            if (!target.isEmpty()) {
                incoming.computeIfAbsent(target,
                        ignored -> new ArrayList<>()).add(edge);
            }
            if (target.contains("#exception:")) {
                work.addLast(target);
            }
        }

        Set<String> visited = new LinkedHashSet<>();
        Set<String> demanded = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            for (Map<String, Object> edge : incoming.getOrDefault(cell,
                    Collections.emptyList())) {
                String transfer = text(edge.get("transferKind"));
                String source = text(edge.get("fromCell"));
                if ("HEAP_READ".equals(transfer)
                        && declaredField(source)) {
                    demanded.add(source);
                }
                if (!source.isEmpty()) work.addLast(source);
            }
        }
        return demanded;
    }

    private static String stateDeclaration(Map<String, Object> edge,
                                           String transfer) {
        String cell = text(edge.get("HEAP_READ".equals(transfer)
                ? "fromCell" : "toCell"));
        return declaredField(cell) ? cell : "";
    }

    private static boolean declaredField(String cell) {
        return cell.startsWith("<") && cell.endsWith(">")
                && cell.contains(":") && !cell.contains("(");
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }
}
