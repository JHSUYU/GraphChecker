package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSymbolicInputs;
import edu.uva.liftlab.graphchecker.plan.DependencyRole;

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
        // Roots are manual: the case's symbolic-inputs.jsonl is the one
        // authority on what is symbolic, so every method it names is an
        // anchor and a region root here by declaration, whatever the
        // backward slice from the target did or did not reach.  See
        // DeclaredSymbolicInputs for why the two differ.
        Set<String> declaredAnchors = new LinkedHashSet<>(
                DeclaredSymbolicInputs.configured());
        Set<String> unsliced = new LinkedHashSet<>(declaredAnchors);
        unsliced.removeAll(selected);
        if (!unsliced.isEmpty()) {
            // SeedBackwardStaticAnalyzer seeds every declared method into
            // the slice, so this cannot happen without one of the two rules
            // having been weakened.  Refused rather than intersected away:
            // planning around a declaration the slice dropped is how the
            // declaration became invisible in the first place.
            throw new IllegalStateException(
                    "DECLARED_INPUT_OUTSIDE_STATIC_SLICE: declared symbolic "
                            + "input methods are not in the static slice: "
                            + unsliced);
        }
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
        List<String> roots = new ArrayList<>(regionAuthorities.keySet());
        Collections.sort(roots);
        for (String root : roots) {
            if (!selected.contains(root)
                    || CausynthStaticFacts.constructor(root)) {
                continue;
            }
            List<String> methods = forwardClosure(root, outgoing,
                    regionAuthorities);
            addSkeleton(program, root, regionAuthorities.get(root), methods,
                    failureMethods,
                    communicationAnchors, stateAnchors, declaredAnchors,
                    outgoing, regionAuthorities, transportBoundaries);
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
            if (hasSkeletonRoot(program, endpoint)) continue;
            addSkeleton(program, endpoint, "COMMUNICATION_ENTRY",
                    forwardClosure(endpoint, outgoing, regionAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    declaredAnchors, outgoing, regionAuthorities,
                    transportBoundaries);
        }

        List<String> stateEntries = new ArrayList<>(stateAnchors);
        Collections.sort(stateEntries);
        for (String entry : stateEntries) {
            if (!selected.contains(entry)
                    || CausynthStaticFacts.constructor(entry)
                    || hasSkeletonRoot(program, entry)) {
                continue;
            }
            addSkeleton(program, entry, STATE_WRITER_ENTRY,
                    forwardClosure(entry, outgoing, regionAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    declaredAnchors, outgoing, regionAuthorities,
                    transportBoundaries);
        }

        // Last, so that a declared method some other authority already roots
        // keeps that authority: the region id is minted from the authority
        // and the root, and a declaration must not rename a region the rest
        // of the pipeline already addresses.  What is left here is a
        // declared method no other rule roots -- which is exactly the case
        // this rule exists for.
        List<String> declaredEntries = new ArrayList<>(declaredAnchors);
        Collections.sort(declaredEntries);
        for (String entry : declaredEntries) {
            if (CausynthStaticFacts.constructor(entry)
                    || hasSkeletonRoot(program, entry)) {
                continue;
            }
            addSkeleton(program, entry, DeclaredSymbolicInputs.AUTHORITY,
                    forwardClosure(entry, outgoing, regionAuthorities),
                    failureMethods, communicationAnchors, stateAnchors,
                    declaredAnchors, outgoing, regionAuthorities,
                    transportBoundaries);
        }

        declareCommunicationPorts(program);
        declareRetainedLoops(program);
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
        declareWireEndpoint(program, site, producer, "OUT", byRegion);
        declareWireEndpoint(program, site, consumer, "IN", byRegion);
    }

    private static void declareWireEndpoint(
            StaticProgram program, Map<String, Object> flow,
            Map<String, Object> capture, String side,
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
            row.putAll(capture);
            ports.putIfAbsent(side + "\n" + portId, row);
        }
        if (regions.isEmpty()) {
            program.communicationGaps.add(CommunicationCatalogPlanner.gap(
                    GapKind.COMMUNICATION_REQUEST_PORT_UNRESOLVED,
                    GapClass.BLOCKING,
                    "NO_REGION_HOLDS_WIRE_CAPTURE", method,
                    text(flow.get(CommunicationCatalogContract.CALL_SITE_ID)),
                    portId));
        }
    }

    private static boolean addSkeleton(
            StaticProgram program, String root, String authority,
            List<String> methods, Set<String> failureMethods,
            Set<String> communicationAnchors, Set<String> stateAnchors,
            Set<String> declaredAnchors,
            Map<String, Set<String>> outgoing,
            Map<String, String> regionAuthorities,
            Set<String> transportBoundaries) {
        List<String> failure = intersections(methods, failureMethods);
        List<String> communication = intersections(methods,
                communicationAnchors);
        List<String> state = intersections(methods, stateAnchors);
        // Appended last, so a region whose anchor some other kind already
        // named keeps that anchor: anchorMethod is anchors.get(0) and the
        // plan publishes it as the region's targetMethod.  A declared method
        // this region holds is added to the list, and a region held by
        // nothing else is anchored on its declared root.
        List<String> declared = intersections(methods, declaredAnchors);
        boolean explicitFault = EXPLICIT_FAULT_ENTRY.equals(authority);
        List<String> fault = explicitFault
                ? Collections.singletonList(root)
                : Collections.<String>emptyList();
        List<String> anchors = union(fault, failure, communication, state,
                declared);
        if (anchors.isEmpty()) {
            return false;
        }
        Map<String, Object> row = skeletonRow(root, authority);
        if (declaredAnchors.contains(root)) {
            // The declaration, published.  Every stage after this one reads
            // it off the skeleton rather than re-reading the case file.
            row.put(DeclaredSymbolicInputs.ROOT_FIELD, true);
        }
        row.put("anchorMethod", anchors.get(0));
        row.put("anchorMethods", anchors);
        row.put("methods", methods);
        row.put("selection", explicitFault
                ? "EXPLICIT_FAULT_CONTEXT"
                : !failure.isEmpty()
                ? "EXCEPTION_CONTEXT"
                : !communication.isEmpty()
                ? "COMMUNICATION_CONTEXT" : "STATE_CONTEXT");
        program.regions.add(row);
        return true;
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
