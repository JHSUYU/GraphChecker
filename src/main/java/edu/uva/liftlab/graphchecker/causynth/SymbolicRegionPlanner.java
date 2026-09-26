package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DependencyRole;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.asMap;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/** Builds candidate region skeletons around execution-context entries. */
final class SymbolicRegionPlanner {
    /** A demanded shared-state writer no enclosing task region can own. */
    static final String STATE_WRITER_ENTRY = "STATE_WRITER_ENTRY";
    /** An explicit fault call is itself a replayable request boundary. */
    static final String EXPLICIT_FAULT_ENTRY = "EXPLICIT_FAULT_ENTRY";
    /** The annotated target's own method, when no entry encloses it. */
    static final String FAILURE_TARGET_ENTRY = "FAILURE_TARGET_ENTRY";
    private SymbolicRegionPlanner() {
    }

    static void planSelectedSkeleton(
            StaticProgram program, Collection<String> selectedMethods) {
        Anchors anchors = new Anchors(program, selectedMethods);
        program.regions.clear();
        anchors.root(program, anchors.authorities.keySet(),
                anchors.authorities::get, method -> false);
        anchors.root(program, communicationEndpoints(program),
                method -> "COMMUNICATION_ENTRY",
                method -> !program.regionsHolding(method).isEmpty());
        anchors.root(program, anchors.state, method -> STATE_WRITER_ENTRY,
                method -> false);
        declareCommunicationPorts(program);
        declareRetainedLoops(program);
    }

    /** The slice's call graph and the anchor kinds a skeleton is kept for. */
    private static final class Anchors {
        private final Set<String> selected = new LinkedHashSet<>();
        private final Map<String, Set<String>> outgoing =
                new LinkedHashMap<>();
        private final Map<String, String> authorities;
        private final Set<String> failure = new LinkedHashSet<>();
        /** Either capture of a wire value may own an occurrence. */
        private final Set<String> communication;
        private final Set<String> state = new LinkedHashSet<>();

        private Anchors(StaticProgram program,
                        Collection<String> selectedMethods) {
            if (selectedMethods != null) {
                selected.addAll(selectedMethods);
            }
            selected.remove("");
            communication = communicationEndpoints(program);
            communication.retainAll(selected);
            Set<String> demandedState = failureRelevantState(program.edges);
            for (String method : selected) {
                outgoing.put(method, new LinkedHashSet<>());
            }
            for (Map<String, Object> edge : program.edges) {
                String method = text(edge.get("method"));
                String transfer = text(edge.get("transferKind"));
                if (text(edge.get("toCell")).contains("#exception:")
                        && selected.contains(method)) {
                    failure.add(method);
                }
                if (("HEAP_READ".equals(transfer)
                        || "HEAP_WRITE".equals(transfer))
                        && selected.contains(method)
                        && !CausynthStaticFacts.constructor(method)
                        && demandedState.contains(stateDeclaration(edge,
                        transfer))) {
                    state.add(method);
                }
                String callee = StaticProgram.invocationTarget(edge);
                if (!selected.contains(method) || !selected.contains(callee)
                        || method.equals(callee)) {
                    continue;
                }
                outgoing.get(method).add(callee);
            }
            authorities = new LinkedHashMap<>(
                    program.executionContextAuthorities);
            for (Map<String, Object> edge : program.edges) {
                String method = text(edge.get("method"));
                if (selected.contains(method) && Boolean.TRUE.equals(
                        edge.get("explicitSymbolicFault"))) {
                    authorities.put(method, EXPLICIT_FAULT_ENTRY);
                }
            }
            String target = text(program.targetResolved.get("method"));
            if (!target.isEmpty()) {
                authorities.putIfAbsent(target, FAILURE_TARGET_ENTRY);
            }
        }

        /**
         * Roots a skeleton at each entry, in signature order, unless it is
         * unselected, already a root, {@code skipped}, or a constructor: no
         * execution context, but the target's own method is its region when
         * nothing encloses it (the weave enters it once {@code this} is
         * initialized).
         */
        private void root(StaticProgram program, Collection<String> entries,
                          Function<String, String> authority,
                          Predicate<String> skipped) {
            List<String> ordered = new ArrayList<>(entries);
            Collections.sort(ordered);
            for (String entry : ordered) {
                if (!selected.contains(entry)
                        || hasSkeletonRoot(program, entry)
                        || skipped.test(entry)) {
                    continue;
                }
                String kind = authority.apply(entry);
                if (CausynthStaticFacts.constructor(entry)
                        && !FAILURE_TARGET_ENTRY.equals(kind)) {
                    continue;
                }
                addSkeleton(program, entry, kind);
            }
        }

        /** One skeleton over the root's closure, if it holds an anchor. */
        private void addSkeleton(StaticProgram program, String root,
                                 String authority) {
            List<String> methods = forwardClosure(root, outgoing,
                    authorities);
            List<String> failed = intersections(methods, failure);
            List<String> communicating = intersections(methods,
                    communication);
            List<String> stateful = intersections(methods, state);
            boolean explicitFault = EXPLICIT_FAULT_ENTRY.equals(authority);
            List<String> fault = explicitFault
                    ? Collections.singletonList(root)
                    : Collections.<String>emptyList();
            List<String> anchors = union(fault, failed, communicating,
                    stateful);
            if (anchors.isEmpty()) {
                return;
            }
            Map<String, Object> row = skeletonRow(root, authority);
            row.put("anchorMethod", anchors.get(0));
            row.put("anchorMethods", anchors);
            row.put("methods", methods);
            row.put("selection", explicitFault
                    ? "EXPLICIT_FAULT_CONTEXT"
                    : !failed.isEmpty()
                    ? "EXCEPTION_CONTEXT"
                    : !communicating.isEmpty()
                    ? "COMMUNICATION_CONTEXT" : "STATE_CONTEXT");
            program.regions.add(row);
        }
    }

    /** Whether some skeleton is already rooted at {@code method}. */
    private static boolean hasSkeletonRoot(StaticProgram program,
                                           String method) {
        for (Map<String, Object> region : program.regions) {
            if (method.equals(text(region.get("rootMethod")))) {
                return true;
            }
        }
        return false;
    }

    /** Declares on each region the retained loops of the methods it holds. */
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

    /**
     * README section 3: declares every cut's ports on the regions owning its
     * two sides -- the producer's region gets an OUT, the consumer's an IN.
     * Composition substitutes the producer expression directly; both ends are
     * still declared so an absent or ambiguous handoff fails closed.  A value
     * held across a synchronous call stays in one region and has no port.
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

    /** Every declared producer and consumer capture method. */
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

    /** The declared fields the failure slice reads (HEAP_READ sources). */
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
