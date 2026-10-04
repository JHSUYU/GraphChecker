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
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/** Builds candidate region skeletons around execution-context entries. */
final class SymbolicRegionPlanner {
    /** A demanded shared-state writer no enclosing task region can own. */
    static final String STATE_WRITER_ENTRY = "STATE_WRITER_ENTRY";
    /**
     * An explicit fault call is itself a replayable request boundary, where
     * no execution context already roots its method.
     */
    static final String EXPLICIT_FAULT_ENTRY = "EXPLICIT_FAULT_ENTRY";
    /** The declared target's own method, when no entry encloses it. */
    static final String FAILURE_TARGET_ENTRY = "FAILURE_TARGET_ENTRY";
    private SymbolicRegionPlanner() {
    }

    /**
     * @param doors the demanded doors the pass wove ({@link DemandedDoors}):
     *              each roots nothing; the methods of its chain join the
     *              regions holding the chain's first method
     */
    static void planSelectedSkeleton(
            StaticProgram program, Collection<String> selectedMethods,
            List<DemandedDoors.Site> doors) {
        Anchors anchors = new Anchors(program, selectedMethods);
        program.regions.clear();
        anchors.root(program, anchors.authorities.keySet(),
                anchors.authorities::get, method -> false);
        anchors.root(program, communicationEndpoints(program),
                method -> "COMMUNICATION_ENTRY",
                method -> !program.regionsHolding(method).isEmpty());
        anchors.root(program, anchors.state, method -> STATE_WRITER_ENTRY,
                method -> false);
        fold(program, doors);
        declareCommunicationPorts(program);
        declareRetainedLoops(program);
    }

    /**
     * A demanded door's marker is read in the occurrence that runs the
     * demanded site it was chosen for (SYMBOL-SCOPE §4.6): the methods of
     * its chain, from the site's method down to the door's caller, join
     * every region holding the site's method.  No root is added, so no
     * address moves (a utility method rooted as a fault entry opened
     * occurrences wherever it ran, and the test thread's DataNode starts
     * lost their hop: hdfs-adhoc-26, DECLARED_TARGET_BEFORE_WINDOW).
     */
    private static void fold(StaticProgram program,
                             List<DemandedDoors.Site> doors) {
        for (DemandedDoors.Site door : doors) {
            for (Map<String, Object> region : program.regions) {
                @SuppressWarnings("unchecked")
                List<String> methods = (List<String>) region.get("methods");
                if (!methods.contains(door.via.get(0))) continue;
                Set<String> held = new java.util.TreeSet<>(methods);
                held.addAll(door.via);
                region.put("methods", new ArrayList<>(held));
            }
        }
    }

    /** The slice's call graph and the anchor kinds a skeleton is kept for. */
    private static final class Anchors {
        private final Set<String> selected = new LinkedHashSet<>();
        private final Map<String, Set<String>> outgoing =
                new LinkedHashMap<>();
        private final Map<String, String> authorities;
        private final Set<String> failure = new LinkedHashSet<>();
        /** Methods that read an explicit fault marker (a woven door). */
        private final Set<String> faults = new LinkedHashSet<>();
        /** Any capture of a wire value may own an occurrence. */
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
            // A door woven into a method that is already an execution
            // context or the target's own method (a door at calls:
            // PacketResponder#run parses its pipeline's ack) leaves it that
            // region: its address and its selection stay what they were
            // without the door.
            authorities = new LinkedHashMap<>(
                    program.executionContextAuthorities);
            String target = text(program.targetResolved.get("method"));
            if (!target.isEmpty()) {
                authorities.putIfAbsent(target, FAILURE_TARGET_ENTRY);
            }
            // A demanded door's marker roots nothing (fold).
            for (Map<String, Object> edge : program.edges) {
                String method = text(edge.get("method"));
                if (selected.contains(method) && Boolean.TRUE.equals(
                        edge.get("explicitSymbolicFault"))
                        && !LibraryCatalog.demandedMarker(
                        text(edge.get("symbolicName")))) {
                    faults.add(method);
                    authorities.putIfAbsent(method, EXPLICIT_FAULT_ENTRY);
                }
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
            boolean explicitFault = faults.contains(root);
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
            // A region holding the failure is its exception context, a door
            // in it or not: the failure closure starts from those alone.
            row.put("selection", !failed.isEmpty()
                    ? "EXCEPTION_CONTEXT"
                    : explicitFault
                    ? "EXPLICIT_FAULT_CONTEXT"
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
     * SYMBOL-SCOPE §6: declares every capture of every port on the regions
     * holding it -- a producer's region gets an OUT, a consumer's an IN.
     * Composition binds the consumer's v_H to the producer's expression
     * through a message family (PIPELINE §8); both ends are declared so an
     * absent or ambiguous handoff fails closed.  A value
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

    /** Declares every producer and consumer of one wire port. */
    private static void declareWirePort(
            StaticProgram program, Map<String, Object> site,
            Map<String, Map<String, Map<String, Object>>> byRegion) {
        for (Map<String, Object> producer : rows(site.get(
                CommunicationCatalogContract.PORT_PRODUCERS))) {
            declareWireEndpoint(program, site, producer, "OUT", byRegion);
        }
        for (Map<String, Object> consumer : rows(site.get(
                CommunicationCatalogContract.PORT_CONSUMERS))) {
            declareWireEndpoint(program, site, consumer, "IN", byRegion);
        }
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
                    CommunicationCatalogContract.EXCHANGE_SITE_KEY}) {
                row.put(field, flow.get(field));
            }
            row.put(CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                    portId);
            row.putAll(capture);
            ports.putIfAbsent(CommunicationCatalogContract.captureKey(side,
                    row), row);
        }
        if (regions.isEmpty()) {
            program.communicationGaps.add(CommunicationCatalogPlanner.gap(
                    GapKind.COMMUNICATION_REQUEST_PORT_UNRESOLVED,
                    GapClass.BLOCKING,
                    "NO_REGION_HOLDS_WIRE_CAPTURE", method,
                    text(capture.get(
                            CommunicationCatalogContract.CALL_SITE_ID)),
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

    /** Every capture method of every wire port. */
    private static Set<String> communicationEndpoints(
            StaticProgram program) {
        Set<String> entries = new LinkedHashSet<>();
        for (Map<String, Object> site : program.communicationCallSites) {
            for (String side : new String[]{
                    CommunicationCatalogContract.PORT_PRODUCERS,
                    CommunicationCatalogContract.PORT_CONSUMERS}) {
                for (Map<String, Object> capture : rows(site.get(side))) {
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
                // A static final field -- a constant, an enum switch map --
                // is no state an occurrence shares.
                if ("HEAP_READ".equals(transfer)
                        && StaticProgram.declaredField(source)
                        && !CausynthStaticFacts.constantField(source)) {
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
