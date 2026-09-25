package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSymbolicInputs;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.SiteId;

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
import java.util.function.Function;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.asMap;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.strings;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/**
 * The one catalog the static analysis and its runtime finalization are both
 * indexed by: region rows, activations, edges, ports and loop sites.
 *
 * <p>Every per-key index is a method here, built once.  A row list is only
 * appended to or filtered, so its size plus the identity of its last row is
 * an exact staleness stamp for the indexes derived from it.</p>
 */
public final class StaticProgram {
    /** How a retained-loop identity spells its header unit. */
    private static final String LOOP_HEADER_MARKER = "#loop:u";

    final List<Map<String, Object>> edges = new ArrayList<>();
    final List<String> traceMethods = new ArrayList<>();
    /** Methods that are allowed to own a REGION activation. */
    final Map<String, String> executionContextAuthorities =
            new LinkedHashMap<>();
    final List<Map<String, Object>> regions = new ArrayList<>();
    final Map<String, Object> targetResolved = new LinkedHashMap<>();
    /** One {@code COMMUNICATION_CALL_SITE} row per selected call site. */
    final List<Map<String, Object>> communicationCallSites =
            new ArrayList<>();
    /** One row per retained loop of a selected method. */
    final List<Map<String, Object>> retainedLoops = new ArrayList<>();
    final List<Map<String, Object>> communicationGaps = new ArrayList<>();
    /**
     * Gaps the finalizer raised building ports (truncated activation-local
     * accesses, an accessor stream at snapshot capacity).  They reach the
     * runtime plan on {@code Result.gaps}: a port built from a truncated
     * history is a chain element no later stage sees whole.
     */
    final List<Map<String, Object>> planGaps = new ArrayList<>();
    /** Callees that are communication boundaries in the selected slice. */
    final Set<String> communicationCallSiteCallees = new LinkedHashSet<>();
    // Frozen runtime inputs of one finalization

    /** The runtime-refined dataflow rows this finalization reads. */
    List<Map<String, Object>> graph = Collections.emptyList();
    /** The selected region skeletons, decoded once, by region id. */
    final Map<String, RegionRow> skeletons = new LinkedHashMap<>();
    /** Minted region activations, by occurrence id. */
    final Map<String, Map<String, Object>> activations =
            new LinkedHashMap<>();

    // Indexes, each built once

    private Map<String, List<Map<String, Object>>> graphEdgesByRegion;
    private Map<String, List<String>> skeletonRegionIdsByMethod;
    private Map<String, List<Map<String, Object>>> cellIncoming;
    private Map<String, List<Map<String, Object>>> cellOutgoing;
    private String incomingRegion;
    private String outgoingRegion;
    private Map<String, List<Map<String, Object>>> activationsByRegion;
    private Map<String, Map<String, Object>> activationsById;
    private Map<String, Map<String, Object>> regionsById;
    private Map<String, List<String>> regionIdsByMethod;
    private Object regionStamp;
    private int regionCount = -1;

    /**
     * Graph rows indexed by every region that claims them.  Scoping is static:
     * read off the skeletons' {@code methods} sets by {@link
     * #skeletonRegionsHolding}, never off a recorded {@code regionIds}.
     */
    Map<String, List<Map<String, Object>>> edgesByRegion() {
        if (graphEdgesByRegion == null) {
            graphEdgesByRegion = new LinkedHashMap<>();
            for (Map<String, Object> edge : graph) {
                for (String regionId
                        : skeletonRegionsHolding(text(edge.get("method")))) {
                    graphEdgesByRegion.computeIfAbsent(regionId,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
        }
        return graphEdgesByRegion;
    }

    /**
     * The selected skeletons whose method set holds {@code method}.  Not
     * {@link #regionsHolding}: {@link #regions} is still being built (empty)
     * when the graph is first indexed; the skeletons are already complete.
     */
    List<String> skeletonRegionsHolding(String method) {
        if (skeletonRegionIdsByMethod == null) {
            skeletonRegionIdsByMethod = new LinkedHashMap<>();
            for (RegionRow skeleton : skeletons.values()) {
                for (String held : skeleton.methods) {
                    skeletonRegionIdsByMethod.computeIfAbsent(held,
                            ignored -> new ArrayList<>())
                            .add(skeleton.regionId);
                }
            }
        }
        if (method.isEmpty()) {
            return Collections.emptyList();
        }
        return skeletonRegionIdsByMethod.getOrDefault(method,
                Collections.<String>emptyList());
    }

    /** The minted activations of one region, in minting order. */
    List<Map<String, Object>> regionActivations(String regionId) {
        if (activationsByRegion == null) {
            activationsByRegion = new LinkedHashMap<>();
            for (Map<String, Object> activation : activations.values()) {
                activationsByRegion.computeIfAbsent(
                        text(activation.get("regionId")),
                        ignored -> new ArrayList<>()).add(activation);
            }
        }
        return activationsByRegion.getOrDefault(regionId,
                Collections.<Map<String, Object>>emptyList());
    }

    /** Minted activations by the recorded activation each one names. */
    Map<String, Map<String, Object>> activationsByActivationId() {
        if (activationsById == null) {
            activationsById = new LinkedHashMap<>();
            for (Map<String, Object> activation : activations.values()) {
                activationsById.put(text(activation.get("activationId")),
                        activation);
            }
        }
        return activationsById;
    }

    List<Map<String, Object>> regionGraph(String regionId) {
        return edgesByRegion().getOrDefault(regionId,
                Collections.<Map<String, Object>>emptyList());
    }

    /** One region's rows by the cell they flow into; caches one region. */
    Map<String, List<Map<String, Object>>> regionIncoming(String regionId) {
        if (!regionId.equals(incomingRegion)) {
            cellIncoming = index(regionGraph(regionId), "toCell");
            incomingRegion = regionId;
        }
        return cellIncoming;
    }

    /** The same adjacency by the cell a row flows out of. */
    Map<String, List<Map<String, Object>>> regionOutgoing(String regionId) {
        if (!regionId.equals(outgoingRegion)) {
            cellOutgoing = index(regionGraph(regionId), "fromCell");
            outgoingRegion = regionId;
        }
        return cellOutgoing;
    }

    /** The callee one dataflow edge names, dynamic dispatch included. */
    static String invocationTarget(Map<String, Object> edge) {
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

    Map<String, Map<String, Object>> regionsById() {
        indexRegions();
        return regionsById;
    }

    /** The regions whose method set holds {@code method}. */
    List<String> regionsHolding(String method) {
        if (method.isEmpty()) {
            return Collections.emptyList();
        }
        indexRegions();
        return regionIdsByMethod.getOrDefault(method,
                Collections.<String>emptyList());
    }

    private void indexRegions() {
        Object last = regions.isEmpty() ? null
                : regions.get(regions.size() - 1);
        if (regionCount == regions.size() && regionStamp == last) {
            return;
        }
        regionsById = new LinkedHashMap<>();
        regionIdsByMethod = new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            regionsById.put(regionId, region);
            for (String method : strings(region.get("methods"))) {
                regionIdsByMethod.computeIfAbsent(method,
                        ignored -> new ArrayList<>()).add(regionId);
            }
        }
        regionCount = regions.size();
        regionStamp = last;
    }

    /** Rows indexed by one endpoint field, in first-seen order. */
    private static Map<String, List<Map<String, Object>>> index(
            Collection<Map<String, Object>> rows, String field) {
        Map<String, List<Map<String, Object>>> index = new LinkedHashMap<>();
        for (Map<String, Object> row : rows) {
            String key = text(row.get(field));
            if (!key.isEmpty()) {
                index.computeIfAbsent(key,
                        ignored -> new ArrayList<>()).add(row);
            }
        }
        return index;
    }

    /** Whether one cell names a declared field rather than a local. */
    static boolean declaredField(String cell) {
        return cell.startsWith("<") && cell.endsWith(">")
                && cell.contains(":") && !cell.contains("(");
    }

    /**
     * The one breadth-first closure driver: FIFO from the seeds, each node
     * visited once, so result order is first-discovery order.  An adjacency
     * answering {@code null} ends the whole walk (early stop on a witness).
     */
    static <T> Set<T> closure(Collection<? extends T> seeds,
                              Function<T, Collection<T>> adjacency) {
        Set<T> visited = new LinkedHashSet<>();
        Deque<T> work = new ArrayDeque<>(seeds);
        while (!work.isEmpty()) {
            T node = work.removeFirst();
            if (!visited.add(node)) continue;
            Collection<T> next = adjacency.apply(node);
            if (next == null) break;
            work.addAll(next);
        }
        return visited;
    }

    // Root selection: the once-only-root rule

    /**
     * The loop body one region must be rooted at instead of its skeleton
     * root, or {@code null} when the root stands.
     *
     * <p>A once-entered root cannot admit an alias published later (VM frame
     * tracking is push-time), so for a service loop the iteration, not the
     * entry, is the activation.  Fires only when a caller of the anchor issues
     * the demanded call inside one of its retained loops ({@link
     * #serviceLoopCandidate}) and the trace saw that loop decide its
     * continuation more than once in one activation.  The innermost such loop
     * wins.</p>
     */
    Map<String, Object> loopBodyRoot(
            RegionRow skeleton,
            Collection<Map<String, Object>> regionActivations,
            List<Map<String, Object>> branchObservations) {
        String anchor = skeleton.anchorMethod;
        String root = skeleton.rootMethod;
        Map<String, List<Map<String, Object>>> loopsByMethod =
                serviceLoops(skeleton);
        if (anchor.isEmpty() || loopsByMethod.isEmpty()) {
            return null;
        }
        Set<String> iterated = loopsIteratedWithinActivation(loopsByMethod,
                regionActivations, branchObservations);
        if (iterated.isEmpty()) {
            return null;
        }
        Map<String, List<String>> callSites = callSitesByCallee(
                skeleton.regionId);
        Set<String> visited = new LinkedHashSet<>();
        List<String> frontier = Collections.singletonList(anchor);
        while (!frontier.isEmpty()) {
            Set<String> next = new TreeSet<>();
            for (String callee : frontier) {
                if (!visited.add(callee)) continue;
                for (String site : callSites.getOrDefault(callee,
                        Collections.<String>emptyList())) {
                    String caller = site.substring(0, site.lastIndexOf("#u"));
                    int unitIndex = SiteId.unitIndexOf(site);
                    for (Map<String, Object> loop
                            : loopsByMethod.getOrDefault(caller,
                            Collections.<Map<String, Object>>emptyList())) {
                        if (iterated.contains(text(loop.get(
                                LoopBoundPolicy.RUNTIME_LOOP_ID)))
                                && loopContains(loop, unitIndex)) {
                            return rootLoop(loop, caller, unitIndex);
                        }
                    }
                    // The walk stops at the root.
                    if (!caller.equals(root)) next.add(caller);
                }
            }
            next.removeAll(visited);
            frontier = new ArrayList<>(next);
        }
        // The root method itself may hold the service loop.
        int demanded = Integer.MAX_VALUE;
        for (List<String> sites : callSites.values()) {
            for (String site : sites) {
                if (site.startsWith(root + "#u")) {
                    demanded = Math.min(demanded,
                            SiteId.unitIndexOf(site));
                }
            }
        }
        if (demanded != Integer.MAX_VALUE) {
            for (Map<String, Object> loop : loopsByMethod.getOrDefault(root,
                    Collections.<Map<String, Object>>emptyList())) {
                if (iterated.contains(text(loop.get(
                        LoopBoundPolicy.RUNTIME_LOOP_ID)))
                        && loopContains(loop, demanded)) {
                    return rootLoop(loop, root, demanded);
                }
            }
        }
        return null;
    }

    /** The region's retained loops that could be a service loop, by owner. */
    private Map<String, List<Map<String, Object>>> serviceLoops(
            RegionRow skeleton) {
        Map<String, List<Map<String, Object>>> byMethod =
                new LinkedHashMap<>();
        for (Map<String, Object> loop : skeleton.retainedLoops) {
            String owner = text(loop.get("enclosingMethod"));
            if (owner.isEmpty() || !serviceLoopCandidate(skeleton, loop,
                    owner)) {
                continue;
            }
            byMethod.computeIfAbsent(owner,
                    ignored -> new ArrayList<>()).add(loop);
        }
        return byMethod;
    }

    /**
     * Whether one retained loop may be the region's service loop.
     *
     * <p>{@code CONDITION_BOUNDED}: always.  {@code FIXED_COUNT_INDEXED}: only
     * when one iteration is one unit of demanded work -- the body (or a callee)
     * defines a declared wire port, or the body writes a declared field.</p>
     *
     * <p>Trap: a loop inside a port's FRAME METHOD walks the leaves of ONE
     * message ({@code SymbolicMessageEnvelope} addresses leaves by {@code
     * (frame, port, ordinal)}), so it never qualifies; rooting there leaves the
     * frame's leaves outside the loop with no activation, and the whole
     * message is dropped downstream.</p>
     */
    private boolean serviceLoopCandidate(RegionRow skeleton,
                                         Map<String, Object> loop,
                                         String owner) {
        String classification = text(loop.get(
                LoopBoundPolicy.LOOP_CLASSIFICATION));
        if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(classification)) {
            return true;
        }
        if (!LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(classification)) {
            return false;
        }
        Set<String> calledInLoop = new LinkedHashSet<>();
        for (Map<String, Object> edge : regionGraph(skeleton.regionId)) {
            if (!owner.equals(text(edge.get("method")))
                    || !loopContains(loop, number(edge.get("unitIndex"), -1))) {
                continue;
            }
            String callee = invocationTarget(edge);
            if (!callee.isEmpty()) calledInLoop.add(callee);
            if ("HEAP_WRITE".equals(text(edge.get("transferKind")))
                    && declaredField(text(edge.get("toCell")))) {
                return true;
            }
        }
        for (Map<String, Object> port : skeleton.communicationPorts) {
            String definition = text(port.get(CommunicationCatalogContract
                    .PORT_DEFINITION_METHOD));
            if (definition.isEmpty()) continue;
            // A loop in the port's frame walks one message's leaves.
            if (owner.equals(text(port.get(CommunicationCatalogContract
                    .PORT_FRAME_METHOD)))) {
                continue;
            }
            if (calledInLoop.contains(definition)) {
                return true;
            }
            if (owner.equals(definition) && loopContains(loop, number(
                    port.get(CommunicationCatalogContract
                            .PORT_DEFINITION_UNIT_INDEX), -1))) {
                return true;
            }
        }
        return false;
    }

    /** The published loop body a re-rooted region names. */
    private static Map<String, Object> rootLoop(Map<String, Object> loop,
                                                String caller,
                                                int unitIndex) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 1);
        row.put("authority", LoopBoundPolicy.LOOP_BODY_ROOT);
        row.put(LoopBoundPolicy.ROOT_LOOP_METHOD, caller);
        row.put(LoopBoundPolicy.RUNTIME_LOOP_ID,
                loop.get(LoopBoundPolicy.RUNTIME_LOOP_ID));
        row.put(LoopBoundPolicy.LOOP_SITE_ID,
                loop.get(LoopBoundPolicy.LOOP_SITE_ID));
        row.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS,
                loop.get(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS));
        row.put(LoopBoundPolicy.HEADER_UNIT_INDEX, loopHeaderUnitIndex(
                text(loop.get(LoopBoundPolicy.RUNTIME_LOOP_ID))));
        row.put(LoopBoundPolicy.DEMANDED_UNIT_INDEX, unitIndex);
        return row;
    }

    /** Every call this region's rows name, as {@code callee -> [method#uN]}. */
    private Map<String, List<String>> callSitesByCallee(String regionId) {
        Map<String, Set<String>> sites = new LinkedHashMap<>();
        for (Map<String, Object> edge : regionGraph(regionId)) {
            String caller = text(edge.get("method"));
            String callee = invocationTarget(edge);
            int unitIndex = number(edge.get("unitIndex"), -1);
            if (caller.isEmpty() || callee.isEmpty() || unitIndex < 0
                    || caller.equals(callee)) {
                continue;
            }
            sites.computeIfAbsent(callee, ignored -> new TreeSet<String>())
                    .add(SiteId.of(caller, unitIndex));
        }
        Map<String, List<String>> result = new LinkedHashMap<>();
        for (Map.Entry<String, Set<String>> entry : sites.entrySet()) {
            result.put(entry.getKey(), new ArrayList<>(entry.getValue()));
        }
        return result;
    }

    /** Loops seen deciding continuation twice in one call of an activation. */
    private static Set<String> loopsIteratedWithinActivation(
            Map<String, List<Map<String, Object>>> loopsByMethod,
            Collection<Map<String, Object>> regionActivations,
            List<Map<String, Object>> branchObservations) {
        Map<String, String> loopByControlSite = new LinkedHashMap<>();
        for (List<Map<String, Object>> loops : loopsByMethod.values()) {
            for (Map<String, Object> loop : loops) {
                for (String site : strings(loop.get(
                        LoopBoundPolicy.LOOP_CONTROL_SITE_IDS))) {
                    loopByControlSite.put(site, text(loop.get(
                            LoopBoundPolicy.RUNTIME_LOOP_ID)));
                }
            }
        }
        Map<String, Integer> decisionsPerCall = new LinkedHashMap<>();
        Map<String, Set<Long>> callsOfRepeatedLoop = new LinkedHashMap<>();
        for (Map<String, Object> observation : branchObservations) {
            String loopId = loopByControlSite.get(
                    text(observation.get("siteId")));
            long callId = longNumber(observation.get("callId"), -1L);
            if (loopId == null || callId < 0L) continue;
            String decision = loopId + "\n" + callId;
            int count = decisionsPerCall.getOrDefault(decision, 0) + 1;
            decisionsPerCall.put(decision, count);
            if (count > 1) {
                callsOfRepeatedLoop.computeIfAbsent(loopId,
                        ignored -> new LinkedHashSet<>()).add(callId);
            }
        }
        Set<String> iterated = new LinkedHashSet<>();
        for (Map<String, Object> activation : regionActivations) {
            Set<Long> calls = MapFields.longValues(activation.get("callIds"));
            for (Map.Entry<String, Set<Long>> entry
                    : callsOfRepeatedLoop.entrySet()) {
                if (!Collections.disjoint(entry.getValue(), calls)) {
                    iterated.add(entry.getKey());
                }
            }
        }
        return iterated;
    }

    /** The index after the loop-header marker in a loop identity, or -1. */
    private static int loopHeaderUnitIndex(String site) {
        int at = site.lastIndexOf(LOOP_HEADER_MARKER);
        if (at < 0) return -1;
        try {
            return Integer.parseInt(site.substring(
                    at + LOOP_HEADER_MARKER.length()));
        } catch (NumberFormatException notAUnit) {
            return -1;
        }
    }

    /** Whether {@code unitIndex} lies between the loop's header and its end. */
    static boolean loopContains(Map<String, Object> loop,
                                int unitIndex) {
        int header = loopHeaderUnitIndex(text(loop.get(
                LoopBoundPolicy.RUNTIME_LOOP_ID)));
        if (header < 0 || unitIndex < header) return false;
        // End at the latch too: a while(true) loop's only guard is the header.
        int last = number(loop.get(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX),
                header);
        for (String site : strings(loop.get(
                LoopBoundPolicy.LOOP_CONTROL_SITE_IDS))) {
            last = Math.max(last, SiteId.unitIndexOf(site));
        }
        return unitIndex <= last;
    }

    /**
     * One {@code REGION_SKELETON} or {@code SYMBOLIC_REGION} row, decoded once
     * into typed final members; decode refuses any other shape.
     */
    public static final class RegionRow {
        /** The undecoded row, for the writers that republish it verbatim. */
        public final Map<String, Object> json;
        public final String regionId;
        public final String rootMethod;
        public final String rootAuthority;
        /**
         * Whether {@code symbolic-inputs.jsonl} names this root; stamped by
         * the skeleton planner so no later stage re-reads the case file.
         */
        public final boolean declaredInputRoot;
        /** The loop body this region is re-rooted at, or {@code null}. */
        public final Map<String, Object> rootLoop;
        public final String anchorMethod;
        public final String selection;
        /** The admission anchors, the single {@code anchorMethod} included. */
        public final List<String> anchorMethods;
        public final List<String> methods;
        public final List<String> runtimeOccurrenceIds;
        public final List<String> sourcePhaseTraceMethods;
        public final List<Map<String, Object>> retainedLoops;
        public final List<Map<String, Object>> communicationPorts;
        public final List<Map<String, Object>> symbolicInputs;
        public final List<Map<String, Object>> outputs;
        public final List<Map<String, Object>> branchPolicies;
        private final Object sourcePhaseCatalog;
        private Map<String, ConfiguredSourcePhaseContract.Declaration>
                sourcePhasesBySite;

        private RegionRow(Map<String, Object> row, String kind,
                          Object source) {
            if (number(row.get("schemaVersion"), -1)
                    != RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION
                    || !kind.equals(text(row.get("kind")))) {
                throw new IllegalArgumentException("invalid " + kind
                        + " row in " + source);
            }
            json = row;
            // JSON null reads as absent.
            regionId = stringValue(row.get("regionId"));
            rootMethod = stringValue(row.get("rootMethod"));
            rootAuthority = stringValue(row.get(
                    LoopBoundPolicy.ROOT_AUTHORITY));
            rootLoop = asMap(row.get(LoopBoundPolicy.ROOT_LOOP));
            declaredInputRoot = Boolean.TRUE.equals(
                    row.get(DeclaredSymbolicInputs.ROOT_FIELD));
            anchorMethod = stringValue(row.get("anchorMethod"));
            selection = stringValue(row.get("selection"));
            methods = strings(row.get("methods"));
            if (regionId.isEmpty() || rootMethod.isEmpty()
                    || !methods.contains(rootMethod)
                    || !anchorMethod.isEmpty()
                    && !methods.contains(anchorMethod)) {
                throw new IllegalArgumentException(kind + " " + regionId
                        + " must name a root and an anchor its method set"
                        + " holds, in " + source);
            }
            anchorMethods = strings(row.get("anchorMethods"));
            if (anchorMethods.isEmpty() && !anchorMethod.isEmpty()) {
                anchorMethods.add(anchorMethod);
            }
            runtimeOccurrenceIds = strings(row.get("runtimeOccurrenceIds"));
            sourcePhaseTraceMethods = strings(row.get(
                    ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD));
            retainedLoops = rows(row.get(
                    RuntimeSelectedRegionFinalizer.RETAINED_LOOPS));
            communicationPorts = rows(row.get(
                    RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS));
            symbolicInputs = rows(row.get("symbolicInputs"));
            outputs = rows(row.get("outputs"));
            branchPolicies = rows(row.get("branchPolicies"));
            sourcePhaseCatalog = row.get(
                    ConfiguredSourcePhaseContract.DECLARATION_FIELD);
        }

        /**
         * Declared configured-source hook sites by {@code siteId}, decoded
         * lazily so an unread malformed catalog never refuses a run.
         */
        public Map<String, ConfiguredSourcePhaseContract.Declaration>
                sourcePhasesBySite() {
            if (sourcePhasesBySite != null) return sourcePhasesBySite;
            sourcePhasesBySite = new LinkedHashMap<>();
            final List<ConfiguredSourcePhaseContract.Declaration> declared;
            try {
                declared = ConfiguredSourcePhaseContract.declarationsOf(
                        JsonFields.WRITER.toJsonTree(sourcePhaseCatalog));
            } catch (IllegalArgumentException malformed) {
                throw new IllegalArgumentException(
                        "malformed configured-source phase catalog for "
                                + regionId, malformed);
            }
            for (ConfiguredSourcePhaseContract.Declaration declaration
                    : declared) {
                if (sourcePhasesBySite.putIfAbsent(declaration.siteId(),
                        declaration) != null) {
                    throw new IllegalArgumentException(
                            "configured-source phase site "
                            + declaration.siteId() + " is declared more than"
                            + " once in " + regionId);
                }
            }
            return sourcePhasesBySite;
        }
    }

    /** Decodes region rows of one kind, refusing a duplicated identity. */
    public static List<RegionRow> regionRows(
            Collection<Map<String, Object>> rows, String kind,
            Object source) {
        List<RegionRow> decoded = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        for (Map<String, Object> row : rows) {
            RegionRow region = new RegionRow(row, kind, source);
            if (!ids.add(region.regionId)) {
                throw new IllegalArgumentException("duplicate " + kind
                        + " regionId: " + region.regionId);
            }
            decoded.add(region);
        }
        return decoded;
    }
}
