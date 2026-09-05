package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.concolic.JsonFields;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

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
 * The one catalog a static analysis run and its runtime finalization are both
 * indexed by: region skeleton rows, runtime occurrences, edges (typed
 * communication ports and leaves, dataflow edges) and loop sites.
 *
 * <p>Every per-key index the planner and the finalizer used to rebuild in
 * place -- by occurrence, by region, by site, by edge endpoint, by port -- is
 * a method here, built once from the artifact lists and the frozen runtime
 * trace inputs.  A row list is only ever appended to or filtered, never
 * replaced element-wise, so its size together with the identity of its last
 * row is an exact staleness stamp for the indexes derived from it.</p>
 */
public final class StaticProgram {
    final List<Map<String, Object>> edges = new ArrayList<>();
    final List<String> traceMethods = new ArrayList<>();
    /** Methods that are allowed to own a REGION activation. */
    final Map<String, String> executionContextAuthorities =
            new LinkedHashMap<>();
    final List<Map<String, Object>> regions = new ArrayList<>();
    final List<Map<String, Object>> regionEdges = new ArrayList<>();
    final Map<String, Object> targetResolved = new LinkedHashMap<>();
    /**
     * Static communication discovery: one row per target-selected
     * communication call site ({@code COMMUNICATION_CALL_SITE}) and one row
     * per named gap.
     */
    final List<Map<String, Object>> communicationCallSites =
            new ArrayList<>();
    /** One row per retained loop of a selected method. */
    final List<Map<String, Object>> retainedLoops = new ArrayList<>();
    final List<Map<String, Object>> communicationGaps = new ArrayList<>();
    /**
     * Callee signatures that are communication boundaries in the selected
     * slice.
     */
    final Set<String> communicationCallSiteCallees = new LinkedHashSet<>();
    // ------------------------------------------------------------------
    // Frozen runtime inputs of one finalization
    // ------------------------------------------------------------------

    /** The runtime-refined dataflow rows this finalization reads. */
    List<Map<String, Object>> refinedGraph = Collections.emptyList();
    /** The selected region skeletons, by region id. */
    final Map<String, Map<String, Object>> skeletons = new LinkedHashMap<>();
    /** Minted region activations, by occurrence id. */
    final Map<String, Map<String, Object>> activations =
            new LinkedHashMap<>();

    // ------------------------------------------------------------------
    // Indexes, each built once
    // ------------------------------------------------------------------

    private Map<String, List<Map<String, Object>>> refinedEdgesByRegion;
    private Map<String, Set<String>> callersByCallee;
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

    /** Refined-graph rows indexed by every region that claims them. */
    Map<String, List<Map<String, Object>>> edgesByRegion() {
        if (refinedEdgesByRegion == null) {
            refinedEdgesByRegion = new LinkedHashMap<>();
            for (Map<String, Object> edge : refinedGraph) {
                for (String regionId : strings(edge.get("regionIds"))) {
                    refinedEdgesByRegion.computeIfAbsent(regionId,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
        }
        return refinedEdgesByRegion;
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

    /** The refined rows one region claims, in first-seen order. */
    List<Map<String, Object>> regionGraph(String regionId) {
        return edgesByRegion().getOrDefault(regionId,
                Collections.<Map<String, Object>>emptyList());
    }

    /**
     * One region's rows indexed by the cell they flow into.  Every consumer
     * inside one region's stage asks for the same adjacency, so it is built
     * once for the region being worked on rather than once per consumer, and
     * released as soon as the next region starts.
     */
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

    /** Reverse selected invocation index, built once for all client cuts. */
    Map<String, Set<String>> invocationCallers() {
        if (callersByCallee == null) {
            callersByCallee = new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
                String caller = text(edge.get("method"));
                String callee = invocationTarget(edge);
                if (!caller.isEmpty() && !callee.isEmpty()
                        && !caller.equals(callee)) {
                    callersByCallee.computeIfAbsent(callee,
                            ignored -> new TreeSet<String>()).add(caller);
                }
            }
        }
        return callersByCallee;
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

    /** Region rows by their identity. */
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

    /** The recorded call identities one row names. */
    static Set<Long> longValues(Object value) {
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
     * The single breadth-first closure driver of the static planner and the
     * runtime finalizer: FIFO from the seeds, every node visited once, so the
     * visitation order a caller keys its result by is the order of first
     * discovery.  An adjacency that answers {@code null} ends the whole walk,
     * which is how a caller that only needs the first witness stops early.
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

    // ------------------------------------------------------------------
    // Root selection: the once-only-root rule
    // ------------------------------------------------------------------

    /**
     * Answers the loop body one region has to be rooted at instead of its
     * skeleton root, or {@code null} when today's root stands.
     *
     * <p>A root that is entered once per activation cannot admit a receiver
     * alias that arrives later: VM frame tracking is push-time, so an address
     * published after the root frame was pushed never reaches that activation.
     * A service loop is exactly that shape -- one entry, many iterations, one
     * unit of demanded work per iteration -- so the per-iteration boundary,
     * not the entry, is the activation the region describes.</p>
     *
     * <p>The rule fires only on positive evidence of that shape:</p>
     * <ul>
     *   <li>a caller of the region's anchor issues the demanded call from
     *       inside one of its own dominance-proved natural loops, within the
     *       extent the retained-loop row publishes -- from the loop's header
     *       to its last exiting branch;</li>
     *   <li>that loop is {@code CONDITION_BOUNDED}: an indexed walk bounded by
     *       an array cardinality is not a service loop;</li>
     *   <li>the trace observed the loop deciding its own continuation more
     *       than once inside a single activation, which is what makes the root
     *       once-entered relative to the demanded work.</li>
     * </ul>
     *
     * <p>The innermost such loop wins: the walk leaves the anchor and takes
     * the first caller that answers, so a service loop nested inside another
     * names the finer boundary.  Nothing here changes how the runtime admits
     * addresses; it names the boundary the runtime planner and the
     * instrumenter key on.</p>
     */
    Map<String, Object> loopBodyRoot(
            Map<String, Object> skeleton,
            Collection<Map<String, Object>> regionActivations,
            List<Map<String, Object>> branchObservations) {
        String anchor = text(skeleton.get("anchorMethod"));
        String root = text(skeleton.get("rootMethod"));
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
                text(skeleton.get("regionId")));
        Set<String> visited = new LinkedHashSet<>();
        List<String> frontier = Collections.singletonList(anchor);
        while (!frontier.isEmpty()) {
            Set<String> next = new TreeSet<>();
            for (String callee : frontier) {
                if (!visited.add(callee)) continue;
                for (String site : callSites.getOrDefault(callee,
                        Collections.<String>emptyList())) {
                    String caller = site.substring(0, site.lastIndexOf("#u"));
                    int unitIndex = unitIndex(site, "#u");
                    for (Map<String, Object> loop
                            : loopsByMethod.getOrDefault(caller,
                            Collections.<Map<String, Object>>emptyList())) {
                        if (iterated.contains(text(loop.get(
                                LoopBoundPolicy.RUNTIME_LOOP_ID)))
                                && loopContains(loop, unitIndex)) {
                            return rootLoop(loop, caller, unitIndex);
                        }
                    }
                    // The root bounds the walk: above it the region does not
                    // reach.
                    if (!caller.equals(root)) next.add(caller);
                }
            }
            next.removeAll(visited);
            frontier = new ArrayList<>(next);
        }
        // The root method itself may be the once-entered service loop: then
        // the body containing the region's own call sites is the root.
        int demanded = Integer.MAX_VALUE;
        for (List<String> sites : callSites.values()) {
            for (String site : sites) {
                if (site.startsWith(root + "#u")) {
                    demanded = Math.min(demanded, unitIndex(site, "#u"));
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
    private static Map<String, List<Map<String, Object>>> serviceLoops(
            Map<String, Object> skeleton) {
        Map<String, List<Map<String, Object>>> byMethod =
                new LinkedHashMap<>();
        for (Map<String, Object> loop : rows(skeleton.get(
                RuntimeSelectedRegionFinalizer.RETAINED_LOOPS))) {
            String owner = text(loop.get("enclosingMethod"));
            if (owner.isEmpty() || !LoopBoundPolicy.LOOP_CONDITION_BOUNDED
                    .equals(text(loop.get(
                            LoopBoundPolicy.LOOP_CLASSIFICATION)))) {
                continue;
            }
            byMethod.computeIfAbsent(owner,
                    ignored -> new ArrayList<>()).add(loop);
        }
        return byMethod;
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
        row.put(LoopBoundPolicy.HEADER_UNIT_INDEX, unitIndex(text(loop.get(
                LoopBoundPolicy.RUNTIME_LOOP_ID)), "#loop:u"));
        row.put("demandedUnitIndex", unitIndex);
        return row;
    }

    /**
     * Every call this region's rows name, as {@code callee -> [method#uN]}.
     */
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
                    .add(caller + "#u" + unitIndex);
        }
        Map<String, List<String>> result = new LinkedHashMap<>();
        for (Map.Entry<String, Set<String>> entry : sites.entrySet()) {
            result.put(entry.getKey(), new ArrayList<>(entry.getValue()));
        }
        return result;
    }

    /**
     * The candidate loops the trace observed deciding their own continuation
     * more than once inside one activation.  A loop's continuation is decided
     * once per iteration in the frame that runs it, so the recorded call the
     * decision belongs to is the unit both counted and joined on.
     */
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
            Set<Long> calls = longValues(activation.get("callIds"));
            for (Map.Entry<String, Set<Long>> entry
                    : callsOfRepeatedLoop.entrySet()) {
                if (!Collections.disjoint(entry.getValue(), calls)) {
                    iterated.add(entry.getKey());
                }
            }
        }
        return iterated;
    }

    /**
     * Whether {@code unitIndex} lies in the extent a retained-loop row
     * publishes: from the loop's dominance-proved header to its last exiting
     * branch.
     */
    private static boolean loopContains(Map<String, Object> loop,
                                        int unitIndex) {
        int header = unitIndex(text(loop.get(
                LoopBoundPolicy.RUNTIME_LOOP_ID)), "#loop:u");
        if (header < 0 || unitIndex < header) return false;
        // The body ends at the loop's latch; a while(true) service loop keeps
        // its only guard at the header, so the guards alone would exclude
        // the whole body.
        int last = number(loop.get(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX),
                header);
        for (String site : strings(loop.get(
                LoopBoundPolicy.LOOP_CONTROL_SITE_IDS))) {
            last = Math.max(last, unitIndex(site, "#u"));
        }
        return unitIndex <= last;
    }

    private static int unitIndex(String site, String marker) {
        int at = site.lastIndexOf(marker);
        if (at < 0) return -1;
        try {
            return Integer.parseInt(site.substring(at + marker.length()));
        } catch (NumberFormatException notAUnit) {
            return -1;
        }
    }

    // ------------------------------------------------------------------
    // RegionRow: the one decode of a region row
    // ------------------------------------------------------------------

    /**
     * One region row -- a static {@code REGION_SKELETON} or the runtime
     * {@code SYMBOLIC_REGION} refined from it -- decoded once into typed
     * members.  Consumers take this object; nobody re-reads the map behind
     * it, and decode refuses a row of any other shape.  Members are final
     * and read directly, as on the trace event rows.
     */
    public static final class RegionRow {
        /** The undecoded row, for the writers that republish it verbatim. */
        public final Map<String, Object> json;
        public final String regionId;
        public final String rootMethod;
        public final String rootAuthority;
        /** The loop body this region is re-rooted at, or {@code null}. */
        public final Map<String, Object> rootLoop;
        public final String anchorMethod;
        public final String selection;
        public final String graphKind;
        /** The admission anchors, the single {@code anchorMethod} included. */
        public final List<String> anchorMethods;
        public final List<String> methods;
        public final List<String> demandScopeMethods;
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
            // The JSON null literal reads as absent, the way every consumer
            // of these members compares them.
            regionId = stringValue(row.get("regionId"));
            rootMethod = stringValue(row.get("rootMethod"));
            rootAuthority = stringValue(row.get(
                    LoopBoundPolicy.ROOT_AUTHORITY));
            rootLoop = asMap(row.get(LoopBoundPolicy.ROOT_LOOP));
            anchorMethod = stringValue(row.get("anchorMethod"));
            selection = stringValue(row.get("selection"));
            graphKind = stringValue(row.get("graphKind"));
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
            demandScopeMethods = strings(row.get(
                    RuntimeSelectedRegionFinalizer.DEMAND_SCOPE));
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
         * The declared configured-source hook sites, by {@code siteId},
         * decoded on first use.  A region no activation plans states a
         * catalog no stage has to accept, so decoding it eagerly would
         * refuse a run over a declaration nothing reads.
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
