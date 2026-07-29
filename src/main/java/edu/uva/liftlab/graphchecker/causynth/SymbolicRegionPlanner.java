package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Lifts method-level symbolic guidance into demand-driven, same-thread regions.
 *
 * <p>The planner intentionally produces an over-approximation. Runtime call
 * trees later choose an invocation-specific subset and resolve virtual calls.
 * The unit of concolic execution is a region, not an individual edge.</p>
 */
final class SymbolicRegionPlanner {
    private static final int REGION_SCHEMA_VERSION = 2;
    private static final int MAX_ANCHORS = 16;
    private static final int MAX_REGIONS = 64;
    private static final int MAX_REGION_METHODS = 64;
    private static final int MAX_PARENT_DEPTH = 8;
    private static final int MAX_PARENTS_PER_METHOD = 4;
    private static final int MAX_PORTS = 128;
    private static final int MAX_BACKWARD_SLICE_CELLS = 20000;
    /**
     * Requested-output slices are more precise than the broad region method
     * closure and may therefore retain a larger, independently bounded set of
     * same-thread helpers.  Hitting this limit is a structural completeness
     * failure; runtime refinement may remove unobserved alternatives, but it
     * must never repair a statically truncated dependency walk.
     */
    private static final int MAX_REQUESTED_OUTPUT_SLICE_METHODS = 256;
    /**
     * Total input-port budget after requested-output dependency promotion.
     *
     * <p>{@link #MAX_PORTS} deliberately bounds the broad, region-wide
     * frontier.  A requested-output slice is substantially more precise: it
     * may promote only a dependency with an exact materialization site.  Do
     * not let an unrelated broad-frontier entry hide such a dependency merely
     * because the first 128 slots are occupied.  Promotions remain bounded
     * and fail closed when this independent budget is exhausted.</p>
     */
    private static final int MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS =
            512;

    /*
     * These patterns are used while scanning edges/cells, often once per
     * candidate in several independent region passes.  Pattern is immutable
     * and thread-safe; callers still create an activation-local Matcher.
     */
    private static final Pattern FIELD_PATH_SEGMENT_PATTERN =
            Pattern.compile("#field:([^#]+)");
    private static final Pattern PROJECTED_RETURN_FIELD_PATTERN =
            Pattern.compile("^<[^:]+:\\s+([^\\s]+)\\s+[^\\s(]+"
                    + "\\([^)]*\\)>\\.return#field:([^#]+)$");
    private static final Pattern PROJECTED_PARAMETER_FIELD_PATTERN =
            Pattern.compile("^<.+>\\.param\\d+:([^#]+)#field:([^#]+)$");
    private static final Pattern GLOBAL_FIELD_OWNER_PATTERN =
            Pattern.compile("^<([^:]+):\\s+[^()<>]+\\s+[^\\s()>]+>"
                    + "(?:#field:.*)?$");
    private static final Pattern PARAMETER_TYPE_PATTERN = Pattern.compile(
            "\\.param\\d+:([^#]+)(?:#field:.*)?$");
    private static final Pattern FIELD_CELL_TYPE_PATTERN = Pattern.compile(
            "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$");
    private static final Pattern RETURN_CELL_TYPE_PATTERN = Pattern.compile(
            "^<[^:]+:\\s+([^<>\\s]+)\\s+[^<>\\s(]+\\([^>]*\\)>"
                    + "\\.return(?:#.*)?$");
    private static final Pattern CAST_LOCAL_PATTERN = Pattern.compile(
            "^\\([^)]*\\)\\s*([$]?[A-Za-z_][A-Za-z0-9_]*)$");
    private static final Pattern GLOBAL_FIELD_LEAF_PATTERN = Pattern.compile(
            "^<[^:]+:\\s+[^()<>]+\\s+([^\\s()>]+)>$");
    private static final Pattern SEMANTIC_GLOBAL_FIELD_PATTERN =
            Pattern.compile("^<([^:]+):\\s+[^()<>]+\\s+([^\\s()>]+)>"
                    + "(.*)$");
    private static final Pattern REQUIRED_OUTCOME_PATTERN = Pattern.compile(
            "requires Jimple outcome (true|false)");
    private static final Pattern PARAMETER_INDEX_PATTERN = Pattern.compile(
            "\\.param(\\d+):");

    private SymbolicRegionPlanner() {
    }

    static void plan(StaticProgram program) {
        new Planner(program.graph()).plan(program);
    }

    static void planSelected(StaticProgram program,
                             Collection<String> observedMethods) {
        new Planner(program.graph()).planSelected(program,
                new LinkedHashSet<>(observedMethods));
    }

    /**
     * Exact static proof that a boundary-local projected endpoint is an alias
     * of one canonical, slice-backed region output.  The raw endpoint remains
     * part of the region edge because runtime endpoint fingerprinting observes
     * that concrete caller local.  This record is used only to select the
     * producer summary requested after that runtime relation is confirmed.
     */
    private static final class CanonicalOutputResolution {
        private final String port;
        private final String cell;
        private final List<String> proofEdgeIds;

        private CanonicalOutputResolution(String port, String cell,
                                          Collection<String> proofEdgeIds) {
            this.port = port;
            this.cell = cell;
            this.proofEdgeIds = new ArrayList<>(proofEdgeIds);
            Collections.sort(this.proofEdgeIds);
        }
    }

    private static final class Planner {
        private final StaticGraphIndex graph;
        private final Map<String, Set<String>> calleesByCaller = new LinkedHashMap<>();
        private final Map<String, Set<String>> parentsByCallee = new LinkedHashMap<>();
        private final Map<String, Map<String, Set<String>>>
                dynamicDispatchTargetsByCallerSite = new LinkedHashMap<>();
        private final List<Map<String, Object>> boundaryEdges =
                new ArrayList<>();
        private final Map<String, Set<Map<String, Object>>>
                exceptionCausalEdgesByRegion = new LinkedHashMap<>();
        private final Set<String> overlappingWriterAnchors =
                new LinkedHashSet<>();
        private final Set<String> anchorMethods = new LinkedHashSet<>();
        private Planner(StaticGraphIndex graph) {
            this.graph = graph;
            index();
        }

        private void plan(StaticProgram result) {
            List<String> anchors = initialAnchors();
            Set<String> emittedMethodSets = new LinkedHashSet<>();
            Set<String> queuedAnchorStates = new LinkedHashSet<>();
            for (String anchor : anchors) {
                queuedAnchorStates.add(anchor + "\nNORMAL");
            }
            Deque<String> anchorQueue = new ArrayDeque<>(anchors);
            int regionIndex = 0;
            while (!anchorQueue.isEmpty() && regionIndex < MAX_REGIONS) {
                String anchor = anchorQueue.removeFirst();
                for (RegionDraft draft : buildRegions(anchor)) {
                    if (draft.methods.isEmpty()) {
                        continue;
                    }
                    String dedup = regionDedupKey(draft);
                    if (!emittedMethodSets.add(dedup)) {
                        continue;
                    }
                    draft.regionId = "REGION." + regionIndex++;
                    result.regions.add(toRegionRow(draft));
                }
                for (String upstream : upstreamAnchors(result.regions)) {
                    String state = upstream + "\n"
                            + (overlappingWriterAnchors.contains(upstream)
                            ? "OVERLAPPING_WRITER" : "NORMAL");
                    if (queuedAnchorStates.add(state)) {
                        anchorQueue.addLast(upstream);
                    }
                }
            }

            Set<String> coveredBeforeModels = methodsCovered(result.regions);
            for (String method : graph.methods()) {
                if (coveredBeforeModels.contains(method)) {
                    continue;
                }
                if (regionIndex >= MAX_REGIONS) {
                    continue;
                }
                for (RegionDraft draft : buildRegions(method)) {
                    if (regionIndex >= MAX_REGIONS) {
                        break;
                    }
                    String dedup = regionDedupKey(draft);
                    if (!emittedMethodSets.add(dedup)) {
                        continue;
                    }
                    draft.regionId = "REGION." + regionIndex++;
                    result.regions.add(toRegionRow(draft));
                }
                coveredBeforeModels = methodsCovered(result.regions);
            }
            buildRegionEdges(result);
            result.coverageComplete = coverageComplete(result);

        }

        /**
         * Finalizes only region roots that occurred in the discovery trace.
         * Runtime evidence chooses the activation boundary; the complete
         * static method set inside each selected draft remains intact so
         * unobserved branch successors are still available to concolic path
         * exploration.
         */
        private void planSelected(StaticProgram result,
                                  Set<String> observedMethods) {
            if (observedMethods.isEmpty()) {
                return;
            }
            List<String> anchors = initialAnchors(observedMethods);
            Set<String> emittedMethodSets = new LinkedHashSet<>();
            Set<String> queuedAnchorStates = new LinkedHashSet<>();
            for (String anchor : anchors) {
                queuedAnchorStates.add(anchor + "\nNORMAL");
            }
            Deque<String> anchorQueue = new ArrayDeque<>(anchors);
            int regionIndex = 0;
            while (!anchorQueue.isEmpty() && regionIndex < MAX_REGIONS) {
                String anchor = anchorQueue.removeFirst();
                for (RegionDraft draft : buildRegions(anchor)) {
                    if (draft.methods.isEmpty()
                            || !observedMethods.contains(draft.anchorMethod)
                            || !observedMethods.contains(draft.rootMethod)) {
                        continue;
                    }
                    String dedup = regionDedupKey(draft);
                    if (!emittedMethodSets.add(dedup)) {
                        continue;
                    }
                    draft.regionId = "REGION." + regionIndex++;
                    result.regions.add(toRegionRow(draft));
                }
                for (String upstream : upstreamAnchors(result.regions)) {
                    if (!observedMethods.contains(upstream)) {
                        continue;
                    }
                    String state = upstream + "\n"
                            + (overlappingWriterAnchors.contains(upstream)
                            ? "OVERLAPPING_WRITER" : "NORMAL");
                    if (queuedAnchorStates.add(state)) {
                        anchorQueue.addLast(upstream);
                    }
                }
            }
            buildRegionEdges(result);
        }

        private List<String> initialAnchors() {
            return initialAnchors(null);
        }

        private List<String> initialAnchors(Set<String> observedMethods) {
            List<String> anchors = new ArrayList<>(anchorMethods);
            if (observedMethods != null) {
                anchors.retainAll(observedMethods);
            }
            Collections.sort(anchors);
            if (anchors.isEmpty()) {
                for (String method : graph.methods()) {
                    if (graph.requiresSymbolicExecution(method)
                            && (observedMethods == null
                            || observedMethods.contains(method))) {
                        anchors.add(method);
                    }
                }
            }
            if (anchors.size() > MAX_ANCHORS) {
                return new ArrayList<>(anchors.subList(0, MAX_ANCHORS));
            }
            return anchors;
        }

        private String regionDedupKey(RegionDraft draft) {
            return draft.rootMethod + "\n"
                    + (overlappingWriterAnchors.contains(
                    draft.anchorMethod) ? draft.anchorMethod : "") + "\n"
                    + joinSorted(draft.methods);
        }

        private boolean coverageComplete(StaticProgram result) {
            Map<String, Set<String>> regionsByMethod = new LinkedHashMap<>();
            Map<String, Set<String>> methodsByRegion = new LinkedHashMap<>();
            for (Map<String, Object> region : result.regions) {
                String regionId = string(region.get("regionId"));
                Set<String> methods = new LinkedHashSet<>(strings(region.get("methods")));
                methodsByRegion.put(regionId, methods);
                for (String method : methods) {
                    regionsByMethod.computeIfAbsent(method,
                            ignored -> new LinkedHashSet<>()).add(regionId);
                }
            }
            for (String method : graph.methods()) {
                if (!regionsByMethod.containsKey(method)) {
                    return false;
                }
            }

            Set<String> boundarySites = new LinkedHashSet<>();
            for (Map<String, Object> regionEdge : result.regionEdges) {
                String site = string(regionEdge.get("siteId"));
                if (!site.isEmpty()) {
                    boundarySites.add(site);
                }
            }
            for (Map<String, Object> edge : graph.edges()) {
                String method = string(edge.get("method"));
                String site = string(edge.get("siteId"));
                if (isBoundary(edge)) {
                    if (!boundarySites.contains(site)) {
                        return false;
                    }
                    continue;
                }
                String callee = string(edge.get("invoke"));
                if (callee.isEmpty() || !graph.hasMethod(callee)) {
                    callee = invokedMethodFromCells(edge);
                }
                if (!callee.isEmpty() && graph.hasMethod(callee)) {
                    if (!shareRegion(method, callee, regionsByMethod,
                            methodsByRegion)
                            && !alternativeNonCausalEdge(edge,
                            regionsByMethod)) {
                        return false;
                    }
                } else if (!regionsByMethod.containsKey(method)) {
                    return false;
                }
            }
            return true;
        }

        private boolean alternativeNonCausalEdge(
                Map<String, Object> edge,
                Map<String, Set<String>> regionsByMethod) {
            String edgeId = string(edge.get("id"));
            if (edgeId.isEmpty()) {
                return false;
            }
            for (String regionId : values(regionsByMethod.get(
                    string(edge.get("method"))))) {
                Set<Map<String, Object>> causalEdges =
                        exceptionCausalEdgesByRegion.get(
                        regionId);
                if (causalEdges != null && !causalEdges.contains(edge)) {
                    return true;
                }
            }
            return false;
        }

        private boolean shareRegion(String first, String second,
                                    Map<String, Set<String>> regionsByMethod,
                                    Map<String, Set<String>> methodsByRegion) {
            Set<String> regions = regionsByMethod.get(first);
            if (regions == null) {
                return false;
            }
            for (String region : regions) {
                Set<String> methods = methodsByRegion.get(region);
                if (methods != null && methods.contains(second)) {
                    return true;
                }
            }
            return false;
        }

        private Set<String> methodsCovered(List<Map<String, Object>> regions) {
            Set<String> covered = new LinkedHashSet<>();
            for (Map<String, Object> region : regions) {
                covered.addAll(strings(region.get("methods")));
            }
            return covered;
        }

        private List<String> upstreamAnchors(
                List<Map<String, Object>> regions) {
            Set<String> coveredMethods = methodsCovered(regions);
            Set<String> anchors = new LinkedHashSet<>();
            Set<String> consumedFields = new LinkedHashSet<>();
            for (Map<String, Object> edge : graph.edges()) {
                String method = string(edge.get("method"));
                String transfer = string(edge.get("transferKind"));
                if (coveredMethods.contains(method) && "HEAP_READ".equals(transfer)) {
                    String field = string(edge.get("fromCell"));
                    if (globalFieldCell(field)) {
                        consumedFields.add(field);
                    }
                }
                if (!isBoundary(edge)) {
                    continue;
                }
                String toMethod = methodForCell(string(edge.get("toCell")));
                if (toMethod.isEmpty()) {
                    toMethod = method;
                }
                String fromMethod = methodForCell(string(edge.get("fromCell")));
                if (coveredMethods.contains(toMethod)
                        && !fromMethod.isEmpty()
                        && !coveredMethods.contains(fromMethod)
                        && graph.hasMethod(fromMethod)) {
                    anchors.add(fromMethod);
                }
            }
            Map<String, List<Map<String, Object>>>
                    demandedSharedConsumers = new LinkedHashMap<>();
            for (Map<String, Object> region : regions) {
                Map<String, Map<String, Object>> inputsByPort =
                        new LinkedHashMap<>();
                for (Map<String, Object> input
                        : maps(region.get("symbolicInputs"))) {
                    String port = string(input.get("portId"));
                    if (!port.isEmpty()) {
                        inputsByPort.put(port, input);
                    }
                    addDemandedSharedConsumer(demandedSharedConsumers,
                            region, input);
                }
                for (Map<String, Object> slice
                        : maps(region.get("outputSlices"))) {
                    if (!completeOutputSlice(slice)) {
                        continue;
                    }
                    for (String port : strings(slice.get("inputPorts"))) {
                        addDemandedSharedConsumer(demandedSharedConsumers,
                                region, inputsByPort.get(port));
                    }
                }
            }
            if (!consumedFields.isEmpty()) {
                for (Map<String, Object> edge : graph.edges()) {
                    String method = string(edge.get("method"));
                    if (!"HEAP_WRITE".equals(string(edge.get("transferKind")))
                            || !consumedFields.contains(string(edge.get("toCell")))
                            || method.isEmpty()
                            || !graph.hasMethod(method)) {
                        continue;
                    }
                    if (coveredMethods.contains(method)) {
                        if (!coveredDynamicDispatchWriter(
                                method, string(edge.get("toCell")),
                                demandedSharedConsumers)) {
                            continue;
                        }
                        overlappingWriterAnchors.add(method);
                    }
                    anchors.add(method);
                }
            }
            List<String> sorted = new ArrayList<>(anchors);
            Collections.sort(sorted);
            return sorted;
        }

        private void addDemandedSharedConsumer(
                Map<String, List<Map<String, Object>>> consumers,
                Map<String, Object> region, Map<String, Object> input) {
            if (region == null || input == null) {
                return;
            }
            String cell = string(input.get("cell"));
            if (!globalFieldCell(cell)
                    || !"SHARED_HEAP".equals(
                    string(input.get("sourceKind")))) {
                return;
            }
            List<Map<String, Object>> rows = consumers.computeIfAbsent(cell,
                    ignored -> new ArrayList<>());
            if (!rows.contains(region)) {
                rows.add(region);
            }
        }

        /**
         * A cheap static candidate can contain mutually exclusive concrete
         * implementations of one virtual worker dispatch.  If the exception
         * branch or an already selected producer output slice consumes a
         * demanded declared field and one sibling writes it, treating that
         * writer as "already covered" loses the producer entirely. Emit a
         * deliberately overlapping candidate only for this exact
         * sibling-dispatch shape; runtime thread/call ancestry later selects
         * the concrete instances.
         */
        private boolean coveredDynamicDispatchWriter(
                String writer, String field,
                Map<String, List<Map<String, Object>>> consumersByField) {
            for (Map<String, Object> consumer : consumersByField.getOrDefault(
                    field, Collections.<Map<String, Object>>emptyList())) {
                String root = string(consumer.get("rootMethod"));
                String anchor = string(consumer.get("anchorMethod"));
                if (siblingDynamicDispatch(root, anchor, writer)) {
                    return true;
                }
            }
            return false;
        }

        private boolean siblingDynamicDispatch(String root, String anchor,
                                               String writer) {
            for (Map.Entry<String, Map<String, Set<String>>> byCaller
                    : dynamicDispatchTargetsByCallerSite.entrySet()) {
                String caller = byCaller.getKey();
                if (!caller.equals(root) && !reachableFrom(root, caller)) {
                    continue;
                }
                for (Set<String> targets : byCaller.getValue().values()) {
                    if (targets.size() < 2) {
                        continue;
                    }
                    for (String consumerChild : targets) {
                        if (!consumerChild.equals(anchor)
                                && !reachableFrom(consumerChild, anchor)) {
                            continue;
                        }
                        for (String writerChild : targets) {
                            if (consumerChild.equals(writerChild)) {
                                continue;
                            }
                            if (writerChild.equals(writer)
                                    || reachableFrom(writerChild, writer)) {
                                return true;
                            }
                        }
                    }
                }
            }
            return false;
        }

        private void index() {
            for (Map<String, Object> edge : graph.edges()) {
                String method = string(edge.get("method"));
                String transfer = string(edge.get("transferKind"));
                String kind = string(edge.get("kind"));
                if (("SEED".equals(transfer)
                        || lower(kind).contains("seed")
                        || string(edge.get("toCell")).contains("#exception:"))
                        && graph.hasMethod(method)) {
                    anchorMethods.add(method);
                }
                boolean boundary = isBoundary(edge);
                if (boundary) {
                    boundaryEdges.add(edge);
                }

                String callee = string(edge.get("invoke"));
                if (callee.isEmpty() || !graph.hasMethod(callee)) {
                    callee = invokedMethodFromCells(edge);
                }
                if (method.isEmpty() || callee.isEmpty()
                        || method.equals(callee)
                        || !graph.hasMethod(method)
                        || !graph.hasMethod(callee)) {
                    continue;
                }
                if (boundary) {
                    continue;
                }
                if ("DYNAMIC_DISPATCH".equals(transfer)) {
                    String site = string(edge.get("siteId"));
                    if (!site.isEmpty()) {
                        dynamicDispatchTargetsByCallerSite
                                .computeIfAbsent(method,
                                        ignored -> new LinkedHashMap<>())
                                .computeIfAbsent(site,
                                        ignored -> new LinkedHashSet<>())
                                .add(callee);
                    }
                }
                add(calleesByCaller, method, callee);
                add(parentsByCallee, callee, method);
            }
        }

        private List<RegionDraft> buildRegions(String anchor) {
            List<String> roots = candidateRoots(anchor);
            CausalSlice baseCausalSlice = exceptionCausalSlice(anchor);
            List<RegionDraft> drafts = new ArrayList<>();
            for (String root : roots) {
                List<String> path = shortestPath(root, anchor);
                if (path.isEmpty()) {
                    continue;
                }
                RegionDraft draft = new RegionDraft(anchor);
                draft.rootMethod = root;
                draft.methods.addAll(path);
                if (baseCausalSlice != null) {
                    draft.exceptionDirected = true;
                    draft.causalEdges.addAll(baseCausalSlice.edges);
                    draft.causalCells.addAll(baseCausalSlice.cells);
                    draft.causalCellBudgetTruncated =
                            baseCausalSlice.causalCellBudgetTruncated;
                    addRequiredCallPathGuards(draft, path);
                    includeCausalMethods(draft);
                } else {
                    includeRelevantCallees(draft);
                }
                draft.methodBudgetTruncated =
                        draft.methods.size() >= MAX_REGION_METHODS;
            drafts.add(draft);
            }
            if (drafts.isEmpty()) {
                RegionDraft fallback = new RegionDraft(anchor);
                fallback.rootMethod = anchor;
                fallback.methods.add(anchor);
                includeRelevantCallees(fallback);
                fallback.methodBudgetTruncated =
                        fallback.methods.size() >= MAX_REGION_METHODS;
                drafts.add(fallback);
            }
            return drafts;
        }

        /**
         * Builds the exception-directed subgraph used for a target receiver
         * region.  The global worklist deliberately contains forward aliases
         * and normal-return facts so it can discover writers and protocol
         * producers.  Those facts are useful globally, but unioning them into
         * the target region also pulls in sibling branches that cannot reach
         * the exception.  Starting at the concrete exception node and walking
         * data-flow edges backwards recovers the causal portion only.
         */
        private CausalSlice exceptionCausalSlice(String anchor) {
            Set<String> seeds = new LinkedHashSet<>();
            for (Map<String, Object> edge : graph.forMethod(anchor)) {
                String target = string(edge.get("toCell"));
                boolean exceptionTarget = target.contains("#exception:");
                if (!"SEED".equals(string(edge.get("transferKind")))
                        && !exceptionTarget) {
                    continue;
                }
                String kind = lower(string(edge.get("kind")));
                if (kind.contains("exception") || exceptionTarget) {
                    seeds.add(target);
                }
            }
            if (seeds.isEmpty()) {
                return null;
            }
            CausalSlice result = new CausalSlice();
            result.causalCellBudgetTruncated |= addBackwardDependencies(
                    result.edges, result.cells, seeds);
            // A projected object return also depends on the base object being
            // produced successfully.  Closing that base is what retains, for
            // example, BlockPoolTokenSecretManager.get(blockPoolId)'s
            // map lookup and non-null guard before fields of the returned
            // The owning state object can be read.
            boolean changed = true;
            while (changed) {
                Set<String> returnBases = new LinkedHashSet<>();
                for (String cell : new ArrayList<>(result.cells)) {
                    int projection = cell.indexOf(">.return#field:");
                    if (projection >= 0) {
                        returnBases.add(cell.substring(0, projection + 8));
                    }
                }
                int before = result.cells.size();
                result.causalCellBudgetTruncated |= addBackwardDependencies(
                        result.edges, result.cells, returnBases);
                changed = result.cells.size() > before;
            }
            return result;
        }

        private boolean addBackwardDependencies(
                Set<Map<String, Object>> sliceEdges,
                Set<String> sliceCells,
                Collection<String> initialCells) {
            return addBackwardDependencies(sliceEdges, sliceCells,
                    initialCells, null);
        }

        /**
         * Adds a bounded backward dependency closure and reports whether any
         * newly discovered cell had to be omitted.  The old loop stopped as
         * soon as the set reached 20k, leaving a non-empty queue without
         * recording that loss; downstream code could then call the slice
         * complete.  Continue processing already-admitted cells, refuse new
         * cells at the exact bound, and propagate the truncation bit instead.
         */
        private boolean addBackwardDependencies(
                Set<Map<String, Object>> sliceEdges, Set<String> sliceCells,
                Collection<String> initialCells, Set<String> allowedMethods) {
            Deque<String> queue = new ArrayDeque<>();
            boolean truncated = false;
            for (String cell : initialCells) {
                if (cell.isEmpty() || sliceCells.contains(cell)) {
                    continue;
                }
                if (sliceCells.size() >= MAX_BACKWARD_SLICE_CELLS) {
                    truncated = true;
                    continue;
                }
                sliceCells.add(cell);
                queue.addLast(cell);
            }
            while (!queue.isEmpty()) {
                String target = queue.removeFirst();
                String owner = projectedBase(target);
                if (!owner.isEmpty() && !sliceCells.contains(owner)) {
                    if (sliceCells.size() >= MAX_BACKWARD_SLICE_CELLS) {
                        truncated = true;
                    } else {
                        sliceCells.add(owner);
                        queue.addLast(owner);
                    }
                }
                for (Map<String, Object> edge : graph.incoming(target)) {
                    String method = string(edge.get("method"));
                    if (allowedMethods != null
                            && !allowedMethods.contains(method)) {
                        continue;
                    }
                    sliceEdges.add(edge);
                    // A protocol edge defines the consumer-side live-in.  Its
                    // producer remains in the remote region and is related by
                    // the emitted region edge instead of becoming a duplicate
                    // local symbol.
                    if (isBoundary(edge)) {
                        continue;
                    }
                    String source = string(edge.get("fromCell"));
                    if (source.isEmpty() || sliceCells.contains(source)) {
                        continue;
                    }
                    if (sliceCells.size() >= MAX_BACKWARD_SLICE_CELLS) {
                        truncated = true;
                        continue;
                    }
                    sliceCells.add(source);
                    queue.addLast(source);
                }
            }
            return truncated;
        }

        /** Adds the controlling conditions for each call on the root-to-seed path. */
        private void addRequiredCallPathGuards(RegionDraft draft,
                                               List<String> path) {
            addRequiredCallPathGuards(draft, path, null);
        }

        private void addRequiredCallPathGuards(
                RegionDraft draft, List<String> path,
                Set<String> allowedDependencyMethods) {
            for (int index = 0; index + 1 < path.size(); index++) {
                String caller = path.get(index);
                String callee = path.get(index + 1);
                Set<Integer> callUnits = new LinkedHashSet<>();
                Set<String> directGuardSources = new LinkedHashSet<>();
                List<Map<String, Object>> callerEdges =
                        graph.forMethod(caller);
                for (Map<String, Object> edge : callerEdges) {
                    if (string(edge.get("kind"))
                            .contains("synchronous_callback_path_guard")
                            && callee.equals(methodForCell(
                            string(edge.get("toCell"))))) {
                        draft.causalEdges.add(edge);
                        draft.causalCells.add(string(edge.get("toCell")));
                        directGuardSources.add(string(edge.get("fromCell")));
                    }
                    if (!callee.equals(calleeForEdge(edge))) {
                        continue;
                    }
                    int unit = integer(edge.get("unitIndex"), -1);
                    if (unit >= 0) {
                        callUnits.add(unit);
                    }
                }
                draft.causalCellBudgetTruncated |= addBackwardDependencies(
                        draft.causalEdges, draft.causalCells,
                        directGuardSources, allowedDependencyMethods);
                if (callUnits.isEmpty()) {
                    continue;
                }
                Set<String> guardSources = new LinkedHashSet<>();
                for (Map<String, Object> edge : callerEdges) {
                    if (!"GUARD".equals(string(edge.get("transferKind")))) {
                        continue;
                    }
                    String evidence = string(edge.get("evidence"));
                    boolean controlsCall = false;
                    for (Integer unit : callUnits) {
                        if (evidence.contains("at u" + unit)) {
                            controlsCall = true;
                            break;
                        }
                    }
                    if (!controlsCall) {
                        continue;
                    }
                    draft.causalEdges.add(edge);
                    draft.causalCells.add(string(edge.get("toCell")));
                    String source = string(edge.get("fromCell"));
                    if (!source.isEmpty()) {
                        guardSources.add(source);
                    }
                }
                draft.causalCellBudgetTruncated |= addBackwardDependencies(
                        draft.causalEdges, draft.causalCells,
                        guardSources, allowedDependencyMethods);
            }
        }

        private String calleeForEdge(Map<String, Object> edge) {
            String callee = string(edge.get("invoke"));
            if (callee.isEmpty() || !graph.hasMethod(callee)) {
                callee = invokedMethodFromCells(edge);
            }
            return callee;
        }

        private void includeCausalMethods(RegionDraft draft) {
            Set<String> candidates = new LinkedHashSet<>();
            Set<String> excluded = callbackContextExcludedMethods();
            excluded.addAll(pathContradictingCallees(draft));
            for (Map<String, Object> edge : draft.causalEdges) {
                String edgeMethod = string(edge.get("method"));
                if (!edgeMethod.isEmpty() && !excluded.contains(edgeMethod)) {
                    candidates.add(edgeMethod);
                }
                String invoked = calleeForEdge(edge);
                if (!invoked.isEmpty() && !excluded.contains(invoked)) {
                    candidates.add(invoked);
                }
                String targetMethod = methodForCell(string(edge.get("toCell")));
                if (!targetMethod.isEmpty() && !excluded.contains(targetMethod)) {
                    candidates.add(targetMethod);
                }
                if (!isBoundary(edge)) {
                    String sourceMethod = methodForCell(string(edge.get("fromCell")));
                    if (!sourceMethod.isEmpty()
                            && !excluded.contains(sourceMethod)) {
                        candidates.add(sourceMethod);
                    }
                }
            }
            for (String method : sorted(candidates)) {
                if (draft.methods.size() >= MAX_REGION_METHODS) {
                    break;
                }
                if (graph.hasMethod(method)
                        && reachableFrom(draft.rootMethod, method)) {
                    draft.methods.add(method);
                }
            }
        }

        private Set<String> callbackContextExcludedMethods() {
            Map<String, Set<String>> registrationsByExecutor =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : graph.edges()) {
                if (!"synchronous_callback_capture_receiver".equals(
                        string(edge.get("kind")))) {
                    continue;
                }
                String executor = string(edge.get("method"));
                String registration = methodForCell(string(edge.get("fromCell")));
                if (!executor.isEmpty() && !registration.isEmpty()) {
                    add(registrationsByExecutor, executor, registration);
                }
            }
            Set<String> excluded = new LinkedHashSet<>();
            for (Map.Entry<String, Set<String>> binding
                    : registrationsByExecutor.entrySet()) {
                for (String parent : values(parentsByCallee.get(binding.getKey()))) {
                    if (!binding.getValue().contains(parent)) {
                        excluded.add(parent);
                    }
                }
            }
            return excluded;
        }

        private Set<String> pathContradictingCallees(RegionDraft draft) {
            Map<String, Boolean> requiredBySite = new LinkedHashMap<>();
            for (Map<String, Object> edge : draft.causalEdges) {
                if (!"GUARD".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                Boolean outcome = requiredOutcome(edge);
                String site = string(edge.get("siteId"));
                if (outcome != null && !site.isEmpty()) {
                    requiredBySite.put(site, outcome);
                }
            }
            Set<String> oppositeBranchCells = new LinkedHashSet<>();
            List<Map<String, Object>> methodEdges =
                    graph.forMethods(draft.methods);
            for (Map<String, Object> edge : methodEdges) {
                String site = string(edge.get("siteId"));
                Boolean required = requiredBySite.get(site);
                Boolean outcome = requiredOutcome(edge);
                if (required != null && outcome != null
                        && !required.equals(outcome)) {
                    oppositeBranchCells.add(string(edge.get("toCell")));
                }
            }

            // Contradiction is a property of an invocation site, not of the
            // callee method. A method may be invoked once on the rejected
            // branch and again on the required path. Excluding the method
            // globally would therefore lose a real external input.
            Map<String, Set<String>> oppositeSitesByCallee =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : methodEdges) {
                String invoked = calleeForEdge(edge);
                if (!invoked.isEmpty()
                        && oppositeBranchCells.contains(
                        string(edge.get("fromCell")))) {
                    add(oppositeSitesByCallee, invoked,
                            invocationSite(edge, invoked));
                }
            }

            Set<String> causallySupported = new LinkedHashSet<>();
            for (Map<String, Object> edge : draft.causalEdges) {
                String invoked = calleeForEdge(edge);
                if (invoked.isEmpty()) {
                    continue;
                }
                Set<String> oppositeSites = oppositeSitesByCallee.get(invoked);
                if (oppositeSites == null || !oppositeSites.contains(
                        invocationSite(edge, invoked))) {
                    causallySupported.add(invoked);
                }
            }

            Set<String> excluded = new LinkedHashSet<>(
                    oppositeSitesByCallee.keySet());
            excluded.removeAll(causallySupported);
            return excluded;
        }

        private String invocationSite(Map<String, Object> edge,
                                      String invoked) {
            return string(edge.get("method")) + "\n"
                    + integer(edge.get("unitIndex"), -1) + "\n" + invoked;
        }

        private boolean reachableFrom(String root, String target) {
            if (root.equals(target)) {
                return true;
            }
            Set<String> seen = new LinkedHashSet<>();
            Deque<String> queue = new ArrayDeque<>();
            seen.add(root);
            queue.add(root);
            while (!queue.isEmpty() && seen.size() <= graph.methods().size()) {
                String current = queue.removeFirst();
                for (String next : values(calleesByCaller.get(current))) {
                    if (!seen.add(next)) {
                        continue;
                    }
                    if (target.equals(next)) {
                        return true;
                    }
                    queue.addLast(next);
                }
            }
            return false;
        }

        private List<String> candidateRoots(String anchor) {
            Set<String> seen = new LinkedHashSet<>();
            Set<String> roots = new LinkedHashSet<>();
            Deque<MethodDepth> queue = new ArrayDeque<>();
            seen.add(anchor);
            queue.add(new MethodDepth(anchor, 0));
            while (!queue.isEmpty() && roots.size() < MAX_ANCHORS) {
                MethodDepth current = queue.removeFirst();
                List<String> parents = sorted(parentsByCallee.get(current.method));
                // A callback-shaped name is not itself a region boundary when
                // static object flow proves a synchronous same-thread parent.
                // Walk to the highest known parent; runtime ancestry remains
                // authoritative when the static graph is incomplete.
                if (!current.method.equals(anchor) && parents.isEmpty()) {
                    roots.add(current.method);
                    continue;
                }
                if (current.depth >= MAX_PARENT_DEPTH) {
                    roots.add(current.method);
                    continue;
                }
                int count = 0;
                for (String parent : parents) {
                    if (count++ >= MAX_PARENTS_PER_METHOD) {
                        break;
                    }
                    if (seen.add(parent)) {
                        queue.addLast(new MethodDepth(parent, current.depth + 1));
                    }
                }
            }
            if (roots.isEmpty()) {
                roots.add(anchor);
            }
            List<String> sorted = new ArrayList<>(roots);
            sorted.sort(Comparator.comparing(SymbolicRegionPlanner::entryPriority)
                    .thenComparing(value -> value));
            return sorted;
        }

        private void includeRelevantCallees(RegionDraft draft) {
            // Relevant sibling producers (for example getIdentifier next to
            // getPassword in a callback handler) are already in the static
            // slice. Include their method summaries without walking through
            // unrelated library descendants.
            boolean changed = true;
            int rounds = 0;
            while (changed && rounds++ < 2 && draft.methods.size() < MAX_REGION_METHODS) {
                changed = false;
                List<String> methods = new ArrayList<>(draft.methods);
                for (String method : methods) {
                    for (String callee : sorted(calleesByCaller.get(method))) {
                        if (draft.methods.size() >= MAX_REGION_METHODS) {
                            break;
                        }
                        if (isLargeLibraryMethod(callee)) {
                            continue;
                        }
                        changed |= draft.methods.add(callee);
                    }
                }
            }
        }

        private List<String> shortestPath(String from, String target) {
            if (from == null || from.isEmpty() || target == null || target.isEmpty()) {
                return Collections.emptyList();
            }
            Map<String, String> predecessor = new LinkedHashMap<>();
            Deque<String> queue = new ArrayDeque<>();
            predecessor.put(from, null);
            queue.add(from);
            while (!queue.isEmpty()
                    && predecessor.size() <= graph.methods().size()) {
                String current = queue.removeFirst();
                if (current.equals(target)) {
                    break;
                }
                for (String next : sorted(calleesByCaller.get(current))) {
                    if (!graph.hasMethod(next)
                            || predecessor.containsKey(next)) {
                        continue;
                    }
                    predecessor.put(next, current);
                    queue.addLast(next);
                }
            }
            if (!predecessor.containsKey(target)) {
                return Collections.emptyList();
            }
            List<String> path = new ArrayList<>();
            for (String current = target; current != null;
                 current = predecessor.get(current)) {
                path.add(current);
            }
            Collections.reverse(path);
            return path;
        }

        private Map<String, Object> toRegionRow(RegionDraft draft) {
            List<String> methods = new ArrayList<>(draft.methods);
            Collections.sort(methods);
            methods.remove(draft.rootMethod);
            methods.add(0, draft.rootMethod);

            Set<String> produced = new LinkedHashSet<>();
            Set<String> inputCandidates = new LinkedHashSet<>();
            Set<String> outputCandidates = new LinkedHashSet<>();
            List<Map<String, Object>> branchPolicies = new ArrayList<>();

            for (String method : draft.methods) {
                if (!graph.hasMethod(method)) {
                    continue;
                }
                Collection<String> inputs = graph.inputs(method);
                Collection<String> outputs = graph.outputs(method);
                inputCandidates.addAll(inputs);
                outputCandidates.addAll(outputs);
                produced.addAll(outputs);
            }
            // A PATH_ASSUMPTION proof must cover every output candidate, not
            // merely the one edge on which the proof happened to be stored.
            // Include mandatory seed outputs before evaluating those proofs.
            addSeedOutputs(draft.methods, outputCandidates);
            // Preserve the edge-level guard/site association.  A method plan's
            // independent guards and siteIds sets cannot tell the concolic
            // scheduler which path-condition entry belongs to which branch.
            // A branch site can have both the broad "branch consumes a
            // relevant value" edge and a more precise control-dependence
            // edge proving that one outcome reaches an output definition.
            // Edge ids are deterministic, but their order is not a semantic
            // priority.  Selecting the first edge used to let a generic
            // guard_dependency hide a later path_guard_dependency for the
            // same site, incorrectly pinning an output-changing scalar
            // branch as PATH_ASSUMPTION.  Aggregate all exact control edges
            // for a site before deriving its outcome/successor contract, and
            // retain one strongest edge only for compatibility metadata.
            Map<String, List<Map<String, Object>>> branchEdgesBySite =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge
                    : graph.forMethods(draft.methods)) {
                if (draft.exceptionDirected
                        && !draft.causalEdges.contains(edge)
                        || !"GUARD".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                String site = string(edge.get("siteId"));
                if (site.isEmpty()) {
                    continue;
                }
                branchEdgesBySite.computeIfAbsent(site,
                        ignored -> new ArrayList<>()).add(edge);
            }
            for (List<Map<String, Object>> siteEdges
                    : branchEdgesBySite.values()) {
                List<Map<String, Object>> policyEdges =
                        authoritativeBranchPolicyEdges(siteEdges);
                Map<String, Object> branchPolicy = branchPolicy(
                        policyEdges, draft);
                branchPolicies.add(branchPolicy);
            }
            InputSelection inputSelection = selectExternalInputs(draft,
                    inputCandidates, produced);
            inputCandidates = inputSelection.externalInputs;

            List<Map<String, Object>> inputPorts = new ArrayList<>();
            int inputIndex = 0;
            for (String input : priorityOrdered(inputCandidates,
                    inputSelection.mandatorySeedGuardInputs)) {
                if (inputPorts.size() >= MAX_PORTS) {
                    continue;
                }
                Map<String, Object> port = object(
                        "portId", draft.regionId + ".in." + inputIndex++,
                        "cell", input,
                        "javaType", cellJavaType(input),
                        "sourceKind", sourceKind(input, draft.rootMethod),
                        "projection", projection(input));
                addRegionInputMaterializationMetadata(port, input, draft);
                inputPorts.add(port);
            }
            boolean broadInputPortTruncated =
                    inputCandidates.size() > inputPorts.size();

            Set<String> prioritySeedOutputs = seedInterfaceCells(draft);
            List<Map<String, Object>> outputPorts = new ArrayList<>();
            int outputIndex = 0;
            for (String output : priorityOrdered(outputCandidates,
                    prioritySeedOutputs)) {
                if (draft.exceptionDirected
                        && (!causalCandidate(output, draft)
                        || !exceptionRegionOutput(output, draft))
                        || !semanticOutput(output, draft)) {
                    continue;
                }
                if (outputPorts.size() >= MAX_PORTS) {
                    continue;
                }
                Map<String, Object> port = object(
                        "portId", draft.regionId + ".out." + outputIndex++,
                        "cell", output,
                        "javaType", cellJavaType(output),
                        "kind", outputKind(output, draft.anchorMethod));
                outputPorts.add(port);
            }
            List<Map<String, Object>> outputSlices = outputSlices(draft,
                    inputPorts, outputPorts);
            mergeRequestedOutputSliceBranchPolicies(draft, outputSlices,
                    branchPolicies);
            if (draft.exceptionDirected) {
                exceptionCausalEdgesByRegion.put(draft.regionId,
                        draft.causalEdges);
            }

            return object(
                    "schemaVersion", REGION_SCHEMA_VERSION,
                    "regionId", draft.regionId,
                    "rootMethod", draft.rootMethod,
                    "anchorMethod", draft.anchorMethod,
                    "methods", methods,
                    "symbolicInputs", inputPorts,
                    "inputSelectionComplete",
                    inputSelection.unresolvedInputDetails.isEmpty()
                            && !broadInputPortTruncated,
                    "outputs", outputPorts,
                    "outputSlices", outputSlices,
                    "branchPolicies", branchPolicies,
                    "selection", draft.exceptionDirected
                            ? "EXCEPTION_BACKWARD_CAUSAL_CLOSURE"
                            : "STATIC_OVER_APPROXIMATION");
        }

        private List<String> causalEdgeIds(
                Set<Map<String, Object>> causalEdges) {
            Set<String> ids = new LinkedHashSet<>();
            for (Map<String, Object> edge : causalEdges) {
                String id = string(edge.get("id"));
                if (!id.isEmpty()) {
                    ids.add(id);
                }
            }
            return sorted(ids);
        }

        private List<String> truncationReasons(RegionDraft draft) {
            List<String> reasons = new ArrayList<>();
            if (draft.methodBudgetTruncated) {
                reasons.add("REQUESTED_OUTPUT_METHOD_LIMIT_EXCEEDED");
            }
            if (draft.causalCellBudgetTruncated) {
                reasons.add("BACKWARD_DEPENDENCY_CELL_LIMIT_EXCEEDED");
            }
            return reasons;
        }

        /**
         * Precomputes demand slices for canonical heap-state outputs and for
         * values that are proven outbound protocol endpoints.
         * Runtime selection later chooses one of these records by stable output
         * port; it never needs application-specific field knowledge.
         *
         * <p>A region exposes many method parameters as {@code SINK_STATE}
         * outputs.  Most are implementation details (streams, maps, callback
         * objects, and other opaque carriers), so admitting every sink output
         * would make the demand closure nearly as large as the whole region.
         * A non-heap formal is admitted only when an explicit static boundary
         * edge carries that exact scalar from this region to a method outside
         * it.  A root-method return is admitted only through authoritative
         * exact value-flow.  Aggregate returns additionally require an exact
         * field-sensitive outbound projection, so an opaque object type never
         * becomes a symbolic protocol summary merely because its raw reference
         * crosses a boundary.</p>
         */
        private List<Map<String, Object>> outputSlices(
                RegionDraft region, List<Map<String, Object>> inputPorts,
                List<Map<String, Object>> outputPorts) {
            List<Map<String, Object>> result = new ArrayList<>();
            for (Map<String, Object> output : outputPorts) {
                String outputCell = string(output.get("cell"));
                boolean heapStateOutput = "HEAP_STATE".equals(
                        string(output.get("kind")))
                        && globalFieldCell(outputCell);
                boolean protocolReturnOutput = outboundProtocolReturnValue(
                        region, outputCell);
                if (!heapStateOutput && !protocolReturnOutput) {
                    continue;
                }
                Map<String, Object> framePrestatePort = heapStateOutput
                        ? ensureFramePrestatePort(region, outputCell,
                        inputPorts)
                        : null;

                RegionDraft slice = outputSlice(region, outputCell);
                Set<String> candidates = new LinkedHashSet<>();
                Set<String> produced = new LinkedHashSet<>();
                for (String method : slice.methods) {
                    if (!graph.hasMethod(method)) {
                        continue;
                    }
                    candidates.addAll(graph.inputs(method));
                    produced.addAll(graph.outputs(method));
                }
                InputSelection selection = selectExternalInputs(slice,
                        candidates, produced);
                // A static region can yield several runtime-rooted
                // activations.  Keep exact causal formals as dormant ports so
                // a constructor/helper replay can use its own parameter as
                // the boundary.  Runtime re-slicing selects only the formals
                // of the invocation that actually became the root.
                selection.externalInputs.addAll(
                        causalActivationParameters(slice));
                boolean promotionCapacityExceeded = false;
                Set<String> selectedPorts = new LinkedHashSet<>();
                List<Map<String, Object>> inputBindings = new ArrayList<>();
                List<Map<String, Object>> unresolvedDetails =
                        new ArrayList<>(selection.unresolvedInputDetails);

                // Port construction and dependency binding must be separate
                // phases.  A synthetic local projection can resolve through
                // an exact alias chain whose canonical declared-field end is
                // itself promoted by this requested-output slice.  Binding
                // while walking the (sorted) dependency set made the result
                // order-dependent: a caller local visited before its
                // canonical field was reported unresolved, while a caller
                // local visited before a second competing canonical field
                // could retain a stale, falsely-unique binding.  First admit
                // every independently materializable frontier.  Only then
                // resolve all dependencies against the final port set, so
                // exactProjectedAliasCarrier sees both late ports and late
                // ambiguities.  This changes no alias authority and does not
                // turn an unmaterializable local into a port.
                Set<String> promotableInputs = new LinkedHashSet<>();
                Map<String, String> portsPromotedByInput =
                        new LinkedHashMap<>();
                // Every phase-one decision observes the same pre-promotion
                // frontier.  Letting this list grow during admission would
                // merely move the order dependence: an earlier canonical
                // promotion could suppress a later, independently
                // materializable competing canonical dependency.
                List<Map<String, Object>> prePromotionInputPorts =
                        new ArrayList<>(inputPorts);
                for (String input : selection.externalInputs) {
                    InputPortResolution resolution = inputPortForCell(input,
                            prePromotionInputPorts, region.rootMethod, slice);
                    if (!resolution.portId.isEmpty()
                            && input.contains("#field:")) {
                        Map<String, Object> existing = inputPort(
                                resolution.portId, inputPorts);
                        if (existing != null
                                && strings(existing.get(
                                "fieldPath")).size() <= 1
                                && materializableDeclaredFieldPathAccess(
                                input, slice) != null) {
                            addOutputSliceFrontierMaterializationMetadata(
                                    existing, input, slice);
                        }
                    }
                    boolean incompatiblePromotedFieldPort =
                            !resolution.portId.isEmpty()
                                    && !exactMaterializableAliasResolution(
                                    resolution, prePromotionInputPorts)
                                    && !promotedDeclaredFieldPortCompatible(
                                    input, resolution.portId,
                                    prePromotionInputPorts, slice);
                    if (incompatiblePromotedFieldPort) {
                        resolution = InputPortResolution.unresolved();
                    }
                    boolean promotable =
                            outputSliceFrontierPromotable(input, slice);
                    if (promotable) {
                        promotableInputs.add(input);
                    }
                    if (resolution.portId.isEmpty()
                            && !incompatiblePromotedFieldPort
                            && promotable) {
                        if (inputPorts.size()
                                < MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS) {
                            String portId = region.regionId + ".in."
                                    + inputPorts.size();
                            Map<String, Object> promotedPort = object(
                                    "portId", portId,
                                    "cell", input,
                                    "javaType", cellJavaType(input),
                                    "sourceKind", sourceKind(input,
                                            region.rootMethod),
                                    "projection", projection(input));
                            addOutputSliceFrontierMaterializationMetadata(
                                    promotedPort, input, slice);
                            inputPorts.add(promotedPort);
                            portsPromotedByInput.put(input, portId);
                        } else {
                            promotionCapacityExceeded = true;
                        }
                    }
                }

                for (String input : selection.externalInputs) {
                    InputPortResolution resolution = inputPortForCell(input,
                            inputPorts, region.rootMethod, slice);
                    boolean incompatiblePromotedFieldPort =
                            !resolution.portId.isEmpty()
                                    && !exactMaterializableAliasResolution(
                                    resolution, inputPorts)
                                    && !promotedDeclaredFieldPortCompatible(
                                    input, resolution.portId, inputPorts,
                                    slice);
                    if (incompatiblePromotedFieldPort) {
                        resolution = InputPortResolution.unresolved();
                    }
                    String promotedPort = portsPromotedByInput.get(input);
                    if (promotedPort != null
                            && promotedPort.equals(resolution.portId)) {
                        resolution = new InputPortResolution(promotedPort,
                                "OUTPUT_SLICE_FRONTIER_PROMOTION");
                    }
                    if (resolution.portId.isEmpty()) {
                        boolean capacityExceeded =
                                promotionCapacityExceeded
                                        && promotableInputs.contains(input);
                        String diagnostic = input + (capacityExceeded
                                ? " [exact output slice dependency exceeds "
                                + "bounded promotion capacity "
                                + MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS
                                + "]"
                                : " [output slice input has no region port]");
                        unresolvedDetails.add(object(
                                "dependencyCell", input,
                                "dependencyMethods",
                                dependencyMethods(input, slice),
                                "reason", capacityExceeded
                                        ? "OUTPUT_SLICE_DEPENDENCY_"
                                        + "PROMOTION_CAPACITY_EXCEEDED"
                                        : incompatiblePromotedFieldPort
                                        ? "INCOMPATIBLE_PROMOTED_"
                                        + "DECLARED_FIELD_PORT"
                                        : "OUTPUT_SLICE_INPUT_HAS_NO_"
                                        + "REGION_PORT",
                                "diagnostic", diagnostic));
                    } else {
                        // A requested-output port can be promoted by an
                        // earlier slice and then reused here.  Promotion
                        // records the exact accessor implementation on the
                        // shared port, but the implementation is part of
                        // each slice's method closure, not the region-wide
                        // port declaration.  Re-admit it only after proving
                        // that this slice has the same exact caller,
                        // callsite, declared callee, resolved implementation,
                        // and declared field.  Otherwise runtime refinement
                        // would either reject the real getter as outside the
                        // static slice or, less safely, admit a same-named
                        // accessor from an unrelated callsite.
                        admitCompatibleAccessorImplementationMethod(input,
                                resolution.portId, inputPorts, slice);
                        selectedPorts.add(resolution.portId);
                        Map<String, Object> inputBinding = object(
                                "dependencyCell", input,
                                "inputPort", resolution.portId,
                                "bindingAuthority", resolution.authority,
                                "dependencyMethods",
                                dependencyMethods(input, slice));
                        inputBindings.add(inputBinding);
                    }
                }
                if (framePrestatePort != null) {
                    String framePortId = string(framePrestatePort.get(
                            "portId"));
                    selectedPorts.add(framePortId);
                    Map<String, Object> frameBinding = null;
                    for (Map<String, Object> binding : inputBindings) {
                        if (outputCell.equals(string(binding.get(
                                "dependencyCell")))
                                && framePortId.equals(string(binding.get(
                                "inputPort")))) {
                            frameBinding = binding;
                            break;
                        }
                    }
                    if (frameBinding == null) {
                        frameBinding = object(
                                "dependencyCell", outputCell,
                                "inputPort", framePortId,
                                "bindingAuthority",
                                "EXACT_HEAP_PRESTATE_FRAME_CONDITION",
                                "dependencyMethods",
                                Collections.singletonList(region.rootMethod));
                        inputBindings.add(frameBinding);
                    } else {
                        frameBinding.put("bindingAuthority",
                                "EXACT_HEAP_PRESTATE_FRAME_CONDITION");
                        Set<String> frameMethods = new LinkedHashSet<>(
                                strings(frameBinding.get(
                                        "dependencyMethods")));
                        frameMethods.add(region.rootMethod);
                        frameBinding.put("dependencyMethods",
                                sorted(frameMethods));
                    }
                    // The exact frame port is the boundary representation for
                    // this output cell.  A provisional frontier-resolution
                    // gap for that same cell is therefore stale, not a second
                    // unresolved dependency.
                    unresolvedDetails.removeIf(detail ->
                            outputCell.equals(string(detail.get(
                                    "dependencyCell"))));
                }

                Set<String> sites = new LinkedHashSet<>();
                for (Map<String, Object> edge : slice.causalEdges) {
                    String site = string(edge.get("siteId"));
                    if (!site.isEmpty()) {
                        sites.add(site);
                    }
                }
                OutputCaptureSelection outputCapture = heapStateOutput
                        ? regionExitFieldCaptureBinding(
                        string(output.get("portId")), outputCell,
                        framePrestatePort)
                        // An ordinary root return is captured by exitRegion.
                        // Its projected cells are interpreted relative to
                        // that same returned object, so no call-argument hook
                        // is either necessary or authoritative here.
                        : OutputCaptureSelection.notRequired();
                Map<String, Object> outputSlice = object(
                        "outputPort", string(output.get("portId")),
                        "outputCell", outputCell,
                        "inputPorts", sorted(selectedPorts),
                        "inputBindings", inputBindings,
                        "methods", orderedMethods(slice.methods,
                                region.rootMethod),
                        "sites", sorted(sites),
                        "causalEdgeIds", causalEdgeIds(slice.causalEdges),
                        "truncationReasons", truncationReasons(slice),
                        "captureBindings", outputCapture.bindings,
                        "captureBindingIssues", outputCapture.issues,
                        "inputGaps", unresolvedDetails);
                result.add(outputSlice);
            }
            return result;
        }

        /**
         * A field output is read at normal region exit.  Reuse its exact
         * entry-state input when present, otherwise add the field port used
         * to resolve the concrete root-to-owner path.  Container values are
         * not reconstructed from write sites: the custom VM returns the
         * activation's final ContainerRelation for this object.
         */
        private Map<String, Object> ensureFramePrestatePort(
                RegionDraft region, String outputCell,
                List<Map<String, Object>> inputPorts) {
            Map<String, Object> exact = null;
            for (Map<String, Object> input : inputPorts) {
                if (!outputCell.equals(string(input.get("cell")))) {
                    continue;
                }
                if (exact != null) {
                    return null;
                }
                exact = input;
            }
            if (exact == null) {
                if (inputPorts.size() >= MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS) {
                    return null;
                }
                exact = object(
                        "portId", region.regionId + ".in."
                                + inputPorts.size(),
                        "cell", outputCell,
                        "javaType", cellJavaType(outputCell),
                        "projection", "value");
                inputPorts.add(exact);
            }
            exact.put("sourceKind", "HEAP_PRESTATE");
            return exact;
        }

        private boolean exactLocalCell(String method, String cell) {
            return !exactLocalName(method, cell).isEmpty();
        }

        private String exactLocalName(String method, String cell) {
            String prefix = string(method) + "::";
            String value = string(cell);
            if (method.isEmpty() || !value.startsWith(prefix)) {
                return "";
            }
            String local = value.substring(prefix.length());
            return local.matches("[$A-Za-z_][$A-Za-z0-9_]*")
                    ? local : "";
        }

        private DeclaredField declaredField(String value) {
            String signature = string(value);
            DeclaredField field = FieldPathSpec.declaredField(signature);
            if (field == null || !field.signature().equals(signature)) {
                return null;
            }
            return field;
        }

        private boolean declaredMetadataMatches(
                Map<String, Object> edge, DeclaredField field) {
            return field != null
                    && field.signature().equals(string(edge.get(
                    "declaredFieldSignature")));
        }

        private OutputCaptureSelection regionExitFieldCaptureBinding(
                String outputPort, String outputCell,
                Map<String, Object> framePrestatePort) {
            DeclaredField field = declaredField(outputCell);
            if (field == null) {
                return OutputCaptureSelection.notRequired();
            }
            if (outputPort.isEmpty() || framePrestatePort == null) {
                return new OutputCaptureSelection(
                        Collections.<Map<String, Object>>emptyList(),
                        Collections.singletonList(
                        "NORMAL_EXIT_FIELD_ACCESS_ROOT_NOT_PROVEN"));
            }
            Map<String, Object> binding = object(
                    "captureBindingId", outputPort + ".exit-field",
                    "outputPort", outputPort,
                    "outputCell", outputCell,
                    "accessRootInputPort", string(framePrestatePort.get(
                            "portId")),
                    "fieldPath", Collections.singletonList(field.name()),
                    "fieldSignature", field.signature(),
                    "javaType", field.type());
            return new OutputCaptureSelection(
                    Collections.singletonList(binding),
                    Collections.<String>emptyList());
        }

        /**
         * A demand walk may enter a synchronous helper omitted by the compact
         * exception region and expose an opaque call result used by a guard
         * (most importantly, object nullness).  Such a result has a concrete
         * capture point and can be promoted to the region frontier.  Other
         * missing aliases remain unresolved: in particular, this must not
         * paper over a missing caller-to-callee parameter relation.
         */
        private boolean materializableOpaqueCallResult(
                String cell, RegionDraft slice) {
            if (!cell.endsWith(">.return")) {
                return false;
            }
            String producer = methodForCell(cell);
            return !producer.isEmpty()
                    && !slice.methods.contains(producer)
                    && boundaryInput(cell, slice.rootMethod);
        }

        private boolean outputSliceFrontierPromotable(
                String cell, RegionDraft slice) {
            return materializableOpaqueCallResult(cell, slice)
                    || causalActivationParameter(cell, slice)
                    || materializableDeclaredFieldPath(cell, slice)
                    || materializableDeclaredFieldAccess(cell, slice) != null;
        }

        private Set<String> causalActivationParameters(RegionDraft slice) {
            Set<String> result = new LinkedHashSet<>();
            for (String cell : slice.causalCells) {
                if (causalActivationParameter(cell, slice)) {
                    result.add(cell);
                }
            }
            return result;
        }

        private boolean causalActivationParameter(
                String cell, RegionDraft slice) {
            String method = methodForCell(cell);
            return slice.methods.contains(method)
                    && !cell.contains("#")
                    && exactParameterCell(method, cell);
        }

        /**
         * Carries the exact declaration and access site into the runtime
         * action for a promoted bare field.  The port is a field-family
         * template: runtime object identity (and, for map iteration, the
         * exact entry/key cursor) still selects each concrete instance.
         */
        private void addOutputSliceFrontierMaterializationMetadata(
                Map<String, Object> port, String cell, RegionDraft slice) {
            DeclaredFieldPathAccess pathAccess =
                    materializableDeclaredFieldPathAccess(cell, slice);
            if (pathAccess != null) {
                addDeclaredFieldPathMaterializationMetadata(port,
                        pathAccess);
                return;
            }
            DeclaredFieldAccess access = materializableDeclaredFieldAccess(
                    cell, slice);
            if (access == null) {
                return;
            }
            addDeclaredFieldAccessMaterializationMetadata(port, access,
                    slice);
        }

        private void addDeclaredFieldAccessMaterializationMetadata(
                Map<String, Object> port, DeclaredFieldAccess access,
                RegionDraft slice) {
            if (access.accessorCall) {
                admitPostSelectionSliceMethod(slice,
                        access.accessorImplementationMethod);
                port.put("materialization", MaterializationSpec
                        .accessorReturn(access.field.type(),
                                access.field.signature(),
                                Collections.singletonList(
                                        access.field.name()),
                                access.method, access.unitIndex,
                                access.invokedMethod,
                                access.accessorImplementationMethod)
                        .toMap());
            } else if (directFieldLeafType(access.field.type())) {
                port.put("materialization", MaterializationSpec.fieldRead(
                        access.field.type(), access.field.signature(),
                        access.field.signature(),
                        Collections.singletonList(access.field.name()),
                        Collections.<String>emptyList(),
                        access.accessSites).toMap());
            }
        }

        private void addDeclaredFieldPathMaterializationMetadata(
                Map<String, Object> port,
                DeclaredFieldPathAccess access) {
            port.put("materialization", MaterializationSpec.fieldRead(
                    access.leafField.type(), access.rootField.signature(),
                    access.leafField.signature(), access.fieldPath,
                    access.proofEdgeIds,
                    Collections.singletonList(access.siteId())).toMap());
        }

        /**
         * Carries the one exact field access selected by the region graph
         * onto every canonical input, including accesses that occur only
         * after a future branch flip. Primitive fields use the lazy field
         * hook; boxed references stay concrete and are symbolized only by an
         * exact primitive accessor-return projection.
         */
        private void addRegionInputMaterializationMetadata(
                Map<String, Object> port, String cell, RegionDraft region) {
            DeclaredFieldPathAccess pathAccess =
                    materializableDeclaredFieldPathAccess(cell, region);
            if (pathAccess != null) {
                addDeclaredFieldPathMaterializationMetadata(port,
                        pathAccess);
                return;
            }
            DeclaredFieldAccess access = materializableDeclaredFieldAccess(
                    cell, region);
            if (access != null) {
                addDeclaredFieldAccessMaterializationMetadata(port, access,
                        region);
            }
        }

        /**
         * Region ports are shared by all requested-output activations.  If a
         * bare field was promoted with one exact read site, another output
         * slice may reuse it only when it proves that same site.  Otherwise a
         * later slice would appear complete while its runtime action could
         * never match the different field read.
         */
        private boolean promotedDeclaredFieldPortCompatible(
                String cell, String portId,
                List<Map<String, Object>> inputPorts, RegionDraft slice) {
            Map<String, Object> port = inputPort(portId, inputPorts);
            if (port == null) {
                return false;
            }
            Map<String, Object> spec = materialization(port);
            if (cell.contains("#field:")) {
                DeclaredFieldPathAccess access =
                        materializableDeclaredFieldPathAccess(cell, slice);
                boolean pathConstrained = strings(spec.get("path"))
                        .size() > 1;
                if (access != null || pathConstrained) {
                    return access != null
                        && "FIELD_READ".equals(string(spec.get("kind")))
                        && access.rootField.signature().equals(string(spec.get(
                        "rootField")))
                        && access.leafField.signature().equals(string(spec.get(
                        "leafField")))
                        && Collections.singletonList(access.siteId()).equals(
                        strings(spec.get("accessSites")))
                        && access.fieldPath.equals(strings(spec.get("path")));
                }
            }
            boolean constrained = !spec.isEmpty();
            if (!constrained) {
                return true;
            }
            return matchingPromotedDeclaredFieldAccess(cell, port, slice)
                    != null;
        }

        /**
         * A dependency may resolve either to its exact executable port or to
         * a different canonical cell through a proven projection chain.  In
         * both cases that identity proof, rather than a second access-site
         * comparison against the dependency's local view, establishes
         * compatibility.  Still require executable leaf metadata so a broad
         * carrier cannot bypass ordinary materialization checks.
         */
        private boolean exactMaterializableAliasResolution(
                InputPortResolution resolution,
                List<Map<String, Object>> inputPorts) {
            if (resolution == null
                    || !("EXACT_CELL_IDENTITY".equals(resolution.authority)
                    || "UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN".equals(
                    resolution.authority)
                    || "UNIQUE_EXACT_DECLARED_FIELD_LEAF".equals(
                    resolution.authority))) {
                return false;
            }
            Map<String, Object> port = inputPort(resolution.portId,
                    inputPorts);
            return port != null && exactAliasMaterializationPort(port);
        }

        private void admitCompatibleAccessorImplementationMethod(
                String cell, String portId,
                List<Map<String, Object>> inputPorts, RegionDraft slice) {
            Map<String, Object> port = inputPort(portId, inputPorts);
            if (port == null) {
                return;
            }
            DeclaredFieldAccess access =
                    matchingPromotedDeclaredFieldAccess(cell, port, slice);
            if (access != null && access.accessorCall) {
                admitPostSelectionSliceMethod(slice,
                        access.accessorImplementationMethod);
            }
        }

        private void admitPostSelectionSliceMethod(
                RegionDraft slice, String method) {
            if (method.isEmpty() || !slice.methods.add(method)) {
                return;
            }
            slice.clearAnalysisCache();
        }

        private Map<String, Object> inputPort(
                String portId, List<Map<String, Object>> inputPorts) {
            for (Map<String, Object> candidate : inputPorts) {
                if (portId.equals(string(candidate.get("portId")))) {
                    return candidate;
                }
            }
            return null;
        }

        @SuppressWarnings("unchecked")
        private Map<String, Object> materialization(
                Map<String, Object> port) {
            Object value = port == null ? null : port.get("materialization");
            return value instanceof Map
                    ? (Map<String, Object>) value
                    : Collections.<String, Object>emptyMap();
        }

        /**
         * Revalidates a shared promoted field port against the dependency in
         * one particular requested-output slice.  Metadata on the port is not
         * authority by itself: it must exactly reproduce the field access
         * proven by this slice's causal edge.
         */
        private DeclaredFieldAccess matchingPromotedDeclaredFieldAccess(
                String cell, Map<String, Object> port, RegionDraft slice) {
            Map<String, Object> spec = materialization(port);
            DeclaredField field = declaredField(cell);
            if (field == null
                    || !field.signature().equals(string(spec.get(
                    "rootField")))) {
                return null;
            }
            DeclaredFieldAccess selected =
                    materializableDeclaredFieldAccess(cell, slice);
            if (selected == null) {
                return null;
            }
            boolean matches = selected.accessorCall
                    ? "ACCESSOR_RETURN".equals(string(spec.get("kind")))
                    && selected.method.equals(string(spec.get("method")))
                    && selected.unitIndex == integer(spec.get(
                    "unitIndex"), -1)
                    && selected.invokedMethod.equals(string(spec.get(
                    "declaredCallee")))
                    && selected.accessorImplementationMethod.equals(
                    string(spec.get("implementationMethod")))
                    : "FIELD_READ".equals(string(spec.get("kind")))
                    && selected.accessSites.equals(
                    strings(spec.get("accessSites")));
            return matches ? selected : null;
        }

        private DeclaredFieldAccess declaredFieldAccessAtEdge(
                Map<String, Object> edge, DeclaredField field,
                RegionDraft slice) {
            if (!field.signature().equals(string(edge.get("fromCell")))
                    || !"HEAP_READ".equals(string(edge.get(
                    "transferKind")))) {
                return null;
            }
            String method = string(edge.get("method"));
            String siteId = string(edge.get("siteId"));
            String kind = string(edge.get("kind"));
            String invokedMethod = string(edge.get("invoke"));
            boolean accessorCall = kind.contains("accessor")
                    && kind.contains("field_return");
            String implementation = string(edge.get(
                    "accessorImplementationMethod"));
            int unitIndex = integer(edge.get("unitIndex"), -1);
            if (!slice.methods.contains(method)
                    || !exactStaticValueFlow(edge)
                    || !declaredMetadataMatches(edge, field)
                    || method.isEmpty() || unitIndex < 0
                    || !siteId.equals(method + "#u" + unitIndex)
                    || string(edge.get("toCell")).isEmpty()
                    || accessorCall != !invokedMethod.isEmpty()
                    || accessorCall && implementation.isEmpty()
                    || !accessorCall && !kind.contains("field_read")) {
                return null;
            }
            String receiverCell = "";
            List<String> accessSites = Collections.emptyList();
            if (!accessorCall) {
                Object staticness = edge.get("declaredFieldStatic");
                if (!(staticness instanceof Boolean)) {
                    return null;
                }
                if (!Boolean.TRUE.equals(staticness)) {
                    Map<String, Object> instance =
                            pairedInstanceFieldRead(edge, field, slice);
                    if (instance == null) {
                        return null;
                    }
                    receiverCell = canonicalFieldReceiver(
                            string(instance.get("objectFromCell")), slice);
                }
                accessSites = Collections.singletonList(siteId);
            }
            return new DeclaredFieldAccess(field, method, unitIndex,
                    accessorCall, invokedMethod, implementation,
                    receiverCell, accessSites);
        }

        private String canonicalFieldReceiver(
                String receiver, RegionDraft slice) {
            Map<String, Object> definition = unique(
                    analysisGraph(slice).incoming(receiver),
                    edge -> "instance_field_read".equals(string(edge.get(
                            "kind")))
                            && exactStaticValueFlow(edge)
                            && Boolean.TRUE.equals(edge.get("fieldSensitive"))
                            && receiver.equals(string(edge.get("toCell")))
                            && receiver.equals(string(edge.get(
                            "objectToCell")))
                            && !string(edge.get("fromCell")).isEmpty());
            return definition == null ? receiver
                    : string(definition.get("fromCell"));
        }

        /**
         * Returns the unique receiver-sensitive row paired with one canonical
         * declared-field read.  The pair shares the exact bytecode site and
         * target local; its receiver cell is the stable identity that lets
         * several control-flow alternatives consume one logical field input.
         */
        private Map<String, Object> pairedInstanceFieldRead(
                Map<String, Object> declaredRead, DeclaredField field,
                RegionDraft slice) {
            Map<String, Object> selected = null;
            for (Map<String, Object> candidate
                    : analysisGraph(slice).edges()) {
                String receiver = string(candidate.get("objectFromCell"));
                if (!"instance_field_read".equals(string(candidate.get(
                        "kind")))
                        || !exactStaticValueFlow(candidate)
                        || !Boolean.TRUE.equals(candidate.get(
                        "fieldSensitive"))
                        || receiver.isEmpty()
                        || !sameExactReadSite(declaredRead, candidate)
                        || !string(declaredRead.get("toCell")).equals(
                        string(candidate.get("toCell")))
                        || !string(declaredRead.get("toCell")).equals(
                        string(candidate.get("objectToCell")))
                        || !(receiver + "#field:" + field.name()).equals(
                        string(candidate.get("fromCell")))
                        || !declaredMetadataMatches(candidate, field)) {
                    continue;
                }
                if (selected != null) {
                    return null;
                }
                selected = candidate;
            }
            return selected;
        }

        /**
         * A bare canonical field is one logical materialization even when
         * control flow reads it at several sites.  Every site must have an
         * exact receiver-sensitive pair, and all pairs must name the same
         * receiver cell; otherwise same-declaration fields on distinct
         * objects would be conflated.
         */
        private DeclaredFieldAccess materializableDeclaredFieldAccess(
                String cell, RegionDraft slice) {
            DeclaredField field = declaredField(cell);
            if (field == null || !closedProtocolScalarType(field.type())) {
                return null;
            }

            DeclaredFieldAccess selected = null;
            for (Map<String, Object> edge
                    : analysisGraph(slice).outgoing(cell)) {
                if (!"HEAP_READ".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                DeclaredFieldAccess candidate = declaredFieldAccessAtEdge(
                        edge, field, slice);
                if (candidate == null) {
                    return null;
                }
                selected = selected == null
                        ? candidate : selected.merge(candidate);
                if (selected == null) return null;
            }
            return selected;
        }

        /**
         * A projected heap frontier is directly materializable when it starts
         * at one exact declared field and the selected causal slice contains
         * an authoritative field-sensitive projection for precisely the same
         * root and path.  The runtime hook can then match the declared root
         * owner/field and follow the remaining path on that concrete object.
         * Bare local projections and projection rows with conflicting metadata
         * deliberately remain unresolved.
         */
        private boolean materializableDeclaredFieldPath(
                String cell, RegionDraft slice) {
            int projection = cell.indexOf("#field:");
            if (projection < 0) {
                return false;
            }
            String root = cell.substring(0, projection);
            String path = cell.substring(projection);
            DeclaredField field = declaredField(root);
            if (field == null || closedProtocolScalarType(field.type())
                    || !path.matches("(?:#field:[^#]+)+")) {
                return false;
            }
            boolean exactProof = false;
            for (Map<String, Object> edge : slice.causalEdges) {
                if (!cell.equals(string(edge.get("fromCell")))) {
                    continue;
                }
                if (!exactStaticValueFlow(edge)
                        || !Boolean.TRUE.equals(edge.get("fieldSensitive"))
                        || !root.equals(string(edge.get("objectFromCell")))
                        || !path.equals(string(edge.get("fieldPath")))) {
                    return false;
                }
                exactProof = true;
            }
            return exactProof;
        }

        /**
         * Proves the complete direct-getfield chain represented by a
         * projected canonical field cell.  Projected rows alone are not
         * sufficient: each segment must have one canonical declared read,
         * one receiver-local read, and (while a suffix remains) their exact
         * paired projections.  The graph's existing four-segment path bound
         * is preserved.  Any missing or duplicate segment fails closed.
         */
        private DeclaredFieldPathAccess
        materializableDeclaredFieldPathAccess(
                String cell, RegionDraft slice) {
            int projectionIndex = cell.indexOf("#field:");
            if (projectionIndex < 0) {
                return null;
            }
            String rootCell = cell.substring(0, projectionIndex);
            String suffix = cell.substring(projectionIndex);
            DeclaredField rootField = declaredField(rootCell);
            List<String> suffixSegments = fieldPathSegments(suffix);
            if (rootField == null || closedProtocolScalarType(rootField.type())
                    || suffixSegments.isEmpty()
                    || 1 + suffixSegments.size() > 4) {
                return null;
            }

            Map<String, Object> rootProjection = uniqueExactProjection(
                    slice, "projected_field_read", cell, rootCell, suffix,
                    "", suffix);
            if (rootProjection == null) {
                return null;
            }
            Map<String, Object> rootDeclaredRead = exactProjectionBase(
                    rootProjection, "field_read", rootField.signature(),
                    string(rootProjection.get("objectToCell")));
            if (rootDeclaredRead == null
                    || !exactDeclaredGetfieldUnit(rootDeclaredRead,
                    rootField, "")) {
                return null;
            }

            List<String> fullPath = new ArrayList<>();
            fullPath.add(rootField.name());
            fullPath.addAll(suffixSegments);
            String fullPathSuffix = fieldPathSuffix(fullPath);
            String rootResult = string(rootProjection.get("objectToCell"));
            Map<String, Object> rootInstanceProjection =
                    uniqueExactProjection(slice,
                            "projected_instance_field_read", "", "",
                            fullPathSuffix, rootResult,
                            suffix);
            if (rootInstanceProjection == null) {
                return null;
            }
            String accessOwnerCell = string(rootInstanceProjection.get(
                    "objectFromCell"));
            Map<String, Object> rootInstanceRead = exactProjectionBase(
                    rootInstanceProjection, "instance_field_read",
                    accessOwnerCell + "#field:" + rootField.name(),
                    rootResult);
            if (rootInstanceRead == null
                    || !sameExactReadSite(rootDeclaredRead,
                    rootInstanceRead)
                    || !exactDeclaredGetfieldUnit(rootInstanceRead,
                    rootField, accessOwnerCell)) {
                return null;
            }

            Set<String> proofIds = new LinkedHashSet<>();
            addProofEdgeIds(proofIds, rootProjection, rootDeclaredRead,
                    rootInstanceProjection, rootInstanceRead);
            List<String> aliases = new ArrayList<>();
            aliases.add(cell);
            String currentLocal = rootResult;
            String expectedOwner = rootField.type();
            List<String> remaining = new ArrayList<>(suffixSegments);
            DeclaredField leafField = null;

            while (!remaining.isEmpty()) {
                String segment = remaining.get(0);
                List<String> tail = new ArrayList<>(remaining.subList(1,
                        remaining.size()));
                if (tail.isEmpty()) {
                    Map<String, Object>[] pair =
                            uniqueDirectFieldReadPair(slice, currentLocal,
                                    expectedOwner, segment);
                    if (pair == null) {
                        return null;
                    }
                    leafField = declaredField(string(pair[0].get(
                            "fromCell")));
                    if (leafField == null
                            || !directFieldLeafType(leafField.type())) {
                        return null;
                    }
                    aliases.add(leafField.signature());
                    addProofEdgeIds(proofIds, pair[0], pair[1]);
                    break;
                }

                String remainingSuffix = fieldPathSuffix(remaining);
                String tailSuffix = fieldPathSuffix(tail);
                Map<String, Object> instanceProjection =
                        uniqueExactProjection(slice,
                                "projected_instance_field_read", "", "",
                                remainingSuffix, "", tailSuffix);
                if (instanceProjection == null
                        || !currentLocal.equals(string(instanceProjection.get(
                        "objectFromCell")))) {
                    return null;
                }
                String nextLocal = string(instanceProjection.get(
                        "objectToCell"));
                Map<String, Object> instanceRead = exactProjectionBase(
                        instanceProjection, "instance_field_read",
                        currentLocal + "#field:" + segment, nextLocal);
                if (instanceRead == null) {
                    return null;
                }
                Map<String, Object> declaredRead =
                        uniqueParallelDeclaredRead(instanceRead,
                                expectedOwner, segment);
                if (declaredRead == null) {
                    return null;
                }
                DeclaredField field = declaredField(string(
                        declaredRead.get("fromCell")));
                if (field == null
                        || !exactDeclaredGetfieldUnit(instanceRead, field,
                        currentLocal)) {
                    return null;
                }
                String canonicalProjectionCell = field.signature()
                        + tailSuffix;
                Map<String, Object> declaredProjection =
                        uniqueExactProjection(slice,
                                "projected_field_read",
                                canonicalProjectionCell, field.signature(),
                                tailSuffix, nextLocal, tailSuffix);
                if (declaredProjection == null
                        || !string(declaredRead.get("id")).equals(string(
                        declaredProjection.get("projectionBaseEdgeId")))) {
                    return null;
                }
                aliases.add(canonicalProjectionCell);
                addProofEdgeIds(proofIds, instanceProjection, instanceRead,
                        declaredRead, declaredProjection);
                currentLocal = nextLocal;
                expectedOwner = field.type();
                remaining = tail;
            }
            if (leafField == null || proofIds.contains("")) {
                return null;
            }
            return new DeclaredFieldPathAccess(cell, rootField, leafField,
                    string(rootDeclaredRead.get("method")), integer(
                    rootDeclaredRead.get("unitIndex"), -1),
                    accessOwnerCell, fullPath, aliases, proofIds);
        }

        private List<String> fieldPathSegments(String suffix) {
            if (!string(suffix).matches("(?:#field:[^#]+)+")) {
                return Collections.emptyList();
            }
            List<String> result = new ArrayList<>();
            Matcher matcher = FIELD_PATH_SEGMENT_PATTERN.matcher(suffix);
            while (matcher.find()) {
                result.add(matcher.group(1));
            }
            return result;
        }

        private String fieldPathSuffix(Collection<String> path) {
            StringBuilder result = new StringBuilder();
            for (String segment : path) {
                result.append("#field:").append(segment);
            }
            return result.toString();
        }

        private Map<String, Object> uniqueExactProjection(
                RegionDraft slice, String kind, String fromCell,
                String objectFromCell, String fieldPath,
                String objectToCell, String targetSuffix) {
            Map<String, Object> selected = null;
            for (Map<String, Object> edge : slice.causalEdges) {
                String targetObject = string(edge.get("objectToCell"));
                String expectedTarget = targetObject + targetSuffix;
                if (!kind.equals(string(edge.get("kind")))
                        || !exactStaticEdge(edge)
                        || !"HEAP_READ".equals(string(edge.get(
                        "transferKind")))
                        || !"value_flow".equals(string(edge.get(
                        "relation")))
                        || !Boolean.TRUE.equals(edge.get("fieldSensitive"))
                        || !"PROJECTED_EDGE_CANNOT_EXCEED_BASE_EDGE_V1"
                        .equals(string(edge.get("authorityInheritance")))
                        || !fromCell.isEmpty() && !fromCell.equals(string(
                        edge.get("fromCell")))
                        || !objectFromCell.isEmpty()
                        && !objectFromCell.equals(string(edge.get(
                        "objectFromCell")))
                        || !fieldPath.equals(string(edge.get("fieldPath")))
                        || !objectToCell.isEmpty()
                        && !objectToCell.equals(targetObject)
                        || !expectedTarget.equals(string(edge.get(
                        "toCell")))
                        || !exactLocalCell(string(edge.get("method")),
                        targetObject)
                        || string(edge.get("projectionBaseEdgeId")).isEmpty()) {
                    continue;
                }
                // The graph writer also publishes a synthetic projection
                // alias for demand propagation.  It is another view of the
                // same projectionBaseEdgeId, not a second accessor witness.
                // Only the projection attached to the concrete getfield
                // site can authorize runtime materialization.  Counting the
                // synthetic view as independent evidence made a two-hop
                // path (entry.value.state.guard.enabled) look ambiguous even
                // though every view named the same immutable base edge.
                if (syntheticProjectionAlias(edge, kind)) {
                    continue;
                }
                if (selected != null) {
                    return null;
                }
                selected = edge;
            }
            return selected;
        }

        private boolean syntheticProjectionAlias(
                Map<String, Object> edge, String kind) {
            String method = string(edge.get("method"));
            return !method.isEmpty()
                    && (method + "#synthetic:" + kind).equals(string(
                    edge.get("siteId")))
                    && integer(edge.get("unitIndex"), -1) < 0
                    && string(edge.get("unit")).isEmpty();
        }

        private Map<String, Object> exactProjectionBase(
                Map<String, Object> projection, String kind,
                String fromCell, String toCell) {
            String baseId = string(projection.get("projectionBaseEdgeId"));
            List<Map<String, Object>> matches = graph.withId(baseId);
            if (matches.size() != 1) {
                return null;
            }
            Map<String, Object> selected = matches.get(0);
            return kind.equals(string(selected.get("kind")))
                    && exactStaticEdge(selected)
                    && "HEAP_READ".equals(string(selected.get(
                    "transferKind")))
                    && "value_flow".equals(string(selected.get("relation")))
                    && fromCell.equals(string(selected.get("fromCell")))
                    && toCell.equals(string(selected.get("toCell")))
                    && sameExactReadSite(projection, selected)
                    ? selected : null;
        }

        private boolean sameExactReadSite(Map<String, Object> left,
                                          Map<String, Object> right) {
            return string(left.get("method")).equals(string(right.get(
                    "method")))
                    && string(left.get("siteId")).equals(string(right.get(
                    "siteId")))
                    && integer(left.get("unitIndex"), -1) == integer(
                    right.get("unitIndex"), -1)
                    && string(left.get("unit")).equals(string(right.get(
                    "unit")));
        }

        private boolean exactDeclaredGetfieldUnit(
                Map<String, Object> edge, DeclaredField field,
                String exactOwnerCell) {
            String method = string(edge.get("method"));
            String target = exactLocalName(method, string(edge.get(
                    "toCell")));
            String unit = string(edge.get("unit")).trim();
            if (target.isEmpty() || field == null) {
                return false;
            }
            if (!exactOwnerCell.isEmpty()) {
                String owner = exactLocalName(method, exactOwnerCell);
                return !owner.isEmpty() && unit.equals(target + " = "
                        + owner + "." + field.signature());
            }
            return unit.matches("^" + Pattern.quote(target)
                    + " = [$A-Za-z_][$A-Za-z0-9_]*\\."
                    + Pattern.quote(field.signature()) + "$");
        }

        @SuppressWarnings("unchecked")
        private Map<String, Object>[] uniqueDirectFieldReadPair(
                RegionDraft slice, String ownerCell, String expectedOwner,
                String fieldName) {
            Map<String, Object>[] result = null;
            for (Map<String, Object> instance : slice.causalEdges) {
                if (!"instance_field_read".equals(string(instance.get(
                        "kind"))) || !exactStaticEdge(instance)
                        || !"HEAP_READ".equals(string(instance.get(
                        "transferKind")))
                        || !"value_flow".equals(string(instance.get(
                        "relation")))
                        || !(ownerCell + "#field:" + fieldName).equals(
                        string(instance.get("fromCell")))) {
                    continue;
                }
                Map<String, Object> declared =
                        uniqueParallelDeclaredRead(instance, expectedOwner,
                                fieldName);
                if (declared != null) {
                    if (result != null) return null;
                    result = new Map[]{declared, instance};
                }
            }
            return result;
        }

        private Map<String, Object> uniqueParallelDeclaredRead(
                Map<String, Object> instance, String expectedOwner,
                String fieldName) {
            return unique(graph.incoming(string(instance.get("toCell"))),
                    edge -> {
                        DeclaredField field = declaredField(string(edge.get(
                                "fromCell")));
                        return field != null
                                && expectedOwner.equals(field.owner())
                                && fieldName.equals(field.name())
                                && "field_read".equals(string(edge.get(
                                "kind")))
                                && exactStaticEdge(edge)
                                && "HEAP_READ".equals(string(edge.get(
                                "transferKind")))
                                && "value_flow".equals(string(edge.get(
                                "relation")))
                                && sameExactReadSite(instance, edge)
                                && exactDeclaredGetfieldUnit(edge, field, "");
                    });
        }

        private void addProofEdgeIds(Set<String> target,
                                     Map<String, Object>... proofEdges) {
            for (Map<String, Object> edge : proofEdges) {
                target.add(string(edge.get("id")));
            }
        }

        /**
         * Recognizes an exact protocol value returned by the region root.
         *
         * <p>A scalar return needs only an exact authoritative boundary row.
         * A reference/array return also needs at least one authoritative
         * projected boundary row rooted at the same return.  This makes the
         * aggregate shape demand-driven and keeps an otherwise opaque object
         * fail-closed.  A projected return itself is accepted only when every
         * outbound row for that exact cell agrees on the base and field path.</p>
         */
        private boolean outboundProtocolReturnValue(
                RegionDraft region, String outputCell) {
            String sourceMethod = methodForCell(outputCell);
            if (sourceMethod.isEmpty()
                    || !region.methods.contains(sourceMethod)) {
                return false;
            }
            String base = sourceMethod + ".return";
            boolean projected = outputCell.startsWith(base + "#field:");
            if (!outputCell.equals(base) && !projected) {
                return false;
            }
            String returnType = declaredReturnType(sourceMethod);
            if (returnType.isEmpty() || "void".equals(returnType)) {
                return false;
            }

            // Protocol return capture relies on exitRegion and therefore
            // applies only to the region root.
            if (!sourceMethod.equals(region.rootMethod)) {
                return false;
            }

            List<Map<String, Object>> outbound =
                    exactOutboundBoundaryRows(region, outputCell);
            if (outbound.isEmpty()) {
                return false;
            }
            if (projected) {
                String path = outputCell.substring(base.length());
                for (Map<String, Object> edge : outbound) {
                    if (!exactProjectedOutboundBoundary(edge, base, path)) {
                        return false;
                    }
                }
                return true;
            }
            if (closedProtocolScalarType(returnType)) {
                return true;
            }
            return hasExactProjectedOutboundBoundary(region, base);
        }

        private List<Map<String, Object>> exactOutboundBoundaryRows(
                RegionDraft region, String outputCell) {
            List<Map<String, Object>> result = new ArrayList<>();
            boolean rejected = false;
            for (Map<String, Object> edge : graph.outgoing(outputCell)) {
                if (!isBoundary(edge)) {
                    continue;
                }
                String targetMethod = methodForCell(
                        string(edge.get("toCell")));
                if (targetMethod.isEmpty()) {
                    targetMethod = string(edge.get("method"));
                }
                if (targetMethod.isEmpty()
                        || region.methods.contains(targetMethod)) {
                    continue;
                }
                if (!exactStaticValueFlow(edge)) {
                    rejected = true;
                    continue;
                }
                result.add(edge);
            }
            return rejected ? Collections.<Map<String, Object>>emptyList()
                    : result;
        }

        private boolean hasExactProjectedOutboundBoundary(
                RegionDraft region, String base) {
            for (Map<String, Object> edge : boundaryEdges) {
                String from = string(edge.get("fromCell"));
                if (!from.startsWith(base + "#field:")) {
                    continue;
                }
                List<Map<String, Object>> exact =
                        exactOutboundBoundaryRows(region, from);
                if (exact.isEmpty()) {
                    continue;
                }
                String path = from.substring(base.length());
                boolean complete = true;
                for (Map<String, Object> candidate : exact) {
                    if (!exactProjectedOutboundBoundary(candidate, base,
                            path)) {
                        complete = false;
                        break;
                    }
                }
                if (complete) {
                    return true;
                }
            }
            return false;
        }

        private boolean exactProjectedOutboundBoundary(
                Map<String, Object> edge, String base, String path) {
            return exactStaticValueFlow(edge)
                    && isBoundary(edge)
                    && Boolean.TRUE.equals(edge.get("fieldSensitive"))
                    && base.equals(string(edge.get("objectFromCell")))
                    && path.equals(string(edge.get("fieldPath")))
                    && (base + path).equals(string(edge.get("fromCell")));
        }

        /** Exact value-flow authority shared by materializable frontiers and
         * outbound return projections. */
        private boolean exactStaticValueFlow(Map<String, Object> edge) {
            return "value_flow".equals(string(edge.get("relation")))
                    && StaticDataflowEdgeSchema.automaticSemantics(edge)
                    && !string(edge.get("id")).isEmpty();
        }

        private boolean exactStaticEdge(Map<String, Object> edge) {
            String method = string(edge.get("method"));
            int unitIndex = integer(edge.get("unitIndex"), -1);
            return !isBoundary(edge)
                    && exactStaticValueFlow(edge)
                    && !method.isEmpty()
                    && unitIndex >= 0
                    && (method + "#u" + unitIndex).equals(string(
                    edge.get("siteId")));
        }

        /** Strict scalar allow-list; arrays, streams, maps, and opaque objects
         * deliberately do not become protocol-output demand roots. */
        private boolean closedProtocolScalarType(String type) {
            return directFieldLeafType(type)
                    || "java.lang.Boolean".equals(type)
                    || "java.lang.Byte".equals(type)
                    || "java.lang.Short".equals(type)
                    || "java.lang.Integer".equals(type)
                    || "java.lang.Long".equals(type)
                    || "java.lang.Character".equals(type)
                    || "java.lang.Float".equals(type)
                    || "java.lang.Double".equals(type)
                    || "java.lang.String".equals(type);
        }

        /** The custom-JDK field hook has exact scalar semantics for JVM
         * primitive fields; boxed references and Strings remain concrete. */
        private boolean directFieldLeafType(String type) {
            return "boolean".equals(type) || "byte".equals(type)
                    || "short".equals(type) || "int".equals(type)
                    || "long".equals(type) || "char".equals(type)
                    || "float".equals(type) || "double".equals(type);
        }

        /**
         * Records the selected method(s) that consume one slice input.  A
         * static region may contain mutually exclusive construction and
         * update paths.  Runtime refinement uses this provenance to discard
         * inputs belonging only to an unobserved alternative; the dependency
         * cell's own method is insufficient for opaque call returns.
         */
        private List<String> dependencyMethods(String input,
                                               RegionDraft slice) {
            Set<String> result = new LinkedHashSet<>();
            String cellMethod = methodForCell(input);
            if (slice.methods.contains(cellMethod)) {
                // Method-local and receiver-projection cells already carry
                // an unambiguous owning method even when the bounded causal
                // slice has no separate leaf-consumption edge for the alias.
                result.add(cellMethod);
            }
            String inputField = semanticFieldKey(input, slice.rootMethod);
            for (Map<String, Object> edge : analysisGraph(slice).edges()) {
                String method = string(edge.get("method"));
                if (method.isEmpty()) {
                    continue;
                }
                String source = string(edge.get("fromCell"));
                boolean consumesInput = input.equals(source);
                if (!consumesInput && !inputField.isEmpty()) {
                    consumesInput = inputField.equals(semanticFieldKey(source,
                            slice.rootMethod));
                }
                // A container mutation reads the receiver's old heap state
                // even though the static edge is represented as a write.
                if (!consumesInput
                        && "field_mutation".equals(string(edge.get("kind")))) {
                    consumesInput = inputField.equals(semanticFieldKey(
                            string(edge.get("toCell")), slice.rootMethod));
                }
                if (consumesInput) {
                    result.add(method);
                }
            }
            return sorted(result);
        }

        private RegionDraft outputSlice(RegionDraft region,
                                        String outputCell) {
            RegionDraft slice = new RegionDraft(region.anchorMethod);
            slice.regionId = region.regionId;
            slice.rootMethod = region.rootMethod;
            slice.exceptionDirected = true;
            // The broad region frontier has its own 64-method budget.  This
            // requested-output walk is rebuilt from the full static graph and
            // is governed by the independent exact-slice budgets below, so a
            // broad-frontier truncation is not inherited.
            // The exception-directed region is intentionally compact and can
            // omit a synchronous helper whose writes were irrelevant to the
            // original exception seed.  A demand slice for another output
            // must nevertheless be allowed to enter such a helper.  Typical
            // examples are a value-object constructor and an accessor used to
            // construct a protocol scalar.  Restricting this walk to
            // region.methods strands the constructed object's fields at an
            // artificial frontier and loses their real operands.
            //
            // Expand only along indexed, non-boundary call edges reachable
            // from the same region root.  Protocol/thread boundaries are not
            // present in calleesByCaller, so a remote writer cannot be folded
            // into this same-thread slice.
            Set<String> sameThreadMethods = sameThreadReachableMethods(
                    region.rootMethod);
            slice.causalCellBudgetTruncated |= addBackwardDependencies(
                    slice.causalEdges, slice.causalCells,
                    Collections.singletonList(outputCell), sameThreadMethods);

            Set<String> writerMethods = new LinkedHashSet<>();
            for (Map<String, Object> edge : slice.causalEdges) {
                String method = string(edge.get("method"));
                if (sameThreadMethods.contains(method)) {
                    writerMethods.add(method);
                }
            }
            for (String writer : writerMethods) {
                List<String> path = shortestPath(region.rootMethod, writer);
                if (path.isEmpty()) {
                    slice.methods.add(writer);
                } else {
                    slice.methods.addAll(path);
                    addRequiredCallPathGuards(slice, path,
                            sameThreadMethods);
                }
            }
            if (slice.methods.isEmpty()) {
                slice.methods.add(region.rootMethod);
            }
            for (Map<String, Object> edge : slice.causalEdges) {
                String method = string(edge.get("method"));
                if (sameThreadMethods.contains(method)) {
                    slice.methods.add(method);
                }
            }
            // Keep each concrete Jimple decision that directly consumes a
            // value in the output dependency closure.  Short-circuit
            // lowering can make both successors eventually reach an output
            // definition, so no path-guard edge exists even though the
            // decision selects which later definition/return is used.
            // Omitting that site folds its VM predicate into the next branch
            // window and makes replay occurrence identity unstable.
            for (Map<String, Object> edge
                    : graph.forMethods(slice.methods)) {
                if ("GUARD".equals(string(edge.get("transferKind")))
                        && slice.causalCells.contains(
                        string(edge.get("fromCell")))) {
                    slice.causalEdges.add(edge);
                }
            }
            admitExactAccessorImplementationMethods(slice);
            slice.methodBudgetTruncated = slice.methods.size()
                    > MAX_REQUESTED_OUTPUT_SLICE_METHODS;
            return slice;
        }

        /**
         * Admits the statically resolved implementation of an accessor call
         * represented by a requested-output dependency edge.
         *
         * <p>The compact call graph is keyed by the declared invocation
         * signature.  For an inherited getter, that signature can name a
         * subclass which has no method body or symbolic plan even though
         * Soot resolved the implementation in a superclass.  The synthetic
         * {@code accessor_field_return} edge already carries that resolution,
         * but the ordinary method walk previously ignored it.  Runtime then
         * observed the real getter and (correctly) rejected it as outside the
         * static requested-output slice.</p>
         *
         * <p>Do not admit a method merely because runtime happened to call
         * it.  Every admission below is tied to one exact static tuple:
         * declared field identity, caller, unit/site, declared callee, and
         * Soot-resolved implementation.  The implementation must also have a
         * static symbolic plan and the declared/implemented method
         * subsignatures must agree.  A malformed or runtime-only candidate is
         * left out so runtime refinement remains fail closed.</p>
         */
        private void admitExactAccessorImplementationMethods(
                RegionDraft slice) {
            Set<String> admitted = new LinkedHashSet<>();
            for (Map<String, Object> edge : slice.causalEdges) {
                if (!"HEAP_READ".equals(string(edge.get("transferKind")))
                        || !"accessor_field_return".equals(
                        string(edge.get("kind")))) {
                    continue;
                }
                DeclaredField field = declaredField(
                        string(edge.get("fromCell")));
                String caller = string(edge.get("method"));
                int unitIndex = integer(edge.get("unitIndex"), -1);
                String siteId = string(edge.get("siteId"));
                String declaredCallee = string(edge.get("invoke"));
                String implementation = string(edge.get(
                        "accessorImplementationMethod"));
                String declaredSubSignature = methodSubSignature(
                        declaredCallee);
                String implementationSubSignature = methodSubSignature(
                        implementation);
                if (field == null
                        || !slice.methods.contains(caller)
                        || !exactStaticValueFlow(edge)
                        || !declaredMetadataMatches(edge, field)
                        || caller.isEmpty() || unitIndex < 0
                        || !siteId.equals(caller + "#u" + unitIndex)
                        || string(edge.get("toCell")).isEmpty()
                        || declaredCallee.isEmpty()
                        || implementation.isEmpty()
                        || !graph.hasMethod(implementation)
                        || declaredSubSignature.isEmpty()
                        || !declaredSubSignature.equals(
                                implementationSubSignature)
                        || !field.type().equals(
                                declaredReturnType(declaredCallee))
                        || !field.type().equals(
                                declaredReturnType(implementation))) {
                    continue;
                }
                String identity = field.signature() + "\n" + caller + "\n"
                        + siteId + "\n" + unitIndex + "\n"
                        + declaredCallee + "\n" + implementation;
                if (!admitted.add(identity)) {
                    continue;
                }
                slice.methods.add(implementation);
            }
        }

        private String methodSubSignature(String method) {
            String value = string(method);
            int colon = value.indexOf(':');
            if (!value.startsWith("<") || !value.endsWith(">")
                    || colon < 1 || colon + 1 >= value.length() - 1) {
                return "";
            }
            return value.substring(colon + 1, value.length() - 1).trim();
        }

        private Set<String> sameThreadReachableMethods(String rootMethod) {
            Set<String> reachable = new LinkedHashSet<>();
            Deque<String> queue = new ArrayDeque<>();
            if (!rootMethod.isEmpty()
                    && graph.hasMethod(rootMethod)) {
                reachable.add(rootMethod);
                queue.add(rootMethod);
            }
            while (!queue.isEmpty()
                    && reachable.size() <= graph.methods().size()) {
                String method = queue.removeFirst();
                for (String callee : values(calleesByCaller.get(method))) {
                    if (graph.hasMethod(callee)
                            && reachable.add(callee)) {
                        queue.addLast(callee);
                    }
                }
            }
            return reachable;
        }

        private InputPortResolution inputPortForCell(
                String cell, List<Map<String, Object>> inputPorts,
                String rootMethod, RegionDraft slice) {
            // An exact port cell is already the canonical boundary value.
            // Do not walk its own projected aliases and then downgrade that
            // identity into another representation of the same leaf.
            for (Map<String, Object> input : inputPorts) {
                if (cell.equals(string(input.get("cell")))
                        && (!cell.contains("#field:")
                        || exactAliasMaterializationPort(input))) {
                    InputPortResolution leaf =
                            uniqueDeclaredLeafPort(input, inputPorts);
                    if (!leaf.portId.isEmpty()) {
                        return leaf;
                    }
                    return new InputPortResolution(
                            string(input.get("portId")),
                            "EXACT_CELL_IDENTITY");
                }
            }
            InputPortResolution projectedCarrier =
                    exactProjectedValueCarrier(cell, inputPorts, slice);
            if (!projectedCarrier.portId.isEmpty()) {
                return projectedCarrier;
            }
            InputPortResolution declaredLeaf =
                    uniquePortForDeclaredLeaf(cell, inputPorts);
            if (!declaredLeaf.portId.isEmpty()) {
                return declaredLeaf;
            }
            InputPortResolution projectedAliasCarrier =
                    exactProjectedAliasCarrier(cell, inputPorts, slice);
            if (!projectedAliasCarrier.portId.isEmpty()) {
                return projectedAliasCarrier;
            }
            String semantic = semanticFieldKey(cell, rootMethod);
            if (!semantic.isEmpty()) {
                String match = "";
                for (Map<String, Object> input : inputPorts) {
                    String inputCell = string(input.get("cell"));
                    if (syntheticValueProjection(inputCell)
                            || !semantic.equals(semanticFieldKey(
                            inputCell, rootMethod))) {
                        continue;
                    }
                    if (!match.isEmpty()) {
                        match = "";
                        break;
                    }
                    match = string(input.get("portId"));
                }
                if (!match.isEmpty()) {
                    return new InputPortResolution(match,
                            "UNIQUE_SEMANTIC_FIELD_ALIAS");
                }
            }

            // Field-sensitive analysis can expose a field of an opaque return
            // or formal before it exposes the corresponding canonical global
            // field cell.  Resolve that projection only when the declared
            // carrier type and terminal field name identify one unique global
            // input port.  A local without a declared carrier type, a nested
            // projection, or an ambiguous match remains fail-closed.
            String projected = declaredProjectedField(cell);
            if (!projected.isEmpty()) {
                String match = "";
                for (Map<String, Object> input : inputPorts) {
                    String inputCell = string(input.get("cell"));
                    if (!globalFieldCell(inputCell)) {
                        continue;
                    }
                    DeclaredField candidate = exactDeclaredField(inputCell);
                    if (candidate == null
                            || !projected.equals(fieldKey(candidate.owner(),
                            candidate.name()))) {
                        continue;
                    }
                    if (!match.isEmpty()) {
                        return InputPortResolution.unresolved();
                    }
                    match = string(input.get("portId"));
                }
                if (!match.isEmpty()) {
                    return new InputPortResolution(match,
                            "UNIQUE_DECLARED_PROJECTED_FIELD");
                }
            }

            // A dependency may be a field projection of an object that enters
            // through a root argument while the public region frontier exposes
            // only that argument carrier. Resolve it only for an exact static
            // owner/type match and only when the carrier is unique. Runtime
            // materialization remains responsible for selecting the observed
            // fields of that concrete argument object.
            String fieldOwner = globalFieldOwner(cell);
            if (fieldOwner.isEmpty()) {
                return InputPortResolution.unresolved();
            }
            String carrier = "";
            for (Map<String, Object> input : inputPorts) {
                String inputCell = string(input.get("cell"));
                if (!rootParameter(inputCell, rootMethod)
                        || !fieldOwner.equals(parameterType(inputCell))) {
                    continue;
                }
                if (!carrier.isEmpty()) {
                    return InputPortResolution.unresolved();
                }
                carrier = string(input.get("portId"));
            }
            return carrier.isEmpty()
                    ? InputPortResolution.unresolved()
                    : new InputPortResolution(carrier,
                    "UNIQUE_ROOT_ARGUMENT_CARRIER");
        }

        /**
         * Resolves a projected local through an exact, field-sensitive alias
         * chain to a materializable declared-field port.  This is the common
         * shape produced by a wire carrier getter:
         *
         * <pre>
         * Command.keys#field:p -> getKeys().return#field:p
         *                         -> receiverLocal#field:p
         * </pre>
         *
         * The receiver local itself is not a replayable input definition, but
         * the declared field at the beginning of the chain is.  Only static
         * value/identity edges that preserve one exact relative field path
         * are traversed.  Protocol mappings, controls, computations, missing
         * metadata, and multiple equally-near ports all fail closed.
         */
        private InputPortResolution exactProjectedAliasCarrier(
                String cell, List<Map<String, Object>> inputPorts,
                RegionDraft slice) {
            // Besides a synthetic local/return projection, a canonical
            // declared scalar can be one of two exact representations of the
            // same JVM getfield/accessor result.  The other representation is
            // a receiver projection which may already have a materializable
            // region port (for example owner.carrier#field:value).  Admit the
            // canonical end only through the exact parallel-read join below.
            if (!syntheticValueProjection(cell)
                    && declaredField(cell) == null
                    && !declaredFieldProjection(cell)) {
                return InputPortResolution.unresolved();
            }

            Map<String, Integer> distance = new LinkedHashMap<>();
            Deque<String> work = new ArrayDeque<>();
            if (exactAliasPath(cell).isEmpty()) {
                return InputPortResolution.unresolved();
            }
            distance.put(cell, 0);
            work.add(cell);
            Map<Integer, Set<String>> exactPorts = new LinkedHashMap<>();
            Map<Integer, Set<String>> projectedPorts =
                    new LinkedHashMap<>();
            Map<Integer, Set<String>> basePorts = new LinkedHashMap<>();

            while (!work.isEmpty() && distance.size() <= MAX_PORTS) {
                String current = work.removeFirst();
                int currentDistance = distance.get(current);
                String base = projectedBase(current);
                for (Map<String, Object> input : inputPorts) {
                    String inputCell = string(input.get("cell"));
                    String port = string(input.get("portId"));
                    if (port.isEmpty()) {
                        continue;
                    }
                    if (current.equals(inputCell)) {
                        if (exactAliasMaterializationPort(input)) {
                            exactPorts.computeIfAbsent(currentDistance,
                                    ignored -> new LinkedHashSet<>()).add(port);
                        } else if (declaredFieldProjection(inputCell)) {
                            projectedPorts.computeIfAbsent(currentDistance,
                                    ignored -> new LinkedHashSet<>()).add(port);
                        }
                    } else if (base.equals(inputCell)
                            && materializableProjectedAliasBase(inputCell,
                            slice.rootMethod)) {
                        basePorts.computeIfAbsent(currentDistance,
                                ignored -> new LinkedHashSet<>()).add(port);
                    }
                }

                for (Map<String, Object> edge : slice.causalEdges) {
                    if (!exactProjectedAliasEdge(edge)) {
                        continue;
                    }
                    String source = "";
                    if (current.equals(string(edge.get("toCell")))) {
                        source = string(edge.get("fromCell"));
                    } else if (current.equals(string(edge.get(
                            "fromCell")))) {
                        // These are exact alias-preserving projection/copy
                        // rows, not computations.  Treating them as an
                        // undirected equivalence edge lets a broad upstream
                        // projection reach the canonical declared leaf that
                        // is read in a deeper synchronous helper.
                        source = string(edge.get("toCell"));
                    }
                    if (!source.isEmpty() && !distance.containsKey(source)) {
                        distance.put(source, currentDistance + 1);
                        work.addLast(source);
                    }
                }
                for (String source : exactParallelFieldReadAliases(current,
                        slice, exactAliasPath(current))) {
                    if (!source.isEmpty() && !distance.containsKey(source)) {
                        distance.put(source, currentDistance + 1);
                        work.addLast(source);
                    }
                }
            }

            // Do not claim uniqueness from a prefix of the alias graph.  A
            // second equally-near port may sit just beyond the traversal
            // bound, so exhausting the worklist is part of the proof.
            if (!work.isEmpty()) {
                return InputPortResolution.unresolved();
            }

            if (!exactPorts.isEmpty()) {
                String exact = uniquePort(exactPorts);
                return exact.isEmpty() ? InputPortResolution.unresolved()
                        : new InputPortResolution(exact,
                        "UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN");
            }
            // A canonical declared leaf is itself executable evidence, not a
            // request to reuse an opaque receiver projection.  Leaving it
            // unresolved here lets requested-output promotion construct its
            // exact FIELD_ACCESS port (or lets the ordinary exact-cell path
            // select an already-declared port).  Otherwise discovery order
            // can make an earlier metadata-free projection hide the leaf
            // before that leaf has had a chance to be promoted.
            if (declaredField(cell) != null) {
                return InputPortResolution.unresolved();
            }
            if (!projectedPorts.isEmpty()) {
                String projected = uniqueNearestPort(projectedPorts);
                return projected.isEmpty()
                        ? InputPortResolution.unresolved()
                        : new InputPortResolution(projected,
                        "UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN");
            }
            String base = uniqueNearestPort(basePorts);
            return base.isEmpty() ? InputPortResolution.unresolved()
                    : new InputPortResolution(base,
                    "UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN");
        }

        /**
         * Only a port with a concrete, statically proven runtime access is a
         * terminal of the projected-field alias graph.  Broad region ports
         * may name a useful projection without carrying the leaf declaration
         * or access site needed to execute it; such a port remains an alias
         * node and must not hide a canonical leaf promoted by the exact
         * requested-output slice.
         */
        private boolean exactAliasMaterializationPort(
                Map<String, Object> port) {
            Map<String, Object> spec = materialization(port);
            if (strings(spec.get("path")).isEmpty()
                    || string(spec.get("leafField")).isEmpty()) {
                return false;
            }
            if (!"FIELD_READ".equals(string(spec.get("kind")))
                    && !"ACCESSOR_RETURN".equals(string(spec.get("kind")))) {
                return false;
            }
            Collection<String> path = strings(spec.get("path"));
            return path.size() >= 1 && path.size() <= 4;
        }

        /**
         * A proven multi-field carrier path and its final declared getfield
         * are two names for one JVM value. Prefer the unique declared leaf so
         * static and runtime demand slicing share one port identity.
         */
        private InputPortResolution uniqueDeclaredLeafPort(
                Map<String, Object> projected,
                List<Map<String, Object>> inputPorts) {
            Map<String, Object> spec = materialization(projected);
            Collection<String> path = strings(spec.get("path"));
            String leaf = string(spec.get("leafField"));
            if (path.size() < 2 || leaf.isEmpty()
                    || declaredField(leaf) == null) {
                return InputPortResolution.unresolved();
            }
            String selected = "";
            for (Map<String, Object> input : inputPorts) {
                if (!leaf.equals(string(input.get("cell")))
                        || !exactAliasMaterializationPort(input)) {
                    continue;
                }
                String port = string(input.get("portId"));
                if (port.isEmpty() || !selected.isEmpty()
                        && !selected.equals(port)) {
                    return InputPortResolution.unresolved();
                }
                selected = port;
            }
            return selected.isEmpty()
                    ? InputPortResolution.unresolved()
                    : new InputPortResolution(selected,
                    "UNIQUE_EXACT_DECLARED_FIELD_LEAF");
        }

        private InputPortResolution uniquePortForDeclaredLeaf(
                String cell, List<Map<String, Object>> inputPorts) {
            if (declaredField(cell) == null) {
                return InputPortResolution.unresolved();
            }
            String selected = "";
            for (Map<String, Object> input : inputPorts) {
                Map<String, Object> spec = materialization(input);
                if (!cell.equals(string(spec.get("leafField")))
                        || !exactAliasMaterializationPort(input)) {
                    continue;
                }
                String port = string(input.get("portId"));
                if (port.isEmpty() || !selected.isEmpty()
                        && !selected.equals(port)) {
                    return InputPortResolution.unresolved();
                }
                selected = port;
            }
            return selected.isEmpty()
                    ? InputPortResolution.unresolved()
                    : new InputPortResolution(selected,
                    "UNIQUE_EXACT_DECLARED_FIELD_LEAF");
        }

        private String uniquePort(
                Map<Integer, Set<String>> portsByDistance) {
            Set<String> ports = new LinkedHashSet<>();
            for (Set<String> atDistance : portsByDistance.values()) {
                if (atDistance != null) {
                    ports.addAll(atDistance);
                }
            }
            return ports.size() == 1 ? ports.iterator().next() : "";
        }

        /**
         * Joins the canonical declared-field and receiver-projection rows
         * emitted for one physical getfield/accessor read.  This is not a
         * name-based heap alias: both rows must define the same local at the
         * same exact method/unit/site, carry automatic-derivation authority,
         * and the receiver projection must name the same terminal field on
         * the declaring receiver type.  Any other convergence remains
         * outside this equivalence relation.
         */
        private Set<String> exactParallelFieldReadAliases(
                String current, RegionDraft slice, String requiredPath) {
            return exactParallelFieldReadAliases(current, slice.causalEdges,
                    requiredPath);
        }

        private Set<String> exactParallelFieldReadAliases(
                String current, Collection<Map<String, Object>> edges,
                String requiredPath) {
            Set<String> result = new LinkedHashSet<>();
            for (Map<String, Object> selected : edges) {
                if (!current.equals(string(selected.get("fromCell")))
                        || !exactParallelFieldReadRow(selected)) {
                    continue;
                }
                for (Map<String, Object> parallel : edges) {
                    if (selected == parallel
                            || !exactParallelFieldReadRow(parallel)
                            || !sameExactDefinitionSite(selected, parallel)
                            || !parallelFieldReadDeclarationsAgree(selected,
                            parallel, requiredPath)) {
                        continue;
                    }
                    result.add(string(parallel.get("fromCell")));
                }
            }
            result.remove(current);
            result.remove("");
            return result;
        }

        private String exactAliasPath(String cell) {
            String path = projectedPath(cell);
            DeclaredField field = declaredField(cell);
            return path.isEmpty() && field != null
                    ? "#field:" + field.name() : path;
        }

        private boolean exactParallelFieldReadRow(
                Map<String, Object> edge) {
            String transfer = string(edge.get("transferKind"));
            String kind = string(edge.get("kind"));
            return !isBoundary(edge)
                    && exactStaticValueFlow(edge)
                    && ("HEAP_READ".equals(transfer)
                    || "PROJECTION".equals(transfer))
                    && (kind.contains("field_read")
                    || kind.contains("field_return"));
        }

        private boolean sameExactDefinitionSite(Map<String, Object> first,
                                                Map<String, Object> second) {
            return sameExactDefinitionSiteIgnoringTarget(first, second)
                    && string(first.get("toCell")).equals(string(second.get(
                    "toCell")));
        }

        private boolean parallelFieldReadDeclarationsAgree(
                Map<String, Object> first, Map<String, Object> second,
                String requiredPath) {
            DeclaredField firstDeclared = declaredField(
                    string(first.get("fromCell")));
            DeclaredField secondDeclared = declaredField(
                    string(second.get("fromCell")));
            if ((firstDeclared == null) == (secondDeclared == null)) {
                return false;
            }
            DeclaredField declared = firstDeclared != null
                    ? firstDeclared : secondDeclared;
            Map<String, Object> projected = firstDeclared == null
                    ? first : second;
            String source = string(projected.get("fromCell"));
            String path = string(projected.get("fieldPath"));
            String base = string(projected.get("objectFromCell"));
            if (!Boolean.TRUE.equals(projected.get("fieldSensitive"))
                    || base.isEmpty() || path.isEmpty()
                    || !requiredPath.equals(path)
                    || !source.equals(base + path)
                    || !path.endsWith("#field:" + declared.name())) {
                return false;
            }
            // For a direct receiver read, the receiver method declaration is
            // the owner of the canonical field.  For an accessor projection,
            // the resolved declared-field tuple on the edge supplies the same
            // proof across inheritance.
            boolean receiverOwner = declared.owner().equals(owner(
                    methodForCell(base)));
            boolean resolvedTuple = declaredMetadataMatches(projected,
                    declared);
            return receiverOwner || resolvedTuple;
        }

        private boolean exactProjectedAliasEdge(Map<String, Object> edge) {
            String kind = string(edge.get("kind"));
            String transfer = string(edge.get("transferKind"));
            boolean exactAliasKind = kind.startsWith("projected_")
                    || "method_receiver_field".equals(kind);
            if (!exactAliasKind
                    || isBoundary(edge)
                    || !Boolean.TRUE.equals(edge.get("fieldSensitive"))) {
                return false;
            }
            if (!("HEAP_READ".equals(transfer)
                    || "FUNCTION_RETURN".equals(transfer)
                    || "IDENTITY_BINDING".equals(transfer)
                    || "VALUE_PASS".equals(transfer)
                    || "PROJECTION".equals(transfer))) {
                return false;
            }
            if (kind.startsWith("projected_")
                    && exactProjectedBaseAliasAuthority(edge)) {
                return true;
            }
            if (!exactStaticValueFlow(edge)) {
                return false;
            }
            if ("projected_local_def_use".equals(kind)
                    && "VALUE_PASS".equals(transfer)
                    && !exactProjectedDirectCopyAuthority(edge)) {
                return false;
            }
            String path = string(edge.get("fieldPath"));
            String fromBase = string(edge.get("objectFromCell"));
            String toBase = string(edge.get("objectToCell"));
            return !path.isEmpty() && !fromBase.isEmpty()
                    && !toBase.isEmpty()
                    && (fromBase + path).equals(string(edge.get("fromCell")))
                    && (toBase + path).equals(string(edge.get("toCell")));
        }

        /**
         * Proves a projected alias from the unique raw Soot edge that created
         * it.  A getfield can shorten the visible path -- for example
         * {@code owner#field:profile#field:weight} becomes
         * {@code profileLocal#field:weight}.  Requiring one fixed path string
         * for the whole alias walk therefore rejects a valid identity.  The
         * invariant that survives the read is the identical non-empty suffix
         * appended to both endpoints of the raw edge.
         *
         * <p>The projection is admitted only when its producer reference is
         * unique, the raw edge retains automatic SMT/value-flow authority,
         * both rows name the same method and bytecode definition, and the
         * raw transfer itself is alias preserving.  A projected parameter
         * identity is accepted from Soot's exact parameter binding even
         * though the compact projected row is conservatively labelled
         * {@code taint_depends_on}.  Ordinary local assignments and returns
         * retain their stronger two-reference/direct-copy proof below.</p>
         */
        private boolean exactProjectedBaseAliasAuthority(
                Map<String, Object> projected) {
            if (!"PROJECTED_EDGE_CANNOT_EXCEED_BASE_EDGE_V1".equals(
                    string(projected.get("authorityInheritance")))
                    || !exactStaticValueFlow(projected)
                    || !StaticDataflowEdgeSchema.automaticSemantics(
                    projected)) {
                return false;
            }
            String baseId = string(projected.get("projectionBaseEdgeId"));
            if (baseId.isEmpty()) {
                return false;
            }
            List<Map<String, Object>> matches = graph.withId(baseId);
            if (matches.size() != 1) {
                return false;
            }
            Map<String, Object> base = matches.get(0);
            if (base == projected || isBoundary(base)
                    || !exactStaticValueFlow(base)
                    || !string(projected.get("method")).equals(
                    string(base.get("method")))
                    || !string(projected.get("siteId")).equals(
                    string(base.get("siteId")))
                    || integer(projected.get("unitIndex"), -1) < 0
                    || integer(projected.get("unitIndex"), -1) != integer(
                    base.get("unitIndex"), -1)
                    || !string(projected.get("transferKind")).equals(
                    string(base.get("transferKind")))) {
                return false;
            }
            String projectedKind = string(projected.get("kind"));
            if (!projectedKind.startsWith("projected_")
                    || !projectedKind.substring("projected_".length())
                    .equals(string(base.get("kind")))) {
                return false;
            }
            String transfer = string(base.get("transferKind"));
            if (!("HEAP_READ".equals(transfer)
                    || "FUNCTION_RETURN".equals(transfer)
                    || "IDENTITY_BINDING".equals(transfer)
                    || "VALUE_PASS".equals(transfer)
                    || "PROJECTION".equals(transfer))) {
                return false;
            }

            String baseFrom = string(base.get("fromCell"));
            String baseTo = string(base.get("toCell"));
            String from = string(projected.get("fromCell"));
            String to = string(projected.get("toCell"));
            if (baseFrom.isEmpty() || baseTo.isEmpty()
                    || !from.startsWith(baseFrom + "#field:")) {
                return false;
            }
            String suffix = from.substring(baseFrom.length());
            if (!to.equals(baseTo + suffix)) {
                return false;
            }

            if (!"projected_local_def_use".equals(projectedKind)) {
                return true;
            }
            return exactProjectedDirectCopyAuthority(projected);
        }

        /**
         * Verifies that a projected local copy inherits its value-flow
         * authority from one, and only one, raw Soot-certified direct copy.
         * The projected row is synthetic and therefore cannot establish this
         * fact by its kind or endpoint spelling alone.  Its two producer
         * references must agree, resolve uniquely in the input graph, and the
         * resolved base must retain the exact method and endpoint shape of the
         * projection's aggregate carriers.
         */
        private boolean exactProjectedDirectCopyAuthority(
                Map<String, Object> projected) {
            String projectedAuthority = string(projected.get(
                    "valueFlowAuthority"));
            String declaredBaseAuthority = string(projected.get(
                    "baseValueFlowAuthority"));
            boolean projectedLocal = "PROJECTED_FROM_SOOT_EXACT_LOCAL_"
                    .concat("DIRECT_COPY_V1").equals(projectedAuthority)
                    && "SOOT_EXACT_LOCAL_DIRECT_COPY_V1".equals(
                    declaredBaseAuthority);
            boolean projectedParameter =
                    "PROJECTED_FROM_SOOT_EXACT_PARAMETER_IDENTITY_"
                    .concat("BINDING_V1").equals(projectedAuthority)
                    && "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1".equals(
                    declaredBaseAuthority);
            if ((!projectedLocal && !projectedParameter)
                    || !"PROJECTED_EDGE_CANNOT_EXCEED_BASE_EDGE_V1".equals(
                    string(projected.get("authorityInheritance")))) {
                return false;
            }
            String baseId = string(projected.get("baseValueFlowEdgeId"));
            if (baseId.isEmpty() || !baseId.equals(string(projected.get(
                    "projectionBaseEdgeId")))) {
                return false;
            }

            List<Map<String, Object>> matches = graph.withId(baseId);
            if (matches.size() != 1) {
                return false;
            }
            Map<String, Object> base = matches.get(0);
            if (base == projected
                    || !"local_def_use".equals(string(base.get("kind")))
                    || !"VALUE_PASS".equals(string(base.get(
                    "transferKind")))
                    || !exactStaticValueFlow(base)
                    || !string(base.get("valueFlowAuthority")).equals(
                    string(projected.get("baseValueFlowAuthority")))) {
                return false;
            }

            String method = string(projected.get("method"));
            String from = string(base.get("fromCell"));
            String to = string(base.get("toCell"));
            if (method.isEmpty()
                    || !method.equals(string(base.get("method")))
                    || !from.equals(string(projected.get(
                    "objectFromCell")))
                    || !to.equals(string(projected.get("objectToCell")))) {
                return false;
            }

            String directCopyKind = string(base.get("directCopyKind"));
            if (projectedParameter) {
                return "PARAMETER_IDENTITY".equals(directCopyKind)
                        && exactParameterCell(method, from)
                        && exactLocalCell(method, to);
            }
            if ("RETURN_LOCAL".equals(directCopyKind)) {
                return exactLocalCell(method, from)
                        && (method + ".return").equals(to);
            }
            return "LOCAL_ASSIGN_LOCAL".equals(directCopyKind)
                    && exactLocalCell(method, from)
                    && exactLocalCell(method, to);
        }

        private boolean exactParameterCell(String method, String cell) {
            String prefix = string(method) + ".param";
            String value = string(cell);
            if (method.isEmpty() || !value.startsWith(prefix)) {
                return false;
            }
            int colon = value.indexOf(':', prefix.length());
            if (colon <= prefix.length() || colon + 1 >= value.length()) {
                return false;
            }
            for (int index = prefix.length(); index < colon; index++) {
                if (!Character.isDigit(value.charAt(index))) {
                    return false;
                }
            }
            return true;
        }

        private String projectedPath(String cell) {
            int projection = string(cell).indexOf("#field:");
            return projection < 0 ? "" : cell.substring(projection);
        }

        private String uniqueNearestPort(
                Map<Integer, Set<String>> portsByDistance) {
            for (int distance : sortedIntegers(portsByDistance.keySet())) {
                Set<String> ports = portsByDistance.get(distance);
                if (ports == null || ports.isEmpty()) {
                    continue;
                }
                return ports.size() == 1 ? ports.iterator().next() : "";
            }
            return "";
        }

        private List<Integer> sortedIntegers(Collection<Integer> values) {
            List<Integer> result = new ArrayList<>(values);
            Collections.sort(result);
            return result;
        }

        private String projectedBase(String cell) {
            int projection = string(cell).indexOf("#field:");
            return projection < 0 ? "" : cell.substring(0, projection);
        }

        private boolean declaredFieldProjection(String cell) {
            String base = projectedBase(cell);
            return !base.isEmpty() && declaredField(base) != null;
        }

        private boolean materializableProjectedAliasBase(
                String cell, String rootMethod) {
            return globalFieldCell(cell) || rootParameter(cell, rootMethod);
        }

        private boolean syntheticValueProjection(String cell) {
            int projection = string(cell).indexOf("#field:");
            if (projection < 0) {
                return false;
            }
            String base = cell.substring(0, projection);
            return base.endsWith(">.return")
                    || exactLocalCell(methodForCell(base), base);
        }

        /**
         * Collapses an exact projected call/protocol value onto its concrete
         * aggregate carrier.  The scheduler can instrument a local definition
         * or a call return, but a synthetic {@code local#field:path} cell has
         * no independent bytecode definition.  Treating that projection as a
         * separate live-in would make a statically complete slice impossible
         * to execute.
         *
         * <p>The collapse is allowed only for one exact base port and one
         * exact projection family.  A local base additionally requires the
         * raw and projected forms of the same incoming boundary value.  An
         * opaque return base must already be a materializable call-result
         * frontier.  Declared heap paths are intentionally handled elsewhere
         * so their precise leaf, rather than their whole carrier object, stays
         * symbolic.</p>
         */
        private InputPortResolution exactProjectedValueCarrier(
                String cell, List<Map<String, Object>> inputPorts,
                RegionDraft slice) {
            int projection = cell.indexOf("#field:");
            if (projection < 0) {
                return InputPortResolution.unresolved();
            }
            String base = cell.substring(0, projection);
            String path = cell.substring(projection);
            boolean localBase = exactLocalCell(methodForCell(base), base);
            boolean returnBase = base.endsWith(">.return");
            if (!localBase && !returnBase) {
                return InputPortResolution.unresolved();
            }

            String basePort = "";
            for (Map<String, Object> input : inputPorts) {
                if (!base.equals(string(input.get("cell")))) {
                    continue;
                }
                if (!basePort.isEmpty()) {
                    return InputPortResolution.unresolved();
                }
                basePort = string(input.get("portId"));
            }
            if (basePort.isEmpty()) {
                return InputPortResolution.unresolved();
            }

            if (returnBase) {
                if (!materializableOpaqueCallResult(base, slice)) {
                    return InputPortResolution.unresolved();
                }
                boolean proof = false;
                for (Map<String, Object> edge : graph.outgoing(cell)) {
                    if (!exactStaticValueFlow(edge)
                            || !Boolean.TRUE.equals(edge.get(
                            "fieldSensitive"))
                            || !base.equals(string(edge.get(
                            "objectFromCell")))
                            || !path.equals(string(edge.get("fieldPath")))) {
                        return InputPortResolution.unresolved();
                    }
                    proof = true;
                }
                return proof ? new InputPortResolution(basePort,
                        "UNIQUE_EXACT_PROJECTED_VALUE_CARRIER")
                        : InputPortResolution.unresolved();
            }

            if (!boundaryInputs(slice.methods,
                    new LinkedHashSet<String>()).contains(base)) {
                return InputPortResolution.unresolved();
            }
            Set<String> projectedSources = new LinkedHashSet<>();
            for (Map<String, Object> edge : graph.incoming(cell)) {
                if (!isBoundary(edge)) {
                    continue;
                }
                if (!exactStaticValueFlow(edge)
                        || !Boolean.TRUE.equals(edge.get("fieldSensitive"))
                        || !base.equals(string(edge.get("objectToCell")))
                        || !path.equals(string(edge.get("fieldPath")))) {
                    return InputPortResolution.unresolved();
                }
                String sourceBase = string(edge.get("objectFromCell"));
                if (!cell.equals(base + path)
                        || !string(edge.get("fromCell")).equals(
                        sourceBase + path)) {
                    return InputPortResolution.unresolved();
                }
                projectedSources.add(sourceBase);
            }
            if (projectedSources.isEmpty()) {
                return InputPortResolution.unresolved();
            }
            // Several source bases are valid static alternatives when they
            // all feed the same concrete target local (for example interface,
            // server-implementation, and runtime-selected RPC aliases).  The
            // target carrier remains unique; require a raw exact row for each
            // projected alternative and let runtime select the observed one.
            for (String sourceBase : projectedSources) {
                boolean rawProof = false;
                for (Map<String, Object> edge : graph.outgoing(sourceBase)) {
                    if (!isBoundary(edge)
                            || !base.equals(string(edge.get("toCell")))) {
                        continue;
                    }
                    if (!exactStaticValueFlow(edge)) {
                        return InputPortResolution.unresolved();
                    }
                    rawProof = true;
                }
                if (!rawProof) {
                    return InputPortResolution.unresolved();
                }
            }
            return new InputPortResolution(basePort,
                    "UNIQUE_EXACT_PROJECTED_VALUE_CARRIER");
        }

        private String declaredProjectedField(String cell) {
            String value = string(cell);
            int field = value.indexOf("#field:");
            if (field < 0 || field != value.lastIndexOf("#field:")) {
                return "";
            }
            Matcher returned = PROJECTED_RETURN_FIELD_PATTERN.matcher(value);
            if (returned.matches()) {
                return fieldKey(returned.group(1), returned.group(2));
            }
            Matcher parameter = PROJECTED_PARAMETER_FIELD_PATTERN.matcher(
                    value);
            if (parameter.matches()) {
                return fieldKey(parameter.group(1), parameter.group(2));
            }
            return "";
        }

        private String globalFieldOwner(String cell) {
            Matcher field = GLOBAL_FIELD_OWNER_PATTERN.matcher(string(cell));
            return field.matches() ? field.group(1) : "";
        }

        private String parameterType(String cell) {
            Matcher parameter = PARAMETER_TYPE_PATTERN.matcher(string(cell));
            return parameter.find() ? parameter.group(1).trim() : "";
        }

        private String cellJavaType(String cell) {
            String value = string(cell);
            Matcher parameter = PARAMETER_TYPE_PATTERN.matcher(value);
            if (parameter.find()) {
                return parameter.group(1).trim();
            }
            Matcher field = FIELD_CELL_TYPE_PATTERN.matcher(value);
            if (field.matches()) {
                return field.group(1).trim();
            }
            Matcher returned = RETURN_CELL_TYPE_PATTERN.matcher(value);
            return returned.matches() ? returned.group(1).trim() : "";
        }

        private List<String> orderedMethods(Collection<String> methods,
                                            String rootMethod) {
            List<String> result = sorted(methods);
            if (result.remove(rootMethod)) {
                result.add(0, rootMethod);
            }
            return result;
        }

        /**
         * Computes region live-ins rather than unioning method live-ins.
         *
         * <p>A call made by a method in the region is part of the region's
         * execution (or is represented by one of the region's models).  Its
         * return value is therefore derived from existing symbols and must not
         * become an independent symbol.  The same rule applies to parameters,
         * receivers, and locals of non-root methods reached inside the region.
         * Only root arguments, root receiver state, protocol/environment
         * boundaries, and heap state actually read by the region remain at the
         * symbolic frontier.</p>
         */
        private InputSelection selectExternalInputs(RegionDraft draft,
                                                     Set<String> candidates,
                                                     Set<String> produced) {
            InputSelection result = new InputSelection();
            Set<String> boundarySources = new LinkedHashSet<>();
            Set<String> boundaryInputs = boundaryInputs(draft.methods,
                    boundarySources);
            Set<String> opaqueCallReturns = opaqueCallReturnFrontier(draft);
            SeedGuardInputFrontier seedGuardFrontier =
                    seedGuardInputFrontier(draft, boundaryInputs,
                            opaqueCallReturns);
            Set<String> mandatorySeedGuardInputs =
                    seedGuardFrontier.liveIns;
            Set<String> separatedHeapProducerInputs =
                    upstreamOfGuardHeapPrestateWriters(draft,
                            mandatorySeedGuardInputs);
            Set<String> readFieldKeys = new LinkedHashSet<>();
            Map<String, String> mutableHeapPrestates =
                    mutableHeapPrestateCells(draft, readFieldKeys);
            readFieldKeys.addAll(mutableHeapPrestates.keySet());
            Map<String, String> fieldsBySemanticKey = new LinkedHashMap<>();

            Set<String> allCandidates = new LinkedHashSet<>(candidates);
            allCandidates.addAll(boundaryInputs);
            // Guard operands are not automatically region inputs.  Preserve
            // only their authoritative backward frontier: root/protocol
            // inputs, heap prestates, environment reads, or opaque calls.
            // This keeps guard = f(region.in) when a deeper callee parameter
            // is supplied by an in-region caller while still protecting the
            // real live-ins from the broad 128-port cap.
            allCandidates.addAll(mandatorySeedGuardInputs);
            allCandidates.addAll(seedGuardFrontier.gapCells);
            // A mutation consumes both its explicit operands and any field
            // value read on a path that may precede the write.  Static region
            // membership alone cannot prove that a later (or alternative)
            // write initialized that field.  Preserve the prestate here and
            // let concrete runtime-path/initializer evidence prune it.
            allCandidates.addAll(mutableHeapPrestates.values());
            // Method-level plans are deliberately bounded.  Recover leaf
            // dependencies directly from the exception slice so an opaque
            // invocation used by a guard cannot disappear merely because the
            // callee has no plan/body in the current analysis scope.
            allCandidates.addAll(causalFrontierCells(draft));
            for (String candidate : sorted(allCandidates)) {
                if (candidate.isEmpty()) {
                    continue;
                }
                boolean mandatorySeedGuardInput =
                        mandatorySeedGuardInputs.contains(candidate);
                if (seedGuardFrontier.gapCells.contains(candidate)) {
                    // Unknown provenance is not authority to create a free
                    // symbol.  Keep the value observed by this concrete
                    // activation and continue exploring the remainder of the
                    // region.  A later runtime/static refinement can replace
                    // this fallback with a proven live-in ancestor.
                    continue;
                }
                if (!mandatorySeedGuardInput
                        && separatedHeapProducerInputs.contains(candidate)) {
                    // A shared-field read consumes the state visible at this
                    // activation boundary.  Static writers are producer
                    // regions whose relation to this read must be selected by
                    // runtime read-from/object identity.  Their own inputs do
                    // not become direct inputs of the consumer region merely
                    // because the global exception slice crosses HEAP_WRITE.
                    continue;
                }
                boolean opaqueCall = opaqueCallReturns.contains(candidate);
                boolean boundaryTarget = boundaryInputs.contains(candidate);
                if (boundaryTarget && !opaqueCall
                        && internallyDefinedBoundaryAlias(candidate, draft)) {
                    continue;
                }
                boolean boundary = boundaryTarget || opaqueCall;
                if (boundarySources.contains(candidate)) {
                    continue;
                }
                // A projected method local has no independently replayable
                // field definition.  Even when a protocol mapping names it
                // as a boundary target, retain it in an exception-directed
                // slice only when that exact projected cell is causal.  A
                // same-named field elsewhere in the method/owner is not
                // authority for symbolizing this local projection.
                boolean projectedLocal = syntheticValueProjection(candidate);
                if (draft.exceptionDirected
                        && (!boundary || projectedLocal)
                        && !causalCandidate(candidate, draft)) {
                    continue;
                }
                if (freshAllocationBackedField(candidate, draft)) {
                    continue;
                }
                String derivedReason = derivedReason(candidate, draft,
                        produced, boundary, mutableHeapPrestates.keySet());
                if (!mandatorySeedGuardInput && !derivedReason.isEmpty()) {
                    continue;
                }

                String fieldKey = semanticFieldKey(candidate, draft.rootMethod);
                if (!fieldKey.isEmpty()) {
                    boolean mutablePrestate = mutableHeapPrestates.containsKey(
                            fieldKey);
                    if (!mandatorySeedGuardInput && !boundary
                            && !readFieldKeys.contains(fieldKey)) {
                        continue;
                    }
                    String previous = fieldsBySemanticKey.get(fieldKey);
                    boolean previousMandatory = previous != null
                            && mandatorySeedGuardInputs.contains(previous);
                    if (previous == null
                            || mandatorySeedGuardInput && !previousMandatory
                            || mandatorySeedGuardInput == previousMandatory
                            && inputPreference(candidate, draft.rootMethod,
                            boundary, mutablePrestate)
                            < inputPreference(previous, draft.rootMethod,
                            boundaryInputs.contains(previous),
                            mutablePrestate)) {
                        fieldsBySemanticKey.put(fieldKey, candidate);
                    }
                    continue;
                }
                if (!boundaryInput(candidate, draft.rootMethod)) {
                    String diagnostic = candidate
                            + " [causal dependency has no materializable "
                            + "region-boundary representation]";
                    result.unresolvedInputDetails.add(object(
                            "dependencyCell", candidate,
                            "dependencyMethods",
                            dependencyMethods(candidate, draft),
                            "reason",
                            "NO_MATERIALIZABLE_REGION_BOUNDARY_"
                                    + "REPRESENTATION",
                            "diagnostic", diagnostic));
                    continue;
                }
                result.externalInputs.add(candidate);
                if (mandatorySeedGuardInput) {
                    result.mandatorySeedGuardInputs.add(candidate);
                }
            }
            result.externalInputs.addAll(fieldsBySemanticKey.values());
            for (String field : fieldsBySemanticKey.values()) {
                if (mandatorySeedGuardInputs.contains(field)) {
                    result.mandatorySeedGuardInputs.add(field);
                }
            }
            collapseExactDeclaredFieldPathAliases(result, draft);
            return result;
        }

        private boolean freshAllocationBackedField(
                String candidate, RegionDraft draft) {
            String key = semanticFieldKey(candidate, draft.rootMethod);
            if (key.isEmpty()) {
                return false;
            }
            boolean read = false;
            for (Map<String, Object> edge : analysisGraph(draft).edges()) {
                String source = string(edge.get("fromCell"));
                String kind = string(edge.get("kind"));
                if (!"HEAP_READ".equals(string(edge.get("transferKind")))
                        || !("field_read".equals(kind)
                        || "projected_field_read".equals(kind))
                        || !key.equals(semanticFieldKey(source,
                        draft.rootMethod))) {
                    continue;
                }
                read = true;
                Set<String> receivers = freshReadReceivers(source);
                if (receivers.isEmpty()) {
                    return false;
                }
                for (String receiver : receivers) {
                    if (!freshProjectedReceiver(receiver,
                            new LinkedHashSet<>())) {
                        return false;
                    }
                }
            }
            return read;
        }

        private Set<String> freshReadReceivers(
                String source) {
            Collection<Map<String, Object>> edges = graph.edges();
            Set<String> result = exactParallelFieldReadAliases(source, edges,
                    exactAliasPath(source));
            for (Map<String, Object> declared : edges) {
                if (!source.equals(string(declared.get("fromCell")))
                        || !"projected_field_read".equals(string(
                        declared.get("kind")))) {
                    continue;
                }
                result.addAll(parallelProjectedReadReceivers(declared,
                        edges));
            }
            result.remove("");
            return result;
        }

        private Set<String> parallelProjectedReadReceivers(
                Map<String, Object> declared,
                Collection<Map<String, Object>> edges) {
            Set<String> result = new LinkedHashSet<>();
            DeclaredField root = declaredField(string(
                    declared.get("objectFromCell")));
            if (!exactProjectedAliasEdge(declared) || root == null) {
                return result;
            }
            String receiverPath = "#field:" + root.name()
                    + string(declared.get("fieldPath"));
            for (Map<String, Object> receiver : edges) {
                if ("projected_instance_field_read".equals(string(
                        receiver.get("kind")))
                        && exactProjectedAliasEdge(receiver)
                        && sameExactDefinitionSite(declared, receiver)
                        && receiverProjectionDeclares(receiver, root)
                        && receiverPath.equals(string(receiver.get(
                        "fieldPath")))) {
                    result.add(string(receiver.get("fromCell")));
                }
            }
            return result;
        }

        private boolean receiverProjectionDeclares(
                Map<String, Object> projection, DeclaredField field) {
            Map<String, Object> base = exactProjectionBase(projection,
                    "instance_field_read",
                    string(projection.get("objectFromCell"))
                            + "#field:" + field.name(),
                    string(projection.get("objectToCell")));
            return base != null && declaredMetadataMatches(base, field);
        }

        private boolean freshProjectedReceiver(
                String cell, Set<String> visiting) {
            String base = projectedBase(cell);
            if (freshObjectBase(base, new LinkedHashSet<>())) {
                return true;
            }
            if (!visiting.add(cell)) {
                return false;
            }
            boolean defined = false;
            Collection<Map<String, Object>> edges = graph.edges();
            for (Map<String, Object> edge : graph.incoming(cell)) {
                if ("projected_field_read".equals(string(edge.get("kind")))
                        && !parallelProjectedReadReceivers(edge, edges)
                        .isEmpty()) {
                    continue;
                }
                if (!exactProjectedAliasEdge(edge)) {
                    continue;
                }
                defined = true;
                if (!freshProjectedReceiver(string(edge.get("fromCell")),
                        visiting)) {
                    return false;
                }
            }
            visiting.remove(cell);
            return defined;
        }

        private boolean freshObjectBase(
                String cell, Set<String> visiting) {
            if (cell.isEmpty() || !visiting.add(cell)) {
                return false;
            }
            boolean defined = false;
            for (Map<String, Object> edge : graph.incoming(cell)) {
                String source = string(edge.get("fromCell"));
                if (source.startsWith("new ")) {
                    visiting.remove(cell);
                    return true;
                }
                String transfer = string(edge.get("transferKind"));
                if (string(edge.get("kind")).startsWith("projected_")
                        || !exactStaticValueFlow(edge)
                        || !("IDENTITY_BINDING".equals(transfer)
                        || "VALUE_PASS".equals(transfer)
                        || "FUNCTION_RETURN".equals(transfer))) {
                    continue;
                }
                defined = true;
                if (!freshObjectBase(source, visiting)) {
                    return false;
                }
            }
            visiting.remove(cell);
            return defined;
        }

        /**
         * The field-sensitive graph intentionally carries a canonical cell
         * for every suffix of a direct access chain.  Once the complete chain
         * is uniquely proven, those suffixes are aliases, not independent
         * primitive inputs.  Keep only the longest selected path.  If two
         * unrelated longest paths claim the same suffix, retain that suffix
         * and fail closed instead of guessing an owner.
         */
        private void collapseExactDeclaredFieldPathAliases(
                InputSelection selection, RegionDraft draft) {
            Map<String, DeclaredFieldPathAccess> accesses =
                    new LinkedHashMap<>();
            for (String input : new ArrayList<>(selection.externalInputs)) {
                DeclaredFieldPathAccess access =
                        materializableDeclaredFieldPathAccess(input, draft);
                if (access != null) {
                    accesses.put(input, access);
                }
            }
            Set<String> nestedCandidates = new LinkedHashSet<>();
            for (DeclaredFieldPathAccess outer : accesses.values()) {
                for (String alias : outer.aliases) {
                    if (!outer.cell.equals(alias)
                            && accesses.containsKey(alias)) {
                        nestedCandidates.add(alias);
                    }
                }
            }
            List<DeclaredFieldPathAccess> maximal = new ArrayList<>();
            for (DeclaredFieldPathAccess access : accesses.values()) {
                if (!nestedCandidates.contains(access.cell)) {
                    maximal.add(access);
                }
            }
            Map<String, List<DeclaredFieldPathAccess>> claims =
                    new LinkedHashMap<>();
            for (DeclaredFieldPathAccess access : maximal) {
                for (String alias : access.aliases) {
                    if (!alias.equals(access.cell)
                            && selection.externalInputs.contains(alias)) {
                        claims.computeIfAbsent(alias,
                                ignored -> new ArrayList<>()).add(access);
                    }
                }
            }
            for (Map.Entry<String, List<DeclaredFieldPathAccess>> claim
                    : claims.entrySet()) {
                if (claim.getValue().size() != 1) {
                    continue;
                }
                String alias = claim.getKey();
                DeclaredFieldPathAccess replacement = claim.getValue().get(0);
                if (!aliasReadsCoveredByPathProof(alias, replacement,
                        draft)) {
                    continue;
                }
                if (!selection.externalInputs.remove(alias)) {
                    continue;
                }
                boolean mandatory = selection.mandatorySeedGuardInputs
                        .remove(alias);
                if (mandatory) {
                    selection.mandatorySeedGuardInputs.add(replacement.cell);
                }
            }
        }

        /**
         * A canonical declared-field cell may represent reads from several
         * runtime owners.  Collapse it only when every read in this region is
         * one of the exact read sites proving the selected direct path.
         */
        private boolean aliasReadsCoveredByPathProof(
                String alias, DeclaredFieldPathAccess replacement,
                RegionDraft draft) {
            boolean observed = false;
            for (Map<String, Object> edge
                    : analysisGraph(draft).outgoing(alias)) {
                String kind = string(edge.get("kind"));
                if (syntheticProjectionAlias(edge, kind)) {
                    continue;
                }
                if (!("field_read".equals(kind)
                        || "projected_field_read".equals(kind))) {
                    continue;
                }
                observed = true;
                if (!replacement.proofEdgeIds.contains(string(edge.get(
                        "id")))) {
                    return false;
                }
            }
            return observed;
        }

        private Set<String> upstreamOfGuardHeapPrestateWriters(
                RegionDraft draft, Set<String> guardLiveIns) {
            Set<String> heapPrestates = new LinkedHashSet<>();
            for (String liveIn : guardLiveIns) {
                if (globalFieldCell(liveIn)) {
                    heapPrestates.add(liveIn);
                }
            }
            if (heapPrestates.isEmpty()) {
                return Collections.emptySet();
            }
            StaticGraphIndex analysis = analysisGraph(draft);
            Deque<String> work = new ArrayDeque<>();
            for (Map<String, Object> edge : analysis.edges()) {
                String target = string(edge.get("toCell"));
                if (heapPrestates.contains(target)
                        && "HEAP_WRITE".equals(string(edge.get(
                        "transferKind")))
                        && authoritativeGuardDerivationEdge(edge)) {
                    String source = string(edge.get("fromCell"));
                    if (!source.isEmpty()) {
                        work.addLast(source);
                    }
                }
            }
            Set<String> upstream = new LinkedHashSet<>();
            while (!work.isEmpty()) {
                String current = work.removeFirst();
                if (heapPrestates.contains(current)
                        || !upstream.add(current)) {
                    continue;
                }
                for (Map<String, Object> edge : analysis.incoming(current)) {
                    if (isBoundary(edge)
                            && authoritativeGuardProtocolBoundary(edge)) {
                        continue;
                    }
                    if (!authoritativeGuardDerivationEdge(edge)) {
                        continue;
                    }
                    String source = string(edge.get("fromCell"));
                    if (!source.isEmpty()) {
                        work.addLast(source);
                    }
                }
            }
            return upstream;
        }

        /**
         * Computes the authoritative region live-in ancestors of the guard
         * controlling the exception seed.
         *
         * <p>The guard operand itself is normally an in-region value.  Making
         * every deep operand an independent input destroys the relation
         * {@code guard = f(region.in)}.  Instead, this walk crosses exact
         * in-region definition/data-dependency edges (including call argument
         * bindings) until it reaches a root argument, shared heap prestate,
         * environment input, incoming protocol endpoint, or opaque call
         * result.  Only those frontier cells are mandatory and therefore
         * protected from the broad port cap.</p>
         *
         * <p>A missing or non-authoritative predecessor is not permission to
         * invent a free variable.  It becomes an explicit derivation gap and
         * remains bound to the value observed in the concrete activation.
         * Runtime refinement may later supply exact call/receiver evidence
         * and promote its proven ancestor.  Thus an incomplete symbolic
         * relation does not prevent concrete-path analysis, while unknown
         * values never silently become symbolic.  No application class,
         * method, or field name participates in the decision.</p>
         */
        private SeedGuardInputFrontier seedGuardInputFrontier(
                RegionDraft draft, Set<String> boundaryInputs,
                Set<String> opaqueCallReturns) {
            SeedGuardInputFrontier result = new SeedGuardInputFrontier();
            if (!draft.exceptionDirected) {
                return result;
            }
            Set<String> seedCells = seedInterfaceCells(draft);
            if (seedCells.isEmpty()) {
                return result;
            }

            StaticGraphIndex analysis = analysisGraph(draft);
            Set<String> guardSources = new LinkedHashSet<>();
            for (Map<String, Object> edge : analysis.edges()) {
                String target = string(edge.get("toCell"));
                if (draft.anchorMethod.equals(string(edge.get("method")))
                        && "GUARD".equals(string(edge.get("transferKind")))
                        && seedCells.contains(target)) {
                    String source = string(edge.get("fromCell"));
                    if (!source.isEmpty()) {
                        guardSources.add(source);
                    }
                }
            }

            Deque<String> work = new ArrayDeque<>(guardSources);
            Set<String> visited = new LinkedHashSet<>();
            while (!work.isEmpty()) {
                String current = work.removeFirst();
                if (!visited.add(current)) {
                    continue;
                }
                if (authoritativeGuardLiveIn(current, draft,
                        boundaryInputs, opaqueCallReturns)) {
                    result.liveIns.add(current);
                    continue;
                }

                List<Map<String, Object>> definitions = new ArrayList<>();
                boolean incomingProtocolBoundary = false;
                for (Map<String, Object> edge : analysis.incoming(current)) {
                    if (isBoundary(edge)) {
                        // The consumer-side endpoint is the region live-in.
                        // Its producer belongs to another region and is
                        // connected later by the region worklist.
                        // A mapping-only/unvalidated contract is only a
                        // discovery hint.  It must not hide an exact getter or
                        // other in-region definition behind that endpoint.
                        if (authoritativeGuardProtocolBoundary(edge)) {
                            incomingProtocolBoundary = true;
                        }
                        continue;
                    }
                    if (authoritativeGuardDerivationEdge(edge)) {
                        definitions.add(edge);
                    }
                }
                definitions = nonRedundantGuardDefinitions(definitions);
                if (incomingProtocolBoundary) {
                    result.liveIns.add(current);
                    continue;
                }
                if (definitions.isEmpty()) {
                    result.addGap(current);
                    continue;
                }
                for (Map<String, Object> definition : definitions) {
                    String source = string(definition.get("fromCell"));
                    if (source.isEmpty() || source.equals(current)) {
                        result.addGap(current);
                    } else {
                        work.addLast(source);
                    }
                }
            }
            return result;
        }

        /**
         * Removes alternate encodings of the same exact Jimple definition.
         *
         * <p>The static graph deliberately records both executable operands
         * and convenient aliases: an invoke result has a {@code call_return}
         * row as well as its modeled receiver/argument dependencies, a field
         * read has both declared-field and receiver-projection rows, and Soot
         * may expose both a cast expression and its leaf local.  Traversing
         * every one of those rows as an independent predecessor creates fake
         * derivation gaps even though concolic execution evaluates the one
         * definition at that site.  Prefer the executable/model dependency or
         * canonical declared field only when it has the same target and exact
         * site.  Different sites remain separate reaching definitions.</p>
         */
        private List<Map<String, Object>> nonRedundantGuardDefinitions(
                List<Map<String, Object>> definitions) {
            if (definitions.size() < 2) {
                return definitions;
            }
            List<Map<String, Object>> result = new ArrayList<>();
            for (Map<String, Object> edge : definitions) {
                if (redundantCallReturnAlias(edge, definitions)
                        || redundantProjectedFieldAlias(edge, definitions)
                        || redundantCastExpressionAlias(edge, definitions)) {
                    continue;
                }
                result.add(edge);
            }
            return result;
        }

        private boolean redundantCallReturnAlias(
                Map<String, Object> edge,
                List<Map<String, Object>> definitions) {
            String kind = string(edge.get("kind"));
            if (!("call_return".equals(kind)
                    || "projected_call_return".equals(kind))) {
                return false;
            }
            for (Map<String, Object> alternative : definitions) {
                String alternativeKind = string(alternative.get("kind"));
                if (alternative == edge
                        || "call_return".equals(alternativeKind)
                        || "projected_call_return".equals(alternativeKind)) {
                    continue;
                }
                if (sameGuardDefinitionSite(edge, alternative)) {
                    return true;
                }
            }
            return false;
        }

        private boolean redundantProjectedFieldAlias(
                Map<String, Object> edge,
                List<Map<String, Object>> definitions) {
            String source = string(edge.get("fromCell"));
            if (globalFieldCell(source) || !source.contains("#field:")) {
                return false;
            }
            String leaf = guardFieldLeaf(source);
            if (leaf.isEmpty()) {
                return false;
            }
            for (Map<String, Object> alternative : definitions) {
                String alternativeSource = string(alternative.get(
                        "fromCell"));
                if (alternative != edge
                        && globalFieldCell(alternativeSource)
                        && leaf.equals(guardFieldLeaf(alternativeSource))
                        && sameGuardDefinitionSite(edge, alternative)) {
                    return true;
                }
            }
            return false;
        }

        private boolean redundantCastExpressionAlias(
                Map<String, Object> edge,
                List<Map<String, Object>> definitions) {
            String source = string(edge.get("fromCell"));
            Matcher cast = CAST_LOCAL_PATTERN.matcher(source);
            if (!cast.matches()) {
                return false;
            }
            String local = cast.group(1);
            for (Map<String, Object> alternative : definitions) {
                String alternativeSource = string(alternative.get(
                        "fromCell"));
                if (alternative != edge
                        && alternativeSource.endsWith("::" + local)
                        && sameGuardDefinitionSite(edge, alternative)) {
                    return true;
                }
            }
            return false;
        }

        private boolean sameGuardDefinitionSite(
                Map<String, Object> left, Map<String, Object> right) {
            String site = string(left.get("siteId"));
            return !site.isEmpty()
                    && site.equals(string(right.get("siteId")))
                    && string(left.get("toCell")).equals(string(right.get(
                    "toCell")));
        }

        private String guardFieldLeaf(String cell) {
            String value = string(cell);
            int projection = value.lastIndexOf("#field:");
            if (projection >= 0) {
                return value.substring(projection + "#field:".length());
            }
            Matcher global = GLOBAL_FIELD_LEAF_PATTERN.matcher(value);
            return global.matches() ? global.group(1) : "";
        }

        private boolean authoritativeGuardLiveIn(
                String cell, RegionDraft draft, Set<String> boundaryInputs,
                Set<String> opaqueCallReturns) {
            if (cell.isEmpty() || internalExpression(cell)) {
                return false;
            }
            if (globalFieldCell(cell) || isEnvironmentCell(cell)
                    || opaqueCallReturns.contains(cell)) {
                return true;
            }
            if (boundaryInputs.contains(cell)
                    && !internallyDefinedBoundaryAlias(cell, draft)) {
                return true;
            }
            String method = methodForCell(cell);
            return draft.rootMethod.equals(method)
                    && (cell.contains(".param")
                    || cell.startsWith("@this:"));
        }

        private boolean authoritativeGuardProtocolBoundary(
                Map<String, Object> edge) {
            if (!isBoundary(edge)
                    || !StaticDataflowEdgeSchema.automaticSemantics(edge)) {
                return false;
            }
            String relation = string(edge.get("relation"));
            return "value_flow".equals(relation)
                    || "taint_depends_on".equals(relation);
        }

        /**
         * The edge need not already encode the transfer function: concolic
         * execution evaluates in-region bytecode.  It must, however, be an
         * admitted backward data dependency with exact static provenance.
         */
        private boolean authoritativeGuardDerivationEdge(
                Map<String, Object> edge) {
            if (!definitionLikeGuardEdge(edge)
                    || !StaticDataflowEdgeSchema.automaticSemantics(edge)
                    || string(edge.get("id")).isEmpty()) {
                return false;
            }
            String relation = string(edge.get("relation"));
            return "value_flow".equals(relation)
                    || "taint_depends_on".equals(relation);
        }

        private boolean definitionLikeGuardEdge(Map<String, Object> edge) {
            String transfer = string(edge.get("transferKind"));
            return !"GUARD".equals(transfer)
                    && !"SEED".equals(transfer)
                    && !"EXCEPTION".equals(transfer)
                    && !"control_depends_on".equals(string(edge.get(
                    "relation")));
        }

        /**
         * Recognizes a synthetic protocol target that is only an alias for a
         * value computed by the receiving region. Configured protocol mappings can
         * attach a protocol edge directly to a caller local even though the
         * same local is defined by an in-region accessor call.  Keeping that
         * bare local as another boundary symbol both duplicates the real
         * carrier/field frontier and cannot be materialized independently.
         *
         * <p>This check is deliberately fail-closed.  It applies only to a
         * bare method local and requires an incoming value-flow definition
         * whose edge and, when identifiable, source method are both in this
         * region.  A protocol edge or a guard/control dependency is never
         * sufficient to demote a real boundary input.</p>
         */
        private boolean internallyDefinedBoundaryAlias(
                String candidate, RegionDraft draft) {
            if (!candidate.contains("::") || candidate.contains("#field:")
                    || candidate.contains(".param")
                    || candidate.endsWith(".return")
                    || methodForCell(candidate).isEmpty()) {
                return false;
            }
            for (Map<String, Object> edge
                    : analysisGraph(draft).incoming(candidate)) {
                if (isBoundary(edge)
                        || "GUARD".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                String relation = string(edge.get("relation"));
                if (!"value_flow".equals(relation)
                        && !"taint_depends_on".equals(relation)) {
                    continue;
                }
                String edgeMethod = string(edge.get("method"));
                if (!draft.methods.contains(edgeMethod)) {
                    continue;
                }
                String sourceMethod = methodForCell(
                        string(edge.get("fromCell")));
                if (!sourceMethod.isEmpty()
                        && !draft.methods.contains(sourceMethod)) {
                    continue;
                }
                return true;
            }
            return false;
        }

        /**
         * Returns leaf cells of the selected backward slice.  These are the
         * only values eligible to become independent symbols; intermediate
         * locals and call results with an in-region definition stay derived.
         */
        private Set<String> causalFrontierCells(RegionDraft draft) {
            Set<String> frontier = new LinkedHashSet<>();
            if (!draft.exceptionDirected) {
                return frontier;
            }
            Set<String> defined = new LinkedHashSet<>();
            for (Map<String, Object> edge : draft.causalEdges) {
                String target = string(edge.get("toCell"));
                if (!target.isEmpty()) {
                    defined.add(target);
                }
            }
            for (Map<String, Object> edge : draft.causalEdges) {
                String source = string(edge.get("fromCell"));
                if (!source.isEmpty() && !defined.contains(source)) {
                    frontier.add(source);
                }
            }
            return frontier;
        }

        /**
         * Finds call results consumed by this region whose semantics are not
         * closed by an analysed callee body.  A static transform label is not
         * semantic evidence and therefore cannot close this frontier.
         */
        private Set<String> opaqueCallReturnFrontier(RegionDraft draft) {
            Set<String> opaque = new LinkedHashSet<>();
            for (Map<String, Object> edge : analysisGraph(draft).edges()) {
                if (isBoundary(edge)) {
                    continue;
                }
                // A global exception slice can cross a shared-field write
                // into an upstream producer.  Calls made by that producer
                // are inputs of the producer region, not of this consumer
                // region.  Only a call whose result is consumed by one of
                // the current region's methods can terminate this region's
                // live-in walk.  Runtime later selects the concrete subset
                // of these same-thread methods.
                if (!draft.methods.contains(string(edge.get("method")))) {
                    continue;
                }
                String candidate = string(edge.get("fromCell"));
                if (!candidate.endsWith(">.return")) {
                    continue;
                }
                if (JavaPrimitiveBoxing.deterministicValueOfReturn(
                        candidate)) {
                    continue;
                }
                if (callResultHasCausalAlternative(candidate, draft)) {
                    continue;
                }
                if (!internallyDerivedCallResult(candidate, draft)) {
                    opaque.add(candidate);
                }
            }
            return opaque;
        }

        private boolean internallyDerivedCallResult(String candidate,
                                                     RegionDraft draft) {
            String returnedMethod = methodForCell(candidate);
            if (returnedMethod.isEmpty()) {
                return false;
            }
            if (draft.methods.contains(returnedMethod)) {
                return internallyDerivedTargets(draft).contains(candidate);
            }
            return planBackedSameThreadCallResult(candidate, returnedMethod,
                    draft);
        }

        /**
         * Proves that a return just beyond the broad region method budget is
         * nevertheless computed by this activation rather than supplied as a
         * free live-in.
         *
         * <p>Non-exception regions intentionally keep a compact method list;
         * requested-output slices later rebuild the exact same-thread closure
         * from the full call graph.  A helper one level beyond that compact
         * list therefore used to be labelled {@code OPAQUE_CALL_RETURN} even
         * when an exact call-return edge and an analysed callee plan already
         * proved its definition.  Besides ordinary helpers, javac-generated
         * access bridges have precisely this shape.  Treating their result as
         * an independent input over-approximates the program and can make the
         * final query satisfiable for values no Java execution can produce.</p>
         *
         * <p>The proof below is deliberately structural and fail closed.  It
         * does not inspect method or class names.  The caller must already be
         * in this draft, the edge must be an authoritative non-boundary
         * {@code call_return}, its declared callee must be the method encoded
         * by the return cell, that method must be reachable without crossing
         * a protocol boundary, and its symbolic plan must explicitly define
         * the exact return cell.  Truly native/library/unanalyzed calls still
         * terminate the symbolic frontier.</p>
         */
        private boolean planBackedSameThreadCallResult(
                String candidate, String returnedMethod, RegionDraft draft) {
            if (!graph.outputs(returnedMethod).contains(candidate)
                    || !reachableFrom(draft.rootMethod, returnedMethod)) {
                return false;
            }
            for (Map<String, Object> edge
                    : analysisGraph(draft).outgoing(candidate)) {
                if (!draft.methods.contains(string(edge.get("method")))
                        || isBoundary(edge)
                        || !"FUNCTION_RETURN".equals(string(edge.get(
                        "transferKind")))
                        || !"call_return".equals(string(edge.get("kind")))
                        || !returnedMethod.equals(string(edge.get("invoke")))
                        || !exactStaticValueFlow(edge)) {
                    continue;
                }
                return true;
            }
            return false;
        }

        private Set<String> internallyDerivedTargets(RegionDraft draft) {
            if (draft.internallyDerivedTargets != null) {
                return draft.internallyDerivedTargets;
            }
            Set<String> targets = new LinkedHashSet<>();
            for (String method : draft.methods) {
                targets.addAll(graph.outputs(method));
            }
            for (Map<String, Object> edge : analysisGraph(draft).edges()) {
                if (draft.methods.contains(string(edge.get("method")))) {
                    String target = string(edge.get("toCell"));
                    if (!target.isEmpty()) {
                        targets.add(target);
                    }
                }
            }
            draft.internallyDerivedTargets = targets;
            return draft.internallyDerivedTargets;
        }

        private StaticGraphIndex analysisGraph(RegionDraft draft) {
            if (draft.analysisGraph != null) {
                return draft.analysisGraph;
            }
            List<Map<String, Object>> relevant = draft.exceptionDirected
                    ? new ArrayList<>(draft.causalEdges)
                    : graph.forMethods(draft.methods);
            draft.analysisGraph = new StaticGraphIndex(relevant);
            return draft.analysisGraph;
        }

        private boolean exceptionRegionOutput(String output,
                                              RegionDraft draft) {
            if (output.contains("#exception:")) {
                return true;
            }
            for (Map<String, Object> edge : draft.causalEdges) {
                if ("HEAP_WRITE".equals(string(edge.get("transferKind")))
                        && output.equals(string(edge.get("toCell")))) {
                    return true;
                }
            }
            return false;
        }

        private boolean causalCandidate(String candidate, RegionDraft draft) {
            if (!draft.exceptionDirected) {
                return true;
            }
            if (draft.causalCells.contains(candidate)) {
                return true;
            }
            // Synthetic return/local projections are exact runtime values,
            // not declared heap identities.  Do not admit one through the
            // semantic field-family fallback: that could make an unrelated
            // projected boundary field look causal merely because another
            // field with the same owner/name appears in the slice.  Declared
            // and global field aliases keep the existing fallback below.
            if (syntheticValueProjection(candidate)) {
                return false;
            }
            String candidateField = semanticFieldKey(candidate, draft.rootMethod);
            if (candidateField.isEmpty()) {
                return false;
            }
            for (String causal : draft.causalCells) {
                if (candidateField.equals(semanticFieldKey(causal,
                        draft.rootMethod))) {
                    return true;
                }
            }
            return false;
        }

        private String derivedReason(String candidate, RegionDraft draft,
                                     Set<String> produced, boolean boundary,
                                     Set<String> mutableHeapPrestateKeys) {
            if (boundary || environmentInput(candidate)) {
                return "";
            }
            if (internalExpression(candidate)) {
                return "expression or allocation is evaluated inside the region";
            }
            if (immutableStaticConstant(candidate)) {
                return "static constant is fixed program state, not a symbolic input";
            }
            String fieldKey = semanticFieldKey(candidate, draft.rootMethod);
            boolean mutableHeapPrestate = !fieldKey.isEmpty()
                    && mutableHeapPrestateKeys.contains(fieldKey);
            // Root argument carriers are always materializable live-ins, but
            // their field projections need not be: an authoritative CFG
            // must-def may prove that a projection is overwritten before any
            // in-region read.  Keep this check after the field proof so a
            // projected root field is not admitted merely because its cell
            // encoding also contains ".paramN".
            if (rootParameter(candidate, draft.rootMethod)) {
                return "";
            }
            if (candidate.startsWith("@this:")
                    && !candidate.contains("#field:")) {
                return "receiver identity is a concrete carrier; its read fields are the inputs";
            }
            if (exactAggregateFieldCarrier(candidate, draft)) {
                return "aggregate field identity is a concrete carrier; "
                        + "its exact projected fields are the inputs";
            }
            if (callResultHasCausalAlternative(candidate, draft)) {
                return "call result has a tracked in-region operand or field projection";
            }
            if (JavaPrimitiveBoxing.deterministicValueOfReturn(candidate)) {
                return "primitive boxing return is derived by the exact "
                        + "valueOf operand";
            }
            if (internallyDerivedCallResult(candidate, draft)) {
                return "return value is derived by a call executed inside the region";
            }
            String method = methodForCell(candidate);
            if (!method.isEmpty() && draft.methods.contains(method)) {
                if (method.equals(draft.rootMethod)) {
                    if (candidate.contains("::")) {
                        return "root local is defined inside the region";
                    }
                } else if (candidate.contains(".param")
                        || candidate.startsWith("@this:")
                        || candidate.contains("::")
                        || candidate.endsWith(".return")) {
                    return "callee value is supplied or computed inside the region";
                }
            }
            if (!mutableHeapPrestate && produced.contains(candidate)) {
                return "value has an internal region definition";
            }
            return "";
        }

        /**
         * Treats an aggregate reference as a concrete carrier only when each
         * selected read of that exact declared field is shadowed by at least
         * one authoritative field-sensitive value-flow row for the same JVM
         * definition.  The carrier/nullness remains pinned to the concrete
         * path; only the proven projected leaves become symbolic inputs.
         * Scalar fields, unprojected uses, writes/mutations, and ambiguous
         * metadata stay at the fail-closed frontier.
         */
        private boolean exactAggregateFieldCarrier(
                String candidate, RegionDraft draft) {
            DeclaredField field = declaredField(candidate);
            if (field == null || closedProtocolScalarType(field.type())) {
                return false;
            }
            boolean read = false;
            StaticGraphIndex analysis = analysisGraph(draft);
            for (Map<String, Object> raw : analysis.outgoing(candidate)) {
                if (!"HEAP_READ".equals(string(raw.get("transferKind")))
                        || Boolean.TRUE.equals(raw.get("fieldSensitive"))
                        || !exactStaticValueFlow(raw)) {
                    return false;
                }
                read = true;
                boolean projected = false;
                for (Map<String, Object> shadow : analysis.edges()) {
                    String path = string(shadow.get("fieldPath"));
                    if (path.isEmpty()
                            || !Boolean.TRUE.equals(shadow.get(
                            "fieldSensitive"))
                            || !exactStaticValueFlow(shadow)
                            || !sameExactDefinitionSiteIgnoringTarget(raw,
                            shadow)
                            || !candidate.equals(string(shadow.get(
                            "objectFromCell")))
                            || !string(raw.get("toCell")).equals(string(
                            shadow.get("objectToCell")))
                            || !(candidate + path).equals(string(shadow.get(
                            "fromCell")))
                            || !(string(raw.get("toCell")) + path).equals(
                            string(shadow.get("toCell")))) {
                        continue;
                    }
                    projected = true;
                    break;
                }
                if (!projected) {
                    return false;
                }
            }
            return read;
        }

        private boolean sameExactDefinitionSiteIgnoringTarget(
                Map<String, Object> first, Map<String, Object> second) {
            return string(first.get("method")).equals(string(second.get(
                    "method")))
                    && string(first.get("siteId")).equals(string(second.get(
                    "siteId")))
                    && integer(first.get("unitIndex"), -1) >= 0
                    && integer(first.get("unitIndex"), -1) == integer(
                    second.get("unitIndex"), -1)
                    && string(first.get("unit")).equals(string(second.get(
                    "unit")));
        }

        /**
         * Detects duplicate call-result aliases in the static graph. Soot may
         * emit both a semantic dependency (for example receiver.field or a
         * boxing operand) and a generic callee.return edge for the same Jimple
         * definition. The semantic edge is the dependency; exposing the
         * return alias as another independent input would break relational
         * summaries and conflate multiple call sites of the same method.
         */
        private boolean callResultHasCausalAlternative(
                String candidate, RegionDraft draft) {
            if (candidate == null || !candidate.contains(">.return")) {
                return false;
            }
            return callResultsWithCausalAlternative(draft).contains(
                    candidate);
        }

        private Set<String> callResultsWithCausalAlternative(
                RegionDraft draft) {
            if (draft.callResultsWithCausalAlternative != null) {
                return draft.callResultsWithCausalAlternative;
            }
            List<Map<String, Object>> selected =
                    analysisGraph(draft).edges();
            Map<String, Set<String>> returnsBySite =
                    new LinkedHashMap<>();
            Set<String> alternativeSites = new LinkedHashSet<>();
            for (Map<String, Object> edge : selected) {
                if (isBoundary(edge)) {
                    continue;
                }
                String source = string(edge.get("fromCell"));
                String target = string(edge.get("toCell"));
                String method = string(edge.get("method"));
                int unit = integer(edge.get("unitIndex"), -1);
                if (target.isEmpty() || method.isEmpty() || unit < 0) {
                    continue;
                }
                String site = target + "\n" + method + "\n" + unit;
                if (source.contains(">.return")) {
                    returnsBySite.computeIfAbsent(site,
                            ignored -> new LinkedHashSet<>()).add(source);
                } else if (!source.isEmpty()) {
                    alternativeSites.add(site);
                }
            }
            Set<String> result = new LinkedHashSet<>();
            for (String site : alternativeSites) {
                Set<String> returned = returnsBySite.get(site);
                if (returned != null) {
                    result.addAll(returned);
                }
            }
            draft.callResultsWithCausalAlternative = result;
            return draft.callResultsWithCausalAlternative;
        }

        private boolean internalExpression(String value) {
            String candidate = value == null ? "" : value.trim();
            if (candidate.isEmpty()) {
                return false;
            }
            return candidate.startsWith("new ")
                    || candidate.startsWith("newarray ")
                    || candidate.startsWith("newmultiarray ")
                    || candidate.startsWith("lengthof ")
                    || candidate.matches("^<[^>]+>#u\\d+$")
                    || candidate.contains(" instanceof ")
                    || candidate.matches("^\\([^()]+\\)\\s*[$]?[A-Za-z_][A-Za-z0-9_]*$")
                    || candidate.matches("[$]?[A-Za-z_][A-Za-z0-9_]*\\[[^]]+]" )
                    || candidate.matches(".*\\s(?:==|!=|>=|<=|>|<)\\s.*")
                    || candidate.matches(".*\\s[+*/%&|^]\\s.*")
                    || candidate.matches(".*\\s-\\s.*")
                    || "true".equals(candidate)
                    || "false".equals(candidate)
                    || candidate.matches("-?\\d+(?:[lLfFdD])?");
        }

        private boolean immutableStaticConstant(String value) {
            Matcher field = GLOBAL_FIELD_LEAF_PATTERN.matcher(
                    value == null ? "" : value.trim());
            return field.matches()
                    && field.group(1).matches("[A-Z][A-Z0-9_]*");
        }

        private Set<String> boundaryInputs(
                Set<String> methods, Set<String> externalSources) {
            Set<String> inputs = new LinkedHashSet<>();
            for (Map<String, Object> edge : boundaryEdges) {
                String targetMethod = methodForCell(string(edge.get("toCell")));
                if (targetMethod.isEmpty()) {
                    targetMethod = string(edge.get("method"));
                }
                if (!methods.contains(targetMethod)) {
                    continue;
                }
                String target = string(edge.get("toCell"));
                inputs.add(target.isEmpty() ? string(edge.get("fromCell")) : target);
                String sourceMethod = methodForCell(string(edge.get("fromCell")));
                if (!methods.contains(sourceMethod)) {
                    externalSources.add(string(edge.get("fromCell")));
                }
            }
            return inputs;
        }

        private Map<String, String> mutableHeapPrestateCells(
                RegionDraft draft, Set<String> readFieldKeys) {
            Map<String, String> readCells = new LinkedHashMap<>();
            List<Map<String, Object>> methodEdges =
                    graph.forMethods(draft.methods);
            for (Map<String, Object> edge : methodEdges) {
                if (!"HEAP_READ".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                String cell = string(edge.get("fromCell"));
                String key = semanticFieldKey(cell, draft.rootMethod);
                if (!key.isEmpty()) {
                    readFieldKeys.add(key);
                    readCells.putIfAbsent(key, cell);
                }
            }
            Map<String, String> result = new LinkedHashMap<>();
            for (Map<String, Object> edge : methodEdges) {
                if (!"HEAP_WRITE".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                String cell = string(edge.get("toCell"));
                String key = semanticFieldKey(cell, draft.rootMethod);
                if (!key.isEmpty()
                        && "field_mutation".equals(string(edge.get("kind")))
                        && globalFieldCell(cell)) {
                    result.putIfAbsent(key, cell);
                } else if (!key.isEmpty() && readCells.containsKey(key)) {
                    result.putIfAbsent(key, readCells.get(key));
                }
            }
            return result;
        }

        private String semanticFieldKey(String value, String rootMethod) {
            String cell = string(value);
            int projection = cell.indexOf("#field:");
            Matcher global = SEMANTIC_GLOBAL_FIELD_PATTERN.matcher(cell);
            if (global.matches()) {
                String suffix = global.group(3);
                return global.group(1) + "#" + global.group(2)
                        + normalizedFieldSuffix(suffix);
            }
            if (cell.startsWith("@this: ") && projection >= 0) {
                String receiverOwner = cell.substring("@this: ".length(),
                        projection).trim();
                return receiverOwner + "#"
                        + cell.substring(projection + "#field:".length())
                        .replace("#field:", "#");
            }
            if (projection >= 0) {
                String method = methodForCell(cell);
                if (!method.isEmpty()) {
                    String methodOwner = owner(method);
                    String rootOwner = owner(rootMethod);
                    if (methodOwner.equals(rootOwner)
                            || methodOwner.startsWith(rootOwner + "$")) {
                        return methodOwner + "#"
                                + cell.substring(projection + "#field:".length())
                                .replace("#field:", "#");
                    }
                }
            }
            return "";
        }

        private String normalizedFieldSuffix(String suffix) {
            return suffix == null || suffix.isEmpty()
                    ? "" : suffix.replace("#field:", "#");
        }

        private int inputPreference(String value, String rootMethod,
                                    boolean boundary,
                                    boolean mutableHeapPrestate) {
            if (mutableHeapPrestate && globalFieldCell(value)) {
                // Stable global identity is required to bind the old heap
                // state to the requested output port after runtime path
                // refinement.
                return -1;
            }
            if (boundary) {
                return 0;
            }
            if (value.startsWith("@this: " + owner(rootMethod) + "#field:")) {
                return 1;
            }
            if (globalFieldCell(value) || value.matches(
                    "<[^:]+:\\s+[^()<>]+\\s+[^\\s()>]+>#field:.*")) {
                return 2;
            }
            if (rootMethod.equals(methodForCell(value))) {
                return 3;
            }
            return 4;
        }

        private boolean rootParameter(String value, String rootMethod) {
            return rootMethod.equals(methodForCell(value))
                    && value.contains(".param");
        }

        private boolean environmentInput(String value) {
            return isEnvironmentCell(value)
                    || lower(value).equals("time.now");
        }

        private void addSeedOutputs(Set<String> methods, Set<String> outputs) {
            for (Map<String, Object> edge : graph.forMethods(methods)) {
                if ("SEED".equals(string(edge.get("transferKind")))
                        || lower(string(edge.get("kind"))).contains("seed")) {
                    outputs.add(string(edge.get("fromCell")));
                    outputs.add(string(edge.get("toCell")));
                }
            }
        }

        private Set<String> seedInterfaceCells(RegionDraft draft) {
            Set<String> result = new LinkedHashSet<>();
            if (!draft.exceptionDirected) {
                return result;
            }
            for (Map<String, Object> edge : draft.causalEdges) {
                if (!draft.anchorMethod.equals(string(edge.get("method")))
                        || !"SEED".equals(string(edge.get(
                        "transferKind")))) {
                    continue;
                }
                String source = string(edge.get("fromCell"));
                String target = string(edge.get("toCell"));
                if (!source.isEmpty()) {
                    result.add(source);
                }
                if (!target.isEmpty()) {
                    result.add(target);
                }
            }
            return result;
        }

        private List<String> priorityOrdered(Collection<String> values,
                                             Set<String> priority) {
            List<String> result = new ArrayList<>();
            for (String value : sorted(priority)) {
                if (values.contains(value)) {
                    result.add(value);
                }
            }
            for (String value : sorted(values)) {
                if (!priority.contains(value)) {
                    result.add(value);
                }
            }
            return result;
        }

        /**
         * Region outputs are semantic interfaces, not a dump of every method
         * plan definition.  Keep directed bug predicates, canonical global
         * state, and exact scalar boundary sources.  Compiler locals, branch
         * units, and local/return projections remain in relevantStates and
         * requested-output causal diagnostics but do not receive ports.
         */
        private boolean semanticOutput(String output, RegionDraft region) {
            if (bugPredicateOutput(output)) {
                return true;
            }
            if (output.contains("#field:")) {
                // A projection is an interface only when the exact projected
                // return itself is the proven outbound boundary source.
                return output.contains(".return#field:")
                        && outboundProtocolReturnValue(region, output);
            }
            if (globalFieldCell(output)) {
                return sharedFieldBoundarySource(region, output);
            }
            if (output.endsWith(".return")) {
                return outboundProtocolReturnValue(region, output);
            }
            return false;
        }

        private boolean sharedFieldBoundarySource(
                RegionDraft region, String field) {
            boolean exactDefinition = false;
            boolean anchorDefinition = false;
            for (Map<String, Object> edge : graph.incoming(field)) {
                if (region.methods.contains(string(edge.get("method")))
                        && exactSharedFieldDefinition(edge)) {
                    exactDefinition = true;
                    anchorDefinition |= region.anchorMethod.equals(
                            string(edge.get("method")));
                }
            }
            if (!exactDefinition) {
                return false;
            }
            for (Map<String, Object> edge : graph.outgoing(field)) {
                String method = string(edge.get("method"));
                if (!region.methods.contains(method)
                        && "HEAP_READ".equals(string(edge.get(
                        "transferKind")))) {
                    return true;
                }
                if (isBoundary(edge)) {
                    String targetMethod = methodForCell(string(edge.get(
                            "toCell")));
                    if (!targetMethod.isEmpty()
                            && !region.methods.contains(targetMethod)) {
                        return true;
                    }
                }
            }
            if (anchorDefinition) {
                for (Map<String, Object> edge : graph.outgoing(field)) {
                    if (!"HEAP_READ".equals(string(edge.get(
                            "transferKind")))) {
                        continue;
                    }
                    String reader = string(edge.get("method"));
                    if (!reader.isEmpty() && siblingDynamicDispatch(
                            region.rootMethod, reader,
                            region.anchorMethod)) {
                        return true;
                    }
                }
            }
            if (fieldBacksProjectedBoundary(region, field)) {
                return true;
            }
            // A method plan can expose the downstream live-in even when the
            // compact test/static slice has not retained a separate HEAP_READ
            // row.  Exact cell identity plus a method outside the producer
            // region is still a cross-region def-to-live-in boundary.
            for (String method : graph.methods()) {
                if (!region.methods.contains(method)
                        && graph.inputs(method).contains(field)) {
                    return true;
                }
            }
            return false;
        }

        private boolean exactSharedFieldDefinition(
                Map<String, Object> edge) {
            String kind = string(edge.get("kind"));
            return "HEAP_WRITE".equals(string(edge.get("transferKind")))
                    && ("field_write".equals(kind)
                    || "field_mutation".equals(kind))
                    && !StaticDataflowEdgeSchema.mappingOnly(edge)
                    && !string(edge.get("id")).isEmpty()
                    && !string(edge.get("siteId")).isEmpty()
                    && exactStaticValueFlow(edge);
        }

        private boolean fieldBacksProjectedBoundary(
                RegionDraft region, String fieldCell) {
            DeclaredField field = exactDeclaredField(fieldCell);
            if (field == null) {
                return false;
            }
            for (Map<String, Object> boundary : boundaryEdges) {
                String raw = string(boundary.get("fromCell"));
                String targetMethod = methodForCell(string(boundary.get(
                        "toCell")));
                if (targetMethod.isEmpty()
                        || region.methods.contains(targetMethod)) {
                    continue;
                }
                for (Map<String, Object> proof : graph.incoming(raw)) {
                    if (!eligibleProjectedReturnAlias(proof,
                            region.methods)) {
                        continue;
                    }
                    String source = string(proof.get("fromCell"));
                    String sourceMethod = methodForCell(source);
                    String base = sourceMethod + ".return#field:";
                    if (source.startsWith(base)
                            && field.owner().equals(declaredReturnType(
                            sourceMethod))
                            && field.name().equals(source.substring(
                            base.length()))) {
                        return true;
                    }
                }
            }
            return false;
        }

        private void buildRegionEdges(StaticProgram result) {
            Map<String, List<Map<String, Object>>> regionsByMethod = new LinkedHashMap<>();
            for (Map<String, Object> region : result.regions) {
                for (String method : strings(region.get("methods"))) {
                    regionsByMethod.computeIfAbsent(method, ignored -> new ArrayList<>())
                            .add(region);
                }
            }
            Set<String> emitted = new LinkedHashSet<>();
            int index = 0;
            for (Map<String, Object> edge : boundaryEdges) {
                String fromCell = string(edge.get("fromCell"));
                String toCell = string(edge.get("toCell"));
                String fromMethod = methodForCell(fromCell);
                String toMethod = methodForCell(toCell);
                if (toMethod.isEmpty()) {
                    toMethod = string(edge.get("method"));
                }
                List<Map<String, Object>> fromRegions = regionsByMethod.get(fromMethod);
                List<Map<String, Object>> toRegions = regionsByMethod.get(toMethod);
                if (toRegions == null || toRegions.isEmpty()) {
                    continue;
                }
                // A shared protocol helper can be enclosed by several
                // independently rooted regions.  The static boundary does
                // not identify which enclosing activation executed the
                // transfer, so publishing only the first region silently
                // assigns the endpoint to an arbitrary root.  Emit every
                // enclosing producer as a mapping-only candidate and leave
                // the choice to RuntimeRegionPlanner's exact endpoint
                // fingerprint and ordering checks.  A method outside all
                // regions retains the historical EXTERNAL producer.
                List<Map<String, Object>> sourceCandidates =
                        fromRegions == null || fromRegions.isEmpty()
                                ? Collections.singletonList(null)
                                : fromRegions;
                for (Map<String, Object> toRegion : toRegions) {
                    String toRegionId = string(toRegion.get("regionId"));
                    for (Map<String, Object> fromRegion : sourceCandidates) {
                        String fromRegionId = fromRegion == null
                                ? "EXTERNAL"
                                : string(fromRegion.get("regionId"));
                        String key = fromRegionId + "\n" + toRegionId + "\n"
                                + fromCell + "\n" + toCell + "\n"
                                + string(edge.get("siteId"));
                        if (!emitted.add(key)) {
                            continue;
                        }
                        Map<String, Object> regionEdge = object(
                                "schemaVersion",
                                REGION_SCHEMA_VERSION,
                                "edgeId", "REGION_EDGE." + index++,
                                "fromRegion", fromRegionId,
                                "fromPort", fromCell,
                                "toRegion", toRegionId,
                                "toPort", toCell,
                                "kind", boundaryKind(edge),
                                // A static boundary edge identifies ports and a
                                // possible relation.  It is not evidence that the
                                // values are equal.  RuntimeRegionPlanner may
                                // promote the candidate only after observing a
                                // complete value fingerprint on both endpoints.
                                "semanticMode", "MAPPING_ONLY",
                                "siteId", string(edge.get("siteId")));
                        CanonicalOutputResolution canonical =
                                canonicalProducerOutput(fromRegion, fromCell);
                        if (canonical != null) {
                            regionEdge.put("fromOutputPort", canonical.port);
                            regionEdge.put("fromOutputCell", canonical.cell);
                            regionEdge.put("aliasProofEdgeIds",
                                    canonical.proofEdgeIds);
                            regionEdge.put("aliasProofAuthority",
                                    "STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                                            + "AND_DECLARED_RETURN_FIELD");
                            regionEdge.put("aliasProofComplete", true);
                        }
                        result.regionEdges.add(regionEdge);
                    }
                }
            }

            Map<String, Set<String>> producerRegionsByField = new LinkedHashMap<>();
            Map<String, Set<String>> consumerRegionsByField = new LinkedHashMap<>();
            Set<String> mutationFieldsNeedingProjectedReads = new LinkedHashSet<>();
            for (Map<String, Object> edge
                    : graph.forMethods(regionsByMethod.keySet())) {
                String transfer = string(edge.get("transferKind"));
                String method = string(edge.get("method"));
                List<Map<String, Object>> methodRegions = regionsByMethod.get(method);
                if (methodRegions == null || methodRegions.isEmpty()) {
                    continue;
                }
                String field;
                Map<String, Set<String>> destination;
                if ("HEAP_WRITE".equals(transfer)) {
                    field = string(edge.get("toCell"));
                    destination = producerRegionsByField;
                    if ("field_mutation".equals(string(edge.get("kind")))) {
                        mutationFieldsNeedingProjectedReads.add(field);
                    }
                } else if ("HEAP_READ".equals(transfer)) {
                    field = string(edge.get("fromCell"));
                    destination = consumerRegionsByField;
                } else {
                    continue;
                }
                if (!globalFieldCell(field)) {
                    continue;
                }
                for (Map<String, Object> region : methodRegions) {
                    destination.computeIfAbsent(field, ignored -> new LinkedHashSet<>())
                            .add(string(region.get("regionId")));
                }
            }

            // A collection-valued field is commonly read through a library view,
            // for example `allKeys.values().toArray(...)`.  In that shape the
            // backward slice can retain `this#field:allKeys` while no direct
            // HEAP_READ edge survives across the library call.  Producers are
            // still explicit HEAP_WRITE/field_mutation edges.  Treat a region's
            // field-sensitive inputs as read candidates for those known fields;
            // the resulting edge remains a runtime-required over-approximation.
            for (String field : mutationFieldsNeedingProjectedReads) {
                if (!producerRegionsByField.containsKey(field)) {
                    continue;
                }
                for (Map<String, Object> region : result.regions) {
                    if (regionReferencesField(region, field)) {
                        consumerRegionsByField
                                .computeIfAbsent(field, ignored -> new LinkedHashSet<>())
                                .add(string(region.get("regionId")));
                    }
                }
            }
            for (Map.Entry<String, Set<String>> entry
                    : producerRegionsByField.entrySet()) {
                String field = entry.getKey();
                Set<String> consumers = consumerRegionsByField.get(field);
                if (consumers == null) {
                    continue;
                }
                for (String producer : entry.getValue()) {
                    for (String consumer : consumers) {
                        if (producer.equals(consumer)) {
                            continue;
                        }
                        String key = producer + "\n" + consumer + "\n" + field;
                        if (!emitted.add(key)) {
                            continue;
                        }
                        Map<String, Object> sharedEdge = object(
                                "schemaVersion",
                                REGION_SCHEMA_VERSION,
                                "edgeId", "REGION_EDGE." + index++,
                                "fromRegion", producer,
                                "fromPort", field,
                                "toRegion", consumer,
                                "toPort", field,
                                "kind", "SHARED_STATE",
                                "semanticMode",
                                "RUNTIME_VALIDATION_REQUIRED");
                        result.regionEdges.add(sharedEdge);
                    }
                }
            }
        }

        /**
         * Resolves a local protocol projection to a canonical output without
         * weakening runtime endpoint identity.  A direct slice-backed endpoint
         * needs no alias metadata.  Otherwise every admitted proof must be an
         * exact, SMT-eligible projected return value-flow row and all admitted
         * rows must agree on one declared-field output with one complete slice.
         * Missing or conflicting proof is deliberately fail-closed.
         */
        private CanonicalOutputResolution canonicalProducerOutput(
                Map<String, Object> region, String rawEndpoint) {
            if (region == null || rawEndpoint.isEmpty()
                    || exactCompleteOutput(region, rawEndpoint) != null) {
                return null;
            }
            Set<String> regionMethods = new LinkedHashSet<>(
                    strings(region.get("methods")));
            Map<String, Set<String>> proofIdsByOutput = new LinkedHashMap<>();
            Map<String, Map<String, Object>> outputsByKey =
                    new LinkedHashMap<>();
            boolean rejectedEligibleProof = false;
            for (Map<String, Object> proof : graph.incoming(rawEndpoint)) {
                if (!eligibleProjectedReturnAlias(proof,
                        regionMethods)) {
                    continue;
                }
                String source = string(proof.get("fromCell"));
                String sourceMethod = methodForCell(source);
                String projection = source.substring(
                        (sourceMethod + ".return").length());
                String fieldName = projection.substring(
                        "#field:".length());
                String returnType = declaredReturnType(sourceMethod);
                Map<String, Object> output = uniqueDeclaredFieldOutput(
                        region, returnType, fieldName);
                if (output == null) {
                    rejectedEligibleProof = true;
                    continue;
                }
                String port = string(output.get("portId"));
                String cell = string(output.get("cell"));
                String key = port + "\n" + cell;
                outputsByKey.put(key, output);
                proofIdsByOutput.computeIfAbsent(key,
                        ignored -> new LinkedHashSet<>()).add(
                        string(proof.get("id")));
            }
            if (rejectedEligibleProof || proofIdsByOutput.size() != 1) {
                return null;
            }
            Map.Entry<String, Set<String>> only = proofIdsByOutput.entrySet()
                    .iterator().next();
            if (only.getValue().isEmpty()) {
                return null;
            }
            Map<String, Object> output = outputsByKey.get(only.getKey());
            return new CanonicalOutputResolution(
                    string(output.get("portId")),
                    string(output.get("cell")), only.getValue());
        }

        private boolean eligibleProjectedReturnAlias(
                Map<String, Object> proof, Set<String> regionMethods) {
            String kind = string(proof.get("kind"));
            if (!("projected_call_return".equals(kind)
                    || "projected_caller_return".equals(kind)
                    || "projected_method_caller_return".equals(kind))
                    || !"FUNCTION_RETURN".equals(string(
                    proof.get("transferKind")))
                    || !"value_flow".equals(string(proof.get("relation")))
                    || !Boolean.TRUE.equals(proof.get("fieldSensitive"))
                    || !StaticDataflowEdgeSchema.automaticSemantics(proof)
                    || string(proof.get("id")).isEmpty()) {
                return false;
            }
            String source = string(proof.get("fromCell"));
            String target = string(proof.get("toCell"));
            String sourceMethod = methodForCell(source);
            String targetMethod = methodForCell(target);
            if (sourceMethod.isEmpty() || targetMethod.isEmpty()
                    || !regionMethods.contains(sourceMethod)
                    || !regionMethods.contains(targetMethod)
                    || !targetMethod.equals(string(proof.get("method")))) {
                return false;
            }
            String sourceBase = sourceMethod + ".return";
            if (!source.startsWith(sourceBase + "#field:")) {
                return false;
            }
            String projection = source.substring(sourceBase.length());
            // Declared return type identifies the owner of exactly the first
            // field only.  Nested projections require additional declared
            // type proofs and therefore remain unresolved here.
            if (!projection.matches("#field:[^#]+")
                    || declaredReturnType(sourceMethod).isEmpty()
                    || "void".equals(declaredReturnType(sourceMethod))) {
                return false;
            }
            String objectFrom = string(proof.get("objectFromCell"));
            String objectTo = string(proof.get("objectToCell"));
            return sourceBase.equals(objectFrom)
                    && projection.equals(string(proof.get("fieldPath")))
                    && source.equals(objectFrom + projection)
                    && target.equals(objectTo + projection);
        }

        private Map<String, Object> uniqueDeclaredFieldOutput(
                Map<String, Object> region, String owner, String fieldName) {
            return unique(maps(region.get("outputs")), output -> {
                String cell = string(output.get("cell"));
                DeclaredField field = exactDeclaredField(cell);
                return globalFieldCell(cell) && field != null
                        && owner.equals(field.owner())
                        && fieldName.equals(field.name())
                        && exactCompleteOutput(region, cell) == output;
            });
        }

        private Map<String, Object> exactCompleteOutput(
                Map<String, Object> region, String endpoint) {
            Map<String, Object> match = null;
            for (Map<String, Object> output
                    : maps(region.get("outputs"))) {
                if (!endpoint.equals(string(output.get("portId")))
                        && !endpoint.equals(string(output.get("cell")))) {
                    continue;
                }
                if (!hasUniqueCompleteSlice(region, output)
                        || match != null) {
                    return null;
                }
                match = output;
            }
            return match;
        }

        private boolean hasUniqueCompleteSlice(Map<String, Object> region,
                                               Map<String, Object> output) {
            int matches = 0;
            for (Map<String, Object> slice
                    : maps(region.get("outputSlices"))) {
                if (string(output.get("portId")).equals(string(
                        slice.get("outputPort")))
                        && string(output.get("cell")).equals(string(
                        slice.get("outputCell")))
                        && completeOutputSlice(slice)) {
                    matches++;
                }
            }
            return matches == 1;
        }

        private String declaredReturnType(String method) {
            if (method == null || !method.startsWith("<")) {
                return "";
            }
            int colon = method.indexOf(':');
            int open = method.indexOf('(', colon + 1);
            int nameSeparator = open < 0 ? -1
                    : method.lastIndexOf(' ', open);
            if (colon < 0 || nameSeparator <= colon) {
                return "";
            }
            return method.substring(colon + 1, nameSeparator).trim();
        }

        private boolean regionReferencesField(Map<String, Object> region, String field) {
            DeclaredField signature = exactDeclaredField(field);
            if (signature == null) {
                return false;
            }
            List<String> candidates = new ArrayList<>();
            candidates.addAll(portCells(region.get("symbolicInputs")));
            candidates.addAll(portCells(region.get("outputs")));
            for (String method : strings(region.get("methods"))) {
                candidates.addAll(graph.inputs(method));
                candidates.addAll(graph.outputs(method));
            }
            String thisProjection = "@this: " + signature.owner()
                    + "#field:" + signature.name();
            for (String candidate : candidates) {
                if (field.equals(candidate)
                        || candidate.equals(thisProjection)
                        || candidate.startsWith(thisProjection + "#field:")) {
                    return true;
                }
                String method = methodForCell(candidate);
                if (!method.isEmpty()
                        && signature.owner().equals(owner(method))
                        && (candidate.endsWith("#field:" + signature.name())
                        || candidate.contains("#field:" + signature.name()
                        + "#field:"))) {
                    return true;
                }
            }
            return false;
        }

        private List<String> portCells(Object value) {
            List<String> cells = new ArrayList<>();
            for (Map<String, Object> item : maps(value)) {
                String cell = string(item.get("cell"));
                if (!cell.isEmpty()) {
                    cells.add(cell);
                }
            }
            return cells;
        }

        private DeclaredField exactDeclaredField(String field) {
            String signature = field == null ? "" : field.trim();
            DeclaredField declaration = FieldPathSpec.declaredField(
                    signature);
            return declaration == null
                    || !declaration.signature().equals(signature)
                    ? null : declaration;
        }

        private String fieldKey(String owner, String name) {
            return string(owner).trim() + "\n" + string(name).trim();
        }

        private Boolean requiredOutcome(Map<String, Object> edge) {
            Object explicit = edge.get("requiredOutcome");
            if (explicit instanceof Boolean) {
                return (Boolean) explicit;
            }
            Boolean nested = commonNestedRequiredOutcome(edge);
            if (nested != null) {
                return nested;
            }
            if (hasNestedControlRows(edge)) {
                // Multiple controlled definitions/effects may require
                // opposite outcomes.  The evidence string describes only
                // the first emitted row and must not be promoted to a common
                // Boolean contract for the whole branch site.
                return null;
            }
            Matcher matcher = REQUIRED_OUTCOME_PATTERN.matcher(string(
                    edge.get("evidence")));
            return matcher.find()
                    ? Boolean.valueOf(matcher.group(1)) : null;
        }

        private Boolean commonNestedRequiredOutcome(
                Map<String, Object> edge) {
            Boolean common = null;
            boolean found = false;
            for (String field : Arrays.asList("controlledDefinitions",
                    "guardedMutations", "guardedEffects")) {
                for (Map<String, Object> row : maps(edge.get(field))) {
                    Object outcome = row.get("requiredOutcome");
                    if (!(outcome instanceof Boolean)) {
                        return null;
                    }
                    if (!found) {
                        common = (Boolean) outcome;
                        found = true;
                    } else if (!common.equals(outcome)) {
                        return null;
                    }
                }
            }
            return found ? common : null;
        }

        private boolean hasNestedControlRows(Map<String, Object> edge) {
            for (String field : Arrays.asList("controlledDefinitions",
                    "guardedMutations", "guardedEffects")) {
                Object rows = edge.get(field);
                if (rows instanceof Collection
                        && !((Collection<?>) rows).isEmpty()) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Orders duplicate GUARD edges for one concrete branch site by the
         * strength of their output-causality evidence.  The causal slice and
         * exact control-dependence variants must dominate the generic
         * operand-consumption edge; otherwise file/edge ordering can change
         * whether a real output branch is explored.
         */
        private int branchPolicyEvidenceRank(Map<String, Object> edge,
                                             RegionDraft draft) {
            int rank = draft.causalEdges.contains(edge) ? 16 : 0;
            String kind = string(edge.get("kind"));
            if (ControlDependenceEdgeSupport.requiresSiteIdentity(kind)) {
                rank += 32;
            }
            if (requiredOutcome(edge) != null) {
                rank += 8;
            }
            if (Boolean.TRUE.equals(edge.get("sameCellRedefinition"))) {
                rank += 4;
            }
            if (!string(edge.get("controlledDefinitionSiteId")).isEmpty()) {
                rank += 2;
            }
            return rank;
        }

        private List<Map<String, Object>> authoritativeBranchPolicyEdges(
                List<Map<String, Object>> siteEdges) {
            List<Map<String, Object>> exact = new ArrayList<>();
            for (Map<String, Object> edge : siteEdges) {
                if (ControlDependenceEdgeSupport.requiresSiteIdentity(
                        string(edge.get("kind")))) {
                    exact.add(edge);
                }
            }
            return exact.isEmpty() ? siteEdges : exact;
        }

        private Map<String, Object> branchPolicy(
                List<Map<String, Object>> policyEdges, RegionDraft draft) {
            Map<String, Object> edge = strongestBranchPolicyEdge(
                    policyEdges, draft);
            String site = string(edge.get("siteId"));
            String guard = firstNonEmpty(string(edge.get("unit")),
                    string(edge.get("toCell")), site);
            Map<String, Object> result = object(
                    "siteId", site,
                    "policy", "EXPLORE",
                    "guard", guard,
                    "requiredOutcome", commonRequiredOutcome(policyEdges),
                    "requiredSuccessorIndices",
                    requiredSuccessorIndices(policyEdges),
                    "branchKind", string(edge.get("branchKind")),
                    "switchCaseKeys", integerValues(edge.get(
                            "switchCaseKeys")),
                    "defaultSuccessorIndex", integer(edge.get(
                            "defaultSuccessorIndex"), -1));
            return result;
        }

        /**
         * Requested-output demand slicing can admit synchronous helpers that
         * the compact exception region intentionally omitted.  Their exact
         * control-dependence edges are part of the executable slice, so every
         * such branch needs the same fail-closed policy contract as a branch
         * in the broad region.  A causal guard is always EXPLORE; it cannot be
         * resurrected as a PATH_ASSUMPTION by a coarser broad-region proof.
         */
        private void mergeRequestedOutputSliceBranchPolicies(
                RegionDraft draft, List<Map<String, Object>> outputSlices,
                List<Map<String, Object>> branchPolicies) {
            Set<String> selectedEdgeIds = new LinkedHashSet<>();
            for (Map<String, Object> outputSlice : outputSlices) {
                selectedEdgeIds.addAll(strings(outputSlice.get(
                        "causalEdgeIds")));
            }
            if (selectedEdgeIds.isEmpty()) {
                return;
            }
            Map<String, List<Map<String, Object>>> causalBySite =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge
                    : graph.withIds(selectedEdgeIds)) {
                if (!"GUARD".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                String site = string(edge.get("siteId"));
                if (!site.isEmpty()) {
                    causalBySite.computeIfAbsent(site,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
            Map<String, Integer> policyIndexBySite = new LinkedHashMap<>();
            for (int index = 0; index < branchPolicies.size(); index++) {
                policyIndexBySite.put(string(branchPolicies.get(index).get(
                        "siteId")), index);
            }
            for (Map.Entry<String, List<Map<String, Object>>> entry
                    : causalBySite.entrySet()) {
                List<Map<String, Object>> policyEdges =
                        authoritativeBranchPolicyEdges(entry.getValue());
                Map<String, Object> policy = branchPolicy(policyEdges, draft);
                Integer existingIndex = policyIndexBySite.get(entry.getKey());
                if (existingIndex == null) {
                    policyIndexBySite.put(entry.getKey(),
                            branchPolicies.size());
                    branchPolicies.add(policy);
                } else if (!"EXPLORE".equals(string(branchPolicies.get(
                        existingIndex).get("policy")))) {
                    branchPolicies.set(existingIndex, policy);
                }
            }
        }

        private Map<String, Object> strongestBranchPolicyEdge(
                List<Map<String, Object>> siteEdges, RegionDraft draft) {
            Map<String, Object> strongest = siteEdges.get(0);
            for (int index = 1; index < siteEdges.size(); index++) {
                Map<String, Object> candidate = siteEdges.get(index);
                if (branchPolicyEvidenceRank(candidate, draft)
                        > branchPolicyEvidenceRank(strongest, draft)) {
                    strongest = candidate;
                }
            }
            return strongest;
        }

        private Boolean commonRequiredOutcome(
                Collection<Map<String, Object>> siteEdges) {
            Boolean common = null;
            boolean found = false;
            for (Map<String, Object> edge : siteEdges) {
                Boolean candidate = requiredOutcome(edge);
                if (candidate == null) {
                    return null;
                }
                if (!found) {
                    common = candidate;
                    found = true;
                } else if (!common.equals(candidate)) {
                    return null;
                }
            }
            return found ? common : null;
        }

        private List<Integer> requiredSuccessorIndices(
                Collection<Map<String, Object>> edges) {
            Set<Integer> indices = new LinkedHashSet<>();
            for (Map<String, Object> edge : edges) {
                collectIntegerValues(indices, edge.get(
                        "reachingSuccessorIndices"));
                for (String field : Arrays.asList("controlledDefinitions",
                        "guardedMutations", "guardedEffects")) {
                    for (Map<String, Object> row : maps(edge.get(field))) {
                        collectIntegerValues(indices,
                                row.get("reachingSuccessorIndices"));
                    }
                }
            }
            List<Integer> result = new ArrayList<>(indices);
            Collections.sort(result);
            return result;
        }

        private void collectIntegerValues(Set<Integer> target,
                                          Object values) {
            if (!(values instanceof Collection)) {
                return;
            }
            for (Object value : (Collection<?>) values) {
                if (value instanceof Number) {
                    target.add(((Number) value).intValue());
                }
            }
        }

        private List<Integer> integerValues(Object values) {
            Set<Integer> result = new LinkedHashSet<>();
            collectIntegerValues(result, values);
            return new ArrayList<>(result);
        }

    }

    private static final class RegionDraft {
        private String regionId;
        private String rootMethod;
        private final String anchorMethod;
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<Map<String, Object>> causalEdges = new LinkedHashSet<>();
        private final Set<String> causalCells = new LinkedHashSet<>();
        private boolean exceptionDirected;
        private boolean methodBudgetTruncated;
        private boolean causalCellBudgetTruncated;
        private Set<String> internallyDerivedTargets;
        private Set<String> callResultsWithCausalAlternative;
        private StaticGraphIndex analysisGraph;

        private RegionDraft(String anchorMethod) {
            this.anchorMethod = anchorMethod;
        }

        private void clearAnalysisCache() {
            internallyDerivedTargets = null;
            callResultsWithCausalAlternative = null;
            analysisGraph = null;
        }
    }

    private static final class CausalSlice {
        private final Set<Map<String, Object>> edges = new LinkedHashSet<>();
        private final Set<String> cells = new LinkedHashSet<>();
        private boolean causalCellBudgetTruncated;
    }

    private static final class InputSelection {
        private final Set<String> externalInputs = new LinkedHashSet<>();
        private final Set<String> mandatorySeedGuardInputs =
                new LinkedHashSet<>();
        private final List<Map<String, Object>> unresolvedInputDetails =
                new ArrayList<>();
    }

    private static final class SeedGuardInputFrontier {
        private final Set<String> liveIns = new LinkedHashSet<>();
        private final Set<String> gapCells = new LinkedHashSet<>();

        private void addGap(String cell) {
            if (cell != null && !cell.isEmpty()) {
                gapCells.add(cell);
            }
        }
    }

    private static final class InputPortResolution {
        private final String portId;
        private final String authority;

        private InputPortResolution(String portId, String authority) {
            this.portId = portId;
            this.authority = authority;
        }

        private static InputPortResolution unresolved() {
            return new InputPortResolution("", "UNRESOLVED");
        }
    }

    /** Exact static sites that read one receiver-sensitive scalar field. */
    private static final class DeclaredFieldAccess {
        private final DeclaredField field;
        private final String method;
        private final int unitIndex;
        private final boolean accessorCall;
        private final String invokedMethod;
        private final String accessorImplementationMethod;
        private final String receiverCell;
        private final List<String> accessSites;

        private DeclaredFieldAccess(DeclaredField field,
                                    String method, int unitIndex,
                                    boolean accessorCall,
                                    String invokedMethod,
                                    String accessorImplementationMethod,
                                    String receiverCell,
                                    Collection<String> accessSites) {
            this.field = field;
            this.method = method;
            this.unitIndex = unitIndex;
            this.accessorCall = accessorCall;
            this.invokedMethod = invokedMethod;
            this.accessorImplementationMethod =
                    accessorImplementationMethod;
            this.receiverCell = receiverCell;
            this.accessSites = sorted(accessSites);
        }

        private DeclaredFieldAccess merge(DeclaredFieldAccess other) {
            if (other == null || accessorCall != other.accessorCall) {
                return null;
            }
            if (accessorCall) {
                return method.equals(other.method)
                        && unitIndex == other.unitIndex
                        && invokedMethod.equals(other.invokedMethod)
                        && accessorImplementationMethod.equals(
                        other.accessorImplementationMethod)
                        ? this : null;
            }
            if (receiverCell.isEmpty()
                    || !receiverCell.equals(other.receiverCell)) {
                return null;
            }
            Set<String> sites = new LinkedHashSet<>(accessSites);
            sites.addAll(other.accessSites);
            return new DeclaredFieldAccess(field, "", -1,
                    false, "", "", receiverCell, sites);
        }

    }

    /**
     * Exact direct-getfield proof for one projected scalar frontier.  The
     * hook belongs to {@code rootField}; {@code leafField} is the only field
     * that may become symbolic.
     */
    private static final class DeclaredFieldPathAccess {
        private final String cell;
        private final DeclaredField rootField;
        private final DeclaredField leafField;
        private final String method;
        private final int unitIndex;
        private final String accessOwnerCell;
        private final List<String> fieldPath;
        private final List<String> aliases;
        private final List<String> proofEdgeIds;

        private DeclaredFieldPathAccess(
                String cell, DeclaredField rootField,
                DeclaredField leafField, String method,
                int unitIndex, String accessOwnerCell,
                Collection<String> fieldPath, Collection<String> aliases,
                Collection<String> proofEdgeIds) {
            this.cell = cell;
            this.rootField = rootField;
            this.leafField = leafField;
            this.method = method;
            this.unitIndex = unitIndex;
            this.accessOwnerCell = accessOwnerCell;
            this.fieldPath = new ArrayList<>(fieldPath);
            this.aliases = new ArrayList<>(aliases);
            this.proofEdgeIds = sorted(proofEdgeIds);
        }

        private String siteId() {
            return method + "#u" + unitIndex;
        }

    }

    private static final class OutputCaptureSelection {
        private final List<Map<String, Object>> bindings;
        private final List<String> issues;

        private OutputCaptureSelection(List<Map<String, Object>> bindings,
                                       List<String> issues) {
            this.bindings = new ArrayList<>(bindings);
            this.issues = new ArrayList<>(issues);
        }

        private static OutputCaptureSelection notRequired() {
            return new OutputCaptureSelection(
                    Collections.<Map<String, Object>>emptyList(),
                    Collections.<String>emptyList());
        }
    }

    private static final class MethodDepth {
        private final String method;
        private final int depth;

        private MethodDepth(String method, int depth) {
            this.method = method;
            this.depth = depth;
        }
    }

    private static boolean isBoundary(Map<String, Object> edge) {
        String transfer = string(edge.get("transferKind"));
        String kind = lower(string(edge.get("kind")));
        return "PROTOCOL_TRANSFER".equals(transfer)
                || kind.contains("rpc")
                || kind.contains("async")
                || kind.contains("thread_handoff");
    }

    private static String boundaryKind(Map<String, Object> edge) {
        String kind = lower(string(edge.get("kind")));
        if (kind.contains("rpc") && kind.contains("return")) {
            return "RPC_RETURN";
        }
        if (kind.contains("rpc")) {
            return "RPC_ARGUMENT";
        }
        if (kind.contains("async") || kind.contains("thread")) {
            return "ASYNC_HANDOFF";
        }
        return "SERIALIZATION";
    }

    private static String invokedMethodFromCells(Map<String, Object> edge) {
        String kind = lower(string(edge.get("kind")));
        String from = methodForCell(string(edge.get("fromCell")));
        String to = methodForCell(string(edge.get("toCell")));
        if (kind.contains("argument") || kind.contains("receiver")) {
            return to;
        }
        if (kind.contains("return")) {
            return from;
        }
        return "";
    }

    private static boolean isEntryRoot(String method) {
        String name = methodName(method);
        return "handle".equals(name)
                || "run".equals(name)
                || "call".equals(name)
                || "dispatch".equals(name)
                || "receive".equals(name)
                || "process".equals(name)
                || name.startsWith("on") && name.length() > 2;
    }

    private static int entryPriority(String method) {
        return isEntryRoot(method) ? 0 : 1;
    }

    private static boolean isLargeLibraryMethod(String method) {
        String owner = owner(method);
        if (owner.startsWith("java.") || owner.startsWith("javax.")) {
            String name = methodName(method);
            return !("readFields".equals(name)
                    || "write".equals(name)
                    || "get".equals(name)
                    || "put".equals(name));
        }
        return owner.startsWith("org.slf4j.")
                || owner.startsWith("org.apache.commons.logging.");
    }

    private static boolean boundaryInput(String input, String rootMethod) {
        if (input == null || input.isEmpty()) {
            return false;
        }
        String lower = lower(input);
        return input.contains(".param")
                || input.contains("@this")
                || input.contains("#field:")
                || looksLikeField(input)
                || lower.contains("environment")
                || lower.contains("currenttimemillis")
                || lower.contains("nanotime")
                || lower.contains("rpc")
                || input.endsWith(".return")
                || methodForCell(input).equals(rootMethod);
    }

    private static String sourceKind(String cell, String rootMethod) {
        String lower = lower(cell);
        // Structural sources take precedence over names.  In particular an
        // RPC interface return is still a call result with a concrete
        // definition site; class names containing "rpc" must not turn it into
        // an uninstrumentable generic live-in.
        if (isEnvironmentCell(cell)) {
            return "ENVIRONMENT";
        }
        if (cell.endsWith(".return")) {
            return "OPAQUE_CALL";
        }
        // A field remains shared heap even when its declaring class happens
        // to contain a transport-flavoured word such as "RpcBus".  Runtime
        // can materialize an exact getfield and validate READ_FROM for this
        // source; class-name classification would instead turn it into an
        // unmaterializable generic protocol live-in.
        if (cell.contains("#field:") || looksLikeField(cell)) {
            return cell.contains("@this")
                    ? "RECEIVER_FIELD" : "SHARED_HEAP";
        }
        if (lower.contains("rpc")) {
            return "RPC_INPUT";
        }
        if (cell.contains(".param") && methodForCell(cell).equals(rootMethod)) {
            return "ROOT_ARGUMENT";
        }
        return "REGION_LIVE_IN";
    }

    /**
     * Recognizes an actual nondeterministic/environment source, not a domain
     * identifier that merely contains words such as "time" (for example a
     * regular object field named tokenLifetime).
     */
    private static boolean isEnvironmentCell(String cell) {
        String value = lower(cell);
        if (value.contains("environment.")
                || value.contains("environment:")
                || value.contains("currenttimemillis")
                || value.contains("nanotime")) {
            return true;
        }
        boolean callResult = value.endsWith(".return")
                || value.contains(">.return");
        return callResult && (value.contains("<java.util.random:")
                || value.contains("<java.security.securerandom:"));
    }

    private static boolean bugPredicateOutput(String output) {
        if (output == null || output.isEmpty()) {
            return false;
        }
        String normalized = lower(output);
        return normalized.contains("exception")
                || normalized.contains("invalid")
                || normalized.contains(" == null")
                || normalized.contains("#failure:")
                || normalized.contains("#bug:");
    }

    private static String outputKind(String output, String anchorMethod) {
        String lower = lower(output);
        if (lower.contains("exception") || lower.contains("invalid")
                || lower.contains("failure") || lower.contains(" == null")) {
            return "FAILURE_PREDICATE";
        }
        if (output.contains("#field:") || looksLikeField(output)) {
            return "HEAP_STATE";
        }
        if (output.endsWith(".return")) {
            return "RETURN";
        }
        return methodForCell(output).equals(anchorMethod)
                ? "SINK_STATE" : "REGION_OUTPUT";
    }

    private static String projection(String cell) {
        int field = cell.indexOf("#field:");
        if (field >= 0) {
            return cell.substring(field + 1);
        }
        if (cell.endsWith(".return")) {
            return "return";
        }
        Matcher param = PARAMETER_INDEX_PATTERN.matcher(cell);
        if (param.find()) {
            return "argument[" + param.group(1) + "]";
        }
        return "value";
    }

    private static String methodForCell(String cell) {
        if (cell == null || cell.isEmpty()) {
            return "";
        }
        for (int start = cell.indexOf('<'); start >= 0;
             start = cell.indexOf('<', start + 1)) {
            int colon = cell.indexOf(':', start + 1);
            int open = colon < 0 ? -1 : cell.indexOf('(', colon + 1);
            int close = open < 0 ? -1 : cell.indexOf(')', open + 1);
            if (colon < 0 || open < 0 || close < 0) {
                continue;
            }
            int end = close + 1;
            if (end < cell.length() && cell.charAt(end) == '>') {
                return cell.substring(start, end + 1);
            }
        }
        return "";
    }

    private static String methodName(String signature) {
        if (signature == null) {
            return "";
        }
        int open = signature.indexOf('(');
        if (open < 0) {
            return "";
        }
        int space = signature.lastIndexOf(' ', open);
        return space < 0 ? "" : signature.substring(space + 1, open);
    }

    private static String owner(String signature) {
        if (signature == null || !signature.startsWith("<")) {
            return "";
        }
        int colon = signature.indexOf(':');
        return colon < 0 ? "" : signature.substring(1, colon).trim();
    }

    private static boolean looksLikeField(String value) {
        return value != null && value.matches("<[^:]+:\\s+.+\\s+[^\\s()]+>");
    }

    private static boolean globalFieldCell(String value) {
        return looksLikeField(value) && methodForCell(value).isEmpty();
    }

    private static String joinSorted(Collection<String> values) {
        StringBuilder builder = new StringBuilder();
        for (String value : sorted(values)) {
            if (builder.length() > 0) {
                builder.append('\n');
            }
            builder.append(value);
        }
        return builder.toString();
    }

    private static List<String> sorted(Collection<String> values) {
        List<String> result = new ArrayList<>();
        if (values != null) {
            result.addAll(values);
        }
        Collections.sort(result);
        return result;
    }

    private static Set<String> values(Set<String> values) {
        return values == null ? Collections.emptySet() : values;
    }

    private static Collection<String> strings(Object value) {
        if (!(value instanceof Collection)) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        for (Object item : (Collection<?>) value) {
            String string = string(item);
            if (!string.isEmpty()) {
                result.add(string);
            }
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Collection<Map<String, Object>> maps(Object value) {
        if (!(value instanceof Collection)) {
            return Collections.emptyList();
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (Object item : (Collection<?>) value) {
            if (item instanceof Map) {
                result.add((Map<String, Object>) item);
            }
        }
        return result;
    }

    private static Map<String, Object> unique(
            Collection<Map<String, Object>> candidates,
            Predicate<Map<String, Object>> matches) {
        Map<String, Object> selected = null;
        for (Map<String, Object> candidate : candidates) {
            if (!matches.test(candidate)) continue;
            if (selected != null) return null;
            selected = candidate;
        }
        return selected;
    }

    static boolean completeOutputSlice(Map<?, ?> slice) {
        if (slice == null
                || !strings(slice.get("truncationReasons")).isEmpty()
                || strings(slice.get("causalEdgeIds")).isEmpty()
                || !(slice.get("inputGaps") instanceof Collection<?>)
                || !((Collection<?>) slice.get("inputGaps")).isEmpty()
                || !(slice.get("captureBindingIssues")
                instanceof Collection<?>)
                || !((Collection<?>) slice.get(
                "captureBindingIssues")).isEmpty()) {
            return false;
        }
        return true;
    }

    private static void add(Map<String, Set<String>> map, String key, String value) {
        map.computeIfAbsent(key, ignored -> new LinkedHashSet<>()).add(value);
    }

    private static String string(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static int integer(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(String.valueOf(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonEmpty(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }

    private static String lower(String value) {
        return value == null ? "" : value.toLowerCase(Locale.ROOT);
    }

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> map = new LinkedHashMap<>();
        for (int index = 0; index + 1 < values.length; index += 2) {
            map.put(String.valueOf(values[index]), values[index + 1]);
        }
        return map;
    }
}
