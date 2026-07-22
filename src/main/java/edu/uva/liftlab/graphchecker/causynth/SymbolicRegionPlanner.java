package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
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
    private static final Pattern DECLARED_FIELD_PATTERN = Pattern.compile(
            "^<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>$");
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
    private static final Pattern CAST_LOCAL_PATTERN = Pattern.compile(
            "^\\([^)]*\\)\\s*([$]?[A-Za-z_][A-Za-z0-9_]*)$");
    private static final Pattern GLOBAL_FIELD_LEAF_PATTERN = Pattern.compile(
            "^<[^:]+:\\s+[^()<>]+\\s+([^\\s()>]+)>$");
    private static final Pattern EMBEDDED_FIELD_PATTERN = Pattern.compile(
            ".*\\.<([^:]+):\\s+[^()<>]+\\s+([^\\s()>]+)>.*");
    private static final Pattern SEMANTIC_GLOBAL_FIELD_PATTERN =
            Pattern.compile("^<([^:]+):\\s+[^()<>]+\\s+([^\\s()>]+)>"
                    + "(.*)$");
    private static final Pattern FORMAL_PARAMETER_PATTERN = Pattern.compile(
            "^<.+>\\.param\\d+:([^#]+)$");
    private static final Pattern FIELD_SIGNATURE_PATTERN = Pattern.compile(
            "<([^:]+):\\s+.+\\s+([^\\s()>]+)>");
    private static final Pattern METHOD_OWNER_PATTERN = Pattern.compile(
            "<([^:]+):");
    private static final Pattern REQUIRED_OUTCOME_PATTERN = Pattern.compile(
            "requires Jimple outcome (true|false)");
    private static final Pattern SCALAR_FIELD_PATTERN = Pattern.compile(
            "^<[^:]+:\\s+([^()<>]+)\\s+[^\\s()>]+>$");
    private static final Pattern PARAMETER_INDEX_PATTERN = Pattern.compile(
            "\\.param(\\d+):");

    private SymbolicRegionPlanner() {
    }

    static Result plan(List<Map<String, Object>> edges,
                       List<Map<String, Object>> methodPlans) {
        Planner planner = new Planner(edges, methodPlans);
        return planner.plan();
    }

    static final class Result {
        final List<Map<String, Object>> regions = new ArrayList<>();
        final List<Map<String, Object>> regionEdges = new ArrayList<>();
        final List<Map<String, Object>> modelSummaries = new ArrayList<>();
        final Map<String, Object> coverage = new LinkedHashMap<>();
        final Map<String, Object> summary = new LinkedHashMap<>();
    }

    private static final class FieldSignature {
        private final String owner;
        private final String name;

        private FieldSignature(String owner, String name) {
            this.owner = owner;
            this.name = name;
        }
    }

    private static final class DeclaredFieldIdentity {
        private final String signature;
        private final String owner;
        private final String type;
        private final String name;

        private DeclaredFieldIdentity(String signature, String owner,
                                      String type, String name) {
            this.signature = signature;
            this.owner = owner;
            this.type = type;
            this.name = name;
        }
    }

    /** Exact call-result definition site used to join parallel dependencies. */
    private static final class CallResultSiteKey {
        private final String target;
        private final String method;
        private final int unit;

        private CallResultSiteKey(String target, String method, int unit) {
            this.target = target;
            this.method = method;
            this.unit = unit;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (!(other instanceof CallResultSiteKey)) {
                return false;
            }
            CallResultSiteKey that = (CallResultSiteKey) other;
            return unit == that.unit
                    && target.equals(that.target)
                    && method.equals(that.method);
        }

        @Override
        public int hashCode() {
            int result = target.hashCode();
            result = 31 * result + method.hashCode();
            result = 31 * result + unit;
            return result;
        }
    }

    /** One statically unique container/element/accessor/declared-field join. */
    private static final class ContainerElementFieldCandidate {
        private final Map<String, Object> containerAccessor;
        private final Map<String, Object> arrayLoad;
        private final Map<String, Object> projectedAccessor;
        private final Map<String, Object> declaredAccessor;
        private final Map<String, Object> mapPutValue;
        private final DeclaredFieldIdentity containerField;
        private final DeclaredFieldIdentity elementField;
        private final String baseInputCell;
        private final List<String> fieldPath;
        private final List<String> proofEdgeIds;
        private final String proofAuthority;
        private final int elementIndex;
        private final boolean constantIndex;
        private final boolean materializeFromContainerSnapshot;

        private ContainerElementFieldCandidate(
                Map<String, Object> containerAccessor,
                Map<String, Object> arrayLoad,
                Map<String, Object> projectedAccessor,
                Map<String, Object> declaredAccessor,
                DeclaredFieldIdentity containerField,
                DeclaredFieldIdentity elementField,
                int elementIndex, boolean constantIndex) {
            this(containerAccessor, arrayLoad, projectedAccessor,
                    declaredAccessor, null, containerField, elementField,
                    elementField.signature,
                    Collections.singletonList(elementField.name),
                    elementIndex, constantIndex, false,
                    Collections.<String>emptyList(), "");
        }

        private ContainerElementFieldCandidate(
                Map<String, Object> containerAccessor,
                Map<String, Object> arrayLoad,
                Map<String, Object> projectedAccessor,
                Map<String, Object> declaredAccessor,
                Map<String, Object> mapPutValue,
                DeclaredFieldIdentity containerField,
                DeclaredFieldIdentity elementField,
                String baseInputCell,
                List<String> fieldPath,
                int elementIndex, boolean constantIndex,
                boolean materializeFromContainerSnapshot,
                Collection<String> proofEdgeIds,
                String proofAuthority) {
            this.containerAccessor = containerAccessor;
            this.arrayLoad = arrayLoad;
            this.projectedAccessor = projectedAccessor;
            this.declaredAccessor = declaredAccessor;
            this.mapPutValue = mapPutValue;
            this.containerField = containerField;
            this.elementField = elementField;
            this.baseInputCell = baseInputCell;
            this.fieldPath = new ArrayList<>(fieldPath);
            this.proofEdgeIds = new ArrayList<>(proofEdgeIds);
            this.proofAuthority = proofAuthority == null ? ""
                    : proofAuthority;
            this.elementIndex = elementIndex;
            this.constantIndex = constantIndex;
            this.materializeFromContainerSnapshot =
                    materializeFromContainerSnapshot;
        }
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

    private static final class RequestedStateTransformerContract {
        private final String outputPort;
        private final String outputCell;
        private final List<Map<String, Object>> obligations;
        private final List<String> issues;
        private final boolean complete;
        private final boolean applicable;

        private RequestedStateTransformerContract(
                String outputPort, String outputCell,
                List<Map<String, Object>> obligations,
                List<String> issues, boolean complete,
                boolean applicable) {
            this.outputPort = outputPort;
            this.outputCell = outputCell;
            this.obligations = obligations;
            this.issues = issues;
            this.complete = complete;
            this.applicable = applicable;
        }

        private static RequestedStateTransformerContract notApplicable() {
            return new RequestedStateTransformerContract("", "",
                    Collections.<Map<String, Object>>emptyList(),
                    Collections.<String>emptyList(), true, false);
        }

        private Map<String, Object> toMap() {
            return object(
                    "requestedStateTransformerContractVersion", 1,
                    "requestedStateTransformerContractApplicable",
                    applicable,
                    "requestedStateTransformerContractOutputPort",
                    outputPort,
                    "requestedStateTransformerContractOutputCell",
                    outputCell,
                    "requestedStateTransformerObligations", obligations,
                    "requestedStateTransformerObligationCount",
                    obligations.size(),
                    "requestedStateTransformerContractIssues", issues,
                    "requestedStateTransformerContractComplete", complete,
                    "requestedStateTransformerContractAuthority",
                    "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1");
        }
    }

    private static final class InputTransformerSinks {
        private final List<String> transformerSites;
        private final List<String> guardSites;
        private final List<String> unclassifiedEdgeIds;
        private final boolean complete;
        private final boolean exclusive;

        private InputTransformerSinks(Set<String> transformerSites,
                                      Set<String> guardSites,
                                      Set<String> unclassifiedEdgeIds,
                                      boolean complete,
                                      boolean exclusive) {
            this.transformerSites = new ArrayList<>(transformerSites);
            this.guardSites = new ArrayList<>(guardSites);
            this.unclassifiedEdgeIds = new ArrayList<>(
                    unclassifiedEdgeIds);
            Collections.sort(this.transformerSites);
            Collections.sort(this.guardSites);
            Collections.sort(this.unclassifiedEdgeIds);
            this.complete = complete;
            this.exclusive = exclusive;
        }
    }

    private static final class Planner {
        private final List<Map<String, Object>> edges;
        /**
         * Input-order-preserving indexes for the two demand-driven hot paths.
         * The planner's edge rows are immutable for the lifetime of a plan,
         * so indexing once is semantically equivalent to repeatedly filtering
         * {@link #edges} while avoiding a full graph scan per worklist cell or
         * per call-path level.
         */
        private final Map<String, List<Map<String, Object>>> edgesByMethod =
                new LinkedHashMap<>();
        private final Map<String, List<Map<String, Object>>>
                edgesByMethodSet = new LinkedHashMap<>();
        private final Map<String, List<Map<String, Object>>>
                incomingEdgesByCell = new LinkedHashMap<>();
        private final Map<String, Map<String, Object>> plansByMethod = new LinkedHashMap<>();
        /**
         * Region-local targets that have an in-region definition.  Input
         * selection asks this question for hundreds of candidates; scanning
         * the complete causal edge set for every candidate made large region
         * planning quadratic in practice.
         *
         * A broad exception region and each requested-output demand slice
         * deliberately share the same stable regionId.  They do not share
         * the same method/edge closure: the demand walk can admit synchronous
         * callees that were irrelevant to the original exception seed.
         * Therefore regionId is not a sound cache key for either definition
         * query below.  Key by the concrete immutable-for-selection draft
         * instead.  Otherwise a result computed for the broad region can make
         * a helper return in the expanded output slice look like a new live-in
         * (and, conversely, can hide a real output-slice frontier).
         *
         * Identity semantics are intentional.  RegionDraft is a mutable
         * work record and has no value equality; each draft's dependency
         * closure is fully built before input selection invokes these
         * caches.  The two exact accessor re-admission paths below explicitly
         * invalidate this draft if they add a method after selection.
         */
        private final Map<RegionDraft, Set<String>>
                internallyDerivedTargetsByRegion = new IdentityHashMap<>();
        private final Map<RegionDraft, Set<String>>
                callResultsWithCausalAlternativeByRegion =
                new IdentityHashMap<>();
        private final Map<String, Set<String>> calleesByCaller = new LinkedHashMap<>();
        private final Map<String, Set<String>> parentsByCallee = new LinkedHashMap<>();
        private final Map<String, Set<String>> callSitesByMethod = new LinkedHashMap<>();
        private final Map<String, Map<String, Set<String>>>
                dynamicDispatchTargetsByCallerSite = new LinkedHashMap<>();
        private final Set<String> overlappingWriterAnchors =
                new LinkedHashSet<>();
        private final Set<String> boundaryCallPairs = new LinkedHashSet<>();
        private final Set<String> anchorMethods = new LinkedHashSet<>();
        private Planner(List<Map<String, Object>> edges,
                        List<Map<String, Object>> methodPlans) {
            this.edges = edges == null ? Collections.emptyList() : edges;
            if (methodPlans != null) {
                for (Map<String, Object> row : methodPlans) {
                    String method = string(row.get("method"));
                    if (!method.isEmpty()) {
                        plansByMethod.put(method, row);
                    }
                }
            }
            index();
        }

        private Result plan() {
            Result result = new Result();
            List<String> anchors = new ArrayList<>(anchorMethods);
            Collections.sort(anchors);
            if (anchors.isEmpty()) {
                for (Map.Entry<String, Map<String, Object>> entry : plansByMethod.entrySet()) {
                    if ("SYMBOLIC_EXECUTION".equals(string(
                            entry.getValue().get("classification")))) {
                        anchors.add(entry.getKey());
                    }
                }
            }
            if (anchors.size() > MAX_ANCHORS) {
                anchors = new ArrayList<>(anchors.subList(0, MAX_ANCHORS));
            }

            Set<String> emittedMethodSets = new LinkedHashSet<>();
            Set<String> queuedAnchorStates = new LinkedHashSet<>();
            for (String anchor : anchors) {
                queuedAnchorStates.add(anchor + "\nNORMAL");
            }
            Set<String> expandedAnchors = new LinkedHashSet<>();
            Deque<String> anchorQueue = new ArrayDeque<>(anchors);
            int regionIndex = 0;
            while (!anchorQueue.isEmpty() && regionIndex < MAX_REGIONS) {
                String anchor = anchorQueue.removeFirst();
                expandedAnchors.add(anchor);
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
            for (Map.Entry<String, Map<String, Object>> entry
                    : plansByMethod.entrySet()) {
                String method = entry.getKey();
                if (coveredBeforeModels.contains(method)) {
                    continue;
                }
                Map<String, Object> plan = entry.getValue();
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
            buildCoverageAudit(result);

            Map<String, Integer> rootCounts = new LinkedHashMap<>();
            for (Map<String, Object> region : result.regions) {
                increment(rootCounts, string(region.get("rootMethod")));
            }
            result.summary.put("regionCount", result.regions.size());
            result.summary.put("regionEdgeCount", result.regionEdges.size());
            result.summary.put("seedAnchorCount", anchors.size());
            result.summary.put("expandedAnchorCount", expandedAnchors.size());
            result.summary.put("rootMethods", rootCounts);
            result.summary.put("rootSelection", "RUNTIME_CALL_TREE");
            result.summary.put("maxRegionMethods", MAX_REGION_METHODS);
            result.summary.put("maxRegions", MAX_REGIONS);
            result.summary.put("modelCount", result.modelSummaries.size());
            result.summary.put("coverageComplete", result.coverage.get("complete"));
            result.summary.put("precision", "STATIC_OVER_APPROXIMATION");
            return result;
        }

        private String regionDedupKey(RegionDraft draft) {
            return draft.rootMethod + "\n"
                    + (overlappingWriterAnchors.contains(
                    draft.anchorMethod) ? draft.anchorMethod : "") + "\n"
                    + joinSorted(draft.methods);
        }

        private void buildCoverageAudit(Result result) {
            Map<String, Set<String>> regionsByMethod = new LinkedHashMap<>();
            Map<String, Set<String>> methodsByRegion = new LinkedHashMap<>();
            Map<String, Map<String, Object>> regionById = new LinkedHashMap<>();
            for (Map<String, Object> region : result.regions) {
                String regionId = string(region.get("regionId"));
                regionById.put(regionId, region);
                Set<String> methods = new LinkedHashSet<>(strings(region.get("methods")));
                methodsByRegion.put(regionId, methods);
                for (String method : methods) {
                    regionsByMethod.computeIfAbsent(method,
                            ignored -> new LinkedHashSet<>()).add(regionId);
                }
            }
            Set<String> modeledMethods = new LinkedHashSet<>();
            for (Map<String, Object> model : result.modelSummaries) {
                modeledMethods.add(string(model.get("method")));
            }
            List<String> uncoveredMethods = new ArrayList<>();
            for (String method : plansByMethod.keySet()) {
                if (!regionsByMethod.containsKey(method)
                        && !modeledMethods.contains(method)) {
                    uncoveredMethods.add(method);
                }
            }

            Set<String> boundarySites = new LinkedHashSet<>();
            for (Map<String, Object> regionEdge : result.regionEdges) {
                String site = string(regionEdge.get("siteId"));
                if (!site.isEmpty()) {
                    boundarySites.add(site);
                }
            }
            int internalEdges = 0;
            int interRegionEdges = 0;
            int modelEdges = 0;
            int alternativePathEdges = 0;
            List<String> uncoveredEdges = new ArrayList<>();
            for (Map<String, Object> edge : edges) {
                String method = string(edge.get("method"));
                String site = string(edge.get("siteId"));
                if (isBoundary(edge)) {
                    if (boundarySites.contains(site)) {
                        interRegionEdges++;
                    } else {
                        uncoveredEdges.add(string(edge.get("id")) + ":" + site);
                    }
                    continue;
                }
                if (modeledMethods.contains(method)) {
                    modelEdges++;
                    continue;
                }
                String callee = string(edge.get("invoke"));
                if (callee.isEmpty() || !plansByMethod.containsKey(callee)) {
                    callee = invokedMethodFromCells(edge);
                }
                if (!callee.isEmpty() && plansByMethod.containsKey(callee)) {
                    if (modeledMethods.contains(callee)) {
                        modelEdges++;
                    } else if (shareRegion(method, callee, regionsByMethod,
                            methodsByRegion)) {
                        internalEdges++;
                    } else if (alternativeNonCausalEdge(edge,
                            regionsByMethod, regionById)) {
                        alternativePathEdges++;
                    } else {
                        uncoveredEdges.add(string(edge.get("id")) + ":"
                                + method + "->" + callee);
                    }
                } else if (regionsByMethod.containsKey(method)) {
                    internalEdges++;
                } else if (modeledMethods.contains(method)) {
                    modelEdges++;
                } else {
                    uncoveredEdges.add(string(edge.get("id")) + ":" + method);
                }
            }
            Collections.sort(uncoveredMethods);
            int sampleLimit = Math.min(32, uncoveredEdges.size());
            boolean complete = uncoveredMethods.isEmpty() && uncoveredEdges.isEmpty();
            result.coverage.put("methodPlanCount", plansByMethod.size());
            result.coverage.put("regionCoveredMethodCount", regionsByMethod.size());
            result.coverage.put("modeledMethodCount", modeledMethods.size());
            result.coverage.put("uncoveredMethodCount", uncoveredMethods.size());
            result.coverage.put("uncoveredMethods", uncoveredMethods);
            result.coverage.put("staticEdgeCount", edges.size());
            result.coverage.put("internalEdgeCount", internalEdges);
            result.coverage.put("interRegionEdgeCount", interRegionEdges);
            result.coverage.put("modelEdgeCount", modelEdges);
            result.coverage.put("alternativePathEdgeCount",
                    alternativePathEdges);
            result.coverage.put("uncoveredEdgeCount", uncoveredEdges.size());
            result.coverage.put("uncoveredEdgeSamples",
                    new ArrayList<>(uncoveredEdges.subList(0, sampleLimit)));
            result.coverage.put("complete", complete);
        }

        private boolean alternativeNonCausalEdge(
                Map<String, Object> edge,
                Map<String, Set<String>> regionsByMethod,
                Map<String, Map<String, Object>> regionById) {
            String edgeId = string(edge.get("id"));
            if (edgeId.isEmpty()) {
                return false;
            }
            for (String regionId : values(regionsByMethod.get(
                    string(edge.get("method"))))) {
                Map<String, Object> region = regionById.get(regionId);
                if (region != null
                        && "EXCEPTION_BACKWARD_CAUSAL_CLOSURE".equals(
                        string(region.get("selection")))
                        && !strings(region.get("causalEdgeIds")).contains(edgeId)) {
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
            for (Map<String, Object> edge : edges) {
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
                        && plansByMethod.containsKey(fromMethod)) {
                    anchors.add(fromMethod);
                }
            }
            Map<String, List<Map<String, Object>>>
                    demandedSharedConsumers = new LinkedHashMap<>();
            for (Map<String, Object> region : regions) {
                Set<String> mandatory = new LinkedHashSet<>(strings(
                        region.get("mandatorySeedGuardInputs")));
                Object symbolicInputs = region.get("symbolicInputs");
                if (!(symbolicInputs instanceof Collection<?>)) {
                    continue;
                }
                Map<String, Map<String, Object>> inputsByPort =
                        new LinkedHashMap<>();
                for (Object value : (Collection<?>) symbolicInputs) {
                    if (!(value instanceof Map<?, ?>)) {
                        continue;
                    }
                    @SuppressWarnings("unchecked")
                    Map<String, Object> input =
                            (Map<String, Object>) value;
                    String cell = string(input.get("cell"));
                    String port = string(input.get("portId"));
                    if (!port.isEmpty()) {
                        inputsByPort.put(port, input);
                    }
                    if (mandatory.contains(cell)) {
                        addDemandedSharedConsumer(demandedSharedConsumers,
                                region, input);
                    }
                }
                Object slices = region.get("outputSlices");
                if (!(slices instanceof Collection<?>)) {
                    continue;
                }
                for (Object value : (Collection<?>) slices) {
                    if (!(value instanceof Map<?, ?>)) {
                        continue;
                    }
                    @SuppressWarnings("unchecked")
                    Map<String, Object> slice =
                            (Map<String, Object>) value;
                    if (!Boolean.TRUE.equals(slice.get("complete"))) {
                        continue;
                    }
                    for (String port : strings(slice.get("inputPorts"))) {
                        addDemandedSharedConsumer(demandedSharedConsumers,
                                region, inputsByPort.get(port));
                    }
                }
            }
            if (!consumedFields.isEmpty()) {
                for (Map<String, Object> edge : edges) {
                    String method = string(edge.get("method"));
                    if (!"HEAP_WRITE".equals(string(edge.get("transferKind")))
                            || !consumedFields.contains(string(edge.get("toCell")))
                            || method.isEmpty()
                            || !plansByMethod.containsKey(method)) {
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
            for (Map<String, Object> edge : edges) {
                String method = string(edge.get("method"));
                edgesByMethod.computeIfAbsent(method,
                        ignored -> new ArrayList<>()).add(edge);
                String targetCell = string(edge.get("toCell"));
                incomingEdgesByCell.computeIfAbsent(targetCell,
                        ignored -> new ArrayList<>()).add(edge);
                String transfer = string(edge.get("transferKind"));
                String kind = string(edge.get("kind"));
                if ("SEED".equals(transfer) || lower(kind).contains("seed")) {
                    if (plansByMethod.containsKey(method)) {
                        anchorMethods.add(method);
                    }
                }

                String callee = string(edge.get("invoke"));
                if (callee.isEmpty() || !plansByMethod.containsKey(callee)) {
                    callee = invokedMethodFromCells(edge);
                }
                if (method.isEmpty() || callee.isEmpty()
                        || method.equals(callee)
                        || !plansByMethod.containsKey(method)
                        || !plansByMethod.containsKey(callee)) {
                    continue;
                }
                String pair = pair(method, callee);
                if (isBoundary(edge)) {
                    boundaryCallPairs.add(pair);
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
                String site = string(edge.get("siteId"));
                if (!site.isEmpty()) {
                    add(callSitesByMethod, method, site);
                }
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
                draft.truncated = draft.methodBudgetTruncated
                        || draft.causalCellBudgetTruncated;
                drafts.add(draft);
            }
            if (drafts.isEmpty()) {
                RegionDraft fallback = new RegionDraft(anchor);
                fallback.rootMethod = anchor;
                fallback.methods.add(anchor);
                includeRelevantCallees(fallback);
                fallback.methodBudgetTruncated =
                        fallback.methods.size() >= MAX_REGION_METHODS;
                fallback.truncated = fallback.methodBudgetTruncated
                        || fallback.causalCellBudgetTruncated;
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
            for (Map<String, Object> edge : edges) {
                if (!anchor.equals(string(edge.get("method")))
                        || !"SEED".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                String kind = lower(string(edge.get("kind")));
                String target = string(edge.get("toCell"));
                if (kind.contains("exception") || target.contains("#exception:")) {
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
                for (Map<String, Object> edge : incomingEdgesByCell
                        .getOrDefault(target, Collections
                                .<Map<String, Object>>emptyList())) {
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
                List<Map<String, Object>> callerEdges = edgesByMethod
                        .getOrDefault(caller, Collections
                                .<Map<String, Object>>emptyList());
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
            if (callee.isEmpty() || !plansByMethod.containsKey(callee)) {
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
                if (plansByMethod.containsKey(method)
                        && reachableFrom(draft.rootMethod, method)) {
                    draft.methods.add(method);
                }
            }
        }

        private Set<String> callbackContextExcludedMethods() {
            Map<String, Set<String>> registrationsByExecutor =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
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
            for (Map<String, Object> edge : edges) {
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
            for (Map<String, Object> edge : edges) {
                if (!draft.methods.contains(string(edge.get("method")))) {
                    continue;
                }
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
            while (!queue.isEmpty() && seen.size() <= plansByMethod.size()) {
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
            while (!queue.isEmpty() && predecessor.size() <= plansByMethod.size()) {
                String current = queue.removeFirst();
                if (current.equals(target)) {
                    break;
                }
                for (String next : sorted(calleesByCaller.get(current))) {
                    if (!plansByMethod.containsKey(next)
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

            Set<String> sites = new LinkedHashSet<>();
            Set<String> states = new LinkedHashSet<>();
            Set<String> produced = new LinkedHashSet<>();
            Set<String> inputCandidates = new LinkedHashSet<>();
            Set<String> outputCandidates = new LinkedHashSet<>();
            Set<String> models = new LinkedHashSet<>();
            Set<String> pathAssumptions = new LinkedHashSet<>();
            Set<String> exploreBranches = new LinkedHashSet<>();
            List<Map<String, Object>> branchPolicies = new ArrayList<>();

            for (String method : draft.methods) {
                Map<String, Object> plan = plansByMethod.get(method);
                if (plan == null) {
                    continue;
                }
                Collection<String> inputs = strings(plan.get("symbolicInputs"));
                Collection<String> outputs = strings(plan.get("outputs"));
                inputCandidates.addAll(inputs);
                outputCandidates.addAll(outputs);
                produced.addAll(outputs);
                for (String input : inputs) {
                    if (!draft.exceptionDirected || causalCandidate(input, draft)) {
                        states.add(input);
                    }
                }
                for (String output : outputs) {
                    if (!draft.exceptionDirected || causalCandidate(output, draft)) {
                        states.add(output);
                    }
                }
                models.addAll(strings(plan.get("requiredModels")));
                if (!draft.exceptionDirected) {
                    sites.addAll(strings(plan.get("siteIds")));
                }
            }
            if (draft.exceptionDirected) {
                for (Map<String, Object> edge : draft.causalEdges) {
                    String site = string(edge.get("siteId"));
                    if (!site.isEmpty()) {
                        sites.add(site);
                    }
                }
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
            for (Map<String, Object> edge : edges) {
                String method = string(edge.get("method"));
                if (!draft.methods.contains(method)
                        || draft.exceptionDirected
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
                        policyEdges, draft, outputCandidates, false);
                String site = string(branchPolicy.get("siteId"));
                String policy = string(branchPolicy.get("policy"));
                if ("EXPLORE".equals(policy)) {
                    exploreBranches.add(site);
                } else {
                    pathAssumptions.add(site);
                }
                sites.add(site);
                branchPolicies.add(branchPolicy);
            }
            InputSelection inputSelection = selectExternalInputs(draft,
                    inputCandidates, produced);
            inputCandidates.clear();
            inputCandidates.addAll(inputSelection.externalInputs);

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
                        "sourceKind", sourceKind(input, draft.rootMethod),
                        "selectionReason", inputSelection.selectionReasons.get(input),
                        "projection", projection(input));
                if (inputSelection.mandatorySeedGuardInputs.contains(input)) {
                    port.put("mandatory", true);
                    port.put("selectionPriority",
                            "SEED_GUARD_DEPENDENCY");
                    port.put("selectionAuthority",
                            "SEED_GUARD_AUTHORITATIVE_LIVE_IN_"
                                    + "FRONTIER_V2");
                }
                addRegionInputAccessorMaterializationMetadata(port, input,
                        draft);
                inputPorts.add(port);
            }
            int selectedExternalInputCount = inputCandidates.size();
            int broadInputPortCount = inputPorts.size();
            boolean broadInputPortTruncated =
                    selectedExternalInputCount > broadInputPortCount;

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
                        "kind", outputKind(output, draft.anchorMethod));
                if (prioritySeedOutputs.contains(output)) {
                    port.put("mandatory", true);
                    port.put("selectionPriority", "SEED_OUTPUT");
                    port.put("selectionAuthority",
                            "DIRECT_STATIC_SEED_INTERFACE_V1");
                }
                outputPorts.add(port);
            }
            List<Map<String, Object>> outputSlices = outputSlices(draft,
                    inputPorts, outputPorts);
            mergeRequestedOutputSliceBranchPolicies(draft, outputSlices,
                    outputCandidates, branchPolicies, pathAssumptions,
                    exploreBranches, sites);
            int outputSlicePromotedInputCount = inputPorts.size()
                    - broadInputPortCount;

            if (!draft.exceptionDirected) {
                for (String method : draft.methods) {
                    sites.addAll(values(callSitesByMethod.get(method)));
                }
            }
            return object(
                    "regionId", draft.regionId,
                    "rootMethod", draft.rootMethod,
                    "staticRootCandidate", draft.rootMethod,
                    "rootAuthority", "STATIC_CANDIDATE_ONLY",
                    "rootReason", "static same-thread candidate; runtime call tree selects the final root",
                    "rootValidation", "RUNTIME_REQUIRED",
                    "anchorMethod", draft.anchorMethod,
                    "sinkMethods", Collections.singletonList(draft.anchorMethod),
                    "methods", methods,
                    "callSites", limitedSorted(sites, MAX_PORTS),
                    "relevantStates", limitedSorted(states, MAX_PORTS),
                    "symbolicInputs", inputPorts,
                    "symbolicInputPolicy", "BACKWARD_DEPENDENCY_FRONTIER",
                    "rawSymbolicInputCount", inputSelection.rawInputCount,
                    "selectedExternalInputCount",
                    selectedExternalInputCount,
                    "mandatorySeedGuardInputCount",
                    inputSelection.mandatorySeedGuardInputs.size(),
                    "mandatorySeedGuardInputs", sorted(
                            inputSelection.mandatorySeedGuardInputs),
                    "mandatorySeedGuardInputAuthority",
                    "SEED_GUARD_AUTHORITATIVE_LIVE_IN_FRONTIER_V2",
                    "seedGuardInputDerivationComplete",
                    inputSelection.seedGuardInputDerivationGaps.isEmpty(),
                    "seedGuardInputDerivationGapCount",
                    inputSelection.seedGuardInputDerivationGaps.size(),
                    "seedGuardInputDerivationGaps",
                    inputSelection.seedGuardInputDerivationGaps,
                    "broadInputPortLimit", MAX_PORTS,
                    "broadInputPortCount", broadInputPortCount,
                    "broadInputPortTruncated", broadInputPortTruncated,
                    "outputSliceInputPortLimit",
                    MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS,
                    "outputSlicePromotedInputCount",
                    outputSlicePromotedInputCount,
                    "symbolicInputPortCount", inputPorts.size(),
                    "inputPortSelectionAuthority",
                    "BOUNDED_BROAD_FRONTIER_PLUS_EXACT_REQUESTED_OUTPUT_"
                            + "PROMOTIONS_V1",
                    "derivedInputCount", inputSelection.derivedInputs.size(),
                    "derivedInputs", limitedSorted(inputSelection.derivedInputs,
                            MAX_PORTS),
                    "unresolvedInputCount", inputSelection.unresolvedInputs.size(),
                    "unresolvedInputs", limitedSorted(
                            inputSelection.unresolvedInputs, MAX_PORTS),
                    "inputSelectionComplete",
                    inputSelection.unresolvedInputs.isEmpty()
                            && !broadInputPortTruncated,
                    "outputs", outputPorts,
                    "outputSlices", outputSlices,
                    "pathAssumptionSites", limitedSorted(pathAssumptions, MAX_PORTS),
                    "exploreBranchSites", limitedSorted(exploreBranches, MAX_PORTS),
                    "branchPolicies", branchPolicies,
                    "models", limitedSorted(models, MAX_PORTS),
                    "methodCount", draft.methods.size(),
                    "methodLimit", MAX_REGION_METHODS,
                    "methodBudgetTruncated", draft.methodBudgetTruncated,
                    "causalCellCount", draft.causalCells.size(),
                    "causalCellLimit", MAX_BACKWARD_SLICE_CELLS,
                    "causalCellBudgetTruncated",
                    draft.causalCellBudgetTruncated,
                    "truncated", draft.truncated,
                    "truncationReasons", truncationReasons(draft, false),
                    "causalEdgeIds", draft.exceptionDirected
                            ? causalEdgeIds(draft.causalEdges)
                            : Collections.emptyList(),
                    "selection", draft.exceptionDirected
                            ? "EXCEPTION_BACKWARD_CAUSAL_CLOSURE"
                            : "STATIC_OVER_APPROXIMATION",
                    "precision", "STATIC_OVER_APPROXIMATION");
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

        private List<String> truncationReasons(RegionDraft draft,
                                               boolean requestedOutputSlice) {
            List<String> reasons = new ArrayList<>();
            if (draft.methodBudgetTruncated) {
                reasons.add(requestedOutputSlice
                        ? "REQUESTED_OUTPUT_METHOD_LIMIT_EXCEEDED"
                        : "METHOD_LIMIT_EXCEEDED");
            }
            if (draft.causalCellBudgetTruncated) {
                reasons.add("BACKWARD_DEPENDENCY_CELL_LIMIT_EXCEEDED");
            }
            if (draft.truncated && reasons.isEmpty()) {
                reasons.add("UNCLASSIFIED_STATIC_TRUNCATION");
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
                boolean protocolScalarOutput = outboundProtocolScalarArgument(
                        region, output, outputCell);
                boolean protocolReturnOutput = outboundProtocolReturnValue(
                        region, outputCell);
                if (!heapStateOutput && !protocolScalarOutput
                        && !protocolReturnOutput) {
                    continue;
                }

                RegionDraft slice = outputSlice(region, outputCell);
                List<ContainerElementFieldCandidate> containerCandidates =
                        heapStateOutput
                                ? exactContainerElementFieldCandidates(
                                region, slice, outputCell)
                                : Collections
                                .<ContainerElementFieldCandidate>emptyList();
                Set<String> containerElementSchemaFields =
                        new LinkedHashSet<>();
                // The ordinary backward walk stops at the projected owner
                // cell.  An exact array load connects that owner to the
                // already-selected container accessor and must be retained
                // as part of the requested-output proof, not merely as
                // declaration metadata.
                for (ContainerElementFieldCandidate candidate
                        : containerCandidates) {
                    containerElementSchemaFields.add(
                            candidate.baseInputCell);
                    slice.causalEdges.add(candidate.arrayLoad);
                    slice.causalEdges.add(candidate.containerAccessor);
                    slice.causalCells.add(string(candidate.arrayLoad.get(
                            "fromCell")));
                    slice.causalCells.add(string(candidate.arrayLoad.get(
                            "toCell")));
                    slice.causalCells.add(string(candidate.containerAccessor
                            .get("fromCell")));
                    for (String proofId : candidate.proofEdgeIds) {
                        for (Map<String, Object> proofEdge : edges) {
                            if (!proofId.equals(string(proofEdge.get("id")))) {
                                continue;
                            }
                            slice.causalEdges.add(proofEdge);
                            slice.causalCells.add(string(proofEdge.get(
                                    "fromCell")));
                            slice.causalCells.add(string(proofEdge.get(
                                    "toCell")));
                            break;
                        }
                    }
                }
                RequestedStateTransformerContract transformerContract =
                        heapStateOutput
                                ? requestedStateTransformerContract(slice,
                                string(output.get("portId")), outputCell)
                                : RequestedStateTransformerContract
                                .notApplicable();
                Set<String> candidates = new LinkedHashSet<>();
                Set<String> produced = new LinkedHashSet<>();
                for (String method : slice.methods) {
                    Map<String, Object> plan = plansByMethod.get(method);
                    if (plan == null) {
                        continue;
                    }
                    candidates.addAll(strings(plan.get("symbolicInputs")));
                    produced.addAll(strings(plan.get("outputs")));
                }
                InputSelection selection = selectExternalInputs(slice,
                        candidates, produced);
                int inputPortCountBeforeSlice = inputPorts.size();
                int promotedInputPortCount = 0;
                int promotionCapacityOmittedInputCount = 0;
                Set<String> selectedPorts = new LinkedHashSet<>();
                List<Map<String, Object>> inputBindings = new ArrayList<>();
                Set<String> unresolved = new LinkedHashSet<>(
                        selection.unresolvedInputs);
                Map<String, Map<String, Object>> unresolvedDetails =
                        new LinkedHashMap<>(selection.unresolvedInputDetails);

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
                Map<String, String> promotionReasons = new LinkedHashMap<>();
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
                                && string(existing.get(
                                "fieldPathAuthority")).isEmpty()
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
                    String promotionReason = outputSliceFrontierPromotionReason(
                            input, slice);
                    if (promotionReason.isEmpty()
                            && containerElementSchemaFields.contains(input)) {
                        // The declaration is a schema template.  The exact
                        // array/container proof below selects each concrete
                        // element owner, so this port deliberately has no
                        // single accessor-site materialization metadata.
                        promotionReason =
                                "OUTPUT_SLICE_CONTAINER_ELEMENT_FIELD_"
                                        + "SCHEMA_FRONTIER";
                    }
                    promotionReasons.put(input, promotionReason);
                    if (resolution.portId.isEmpty()
                            && !incompatiblePromotedFieldPort
                            && !promotionReason.isEmpty()) {
                        if (inputPorts.size()
                                < MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS) {
                            String portId = region.regionId + ".in."
                                    + inputPorts.size();
                            Map<String, Object> promotedPort = object(
                                    "portId", portId,
                                    "cell", input,
                                    "sourceKind", sourceKind(input,
                                            region.rootMethod),
                                    "selectionReason",
                                    promotionReason,
                                    "projection", projection(input),
                                    "portOrigin",
                                    "REQUESTED_OUTPUT_FRONTIER_PROMOTION",
                                    "promotedForOutputPort",
                                    string(output.get("portId")),
                                    "promotionAuthority",
                                    "EXACT_MATERIALIZABLE_REQUESTED_OUTPUT_"
                                            + "DEPENDENCY_V1");
                            addOutputSliceFrontierMaterializationMetadata(
                                    promotedPort, input, slice);
                            inputPorts.add(promotedPort);
                            portsPromotedByInput.put(input, portId);
                            promotedInputPortCount++;
                        } else {
                            promotionCapacityOmittedInputCount++;
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
                    String promotionReason = promotionReasons.get(input);
                    if (promotionReason == null) {
                        promotionReason = "";
                    }
                    if (resolution.portId.isEmpty()) {
                        boolean capacityExceeded =
                                promotionCapacityOmittedInputCount > 0
                                        && !promotionReason.isEmpty();
                        String diagnostic = input + (capacityExceeded
                                ? " [exact output slice dependency exceeds "
                                + "bounded promotion capacity "
                                + MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS
                                + "]"
                                : " [output slice input has no region port]");
                        unresolved.add(diagnostic);
                        unresolvedDetails.put(diagnostic, object(
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
                                "diagnostic", diagnostic,
                                "provenanceAuthority",
                                "STATIC_EXACT_DEPENDENCY_METHOD_"
                                        + "CONSUMER_SET_V1"));
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
                        if (heapStateOutput) {
                            InputTransformerSinks sinks =
                                    requestedStateTransformerSinks(input,
                                            outputCell, slice,
                                            transformerContract);
                            inputBinding.put(
                                    "requestedStateTransformerSinkSites",
                                    sinks.transformerSites);
                            inputBinding.put(
                                    "requestedStateTransformerGuardSites",
                                    sinks.guardSites);
                            inputBinding.put(
                                    "requestedStateTransformerSinkClosureComplete",
                                    sinks.complete);
                            inputBinding.put(
                                    "requestedStateTransformerSinkExclusive",
                                    sinks.exclusive);
                            inputBinding.put(
                                    "requestedStateTransformerUnclassifiedEdgeIds",
                                    sinks.unclassifiedEdgeIds);
                            inputBinding.put(
                                    "requestedStateTransformerSinkAuthority",
                                    "STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_"
                                            + "REQUESTED_STATE_TRANSFORMERS");
                        }
                        inputBindings.add(inputBinding);
                    }
                }

                Set<String> sites = new LinkedHashSet<>();
                for (Map<String, Object> edge : slice.causalEdges) {
                    String site = string(edge.get("siteId"));
                    if (!site.isEmpty()) {
                        sites.add(site);
                    }
                }
                List<Map<String, Object>> heapInitializers = heapStateOutput
                        ? heapInitializers(slice,
                        string(output.get("portId")), outputCell)
                        : Collections.emptyList();
                OutputCaptureSelection outputCapture = heapStateOutput
                        ? fieldAssignmentOutputCaptureBindings(slice,
                                transformerContract, string(output.get("portId")),
                        outputCell)
                        : protocolScalarOutput
                        ? outputCaptureBindings(slice,
                        string(output.get("portId")), outputCell)
                        // An ordinary root return is captured by exitRegion.
                        // Its projected cells are interpreted relative to
                        // that same returned object, so no call-argument hook
                        // is either necessary or authoritative here.
                        : protocolReturnOutput
                        ? OutputCaptureSelection.notRequired()
                        : OutputCaptureSelection.notRequired();
                List<Map<String, Object>> containerBindings =
                        containerElementFieldBindings(containerCandidates,
                                inputPorts, selectedPorts,
                                string(output.get("portId")));
                boolean structuralComplete = !slice.truncated
                        && !slice.causalEdges.isEmpty();
                boolean unresolvedInputProvenanceComplete =
                        unresolved.size() == unresolvedDetails.size();
                for (Map<String, Object> detail
                        : unresolvedDetails.values()) {
                    unresolvedInputProvenanceComplete &= !strings(
                            detail.get("dependencyMethods")).isEmpty();
                }
                boolean complete = structuralComplete
                        && unresolved.isEmpty()
                        && (!heapStateOutput
                        || transformerContract.complete)
                        && outputCapture.complete;
                Map<String, Object> outputSlice = object(
                        "outputPort", string(output.get("portId")),
                        "outputCell", outputCell,
                        "inputPorts", sorted(selectedPorts),
                        "inputBindings", inputBindings,
                        "methods", orderedMethods(slice.methods,
                                region.rootMethod),
                        "accessorImplementationAdmissions",
                        slice.accessorImplementationAdmissions,
                        "accessorImplementationAdmissionCount",
                        slice.accessorImplementationAdmissions.size(),
                        "sites", sorted(sites),
                        "causalEdgeIds", causalEdgeIds(slice.causalEdges),
                        "causalEdges", causalEdgeReferences(
                                slice.causalEdges),
                        "causalEdgeCount", slice.causalEdges.size(),
                        "regionTruncated", slice.inheritedRegionTruncated,
                        "methodCount", slice.methods.size(),
                        "methodLimit",
                        MAX_REQUESTED_OUTPUT_SLICE_METHODS,
                        "methodBudgetTruncated",
                        slice.methodBudgetTruncated,
                        "causalCellCount", slice.causalCells.size(),
                        "causalCellLimit", MAX_BACKWARD_SLICE_CELLS,
                        "causalCellBudgetTruncated",
                        slice.causalCellBudgetTruncated,
                        "truncated", slice.truncated,
                        "truncationReasons", truncationReasons(slice, true),
                        "heapInitializers", heapInitializers,
                        "captureBindings", outputCapture.bindings,
                        "captureBindingsRequired", outputCapture.required,
                        "captureBindingsComplete", outputCapture.complete,
                        "captureBindingIssues", outputCapture.issues,
                        "containerElementFieldBindings",
                        containerBindings,
                        "derivedInputs", limitedSorted(selection.derivedInputs,
                                MAX_PORTS),
                        "inputPortCountBeforeSlice",
                        inputPortCountBeforeSlice,
                        "promotedInputPortCount",
                        promotedInputPortCount,
                        "inputPortPromotionLimit",
                        MAX_INPUT_PORTS_WITH_OUTPUT_SLICE_PROMOTIONS,
                        "promotionCapacityOmittedInputCount",
                        promotionCapacityOmittedInputCount,
                        "promotionCapacityTruncated",
                        promotionCapacityOmittedInputCount > 0,
                        "promotionAuthority",
                        "EXACT_MATERIALIZABLE_REQUESTED_OUTPUT_DEPENDENCY_V1",
                        "unresolvedInputs", sorted(unresolved),
                        "unresolvedInputDetails",
                        new ArrayList<>(unresolvedDetails.values()),
                        "unresolvedInputProvenanceComplete",
                        unresolvedInputProvenanceComplete,
                        "structuralComplete", structuralComplete,
                        "complete", complete,
                        "selection",
                        "REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE");
                if (heapStateOutput) {
                    outputSlice.putAll(transformerContract.toMap());
                }
                result.add(outputSlice);
            }
            return result;
        }

        /**
         * Finds the one supported generic container-field provenance shape:
         *
         * <pre>
         * declared array field --C--> array local --A[index]--> owner local
         * owner local#field --P--> scalar result
         * declared scalar field --G----------------> same scalar result
         * </pre>
         *
         * <p>C, P and G must already belong to the requested-output backward
         * slice.  A is recovered from the region's full static graph because
         * the projection edge starts at {@code owner#field}, while the array
         * load defines {@code owner}; the ordinary cell-exact backward walk
         * intentionally does not guess across that projection.  Every join
         * below is exact on method, local, result, site, unit and declared
         * field metadata.  A missing or duplicate segment yields no binding.
         * No field-name, suffix, or type-only fallback is used.</p>
         */
        private List<ContainerElementFieldCandidate>
        exactContainerElementFieldCandidates(RegionDraft region,
                                              RegionDraft slice,
                                              String outputCell) {
            Set<String> sliceEdgeIds = new LinkedHashSet<>(
                    causalEdgeIds(slice.causalEdges));
            Map<String, List<Map<String, Object>>> arrayLoadsByShape =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
                // A requested-output walk can legitimately admit a
                // synchronous helper that the compact/bounded broad region
                // omitted.  Requiring region.methods here silently discarded
                // the exact array-element provenance even though every edge
                // and method was already in the independently bounded slice.
                if (!slice.methods.contains(string(edge.get(
                        "method")))
                        || arrayLoadSelector(edge) == Integer.MIN_VALUE) {
                    continue;
                }
                arrayLoadsByShape.computeIfAbsent(arrayLoadShape(edge),
                        ignored -> new ArrayList<>()).add(edge);
            }

            List<ContainerElementFieldCandidate> result = new ArrayList<>();
            Set<String> emitted = new LinkedHashSet<>();
            for (List<Map<String, Object>> loadGroup
                    : arrayLoadsByShape.values()) {
                if (loadGroup.size() != 1) {
                    continue;
                }
                Map<String, Object> arrayLoad = loadGroup.get(0);
                String method = string(arrayLoad.get("method"));
                String arrayCell = string(arrayLoad.get("fromCell"));
                String ownerCell = string(arrayLoad.get("toCell"));

                List<Map<String, Object>> containers = new ArrayList<>();
                for (Map<String, Object> edge : edges) {
                    if (sliceEdgeIds.contains(string(edge.get("id")))
                            && exactContainerAccessor(edge, method,
                            arrayCell)) {
                        containers.add(edge);
                    }
                }
                if (containers.size() != 1) {
                    continue;
                }
                Map<String, Object> container = containers.get(0);
                DeclaredFieldIdentity containerField = declaredField(
                        string(container.get("fromCell")));
                if (containerField == null
                        || !containerField.type.endsWith("[]")) {
                    continue;
                }

                Map<String, List<Map<String, Object>>> projectionsByShape =
                        new LinkedHashMap<>();
                for (Map<String, Object> edge : edges) {
                    if (!sliceEdgeIds.contains(string(edge.get("id")))
                            || !exactProjectedAccessor(edge, method,
                            ownerCell)) {
                        continue;
                    }
                    projectionsByShape.computeIfAbsent(
                            projectedAccessorShape(edge),
                            ignored -> new ArrayList<>()).add(edge);
                }
                for (List<Map<String, Object>> projectionGroup
                        : projectionsByShape.values()) {
                    if (projectionGroup.size() != 1) {
                        continue;
                    }
                    Map<String, Object> projection = projectionGroup.get(0);
                    DeclaredFieldIdentity elementField = declaredField(
                            string(projection.get(
                                    "declaredFieldSignature")));
                    if (elementField == null
                            || !declaredMetadataMatches(projection,
                            elementField)) {
                        continue;
                    }
                    List<Map<String, Object>> declaredReads =
                            new ArrayList<>();
                    for (Map<String, Object> edge : edges) {
                        if (sliceEdgeIds.contains(string(edge.get("id")))
                                && exactDeclaredAccessorPair(edge,
                                projection, elementField)) {
                            declaredReads.add(edge);
                        }
                    }
                    if (declaredReads.size() != 1) {
                        continue;
                    }
                    Map<String, Object> declaredRead = declaredReads.get(0);
                    Set<String> proofIds = new LinkedHashSet<>(Arrays.asList(
                            string(container.get("id")),
                            string(arrayLoad.get("id")),
                            string(projection.get("id")),
                            string(declaredRead.get("id"))));
                    if (proofIds.size() != 4 || proofIds.contains("")) {
                        continue;
                    }
                    String identity = string(arrayLoad.get("id")) + "\n"
                            + string(projection.get("id")) + "\n"
                            + elementField.signature;
                    if (!emitted.add(identity)) {
                        continue;
                    }
                    int selector = arrayLoadSelector(arrayLoad);
                    result.add(new ContainerElementFieldCandidate(container,
                            arrayLoad, projection, declaredRead,
                            containerField, elementField, selector,
                            selector >= 0));
                }
            }
            addArrayPutValueFieldCandidates(slice, outputCell,
                    sliceEdgeIds, arrayLoadsByShape, result, emitted);
            addDirectArrayFieldPathCandidates(slice, arrayLoadsByShape,
                    result, emitted);
            result.sort(Comparator
                    .comparing((ContainerElementFieldCandidate candidate) ->
                            string(candidate.projectedAccessor.get("siteId")))
                    .thenComparing(candidate -> candidate.elementField.signature)
                    .thenComparing(candidate ->
                            string(candidate.arrayLoad.get("id"))));
            return result;
        }

        /** Exact array[index].a.b.leaf provenance, materialized eagerly. */
        private void addDirectArrayFieldPathCandidates(
                RegionDraft slice,
                Map<String, List<Map<String, Object>>> arrayLoadsByShape,
                List<ContainerElementFieldCandidate> result,
                Set<String> emitted) {
            for (String cell : sorted(slice.causalCells)) {
                DeclaredFieldPathAccess access =
                        materializableDeclaredFieldPathAccess(cell, slice);
                if (access == null) {
                    continue;
                }
                Map<String, Object> rootProjection = null;
                Map<String, Object> leafDeclared = null;
                for (Map<String, Object> edge : slice.causalEdges) {
                    if (cell.equals(string(edge.get("fromCell")))
                            && access.siteId.equals(string(edge.get(
                            "siteId")))) {
                        if (rootProjection != null) {
                            rootProjection = null;
                            break;
                        }
                        rootProjection = edge;
                    }
                }
                for (Map<String, Object> edge : slice.causalEdges) {
                    if (access.leafField.signature.equals(string(edge.get(
                            "fromCell")))
                            && "field_read".equals(string(edge.get(
                            "kind")))) {
                        if (leafDeclared != null) {
                            leafDeclared = null;
                            break;
                        }
                        leafDeclared = edge;
                    }
                }
                if (rootProjection == null || leafDeclared == null) {
                    continue;
                }
                for (List<Map<String, Object>> loadGroup
                        : arrayLoadsByShape.values()) {
                    if (loadGroup.size() != 1) continue;
                    Map<String, Object> arrayLoad = loadGroup.get(0);
                    if (!access.method.equals(string(arrayLoad.get("method")))
                            || !access.accessOwnerCell.equals(string(
                            arrayLoad.get("toCell")))) {
                        continue;
                    }
                    String arrayCell = string(arrayLoad.get("fromCell"));
                    List<Map<String, Object>> containers = new ArrayList<>();
                    for (Map<String, Object> edge : edges) {
                        if (exactContainerAccessor(edge, access.method,
                                arrayCell)) {
                            containers.add(edge);
                        }
                    }
                    if (containers.size() != 1) continue;
                    Map<String, Object> container = containers.get(0);
                    DeclaredFieldIdentity containerField = declaredField(
                            string(container.get("fromCell")));
                    if (containerField == null
                            || !containerField.type.endsWith("[]")) {
                        continue;
                    }
                    Set<String> proof = new LinkedHashSet<>(
                            access.proofEdgeIds);
                    proof.add(string(container.get("id")));
                    proof.add(string(arrayLoad.get("id")));
                    if (proof.contains("")
                            || proof.size() != access.proofEdgeIds.size() + 2) {
                        continue;
                    }
                    String identity = "DIRECT_ARRAY_FIELD_PATH\n"
                            + string(arrayLoad.get("id")) + "\n" + cell;
                    if (!emitted.add(identity)) continue;
                    int selector = arrayLoadSelector(arrayLoad);
                    result.add(new ContainerElementFieldCandidate(container,
                            arrayLoad, rootProjection, leafDeclared, null,
                            containerField, access.leafField, cell,
                            access.fieldPath, selector, selector >= 0, true,
                            proof,
                            "STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_"
                                    + "CHAIN_V1"));
                }
            }
        }

        /**
         * Completes the inverse container projection used by state updates of
         * the form {@code state.put(key, incoming[i])}.  A later activation
         * may read {@code state[key].leaf} even though this producer never
         * invokes the leaf accessor on {@code incoming[i]}.  Requiring that
         * incidental getter call strands the leaf at a concrete object value.
         *
         * <p>The admission remains structural and container-sensitive: one
         * exact declared array accessor, one exact array load, and one exact
         * Java {@code Map.put} value edge must identify the same local.  The
         * demanded scalar leaf must independently have one exact projected /
         * declared accessor pair in the selected output slice.  Runtime then
         * verifies the concrete array index and declared leaf owner before
         * materializing it.  No object reference is reclassified as a scalar
         * and no field-name-only relation is introduced.</p>
         */
        private void addArrayPutValueFieldCandidates(
                RegionDraft slice, String outputCell,
                Set<String> sliceEdgeIds,
                Map<String, List<Map<String, Object>>> arrayLoadsByShape,
                List<ContainerElementFieldCandidate> result,
                Set<String> emitted) {
            Set<String> directlyBoundFields = new LinkedHashSet<>();
            for (ContainerElementFieldCandidate candidate : result) {
                directlyBoundFields.add(candidate.containerField.signature
                        + "\n" + candidate.elementField.signature + "\n"
                        + candidate.fieldPath);
            }

            List<Map<String, Object>[]> accessorPairs =
                    exactProjectedDeclaredAccessorPairs(sliceEdgeIds);
            for (List<Map<String, Object>> loadGroup
                    : arrayLoadsByShape.values()) {
                if (loadGroup.size() != 1) {
                    continue;
                }
                Map<String, Object> arrayLoad = loadGroup.get(0);
                String method = string(arrayLoad.get("method"));
                String arrayCell = string(arrayLoad.get("fromCell"));
                String elementCell = string(arrayLoad.get("toCell"));

                List<Map<String, Object>> containers = new ArrayList<>();
                for (Map<String, Object> edge : edges) {
                    if (sliceEdgeIds.contains(string(edge.get("id")))
                            && exactContainerAccessor(edge, method,
                            arrayCell)) {
                        containers.add(edge);
                    }
                }
                if (containers.size() != 1) {
                    continue;
                }
                Map<String, Object> container = containers.get(0);
                DeclaredFieldIdentity containerField = declaredField(
                        string(container.get("fromCell")));
                if (containerField == null
                        || !containerField.type.endsWith("[]")) {
                    continue;
                }

                List<Map<String, Object>> putValues = new ArrayList<>();
                for (Map<String, Object> edge : slice.causalEdges) {
                    if (exactArrayElementMapPutValue(edge, method,
                            elementCell, outputCell)) {
                        putValues.add(edge);
                    }
                }
                if (putValues.size() != 1) {
                    continue;
                }
                Map<String, Object> putValue = putValues.get(0);

                for (Map<String, Object>[] pair : accessorPairs) {
                    Map<String, Object> projection = pair[0];
                    Map<String, Object> declaredRead = pair[1];
                    DeclaredFieldIdentity elementField = declaredField(
                            string(projection.get(
                                    "declaredFieldSignature")));
                    List<String> fieldPath = exactProjectedFieldPath(
                            projection, elementField);
                    if (elementField == null
                            || !closedProtocolScalarType(elementField.type)
                            || fieldPath.isEmpty()) {
                        continue;
                    }
                    String fieldIdentity = containerField.signature + "\n"
                            + elementField.signature + "\n" + fieldPath;
                    if (directlyBoundFields.contains(fieldIdentity)) {
                        continue;
                    }
                    Set<String> proofIds = new LinkedHashSet<>(Arrays.asList(
                            string(container.get("id")),
                            string(arrayLoad.get("id")),
                            string(putValue.get("id")),
                            string(projection.get("id")),
                            string(declaredRead.get("id"))));
                    if (proofIds.size() != 5 || proofIds.contains("")) {
                        continue;
                    }
                    String identity = "MAP_PUT_VALUE\n"
                            + string(arrayLoad.get("id")) + "\n"
                            + string(putValue.get("id")) + "\n"
                            + elementField.signature + "\n" + fieldPath;
                    if (!emitted.add(identity)) {
                        continue;
                    }
                    int selector = arrayLoadSelector(arrayLoad);
                    result.add(new ContainerElementFieldCandidate(container,
                            arrayLoad, projection, declaredRead, putValue,
                            containerField, elementField,
                            elementField.signature, fieldPath, selector,
                            selector >= 0, true,
                            Collections.<String>emptyList(), ""));
                }
            }
        }

        @SuppressWarnings("unchecked")
        private List<Map<String, Object>[]>
        exactProjectedDeclaredAccessorPairs(Set<String> sliceEdgeIds) {
            List<Map<String, Object>[]> result = new ArrayList<>();
            Map<String, List<Map<String, Object>>> projections =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
                if (!sliceEdgeIds.contains(string(edge.get("id")))
                        || !exactProjectedAccessorPath(edge)) {
                    continue;
                }
                projections.computeIfAbsent(projectedAccessorShape(edge),
                        ignored -> new ArrayList<>()).add(edge);
            }
            for (List<Map<String, Object>> group : projections.values()) {
                if (group.size() != 1) {
                    continue;
                }
                Map<String, Object> projection = group.get(0);
                DeclaredFieldIdentity field = declaredField(string(
                        projection.get("declaredFieldSignature")));
                if (field == null || !declaredMetadataMatches(projection,
                        field)) {
                    continue;
                }
                List<Map<String, Object>> declared = new ArrayList<>();
                for (Map<String, Object> edge : edges) {
                    if (sliceEdgeIds.contains(string(edge.get("id")))
                            && exactDeclaredAccessorPair(edge, projection,
                            field)) {
                        declared.add(edge);
                    }
                }
                if (declared.size() == 1) {
                    result.add(new Map[]{projection, declared.get(0)});
                }
            }
            return result;
        }

        private boolean exactProjectedAccessorPath(
                Map<String, Object> edge) {
            DeclaredFieldIdentity field = declaredField(string(edge.get(
                    "declaredFieldSignature")));
            String method = string(edge.get("method"));
            String from = string(edge.get("fromCell"));
            String objectFrom = string(edge.get("objectFromCell"));
            String to = string(edge.get("toCell"));
            String path = string(edge.get("fieldPath"));
            return exactStaticEdge(edge)
                    && "accessor_field_return".equals(string(edge.get(
                    "kind")))
                    && "PROJECTION".equals(string(edge.get(
                    "transferKind")))
                    && "value_flow".equals(string(edge.get("relation")))
                    && Boolean.TRUE.equals(edge.get("fieldSensitive"))
                    && field != null && declaredMetadataMatches(edge, field)
                    && !objectFrom.isEmpty() && from.equals(objectFrom + path)
                    && path.matches("(?:#field:[^#]+){1,4}")
                    && path.endsWith("#field:" + field.name)
                    && to.equals(string(edge.get("objectToCell")))
                    && exactLocalCell(method, to)
                    && exactUnitDefines(edge, to);
        }

        private List<String> exactProjectedFieldPath(
                Map<String, Object> projection,
                DeclaredFieldIdentity field) {
            if (field == null || !exactProjectedAccessorPath(projection)) {
                return Collections.emptyList();
            }
            List<String> result = new ArrayList<>();
            Matcher matcher = FIELD_PATH_SEGMENT_PATTERN.matcher(string(
                    projection.get("fieldPath")));
            while (matcher.find()) {
                result.add(matcher.group(1));
            }
            return !result.isEmpty()
                    && field.name.equals(result.get(result.size() - 1))
                    ? result : Collections.<String>emptyList();
        }

        private boolean exactArrayElementMapPutValue(
                Map<String, Object> edge, String method,
                String elementCell, String outputCell) {
            if (!exactStaticEdge(edge)
                    || !method.equals(string(edge.get("method")))
                    || !elementCell.equals(string(edge.get("fromCell")))
                    || !outputCell.equals(string(edge.get("toCell")))
                    || !"field_mutation".equals(string(edge.get("kind")))
                    || !"HEAP_WRITE".equals(string(edge.get(
                    "transferKind")))
                    || !"value_flow".equals(string(edge.get("relation")))
                    || !exactJavaMapPut(string(edge.get("invoke")))) {
                return false;
            }
            String local = exactLocalName(method, elementCell);
            String unit = string(edge.get("unit")).trim();
            int open = unit.lastIndexOf('(');
            int close = unit.lastIndexOf(')');
            if (local.isEmpty() || open < 0 || close <= open) {
                return false;
            }
            String[] arguments = unit.substring(open + 1, close).split(",",
                    -1);
            return arguments.length == 2
                    && local.equals(arguments[1].trim());
        }

        private boolean exactJavaMapPut(String invoke) {
            return invoke.matches("^<java\\.util\\.(?:Map|SortedMap|"
                    + "NavigableMap|Hashtable|concurrent\\.ConcurrentMap|"
                    + "concurrent\\.ConcurrentNavigableMap):\\s+"
                    + "java\\.lang\\.Object\\s+put\\(java\\.lang\\.Object,"
                    + "java\\.lang\\.Object\\)>$");
        }

        private List<Map<String, Object>> containerElementFieldBindings(
                List<ContainerElementFieldCandidate> candidates,
                List<Map<String, Object>> inputPorts,
                Set<String> selectedPorts, String outputPort) {
            List<Map<String, Object>> result = new ArrayList<>();
            for (ContainerElementFieldCandidate candidate : candidates) {
                String basePort = uniqueExactSelectedInputPort(inputPorts,
                        selectedPorts, candidate.baseInputCell);
                String containerPort = uniqueExactSelectedInputPort(
                        inputPorts, selectedPorts,
                        candidate.containerField.signature);
                if (basePort.isEmpty() || containerPort.isEmpty()
                        || basePort.equals(containerPort)) {
                    continue;
                }
                List<String> proofIds = new ArrayList<>(
                        candidate.proofEdgeIds);
                if (proofIds.isEmpty()) {
                    proofIds.addAll(Arrays.asList(
                            string(candidate.containerAccessor.get("id")),
                            string(candidate.arrayLoad.get("id")),
                            string(candidate.projectedAccessor.get("id")),
                            string(candidate.declaredAccessor.get("id"))));
                    if (candidate.mapPutValue != null) {
                        proofIds.add(string(candidate.mapPutValue.get("id")));
                    }
                }
                proofIds = sorted(proofIds);
                String selectorAuthority = candidate.constantIndex
                        ? "EXACT_ARRAY_INDEX"
                        : "DISCOVER_UNIQUE_IDENTITY_INDEX";
                result.add(object(
                        "schemaVersion",
                        candidate.materializeFromContainerSnapshot ? 2 : 1,
                        "kind", "ARRAY_ELEMENT_FIELD",
                        "bindingId", outputPort + ".array-element-field."
                                + string(candidate.arrayLoad.get("id"))
                                + (candidate.materializeFromContainerSnapshot
                                ? candidate.mapPutValue == null
                                ? ".direct-field-path."
                                : ".map-put-value."
                                + string(candidate.projectedAccessor.get(
                                "id")) : ""),
                        "baseInputSymbol", basePort,
                        "containerInputPort", containerPort,
                        "containerInputCell",
                        candidate.containerField.signature,
                        "selectorAuthority", selectorAuthority,
                        "elementIndex", candidate.constantIndex
                                ? candidate.elementIndex : -1,
                        "elementOccurrence", candidate.constantIndex
                                ? 1 : -1,
                        "fieldPath", candidate.fieldPath,
                        "declaredFieldSignature",
                        candidate.elementField.signature,
                        "declaredFieldOwnerClass",
                        candidate.elementField.owner,
                        "declaredFieldType", candidate.elementField.type,
                        "declaredFieldName", candidate.elementField.name,
                        "materializationMode",
                        candidate.materializeFromContainerSnapshot
                                ? "CONTAINER_SNAPSHOT"
                                : "FIELD_ACCESS_HOOK",
                        "method", string((candidate
                                .materializeFromContainerSnapshot
                                ? candidate.arrayLoad
                                : candidate.projectedAccessor).get(
                                "method")),
                        "fieldMaterializationSiteId",
                        string((candidate
                                .materializeFromContainerSnapshot
                                ? candidate.mapPutValue == null
                                ? candidate.projectedAccessor
                                : candidate.mapPutValue
                                : candidate.projectedAccessor).get(
                                "siteId")),
                        "arrayLoadSiteId",
                        string(candidate.arrayLoad.get("siteId")),
                        "proofCausalEdgeIds", proofIds,
                        "proofAuthority",
                        !candidate.proofAuthority.isEmpty()
                                ? candidate.proofAuthority
                                : candidate.materializeFromContainerSnapshot
                                ? "STATIC_EXACT_ARRAY_ELEMENT_MAP_PUT_VALUE_"
                                + "AND_DECLARED_FIELD_FIVE_EDGE_JOIN_V1"
                                : "STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_"
                                + "DECLARED_FIELD_FOUR_EDGE_JOIN_V1",
                        "complete", true));
            }
            return result;
        }

        private String uniqueExactSelectedInputPort(
                List<Map<String, Object>> inputPorts,
                Set<String> selectedPorts, String exactCell) {
            String match = "";
            for (Map<String, Object> input : inputPorts) {
                if (!exactCell.equals(string(input.get("cell")))) {
                    continue;
                }
                String port = string(input.get("portId"));
                if (!selectedPorts.contains(port) || !match.isEmpty()) {
                    return "";
                }
                match = port;
            }
            return match;
        }

        private boolean exactContainerAccessor(Map<String, Object> edge,
                                               String method,
                                               String arrayCell) {
            DeclaredFieldIdentity field = declaredField(string(edge.get(
                    "fromCell")));
            if (!exactStaticEdge(edge)
                    || !method.equals(string(edge.get("method")))
                    || !"HEAP_READ".equals(string(edge.get("transferKind")))
                    || !"value_flow".equals(string(edge.get("relation")))
                    || !arrayCell.equals(string(edge.get("toCell")))
                    || field == null || !field.type.endsWith("[]")
                    || !exactLocalCell(method, arrayCell)
                    || !exactUnitDefines(edge, arrayCell)) {
                return false;
            }
            if ("field_read".equals(string(edge.get("kind")))) {
                return exactDeclaredGetfieldUnit(edge, field, "");
            }
            return "accessor_field_return".equals(string(edge.get(
                    "kind")))
                    && declaredMetadataMatches(edge, field);
        }

        private boolean exactProjectedAccessor(Map<String, Object> edge,
                                               String method,
                                               String ownerCell) {
            DeclaredFieldIdentity field = declaredField(string(edge.get(
                    "declaredFieldSignature")));
            if (!exactStaticEdge(edge)
                    || !method.equals(string(edge.get("method")))
                    || !"accessor_field_return".equals(string(edge.get(
                    "kind")))
                    || !"PROJECTION".equals(string(edge.get(
                    "transferKind")))
                    || !"value_flow".equals(string(edge.get("relation")))
                    || !Boolean.TRUE.equals(edge.get("fieldSensitive"))
                    || field == null
                    || !declaredMetadataMatches(edge, field)
                    || !ownerCell.equals(string(edge.get(
                    "objectFromCell")))
                    || !string(edge.get("fromCell")).equals(ownerCell
                    + "#field:" + field.name)
                    || !("#field:" + field.name).equals(string(edge.get(
                    "fieldPath")))
                    || !string(edge.get("toCell")).equals(string(edge.get(
                    "objectToCell")))
                    || !exactLocalCell(method, string(edge.get("toCell")))) {
                return false;
            }
            return exactUnitDefines(edge, string(edge.get("toCell")));
        }

        private boolean exactDeclaredAccessorPair(
                Map<String, Object> edge, Map<String, Object> projection,
                DeclaredFieldIdentity field) {
            return exactStaticEdge(edge)
                    && "accessor_field_return".equals(string(edge.get(
                    "kind")))
                    && "HEAP_READ".equals(string(edge.get("transferKind")))
                    && "value_flow".equals(string(edge.get("relation")))
                    && field.signature.equals(string(edge.get("fromCell")))
                    && string(projection.get("toCell")).equals(string(
                    edge.get("toCell")))
                    && string(projection.get("method")).equals(string(
                    edge.get("method")))
                    && string(projection.get("siteId")).equals(string(
                    edge.get("siteId")))
                    && integer(projection.get("unitIndex"), -1) == integer(
                    edge.get("unitIndex"), -1)
                    && string(projection.get("unit")).equals(string(
                    edge.get("unit")))
                    && string(projection.get("invoke")).equals(string(
                    edge.get("invoke")))
                    && declaredMetadataMatches(edge, field)
                    && exactUnitDefines(edge, string(edge.get("toCell")));
        }

        private boolean exactStaticEdge(Map<String, Object> edge) {
            return !isBoundary(edge)
                    && !string(edge.get("id")).isEmpty()
                    && !Boolean.TRUE.equals(edge.get("mappingOnly"))
                    && Boolean.TRUE.equals(edge.get(
                    "semanticAssertionsAllowed"))
                    && Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticDerivation"))
                    && Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticSmt"))
                    && "backward_provenance".equals(string(edge.get(
                    "direction")))
                    && exactSiteIdentity(edge);
        }

        private boolean exactSiteIdentity(Map<String, Object> edge) {
            String method = string(edge.get("method"));
            int unitIndex = integer(edge.get("unitIndex"), -1);
            return !method.isEmpty() && unitIndex >= 0
                    && (method + "#u" + unitIndex).equals(string(edge.get(
                    "siteId")));
        }

        private int arrayLoadSelector(Map<String, Object> edge) {
            if (!exactStaticEdge(edge)
                    || !"local_def_use".equals(string(edge.get("kind")))
                    || !"VALUE_PASS".equals(string(edge.get(
                    "transferKind")))
                    || !"taint_depends_on".equals(string(edge.get(
                    "relation")))) {
                return Integer.MIN_VALUE;
            }
            String method = string(edge.get("method"));
            String array = exactLocalName(method,
                    string(edge.get("fromCell")));
            String owner = exactLocalName(method,
                    string(edge.get("toCell")));
            if (array.isEmpty() || owner.isEmpty()) {
                return Integer.MIN_VALUE;
            }
            Matcher load = Pattern.compile("^" + Pattern.quote(owner)
                    + "\\s*=\\s*" + Pattern.quote(array)
                    + "\\[([^\\[\\]]+)\\]$").matcher(string(
                    edge.get("unit")).trim());
            if (!load.matches()) {
                return Integer.MIN_VALUE;
            }
            String selector = load.group(1).trim();
            if (selector.matches("[0-9]+")) {
                try {
                    return Integer.parseInt(selector);
                } catch (NumberFormatException ignored) {
                    return Integer.MIN_VALUE;
                }
            }
            return selector.matches("[$A-Za-z_][$A-Za-z0-9_]*")
                    ? -1 : Integer.MIN_VALUE;
        }

        private String arrayLoadShape(Map<String, Object> edge) {
            return string(edge.get("method")) + "\n"
                    + string(edge.get("fromCell")) + "\n"
                    + string(edge.get("toCell")) + "\n"
                    + string(edge.get("siteId")) + "\n"
                    + string(edge.get("unit"));
        }

        private String projectedAccessorShape(Map<String, Object> edge) {
            return string(edge.get("method")) + "\n"
                    + string(edge.get("fromCell")) + "\n"
                    + string(edge.get("toCell")) + "\n"
                    + string(edge.get("siteId")) + "\n"
                    + string(edge.get("unit")) + "\n"
                    + string(edge.get("declaredFieldSignature"));
        }

        private boolean exactUnitDefines(Map<String, Object> edge,
                                         String cell) {
            String local = exactLocalName(string(edge.get("method")), cell);
            String unit = string(edge.get("unit")).trim();
            int assignment = unit.indexOf(" = ");
            return !local.isEmpty() && assignment > 0
                    && local.equals(unit.substring(0, assignment).trim());
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

        private DeclaredFieldIdentity declaredField(String value) {
            Matcher matcher = DECLARED_FIELD_PATTERN.matcher(string(value));
            if (!matcher.matches()) {
                return null;
            }
            return new DeclaredFieldIdentity(string(value),
                    matcher.group(1).trim(), matcher.group(2).trim(),
                    matcher.group(3).trim());
        }

        private boolean declaredMetadataMatches(
                Map<String, Object> edge, DeclaredFieldIdentity field) {
            return field != null
                    && field.signature.equals(string(edge.get(
                    "declaredFieldSignature")))
                    && field.owner.equals(string(edge.get(
                    "declaredFieldOwner")))
                    && field.type.equals(string(edge.get(
                    "declaredFieldType")))
                    && field.name.equals(string(edge.get(
                    "declaredFieldName")))
                    && "SOOT_RESOLVED_DECLARATION_HIERARCHY".equals(
                    string(edge.get("declaredFieldAuthority")));
        }

        /**
         * Resolves an exact requested heap-state transformer to the RHS of
         * its original instance-field {@code AssignStmt}.  This is a separate
         * capture family from outbound call arguments: a void region root or
         * a nearby CALL_ARGUMENT is never used as a substitute for the value
         * actually written to the requested field.
         *
         * <p>The compact data-flow graph can contain synthetic HEAP_WRITE
         * aliases in addition to the canonical {@code field_write} row.  A
         * site is capturable only when exactly one canonical row spells an
         * instance-field assignment to the exact output field and its RHS is
         * an SMT-eligible value-flow cell.  Once any such transformer exists,
         * every requested-state obligation must be covered or the capture
         * plan is incomplete.</p>
         */
        private OutputCaptureSelection fieldAssignmentOutputCaptureBindings(
                RegionDraft slice,
                RequestedStateTransformerContract contract,
                String outputPort, String outputCell) {
            List<Map<String, Object>> assignmentRows = new ArrayList<>();
            String lhsSuffix = "." + outputCell;
            for (Map<String, Object> edge : slice.causalEdges) {
                if (!"HEAP_WRITE".equals(string(edge.get("transferKind")))
                        || !"field_write".equals(string(edge.get("kind")))
                        || !outputCell.equals(string(edge.get("toCell")))) {
                    continue;
                }
                String unit = string(edge.get("unit"));
                int equals = unit.indexOf(" = ");
                if (equals > 0 && unit.substring(0, equals).endsWith(
                        lhsSuffix)) {
                    assignmentRows.add(edge);
                }
            }
            if (assignmentRows.isEmpty()) {
                return OutputCaptureSelection.notRequired();
            }

            List<Map<String, Object>> bindings = new ArrayList<>();
            List<String> issues = new ArrayList<>();
            FieldSignature field = fieldSignature(outputCell);
            if (field == null || outputPort.isEmpty()
                    || !contract.applicable || !contract.complete) {
                issues.add("INCOMPLETE_REQUESTED_FIELD_TRANSFORMER_CONTRACT");
            }
            Map<String, Map<String, Object>> obligationsBySite =
                    new LinkedHashMap<>();
            for (Map<String, Object> obligation : contract.obligations) {
                String site = string(obligation.get("siteId"));
                if (site.isEmpty() || obligationsBySite.put(site,
                        obligation) != null) {
                    issues.add("AMBIGUOUS_REQUESTED_FIELD_TRANSFORMER_SITE:"
                            + site);
                }
            }
            Map<String, List<Map<String, Object>>> assignmentsBySite =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : assignmentRows) {
                assignmentsBySite.computeIfAbsent(string(edge.get("siteId")),
                        ignored -> new ArrayList<>()).add(edge);
            }

            int captureIndex = 0;
            for (Map.Entry<String, Map<String, Object>> obligationEntry
                    : obligationsBySite.entrySet()) {
                String site = obligationEntry.getKey();
                List<Map<String, Object>> candidates = assignmentsBySite.get(
                        site);
                if (candidates == null || candidates.isEmpty()) {
                    issues.add("REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                            + "ASSIGNMENT_RHS:" + site);
                    continue;
                }
                if (candidates.size() != 1) {
                    issues.add("AMBIGUOUS_EXACT_FIELD_ASSIGNMENT_RHS:"
                            + site + ":" + candidates.size());
                    continue;
                }
                Map<String, Object> edge = candidates.get(0);
                String method = string(edge.get("method"));
                String unit = string(edge.get("unit"));
                int unitIndex = integer(edge.get("unitIndex"), -1);
                int equals = unit.indexOf(" = ");
                String lhs = equals < 0 ? "" : unit.substring(0, equals)
                        .trim();
                String rhs = equals < 0 ? "" : unit.substring(equals + 3)
                        .trim();
                String ownerExpression = lhs.endsWith(lhsSuffix)
                        ? lhs.substring(0, lhs.length() - lhsSuffix.length())
                        .trim() : "";
                String rhsCell = string(edge.get("fromCell"));
                String edgeId = string(edge.get("id"));
                @SuppressWarnings("unchecked")
                List<String> obligationEdges = (List<String>)
                        obligationEntry.getValue().get("causalEdgeIds");
                boolean relationComplete = "value_flow".equals(
                        string(edge.get("relation")))
                        && Boolean.TRUE.equals(edge.get(
                        "semanticAssertionsAllowed"))
                        && Boolean.TRUE.equals(edge.get(
                        "eligibleForAutomaticSmt"))
                        && exactAssignmentRhsCell(rhsCell, rhs)
                        && obligationEdges != null
                        && obligationEdges.contains(edgeId);
                boolean exactEndpoint = field != null
                        && !method.isEmpty() && unitIndex >= 0
                        && site.equals(method + "#u" + unitIndex)
                        && !ownerExpression.isEmpty() && !rhs.isEmpty()
                        && !edgeId.isEmpty();
                if (!exactEndpoint) {
                    issues.add("MALFORMED_EXACT_FIELD_ASSIGNMENT_ENDPOINT:"
                            + site);
                }
                if (!relationComplete) {
                    issues.add("INCOMPLETE_FIELD_ASSIGNMENT_RHS_RELATION:"
                            + site);
                }
                bindings.add(object(
                        "captureKind", "FIELD_ASSIGNMENT_RHS",
                        "captureBindingId", outputPort + ".capture."
                                + captureIndex++,
                        "outputPort", outputPort,
                        "outputCell", outputCell,
                        "method", method,
                        "siteId", site,
                        "unitIndex", unitIndex,
                        "unit", unit,
                        "fieldSignature", outputCell,
                        "fieldOwnerExpression", ownerExpression,
                        "fieldOwnerCell", method + "::" + ownerExpression,
                        "fieldOwnerDeclaredType", field == null ? ""
                                : field.owner,
                        "fieldOwnerBindingKind", "INSTANCE_FIELD_LHS_BASE",
                        "fieldOwnerBindingAuthority",
                        "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_LHS",
                        "rhsExpression", rhs,
                        "rhsCell", rhsCell,
                        "rhsCausalEdgeId", edgeId,
                        "rhsRelation", string(edge.get("relation")),
                        "rhsRelationComplete", relationComplete,
                        "rhsRelationAuthority",
                        "STATIC_EXACT_HEAP_WRITE_VALUE_FLOW",
                        "causalEdgeId", edgeId,
                        "transferKind", "HEAP_WRITE",
                        "bindingKind", "field_write",
                        "bindingAuthority",
                        "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS",
                        "occurrence", 0,
                        "occurrenceAuthority",
                        "RUNTIME_INSTANCE_REFINEMENT_REQUIRED"));
            }
            for (String site : assignmentsBySite.keySet()) {
                if (!obligationsBySite.containsKey(site)) {
                    issues.add("FIELD_ASSIGNMENT_NOT_IN_TRANSFORMER_"
                            + "CONTRACT:" + site);
                }
            }

            Collections.sort(issues);
            boolean complete = issues.isEmpty()
                    && bindings.size() == obligationsBySite.size();
            return new OutputCaptureSelection(bindings, true, complete,
                    issues);
        }

        private boolean exactAssignmentRhsCell(String cell,
                                               String rhsExpression) {
            if (cell.isEmpty() || rhsExpression.isEmpty()) {
                return false;
            }
            if (cell.equals(rhsExpression)) {
                return true;
            }
            int local = cell.lastIndexOf("::");
            return local >= 0
                    && cell.substring(local + 2).equals(rhsExpression);
        }

        /**
         * Resolves a non-heap output formal back to the exact original call
         * argument that carries it.  The analysis graph intentionally has
         * several equivalent identity rows for one Java argument
         * ({@code caller_argument}, {@code method_caller_argument}, and
         * {@code call_argument}).  Only the canonical {@code call_argument}
         * row authorizes bytecode instrumentation; the other rows are causal
         * aliases and must not manufacture duplicate capture sites.
         *
         * <p>More than one exact call site is a valid static alternative.  A
         * concrete region instance later retains the observed alternative and
         * supplies its occurrence.  Missing or conflicting canonical rows are
         * fail-closed.</p>
         */
        private OutputCaptureSelection outputCaptureBindings(
                RegionDraft slice, String outputPort, String outputCell) {
            int argumentIndex = parameterIndex(outputCell);
            String callee = methodForCell(outputCell);
            List<Map<String, Object>> candidates = new ArrayList<>();
            List<String> issues = new ArrayList<>();
            if (argumentIndex < 0 || callee.isEmpty()) {
                issues.add("OUTPUT_FORMAL_IS_NOT_AN_EXACT_METHOD_ARGUMENT");
                return new OutputCaptureSelection(candidates, true, false,
                        issues);
            }

            Map<String, List<Map<String, Object>>> bySite =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : slice.causalEdges) {
                if (!"IDENTITY_BINDING".equals(string(edge.get(
                        "transferKind")))
                        || !outputCell.equals(string(edge.get("toCell")))
                        || !callee.equals(string(edge.get("invoke")))) {
                    continue;
                }
                String kind = string(edge.get("kind"));
                if (!("call_argument".equals(kind)
                        || "caller_argument".equals(kind)
                        || "method_caller_argument".equals(kind))) {
                    continue;
                }
                String caller = string(edge.get("method"));
                String siteId = string(edge.get("siteId"));
                int unitIndex = integer(edge.get("unitIndex"), -1);
                String fromCell = string(edge.get("fromCell"));
                if (caller.isEmpty() || siteId.isEmpty() || unitIndex < 0
                        || fromCell.isEmpty()
                        || !slice.methods.contains(caller)) {
                    issues.add("INCOMPLETE_CALL_ARGUMENT_ENDPOINT:"
                            + string(edge.get("id")));
                    continue;
                }
                String identity = caller + "\n" + siteId + "\n"
                        + unitIndex + "\n" + callee + "\n"
                        + argumentIndex;
                bySite.computeIfAbsent(identity,
                        ignored -> new ArrayList<>()).add(edge);
            }

            List<String> identities = sorted(bySite.keySet());
            int captureIndex = 0;
            for (String identity : identities) {
                List<Map<String, Object>> aliases = bySite.get(identity);
                List<Map<String, Object>> canonical = new ArrayList<>();
                for (Map<String, Object> alias : aliases) {
                    if ("call_argument".equals(string(alias.get("kind")))) {
                        canonical.add(alias);
                    }
                }
                if (canonical.size() != 1) {
                    issues.add((canonical.isEmpty()
                            ? "MISSING_CANONICAL_CALL_ARGUMENT:"
                            : "AMBIGUOUS_CANONICAL_CALL_ARGUMENT:")
                            + identity.replace('\n', '|'));
                    continue;
                }
                Map<String, Object> edge = canonical.get(0);
                candidates.add(object(
                        "captureBindingId", outputPort + ".capture."
                                + captureIndex++,
                        "outputPort", outputPort,
                        "outputCell", outputCell,
                        "callerMethod", string(edge.get("method")),
                        "siteId", string(edge.get("siteId")),
                        "unitIndex", integer(edge.get("unitIndex"), -1),
                        "unit", string(edge.get("unit")),
                        "calleeMethod", callee,
                        "argumentIndex", argumentIndex,
                        "argumentCell", string(edge.get("fromCell")),
                        "causalEdgeId", string(edge.get("id")),
                        "transferKind", "IDENTITY_BINDING",
                        "bindingKind", "call_argument",
                        "bindingAuthority",
                        "STATIC_EXACT_ORIGINAL_CALL_ARGUMENT",
                        "occurrence", 0,
                        "occurrenceAuthority",
                        "RUNTIME_INSTANCE_REFINEMENT_REQUIRED"));
            }
            if (candidates.isEmpty()) {
                issues.add("NO_EXACT_CALL_ARGUMENT_CAPTURE_BINDING");
            }
            return new OutputCaptureSelection(candidates, true,
                    !candidates.isEmpty() && issues.isEmpty(), issues);
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

        private String outputSliceFrontierPromotionReason(
                String cell, RegionDraft slice) {
            if (materializableOpaqueCallResult(cell, slice)) {
                return "OUTPUT_SLICE_OPAQUE_CALL_FRONTIER";
            }
            if (materializableDeclaredFieldPath(cell, slice)) {
                return "OUTPUT_SLICE_MATERIALIZABLE_FIELD_PATH_FRONTIER";
            }
            if (materializableDeclaredFieldAccess(cell, slice) != null) {
                return "OUTPUT_SLICE_MATERIALIZABLE_DECLARED_FIELD_FRONTIER";
            }
            return "";
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
            port.put("bindingMode", "FIELD_ACCESS");
            port.put("javaType", access.field.type);
            port.put("accessFieldSignature", access.field.signature);
            port.put("accessOwnerClass", access.field.owner);
            port.put("accessFieldType", access.field.type);
            port.put("accessField", access.field.name);
            if (access.accessorCall) {
                admitPostSelectionSliceMethod(slice,
                        access.accessorImplementationMethod);
                port.put("accessorCallerMethod", access.method);
                port.put("accessorCallSiteId", access.siteId);
                port.put("accessorCallUnitIndex", access.unitIndex);
                port.put("accessorDeclaredCallee", access.invokedMethod);
                port.put("accessorImplementationMethod",
                        access.accessorImplementationMethod);
                port.put("accessorImplementationAuthority",
                        "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
                port.put("accessorCallSiteAuthority",
                        "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                                + "ACCESSOR_CALLSITE_V1");
            } else {
                port.put("accessMethod", access.method);
                port.put("accessSiteId", access.siteId);
                port.put("accessUnitIndex", access.unitIndex);
                port.put("accessSiteAuthority",
                        "STATIC_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1");
            }
            port.put("fieldPath", Collections.singletonList(
                    access.field.name));
            port.put("leafFieldSignature", access.field.signature);
            port.put("leafOwnerClass", access.field.owner);
            port.put("leafField", access.field.name);
        }

        private void addDeclaredFieldPathMaterializationMetadata(
                Map<String, Object> port,
                DeclaredFieldPathAccess access) {
            port.put("bindingMode", "FIELD_ACCESS");
            port.put("javaType", access.leafField.type);
            port.put("accessFieldSignature", access.rootField.signature);
            port.put("accessOwnerClass", access.rootField.owner);
            port.put("accessFieldType", access.rootField.type);
            port.put("accessField", access.rootField.name);
            port.put("accessMethod", access.method);
            port.put("accessSiteId", access.siteId);
            port.put("accessUnitIndex", access.unitIndex);
            port.put("accessSiteAuthority",
                    "STATIC_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1");
            port.put("fieldPath", access.fieldPath);
            port.put("leafFieldSignature", access.leafField.signature);
            port.put("leafOwnerClass", access.leafField.owner);
            port.put("leafFieldType", access.leafField.type);
            port.put("leafField", access.leafField.name);
            port.put("fieldPathProofCausalEdgeIds", access.proofEdgeIds);
            port.put("fieldPathAuthority",
                    "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        }

        /**
         * Carries an exact accessor site onto an already-selected canonical
         * declared-field region input.  Broad exception/guard frontiers are
         * built before requested-output slices, so relying only on output
         * promotion metadata leaves a directly selected field without the
         * site evidence that the runtime trace needs to identify its owner.
         *
         * <p>The authority is deliberately narrow: exactly one eligible
         * {@code accessor_field_return} edge in this region's causal slice
         * must match the complete declared field tuple, caller, canonical
         * unit/site, declared callee and Soot-resolved implementation.  A
         * direct getfield, a duplicate accessor edge, or any malformed tuple
         * leaves the input unchanged.</p>
         */
        private void addRegionInputAccessorMaterializationMetadata(
                Map<String, Object> port, String cell, RegionDraft region) {
            DeclaredFieldPathAccess pathAccess =
                    materializableDeclaredFieldPathAccess(cell, region);
            if (pathAccess != null) {
                addDeclaredFieldPathMaterializationMetadata(port,
                        pathAccess);
                return;
            }
            DeclaredFieldIdentity field = declaredField(cell);
            if (field == null || !closedProtocolScalarType(field.type)) {
                return;
            }
            DeclaredFieldAccess selected = null;
            for (Map<String, Object> edge : region.causalEdges) {
                DeclaredFieldAccess access = declaredFieldAccessAtEdge(edge,
                        field, region);
                if (access == null || !access.accessorCall
                        || !field.type.equals(declaredReturnType(
                        access.invokedMethod))
                        || !field.type.equals(declaredReturnType(
                        access.accessorImplementationMethod))
                        || !methodSubSignature(access.invokedMethod).equals(
                        methodSubSignature(
                                access.accessorImplementationMethod))) {
                    continue;
                }
                if (selected != null) {
                    return;
                }
                selected = access;
            }
            if (selected == null) {
                return;
            }
            port.put("bindingMode", "FIELD_ACCESS");
            port.put("javaType", field.type);
            port.put("accessFieldSignature", field.signature);
            port.put("accessOwnerClass", field.owner);
            port.put("accessFieldType", field.type);
            port.put("accessField", field.name);
            port.put("accessorCallerMethod", selected.method);
            port.put("accessorCallSiteId", selected.siteId);
            port.put("accessorCallUnitIndex", selected.unitIndex);
            port.put("accessorDeclaredCallee", selected.invokedMethod);
            port.put("accessorImplementationMethod",
                    selected.accessorImplementationMethod);
            port.put("accessorImplementationAuthority",
                    "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
            port.put("accessorCallSiteAuthority",
                    "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                            + "ACCESSOR_CALLSITE_V1");
            port.put("fieldPath", Collections.singletonList(field.name));
            port.put("leafFieldSignature", field.signature);
            port.put("leafOwnerClass", field.owner);
            port.put("leafField", field.name);
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
            if (cell.contains("#field:")) {
                DeclaredFieldPathAccess access =
                        materializableDeclaredFieldPathAccess(cell, slice);
                boolean pathConstrained = !string(port.get(
                        "fieldPathAuthority")).isEmpty();
                if (access != null || pathConstrained) {
                    return access != null
                        && access.rootField.signature.equals(string(port.get(
                        "accessFieldSignature")))
                        && access.leafField.signature.equals(string(port.get(
                        "leafFieldSignature")))
                        && access.method.equals(string(port.get(
                        "accessMethod")))
                        && access.siteId.equals(string(port.get(
                        "accessSiteId")))
                        && access.unitIndex == integer(port.get(
                        "accessUnitIndex"), -1)
                        && access.fieldPath.equals(strings(port.get(
                        "fieldPath")))
                        && "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1"
                        .equals(string(port.get("fieldPathAuthority")));
                }
            }
            String directAuthority = string(port.get("accessSiteAuthority"));
            String accessorAuthority = string(port.get(
                    "accessorCallSiteAuthority"));
            boolean constrained = !directAuthority.isEmpty()
                    || !accessorAuthority.isEmpty()
                    || "OUTPUT_SLICE_MATERIALIZABLE_DECLARED_FIELD_FRONTIER"
                    .equals(string(port.get("selectionReason")));
            if (!constrained) {
                return true;
            }
            return matchingPromotedDeclaredFieldAccess(cell, port, slice)
                    != null;
        }

        /**
         * A projected dependency may deliberately resolve to a different
         * canonical cell.  In that case the exact alias walk, rather than a
         * second direct-access comparison against the original projection,
         * is the compatibility proof.  Still require the selected terminal
         * to carry executable leaf metadata so the weaker projected-port
         * fallback cannot bypass the ordinary materialization checks.
         */
        private boolean exactMaterializableAliasResolution(
                InputPortResolution resolution,
                List<Map<String, Object>> inputPorts) {
            if (resolution == null
                    || !"UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN".equals(
                    resolution.authority)) {
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
            internallyDerivedTargetsByRegion.remove(slice);
            callResultsWithCausalAlternativeByRegion.remove(slice);
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

        /**
         * Revalidates a shared promoted field port against the dependency in
         * one particular requested-output slice.  Metadata on the port is not
         * authority by itself: it must exactly reproduce the field access
         * proven by this slice's causal edge.
         */
        private DeclaredFieldAccess matchingPromotedDeclaredFieldAccess(
                String cell, Map<String, Object> port, RegionDraft slice) {
            DeclaredFieldIdentity field = declaredField(cell);
            if (field == null
                    || !field.signature.equals(string(port.get(
                    "accessFieldSignature")))) {
                return null;
            }
            String directAuthority = string(port.get("accessSiteAuthority"));
            String accessorAuthority = string(port.get(
                    "accessorCallSiteAuthority"));
            DeclaredFieldAccess selected = null;
            for (Map<String, Object> edge : slice.causalEdges) {
                DeclaredFieldAccess access = declaredFieldAccessAtEdge(
                        edge, field, slice);
                if (access == null) {
                    continue;
                }
                boolean matches;
                if (access.accessorCall) {
                    matches = "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                            .concat("ACCESSOR_CALLSITE_V1").equals(
                                    accessorAuthority)
                            && access.method.equals(string(port.get(
                            "accessorCallerMethod")))
                            && access.siteId.equals(string(port.get(
                            "accessorCallSiteId")))
                            && access.unitIndex == integer(port.get(
                            "accessorCallUnitIndex"), -1)
                            && access.invokedMethod.equals(string(port.get(
                            "accessorDeclaredCallee")))
                            && access.accessorImplementationMethod.equals(
                            string(port.get(
                                    "accessorImplementationMethod")))
                            && "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY"
                            .equals(string(port.get(
                                    "accessorImplementationAuthority")));
                } else {
                    matches = "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                            .concat("READ_SITE_V1").equals(directAuthority)
                            && access.method.equals(string(port.get(
                            "accessMethod")))
                            && access.siteId.equals(string(port.get(
                            "accessSiteId")))
                            && access.unitIndex == integer(port.get(
                            "accessUnitIndex"), -1);
                }
                if (!matches) {
                    continue;
                }
                if (selected != null) {
                    // Duplicate exact rows make even the port-selected site
                    // non-unique; retain the fail-closed behavior.
                    return null;
                }
                selected = access;
            }
            return selected;
        }

        private DeclaredFieldAccess declaredFieldAccessAtEdge(
                Map<String, Object> edge, DeclaredFieldIdentity field,
                RegionDraft slice) {
            if (!field.signature.equals(string(edge.get("fromCell")))
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
                    || accessorCall && (implementation.isEmpty()
                    || !"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY"
                    .equals(string(edge.get(
                            "accessorImplementationAuthority"))))
                    || !accessorCall && !kind.contains("field_read")) {
                return null;
            }
            return new DeclaredFieldAccess(field, method, siteId, unitIndex,
                    accessorCall, invokedMethod, implementation);
        }

        /**
         * A bare canonical field is materializable only when the selected
         * output slice contains one exact, owner-resolved read of that field.
         * Requiring one static access site prevents a region-wide action from
         * silently matching an unrelated read of the same inherited field.
         * Repeated runtime occurrences at that one site remain valid and are
         * separated by the runtime object/map-entry identity machinery.
         */
        private DeclaredFieldAccess materializableDeclaredFieldAccess(
                String cell, RegionDraft slice) {
            DeclaredFieldIdentity field = declaredField(cell);
            if (field == null || !closedProtocolScalarType(field.type)) {
                return null;
            }

            DeclaredFieldAccess selected = null;
            for (Map<String, Object> edge : slice.causalEdges) {
                if (!cell.equals(string(edge.get("fromCell")))
                        || !"HEAP_READ".equals(string(edge.get(
                        "transferKind")))) {
                    continue;
                }
                String method = string(edge.get("method"));
                String siteId = string(edge.get("siteId"));
                String kind = string(edge.get("kind"));
                String invokedMethod = string(edge.get("invoke"));
                boolean accessorCall = kind.contains("accessor")
                        && kind.contains("field_return");
                String accessorImplementationMethod = string(edge.get(
                        "accessorImplementationMethod"));
                int unitIndex = integer(edge.get("unitIndex"), -1);
                if (!slice.methods.contains(method)
                        || !exactStaticValueFlow(edge)
                        || !declaredMetadataMatches(edge, field)
                        || method.isEmpty() || unitIndex < 0
                        || !siteId.equals(method + "#u" + unitIndex)
                        || string(edge.get("toCell")).isEmpty()
                        || accessorCall != !invokedMethod.isEmpty()
                        || accessorCall && (accessorImplementationMethod
                        .isEmpty()
                        || !"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY"
                        .equals(string(edge.get(
                                "accessorImplementationAuthority"))))
                        || !accessorCall && !kind.contains("field_read")) {
                    return null;
                }
                DeclaredFieldAccess candidate = new DeclaredFieldAccess(
                        field, method, siteId, unitIndex, accessorCall,
                        invokedMethod, accessorImplementationMethod);
                if (selected != null
                        && (!selected.method.equals(candidate.method)
                        || !selected.siteId.equals(candidate.siteId)
                        || selected.unitIndex != candidate.unitIndex
                        || selected.accessorCall != candidate.accessorCall
                        || !selected.invokedMethod.equals(
                        candidate.invokedMethod)
                        || !selected.accessorImplementationMethod.equals(
                        candidate.accessorImplementationMethod))) {
                    return null;
                }
                selected = candidate;
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
            DeclaredFieldIdentity field = declaredField(root);
            if (field == null || closedProtocolScalarType(field.type)
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
            DeclaredFieldIdentity rootField = declaredField(rootCell);
            List<String> suffixSegments = fieldPathSegments(suffix);
            if (rootField == null || closedProtocolScalarType(rootField.type)
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
                    rootProjection, "field_read", rootField.signature,
                    string(rootProjection.get("objectToCell")));
            if (rootDeclaredRead == null
                    || !exactDeclaredGetfieldUnit(rootDeclaredRead,
                    rootField, "")) {
                return null;
            }

            List<String> fullPath = new ArrayList<>();
            fullPath.add(rootField.name);
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
                    accessOwnerCell + "#field:" + rootField.name,
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
            String expectedOwner = rootField.type;
            List<String> remaining = new ArrayList<>(suffixSegments);
            DeclaredFieldIdentity leafField = null;

            while (!remaining.isEmpty()) {
                String segment = remaining.get(0);
                List<String> tail = new ArrayList<>(remaining.subList(1,
                        remaining.size()));
                if (tail.isEmpty()) {
                    List<Map<String, Object>[]> pairs =
                            exactDirectFieldReadPairs(slice, currentLocal,
                                    expectedOwner, segment);
                    if (pairs.size() != 1) {
                        return null;
                    }
                    Map<String, Object>[] pair = pairs.get(0);
                    leafField = declaredField(string(pair[0].get(
                            "fromCell")));
                    if (leafField == null
                            || !directFieldLeafType(leafField.type)) {
                        return null;
                    }
                    aliases.add(leafField.signature);
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
                List<Map<String, Object>> declaredReads =
                        exactParallelDeclaredReads(instanceRead,
                                expectedOwner, segment);
                if (declaredReads.size() != 1) {
                    return null;
                }
                Map<String, Object> declaredRead = declaredReads.get(0);
                DeclaredFieldIdentity field = declaredField(string(
                        declaredRead.get("fromCell")));
                if (field == null
                        || !exactDeclaredGetfieldUnit(instanceRead, field,
                        currentLocal)) {
                    return null;
                }
                String canonicalProjectionCell = field.signature
                        + tailSuffix;
                Map<String, Object> declaredProjection =
                        uniqueExactProjection(slice,
                                "projected_field_read",
                                canonicalProjectionCell, field.signature,
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
                expectedOwner = field.type;
                remaining = tail;
            }
            if (leafField == null || proofIds.contains("")) {
                return null;
            }
            return new DeclaredFieldPathAccess(cell, rootField, leafField,
                    string(rootDeclaredRead.get("method")),
                    string(rootDeclaredRead.get("siteId")), integer(
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
            Map<String, Object> selected = null;
            for (Map<String, Object> edge : edges) {
                if (!baseId.equals(string(edge.get("id")))) {
                    continue;
                }
                if (selected != null || !kind.equals(string(edge.get(
                        "kind"))) || !exactStaticEdge(edge)
                        || !"HEAP_READ".equals(string(edge.get(
                        "transferKind")))
                        || !"value_flow".equals(string(edge.get(
                        "relation")))
                        || !fromCell.equals(string(edge.get("fromCell")))
                        || !toCell.equals(string(edge.get("toCell")))
                        || !sameExactReadSite(projection, edge)) {
                    return null;
                }
                selected = edge;
            }
            return selected;
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
                Map<String, Object> edge, DeclaredFieldIdentity field,
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
                        + owner + "." + field.signature);
            }
            return unit.matches("^" + Pattern.quote(target)
                    + " = [$A-Za-z_][$A-Za-z0-9_]*\\."
                    + Pattern.quote(field.signature) + "$");
        }

        @SuppressWarnings("unchecked")
        private List<Map<String, Object>[]> exactDirectFieldReadPairs(
                RegionDraft slice, String ownerCell, String expectedOwner,
                String fieldName) {
            List<Map<String, Object>[]> result = new ArrayList<>();
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
                List<Map<String, Object>> declared =
                        exactParallelDeclaredReads(instance, expectedOwner,
                                fieldName);
                if (declared.size() == 1) {
                    result.add(new Map[]{declared.get(0), instance});
                }
            }
            return result;
        }

        private List<Map<String, Object>> exactParallelDeclaredReads(
                Map<String, Object> instance, String expectedOwner,
                String fieldName) {
            List<Map<String, Object>> result = new ArrayList<>();
            for (Map<String, Object> edge : edges) {
                DeclaredFieldIdentity field = declaredField(string(edge.get(
                        "fromCell")));
                if (field == null || !expectedOwner.equals(field.owner)
                        || !fieldName.equals(field.name)
                        || !"field_read".equals(string(edge.get("kind")))
                        || !exactStaticEdge(edge)
                        || !"HEAP_READ".equals(string(edge.get(
                        "transferKind")))
                        || !"value_flow".equals(string(edge.get(
                        "relation")))
                        || !string(instance.get("toCell")).equals(string(
                        edge.get("toCell")))
                        || !sameExactReadSite(instance, edge)
                        || !exactDeclaredGetfieldUnit(edge, field, "")) {
                    continue;
                }
                result.add(edge);
            }
            return result;
        }

        private void addProofEdgeIds(Set<String> target,
                                     Map<String, Object>... proofEdges) {
            for (Map<String, Object> edge : proofEdges) {
                target.add(string(edge.get("id")));
            }
        }

        /**
         * Recognizes a scalar formal that is an actual outbound inter-region
         * endpoint, rather than merely another parameter in a large sink
         * method.  The exact-cell and outside-region checks are intentional:
         * a textual protocol-looking name or an internal synchronous handoff
         * is not sufficient authority for a demand slice.
         */
        private boolean outboundProtocolScalarArgument(
                RegionDraft region, Map<String, Object> output,
                String outputCell) {
            if (!"SINK_STATE".equals(string(output.get("kind")))) {
                return false;
            }
            return outboundProtocolScalarCell(region, outputCell);
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
            for (Map<String, Object> edge : edges) {
                if (!isBoundary(edge)
                        || !outputCell.equals(string(edge.get("fromCell")))) {
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
            for (Map<String, Object> edge : edges) {
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
                    && !Boolean.TRUE.equals(edge.get("mappingOnly"))
                    && Boolean.TRUE.equals(edge.get(
                    "semanticAssertionsAllowed"))
                    && Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticDerivation"))
                    && Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticSmt"))
                    && "backward_provenance".equals(string(edge.get(
                    "direction")))
                    && !string(edge.get("id")).isEmpty();
        }

        /** Strict scalar allow-list; arrays, streams, maps, and opaque objects
         * deliberately do not become protocol-output demand roots. */
        private boolean closedProtocolScalarType(String type) {
            return "boolean".equals(type)
                    || "byte".equals(type)
                    || "short".equals(type)
                    || "int".equals(type)
                    || "long".equals(type)
                    || "char".equals(type)
                    || "float".equals(type)
                    || "double".equals(type)
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
            for (Map<String, Object> edge : analysisEdges(slice)) {
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

        private List<Map<String, Object>> causalEdgeReferences(
                Set<Map<String, Object>> selected) {
            List<Map<String, Object>> ordered = new ArrayList<>(selected);
            ordered.sort(Comparator.comparing(edge -> string(edge.get("id"))));
            List<Map<String, Object>> result = new ArrayList<>();
            for (Map<String, Object> edge : ordered) {
                Map<String, Object> reference = object(
                        "edgeId", string(edge.get("id")),
                        "method", string(edge.get("method")),
                        "siteId", string(edge.get("siteId")),
                        "fromCell", string(edge.get("fromCell")),
                        "toCell", string(edge.get("toCell")),
                        "transferKind", string(edge.get("transferKind")),
                        "kind", string(edge.get("kind")));
                copyStructuredGuardMetadata(edge, reference);
                result.add(reference);
            }
            return result;
        }

        private void copyStructuredGuardMetadata(
                Map<String, Object> source, Map<String, Object> target) {
            String[] scalarFields = {
                    "guardSiteId", "guardedMutationSiteId",
                    "guardedMutationsAuthority"
            };
            for (String field : scalarFields) {
                String value = string(source.get(field));
                if (!value.isEmpty()) {
                    target.put(field, value);
                }
            }
            Object requiredOutcome = source.get("requiredOutcome");
            if (requiredOutcome instanceof Boolean) {
                target.put("requiredOutcome", requiredOutcome);
            }
            Object guardedMutationCount = source.get(
                    "guardedMutationCount");
            if (guardedMutationCount instanceof Number) {
                target.put("guardedMutationCount", guardedMutationCount);
            }
            Object guardedMutations = source.get("guardedMutations");
            if (guardedMutations instanceof Collection<?>) {
                List<Map<String, Object>> rows = new ArrayList<>();
                for (Object value : (Collection<?>) guardedMutations) {
                    if (!(value instanceof Map<?, ?>)) {
                        continue;
                    }
                    Map<?, ?> item = (Map<?, ?>) value;
                    Map<String, Object> row = object(
                            "guardSiteId", string(item.get("guardSiteId")),
                            "guardedMutationSiteId", string(item.get(
                            "guardedMutationSiteId")),
                            "method", string(item.get("method")),
                            "unitIndex", item.get("unitIndex"));
                    Object outcome = item.get("requiredOutcome");
                    if (outcome instanceof Boolean) {
                        row.put("requiredOutcome", outcome);
                    }
                    rows.add(row);
                }
                target.put("guardedMutations", rows);
            }
        }

        /**
         * Declares only writes whose target is the exact requested heap cell.
         * Other HEAP_WRITE rows can be causal prerequisites (for example a
         * boolean configuration field feeding a later guard), but they are
         * not transformers of this requested state and must not become
         * runtime heap-effect obligations.
         *
         * <p>A semantic-field alias without an exact target row is retained as
         * an explicit contract issue.  This keeps the contract fail-closed
         * instead of allowing the importer to guess receiver aliasing.</p>
         */
        private RequestedStateTransformerContract
        requestedStateTransformerContract(RegionDraft slice,
                                          String outputPort,
                                          String outputCell) {
            Map<String, Map<String, Object>> obligations =
                    new LinkedHashMap<>();
            List<String> issues = new ArrayList<>();
            String outputField = semanticFieldKey(outputCell,
                    slice.rootMethod);
            if (outputPort.isEmpty() || outputCell.isEmpty()
                    || outputField.isEmpty()) {
                issues.add("REQUESTED_HEAP_OUTPUT_HAS_NO_EXACT_FIELD_IDENTITY");
            }
            for (Map<String, Object> edge : slice.causalEdges) {
                if (!"HEAP_WRITE".equals(string(edge.get(
                        "transferKind")))) {
                    continue;
                }
                String target = string(edge.get("toCell"));
                String targetField = semanticFieldKey(target,
                        slice.rootMethod);
                if (!outputCell.equals(target)) {
                    if (!outputField.isEmpty()
                            && outputField.equals(targetField)) {
                        issues.add("NON_EXACT_REQUESTED_STATE_WRITE_TARGET:"
                                + firstNonEmpty(string(edge.get("id")),
                                string(edge.get("siteId"))));
                    }
                    continue;
                }
                String site = string(edge.get("siteId"));
                String method = string(edge.get("method"));
                String edgeId = string(edge.get("id"));
                if (site.isEmpty() || method.isEmpty()
                        || edgeId.isEmpty()) {
                    issues.add("MALFORMED_REQUESTED_STATE_TRANSFORMER:"
                            + firstNonEmpty(edgeId, site));
                    continue;
                }
                Map<String, Object> obligation = obligations.get(site);
                if (obligation == null) {
                    obligation = object(
                            "siteId", site,
                            "method", method,
                            "targetCell", target,
                            "transferKind", "HEAP_WRITE",
                            "kind", string(edge.get("kind")),
                            "causalEdgeIds", new ArrayList<String>(),
                            "authority",
                            "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL");
                    obligations.put(site, obligation);
                } else if (!method.equals(string(obligation.get("method")))
                        || !target.equals(string(obligation.get(
                        "targetCell")))) {
                    issues.add("CONFLICTING_REQUESTED_STATE_TRANSFORMER:"
                            + site);
                    continue;
                }
                @SuppressWarnings("unchecked")
                List<String> edgeIds = (List<String>) obligation.get(
                        "causalEdgeIds");
                if (!edgeIds.contains(edgeId)) {
                    edgeIds.add(edgeId);
                }
            }
            List<Map<String, Object>> ordered = new ArrayList<>(
                    obligations.values());
            ordered.sort(Comparator.comparing(value -> string(
                    value.get("siteId"))));
            for (Map<String, Object> obligation : ordered) {
                @SuppressWarnings("unchecked")
                List<String> edgeIds = (List<String>) obligation.get(
                        "causalEdgeIds");
                Collections.sort(edgeIds);
            }
            Collections.sort(issues);
            boolean complete = !slice.truncated && issues.isEmpty();
            return new RequestedStateTransformerContract(outputPort,
                    outputCell, ordered, issues, complete, true);
        }

        /**
         * Computes the complete set of exact requested-state transformer
         * sites reachable from one input.  A binding is exclusive only when
         * every reachable edge into the output cell is either an exact
         * transformer or a structured guard for exact transformers.  The
         * importer may use such a binding to prove a missing input inactive;
         * any unclassified output edge keeps the input required.
         */
        private InputTransformerSinks requestedStateTransformerSinks(
                String input, String outputCell, RegionDraft slice,
                RequestedStateTransformerContract contract) {
            Set<String> obligationSites = new LinkedHashSet<>();
            for (Map<String, Object> obligation : contract.obligations) {
                obligationSites.add(string(obligation.get("siteId")));
            }
            Set<String> transformerSites = new LinkedHashSet<>();
            Set<String> guardSites = new LinkedHashSet<>();
            Set<String> unclassified = new LinkedHashSet<>();
            if (input.isEmpty() || outputCell.isEmpty()
                    || input.equals(outputCell)) {
                return new InputTransformerSinks(transformerSites,
                        guardSites, unclassified, contract.complete, false);
            }

            Map<String, List<Map<String, Object>>> outgoing =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : slice.causalEdges) {
                String from = string(edge.get("fromCell"));
                if (!from.isEmpty()) {
                    outgoing.computeIfAbsent(from,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
            Deque<String> queue = new ArrayDeque<>();
            Set<String> seen = new LinkedHashSet<>();
            queue.add(input);
            seen.add(input);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                List<Map<String, Object>> next = outgoing.get(current);
                if (next == null) {
                    continue;
                }
                for (Map<String, Object> edge : next) {
                    String target = string(edge.get("toCell"));
                    if (outputCell.equals(target)) {
                        String site = string(edge.get("siteId"));
                        if ("HEAP_WRITE".equals(string(edge.get(
                                "transferKind")))
                                && obligationSites.contains(site)) {
                            transformerSites.add(site);
                            continue;
                        }
                        if ("heap_mutation_path_guard".equals(string(
                                edge.get("kind")))) {
                            Set<String> guarded = guardedMutationSites(edge);
                            if (!guarded.isEmpty()
                                    && obligationSites.containsAll(guarded)) {
                                transformerSites.addAll(guarded);
                                String guardSite = firstNonEmpty(string(
                                        edge.get("guardSiteId")), site);
                                if (!guardSite.isEmpty()) {
                                    guardSites.add(guardSite);
                                }
                                continue;
                            }
                        }
                        unclassified.add(firstNonEmpty(string(edge.get("id")),
                                site));
                        continue;
                    }
                    if (!target.isEmpty() && seen.add(target)) {
                        queue.addLast(target);
                    }
                }
            }
            boolean complete = contract.complete;
            boolean exclusive = complete && !transformerSites.isEmpty()
                    && unclassified.isEmpty();
            return new InputTransformerSinks(transformerSites, guardSites,
                    unclassified, complete, exclusive);
        }

        private Set<String> guardedMutationSites(Map<String, Object> edge) {
            Set<String> result = new LinkedHashSet<>();
            Object values = edge.get("guardedMutations");
            if (values instanceof Collection<?>) {
                for (Object value : (Collection<?>) values) {
                    if (value instanceof Map<?, ?>) {
                        String site = string(((Map<?, ?>) value).get(
                                "guardedMutationSiteId"));
                        if (!site.isEmpty()) {
                            result.add(site);
                        }
                    }
                }
            }
            String singular = string(edge.get("guardedMutationSiteId"));
            if (!singular.isEmpty()) {
                result.add(singular);
            }
            return result;
        }

        /**
         * Finds fresh, zero-argument constructed objects whose allocation has
         * a complete forward value-flow path to the requested heap output.
         * The planner records allocation/constructor/path proof only; API
         * semantics such as "a fresh HashMap is empty" remain the importer's
         * project-independent responsibility.
         */
        private List<Map<String, Object>> heapInitializers(
                RegionDraft slice, String outputPort, String outputCell) {
            List<Map<String, Object>> allocations = new ArrayList<>();
            for (Map<String, Object> edge : slice.causalEdges) {
                String from = string(edge.get("fromCell"));
                if (!from.startsWith("new ")
                        || integer(edge.get(
                        "allocationConstructorArgumentCount"), -1) != 0
                        || string(edge.get("allocationConstructor")).isEmpty()
                        || !"JIMPLE_SPECIALINVOKE_ON_FRESH_LOCAL".equals(
                        string(edge.get("allocationConstructorEvidence")))) {
                    continue;
                }
                allocations.add(edge);
            }
            allocations.sort(Comparator.comparing(edge -> firstNonEmpty(
                    string(edge.get("id")), string(edge.get("siteId")))));

            List<Map<String, Object>> result = new ArrayList<>();
            for (Map<String, Object> allocation : allocations) {
                if (result.size() >= MAX_PORTS) {
                    break;
                }
                String allocatedValue = string(allocation.get("toCell"));
                List<Map<String, Object>> path = forwardCausalPath(
                        allocatedValue, outputCell, slice.causalEdges);
                if (!allocatedValue.equals(outputCell) && path.isEmpty()) {
                    continue;
                }
                List<String> proofEdges = new ArrayList<>();
                String allocationEdgeId = string(allocation.get("id"));
                if (!allocationEdgeId.isEmpty()) {
                    proofEdges.add(allocationEdgeId);
                }
                for (Map<String, Object> edge : path) {
                    String id = string(edge.get("id"));
                    if (!id.isEmpty() && !proofEdges.contains(id)) {
                        proofEdges.add(id);
                    }
                }
                result.add(object(
                        "initializerId", "STATIC_INIT." + slice.regionId
                                + "." + result.size(),
                        "kind", "FRESH_DEFAULT_CONSTRUCTED_OBJECT",
                        "allocatedType", firstNonEmpty(
                                string(allocation.get("allocationType")),
                                string(allocation.get("fromCell"))
                                        .substring("new ".length())),
                        "allocationCell", string(allocation.get("fromCell")),
                        "allocationValueCell", allocatedValue,
                        "allocationEdgeId", string(allocation.get("id")),
                        "allocationMethod", string(allocation.get("method")),
                        "allocationSiteId", string(allocation.get("siteId")),
                        "allocationUnitIndex", integer(
                                allocation.get("unitIndex"), -1),
                        "constructor", string(allocation.get(
                                "allocationConstructor")),
                        "constructorArgumentCount", 0,
                        "constructorSiteId", string(allocation.get(
                                "allocationConstructorSiteId")),
                        "constructorUnitIndex", integer(allocation.get(
                                "allocationConstructorUnitIndex"), -1),
                        "outputPort", outputPort,
                        "outputCell", outputCell,
                        "proofEdgeIds", proofEdges,
                        "proofComplete", true,
                        "selectionAuthority",
                        "STATIC_ALLOCATION_CONSTRUCTOR_AND_FORWARD_CAUSAL_PATH",
                        "captureBoundaryRequirement",
                        "REGION_ROOT_ENTRY_PRECEDES_ALLOCATION"));
            }
            return result;
        }

        private List<Map<String, Object>> forwardCausalPath(
                String start, String target,
                Set<Map<String, Object>> causalEdges) {
            if (start.isEmpty() || target.isEmpty() || start.equals(target)) {
                return Collections.emptyList();
            }
            Map<String, List<Map<String, Object>>> outgoing =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : causalEdges) {
                String from = string(edge.get("fromCell"));
                if (!from.isEmpty()) {
                    outgoing.computeIfAbsent(from,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
            for (List<Map<String, Object>> values : outgoing.values()) {
                values.sort(Comparator.comparing(edge -> firstNonEmpty(
                        string(edge.get("id")), string(edge.get("siteId")))));
            }

            Deque<String> queue = new ArrayDeque<>();
            Set<String> seen = new LinkedHashSet<>();
            Map<String, String> previousCell = new LinkedHashMap<>();
            Map<String, Map<String, Object>> previousEdge =
                    new LinkedHashMap<>();
            queue.add(start);
            seen.add(start);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                List<Map<String, Object>> nextEdges = outgoing.get(current);
                if (nextEdges == null) {
                    continue;
                }
                for (Map<String, Object> edge : nextEdges) {
                    String next = string(edge.get("toCell"));
                    if (next.isEmpty() || !seen.add(next)) {
                        continue;
                    }
                    previousCell.put(next, current);
                    previousEdge.put(next, edge);
                    if (target.equals(next)) {
                        List<Map<String, Object>> reversed = new ArrayList<>();
                        String cursor = target;
                        while (!start.equals(cursor)) {
                            Map<String, Object> step = previousEdge.get(cursor);
                            if (step == null) {
                                return Collections.emptyList();
                            }
                            reversed.add(step);
                            cursor = previousCell.get(cursor);
                        }
                        Collections.reverse(reversed);
                        return reversed;
                    }
                    queue.addLast(next);
                }
            }
            return Collections.emptyList();
        }

        private RegionDraft outputSlice(RegionDraft region,
                                        String outputCell) {
            RegionDraft slice = new RegionDraft(region.anchorMethod);
            slice.regionId = region.regionId;
            slice.rootMethod = region.rootMethod;
            slice.exceptionDirected = true;
            slice.inheritedRegionTruncated = region.truncated;
            // The broad region frontier has its own 64-method budget.  This
            // requested-output walk is rebuilt from the full static graph and
            // is governed by the independent exact-slice budgets below, so a
            // broad-frontier truncation is diagnostic metadata rather than an
            // inherited completeness failure.
            slice.truncated = false;

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
            admitExactAccessorImplementationMethods(slice);
            slice.methodBudgetTruncated = slice.methods.size()
                    > MAX_REQUESTED_OUTPUT_SLICE_METHODS;
            slice.truncated = slice.methodBudgetTruncated
                    || slice.causalCellBudgetTruncated;
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
                DeclaredFieldIdentity field = declaredField(
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
                        || !"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY"
                        .equals(string(edge.get(
                                "accessorImplementationAuthority")))
                        || !plansByMethod.containsKey(implementation)
                        || declaredSubSignature.isEmpty()
                        || !declaredSubSignature.equals(
                                implementationSubSignature)
                        || !field.type.equals(
                                declaredReturnType(declaredCallee))
                        || !field.type.equals(
                                declaredReturnType(implementation))) {
                    continue;
                }
                String identity = field.signature + "\n" + caller + "\n"
                        + siteId + "\n" + unitIndex + "\n"
                        + declaredCallee + "\n" + implementation;
                if (!admitted.add(identity)) {
                    continue;
                }
                slice.methods.add(implementation);
                slice.accessorImplementationAdmissions.add(object(
                        "declaredFieldSignature", field.signature,
                        "declaredFieldOwner", field.owner,
                        "declaredFieldType", field.type,
                        "declaredFieldName", field.name,
                        "callerMethod", caller,
                        "siteId", siteId,
                        "unitIndex", unitIndex,
                        "declaredCallee", declaredCallee,
                        "implementationMethod", implementation,
                        "implementationAuthority",
                        "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY",
                        "admissionAuthority",
                        "STATIC_EXACT_ACCESSOR_CALL_IMPLEMENTATION_V1"));
            }
            slice.accessorImplementationAdmissions.sort(
                    Comparator.comparing(admission ->
                            string(admission.get("callerMethod")) + "\n"
                                    + string(admission.get("siteId")) + "\n"
                                    + string(admission.get(
                                    "declaredFieldSignature")) + "\n"
                                    + string(admission.get(
                                    "implementationMethod"))));
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
            if (!rootMethod.isEmpty() && plansByMethod.containsKey(rootMethod)) {
                reachable.add(rootMethod);
                queue.add(rootMethod);
            }
            while (!queue.isEmpty()
                    && reachable.size() <= plansByMethod.size()) {
                String method = queue.removeFirst();
                for (String callee : values(calleesByCaller.get(method))) {
                    if (plansByMethod.containsKey(callee)
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
            boolean syntheticProjection = syntheticValueProjection(cell);
            // An exact port cell is already the canonical boundary value.
            // Do not walk its own projected aliases and then downgrade that
            // identity into another representation of the same leaf.
            for (Map<String, Object> input : inputPorts) {
                if (cell.equals(string(input.get("cell")))) {
                    // A local projection is not a definition on its own.
                    // It may nevertheless be the canonical port when that
                    // port carries the complete exact field-access action.
                    // A non-executable exact label must still resolve to a
                    // different materializable alias below.
                    if (!cell.contains("#field:")
                            || exactAliasMaterializationPort(input)) {
                        return new InputPortResolution(
                                string(input.get("portId")),
                                "EXACT_CELL_IDENTITY");
                    }
                }
            }
            InputPortResolution projectedCarrier =
                    exactProjectedValueCarrier(cell, inputPorts, slice);
            if (!projectedCarrier.portId.isEmpty()) {
                return projectedCarrier;
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
            FieldSignature projected = declaredProjectedField(cell);
            if (projected != null) {
                String match = "";
                for (Map<String, Object> input : inputPorts) {
                    String inputCell = string(input.get("cell"));
                    if (!globalFieldCell(inputCell)) {
                        continue;
                    }
                    FieldSignature candidate = fieldSignature(inputCell);
                    if (candidate == null
                            || !projected.owner.equals(candidate.owner)
                            || !projected.name.equals(candidate.name)) {
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
            if (!"FIELD_ACCESS".equals(string(port.get("bindingMode")))
                    || strings(port.get("fieldPath")).isEmpty()
                    || string(port.get("leafFieldSignature")).isEmpty()) {
                return false;
            }
            boolean direct = "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                    .concat("READ_SITE_V1").equals(string(port.get(
                            "accessSiteAuthority")));
            boolean accessor = "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                    .concat("ACCESSOR_CALLSITE_V1").equals(string(port.get(
                            "accessorCallSiteAuthority")));
            if (!direct && !accessor) {
                return false;
            }
            Collection<String> path = strings(port.get("fieldPath"));
            return path.size() == 1 || "STATIC_UNIQUE_EXACT_DIRECT_"
                    .concat("GETFIELD_CHAIN_V1").equals(string(port.get(
                            "fieldPathAuthority")));
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
            Set<String> result = new LinkedHashSet<>();
            for (Map<String, Object> selected : slice.causalEdges) {
                if (!current.equals(string(selected.get("fromCell")))
                        || !exactParallelFieldReadRow(selected)) {
                    continue;
                }
                for (Map<String, Object> parallel : slice.causalEdges) {
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
            DeclaredFieldIdentity field = declaredField(cell);
            return path.isEmpty() && field != null
                    ? "#field:" + field.name : path;
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
            return string(first.get("method")).equals(string(second.get(
                    "method")))
                    && string(first.get("siteId")).equals(string(second.get(
                    "siteId")))
                    && integer(first.get("unitIndex"), -1) >= 0
                    && integer(first.get("unitIndex"), -1) == integer(
                    second.get("unitIndex"), -1)
                    && string(first.get("unit")).equals(string(second.get(
                    "unit")))
                    && string(first.get("toCell")).equals(string(second.get(
                    "toCell")));
        }

        private boolean parallelFieldReadDeclarationsAgree(
                Map<String, Object> first, Map<String, Object> second,
                String requiredPath) {
            DeclaredFieldIdentity firstDeclared = declaredField(
                    string(first.get("fromCell")));
            DeclaredFieldIdentity secondDeclared = declaredField(
                    string(second.get("fromCell")));
            if ((firstDeclared == null) == (secondDeclared == null)) {
                return false;
            }
            DeclaredFieldIdentity declared = firstDeclared != null
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
                    || !path.endsWith("#field:" + declared.name)) {
                return false;
            }
            // For a direct receiver read, the receiver method declaration is
            // the owner of the canonical field.  For an accessor projection,
            // the resolved declared-field tuple on the edge supplies the same
            // proof across inheritance.
            boolean receiverOwner = declared.owner.equals(ownerOfMethod(
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
                    || !Boolean.TRUE.equals(projected.get(
                    "semanticAssertionsAllowed"))
                    || !Boolean.TRUE.equals(projected.get(
                    "eligibleForAutomaticDerivation"))
                    || !Boolean.TRUE.equals(projected.get(
                    "eligibleForAutomaticSmt"))
                    || Boolean.TRUE.equals(projected.get("mappingOnly"))
                    || !"backward_provenance".equals(string(projected.get(
                    "direction")))) {
                return false;
            }
            String baseId = string(projected.get("projectionBaseEdgeId"));
            if (baseId.isEmpty()) {
                return false;
            }
            Map<String, Object> base = null;
            int matches = 0;
            for (Map<String, Object> candidate : edges) {
                if (baseId.equals(string(candidate.get("id")))) {
                    base = candidate;
                    matches++;
                }
            }
            if (matches != 1 || base == projected || isBoundary(base)
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

            Map<String, Object> base = null;
            int matches = 0;
            for (Map<String, Object> candidate : edges) {
                if (baseId.equals(string(candidate.get("id")))) {
                    base = candidate;
                    matches++;
                }
            }
            if (matches != 1 || base == projected
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
            String baseReason = "";
            for (Map<String, Object> input : inputPorts) {
                if (!base.equals(string(input.get("cell")))) {
                    continue;
                }
                if (!basePort.isEmpty()) {
                    return InputPortResolution.unresolved();
                }
                basePort = string(input.get("portId"));
                baseReason = string(input.get("selectionReason"));
            }
            if (basePort.isEmpty()) {
                return InputPortResolution.unresolved();
            }

            if (returnBase) {
                if (!("OPAQUE_CALL_RETURN_FRONTIER".equals(baseReason)
                        || "OUTPUT_SLICE_OPAQUE_CALL_FRONTIER".equals(
                        baseReason))
                        || !materializableOpaqueCallResult(base, slice)) {
                    return InputPortResolution.unresolved();
                }
                boolean proof = false;
                for (Map<String, Object> edge : edges) {
                    if (!cell.equals(string(edge.get("fromCell")))) {
                        continue;
                    }
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

            if (!"INTER_REGION_BOUNDARY_FRONTIER".equals(baseReason)) {
                return InputPortResolution.unresolved();
            }
            Set<String> projectedSources = new LinkedHashSet<>();
            for (Map<String, Object> edge : edges) {
                if (!isBoundary(edge)
                        || !cell.equals(string(edge.get("toCell")))) {
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
                for (Map<String, Object> edge : edges) {
                    if (!isBoundary(edge)
                            || !sourceBase.equals(string(edge.get(
                            "fromCell")))
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

        private FieldSignature declaredProjectedField(String cell) {
            String value = string(cell);
            if (countOccurrences(value, "#field:") != 1) {
                return null;
            }
            Matcher returned = PROJECTED_RETURN_FIELD_PATTERN.matcher(value);
            if (returned.matches()) {
                return new FieldSignature(returned.group(1).trim(),
                        returned.group(2).trim());
            }
            Matcher parameter = PROJECTED_PARAMETER_FIELD_PATTERN.matcher(
                    value);
            if (parameter.matches()) {
                return new FieldSignature(parameter.group(1).trim(),
                        parameter.group(2).trim());
            }
            return null;
        }

        private int countOccurrences(String value, String token) {
            int count = 0;
            for (int index = value.indexOf(token); index >= 0;
                 index = value.indexOf(token, index + token.length())) {
                count++;
            }
            return count;
        }

        private String globalFieldOwner(String cell) {
            Matcher field = GLOBAL_FIELD_OWNER_PATTERN.matcher(string(cell));
            return field.matches() ? field.group(1) : "";
        }

        private String parameterType(String cell) {
            Matcher parameter = PARAMETER_TYPE_PATTERN.matcher(string(cell));
            return parameter.find() ? parameter.group(1).trim() : "";
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
            InputSelection result = new InputSelection(candidates.size());
            Set<String> boundaryInputs = boundaryInputs(draft.methods);
            Set<String> boundarySources = incomingBoundarySources(draft.methods);
            Set<String> opaqueCallReturns = opaqueCallReturnFrontier(draft);
            SeedGuardInputFrontier seedGuardFrontier =
                    seedGuardInputFrontier(draft, boundaryInputs,
                            opaqueCallReturns);
            Set<String> mandatorySeedGuardInputs =
                    seedGuardFrontier.liveIns;
            Set<String> separatedHeapProducerInputs =
                    upstreamOfGuardHeapPrestateWriters(draft,
                            mandatorySeedGuardInputs);
            result.seedGuardInputDerivationGaps.addAll(
                    seedGuardFrontier.derivationGaps);
            Set<String> readFieldKeys = readFieldKeys(draft.methods,
                    draft.rootMethod);
            Map<String, String> mutableHeapPrestates =
                    mutableHeapPrestateCells(draft);
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
                Map<String, Object> seedGuardGap =
                        seedGuardFrontier.gapByCell.get(candidate);
                if (seedGuardGap != null) {
                    // Unknown provenance is not authority to create a free
                    // symbol.  Keep the value observed by this concrete
                    // activation and continue exploring the remainder of the
                    // region.  A later runtime/static refinement can replace
                    // this fallback with a proven live-in ancestor.
                    result.derivedInputs.add(candidate
                            + " [seed guard provenance gap; "
                            + "CONCRETE_BOUND_OBSERVED_VALUE fallback]");
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
                    result.derivedInputs.add(candidate
                            + " [upstream shared-heap producer is connected "
                            + "through a read-from region edge]");
                    continue;
                }
                boolean opaqueCall = opaqueCallReturns.contains(candidate);
                boolean boundaryTarget = boundaryInputs.contains(candidate);
                if (boundaryTarget && !opaqueCall
                        && internallyDefinedBoundaryAlias(candidate, draft)) {
                    result.derivedInputs.add(candidate
                            + " [protocol boundary target aliases a value defined inside the region]");
                    continue;
                }
                boolean boundary = boundaryTarget || opaqueCall;
                if (boundarySources.contains(candidate)) {
                    result.derivedInputs.add(candidate
                            + " [remote protocol producer is represented by the incoming boundary port]");
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
                    result.derivedInputs.add(candidate
                            + " [not in the exception-directed backward slice]");
                    continue;
                }
                String derivedReason = derivedReason(candidate, draft,
                        produced, boundary, mutableHeapPrestates.keySet());
                if (!mandatorySeedGuardInput && !derivedReason.isEmpty()) {
                    result.derivedInputs.add(candidate + " [" + derivedReason + "]");
                    continue;
                }

                String fieldKey = semanticFieldKey(candidate, draft.rootMethod);
                if (!fieldKey.isEmpty()) {
                    boolean mutablePrestate = mutableHeapPrestates.containsKey(
                            fieldKey);
                    if (!mandatorySeedGuardInput && !boundary
                            && !fieldReadAtFrontier(candidate, fieldKey,
                            readFieldKeys, draft.rootMethod)) {
                        result.derivedInputs.add(candidate
                                + " [field projection is not read at the region frontier]");
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
                        if (previous != null) {
                            result.derivedInputs.add(previous
                                    + " [duplicate field alias of " + candidate + "]");
                        }
                        fieldsBySemanticKey.put(fieldKey, candidate);
                        result.selectionReasons.put(candidate,
                                mandatorySeedGuardInput
                                        ? "SEED_GUARD_DEPENDENCY_FRONTIER"
                                : mutablePrestate
                                        ? "MUTABLE_HEAP_PRESTATE_FRONTIER"
                                : boundaryInputs.contains(candidate)
                                        ? "INTER_REGION_HEAP_FRONTIER"
                                        : "HEAP_READ_FRONTIER");
                    } else {
                        result.derivedInputs.add(candidate
                                + " [duplicate field alias of " + previous + "]");
                    }
                    continue;
                }
                if (!boundaryInput(candidate, draft.rootMethod)) {
                    String diagnostic = candidate
                            + " [causal dependency has no materializable "
                            + "region-boundary representation]";
                    result.unresolvedInputs.add(diagnostic);
                    result.unresolvedInputDetails.put(diagnostic, object(
                            "dependencyCell", candidate,
                            "dependencyMethods",
                            dependencyMethods(candidate, draft),
                            "reason",
                            "NO_MATERIALIZABLE_REGION_BOUNDARY_"
                                    + "REPRESENTATION",
                            "diagnostic", diagnostic,
                            "provenanceAuthority",
                            "STATIC_EXACT_DEPENDENCY_METHOD_CONSUMER_SET_V1"));
                    continue;
                }
                result.externalInputs.add(candidate);
                result.selectionReasons.put(candidate,
                        mandatorySeedGuardInput
                                ? "SEED_GUARD_DEPENDENCY_FRONTIER"
                                : inputSelectionReason(candidate,
                                draft.rootMethod,
                                boundaryInputs.contains(candidate),
                                opaqueCall));
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
                selection.selectionReasons.remove(alias);
                if (mandatory) {
                    selection.mandatorySeedGuardInputs.add(replacement.cell);
                    selection.selectionReasons.put(replacement.cell,
                            "SEED_GUARD_DEPENDENCY_FRONTIER");
                }
                selection.derivedInputs.add(alias
                        + " [exact suffix alias of complete field path "
                        + replacement.cell + "]");
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
            for (Map<String, Object> edge : analysisEdges(draft)) {
                if (!alias.equals(string(edge.get("fromCell")))) {
                    continue;
                }
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
            Map<String, List<Map<String, Object>>> incoming =
                    new LinkedHashMap<>();
            Deque<String> work = new ArrayDeque<>();
            for (Map<String, Object> edge : analysisEdges(draft)) {
                String target = string(edge.get("toCell"));
                if (!target.isEmpty()) {
                    incoming.computeIfAbsent(target,
                            ignored -> new ArrayList<>()).add(edge);
                }
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
                for (Map<String, Object> edge : incoming.getOrDefault(
                        current, Collections.<Map<String, Object>>emptyList())) {
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

            Map<String, List<Map<String, Object>>> incoming =
                    new LinkedHashMap<>();
            Set<String> guardSources = new LinkedHashSet<>();
            for (Map<String, Object> edge : analysisEdges(draft)) {
                String target = string(edge.get("toCell"));
                if (!target.isEmpty()) {
                    incoming.computeIfAbsent(target,
                            ignored -> new ArrayList<>()).add(edge);
                }
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
                boolean rejectedDefinition = false;
                for (Map<String, Object> edge : incoming.getOrDefault(
                        current, Collections.<Map<String, Object>>emptyList())) {
                    if (isBoundary(edge)) {
                        // The consumer-side endpoint is the region live-in.
                        // Its producer belongs to another region and is
                        // connected later by the region worklist.
                        // A mapping-only/unvalidated contract is only a
                        // discovery hint.  It must not hide an exact getter or
                        // other in-region definition behind that endpoint.
                        if (authoritativeGuardProtocolBoundary(edge)) {
                            incomingProtocolBoundary = true;
                        } else {
                            rejectedDefinition = true;
                        }
                        continue;
                    }
                    if (authoritativeGuardDerivationEdge(edge)) {
                        definitions.add(edge);
                    } else if (definitionLikeGuardEdge(edge)) {
                        rejectedDefinition = true;
                    }
                }
                definitions = nonRedundantGuardDefinitions(definitions);
                if (incomingProtocolBoundary) {
                    result.liveIns.add(current);
                    continue;
                }
                if (definitions.isEmpty()) {
                    result.addGap(current, rejectedDefinition
                                    ? "NON_AUTHORITATIVE_IN_REGION_DEFINITION"
                                    : "MISSING_IN_REGION_DEFINITION",
                            incoming.getOrDefault(current,
                                    Collections.<Map<String, Object>>emptyList()));
                    continue;
                }
                for (Map<String, Object> definition : definitions) {
                    String source = string(definition.get("fromCell"));
                    if (source.isEmpty() || source.equals(current)) {
                        result.addGap(current,
                                "EMPTY_OR_SELF_REFERENTIAL_DEFINITION",
                                Collections.singletonList(definition));
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
                    || Boolean.TRUE.equals(edge.get("mappingOnly"))
                    || !Boolean.TRUE.equals(edge.get(
                    "semanticAssertionsAllowed"))
                    || !Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticDerivation"))
                    || !Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticSmt"))) {
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
                    || Boolean.TRUE.equals(edge.get("mappingOnly"))
                    || !Boolean.TRUE.equals(edge.get(
                    "semanticAssertionsAllowed"))
                    || !Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticDerivation"))
                    || !Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticSmt"))
                    || !"backward_provenance".equals(string(edge.get(
                    "direction")))
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
            for (Map<String, Object> edge : analysisEdges(draft)) {
                if (!candidate.equals(string(edge.get("toCell")))
                        || isBoundary(edge)
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
            for (Map<String, Object> edge : analysisEdges(draft)) {
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
            Map<String, Object> producerPlan = plansByMethod.get(
                    returnedMethod);
            if (producerPlan == null
                    || !strings(producerPlan.get("outputs")).contains(
                    candidate)
                    || !reachableFrom(draft.rootMethod, returnedMethod)) {
                return false;
            }
            for (Map<String, Object> edge : analysisEdges(draft)) {
                if (!candidate.equals(string(edge.get("fromCell")))
                        || !draft.methods.contains(string(edge.get("method")))
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
            Set<String> cached = internallyDerivedTargetsByRegion.get(draft);
            if (cached != null) {
                return cached;
            }
            Set<String> targets = new LinkedHashSet<>();
            for (String method : draft.methods) {
                Map<String, Object> plan = plansByMethod.get(method);
                if (plan != null) {
                    targets.addAll(strings(plan.get("outputs")));
                }
            }
            for (Map<String, Object> edge : analysisEdges(draft)) {
                if (draft.methods.contains(string(edge.get("method")))) {
                    String target = string(edge.get("toCell"));
                    if (!target.isEmpty()) {
                        targets.add(target);
                    }
                }
            }
            internallyDerivedTargetsByRegion.put(draft, targets);
            return targets;
        }

        private Collection<Map<String, Object>> analysisEdges(
                RegionDraft draft) {
            if (draft.exceptionDirected) {
                return draft.causalEdges;
            }
            List<Map<String, Object>> relevant = new ArrayList<>();
            for (Map<String, Object> edge : edges) {
                if (draft.methods.contains(string(edge.get("method")))) {
                    relevant.add(edge);
                }
            }
            return relevant;
        }

        private String inputSelectionReason(String candidate,
                                            String rootMethod,
                                            boolean interRegionBoundary,
                                            boolean opaqueCall) {
            if (opaqueCall) {
                return "OPAQUE_CALL_RETURN_FRONTIER";
            }
            if (interRegionBoundary) {
                return "INTER_REGION_BOUNDARY_FRONTIER";
            }
            if (rootParameter(candidate, rootMethod)) {
                return "ROOT_ARGUMENT_FRONTIER";
            }
            if (environmentInput(candidate)) {
                return "ENVIRONMENT_FRONTIER";
            }
            return "REGION_LIVE_IN_FRONTIER";
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
            if (!mutableHeapPrestate && !fieldKey.isEmpty()
                    && fieldDefinedInsideRegion(fieldKey,
                    draft.methods, draft.rootMethod)) {
                return "field is initialized by an object construction inside the region";
            }
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
            DeclaredFieldIdentity field = declaredField(candidate);
            if (field == null || closedProtocolScalarType(field.type)) {
                return false;
            }
            boolean read = false;
            for (Map<String, Object> raw : analysisEdges(draft)) {
                if (!candidate.equals(string(raw.get("fromCell")))) {
                    continue;
                }
                if (!"HEAP_READ".equals(string(raw.get("transferKind")))
                        || Boolean.TRUE.equals(raw.get("fieldSensitive"))
                        || !exactStaticValueFlow(raw)) {
                    return false;
                }
                read = true;
                boolean projected = false;
                for (Map<String, Object> shadow : analysisEdges(draft)) {
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
            Set<String> cached = callResultsWithCausalAlternativeByRegion.get(
                    draft);
            if (cached != null) {
                return cached;
            }
            Collection<Map<String, Object>> selected = analysisEdges(draft);
            Map<CallResultSiteKey, Set<String>> returnsBySite =
                    new LinkedHashMap<>();
            Set<CallResultSiteKey> alternativeSites = new LinkedHashSet<>();
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
                CallResultSiteKey site = new CallResultSiteKey(target,
                        method, unit);
                if (source.contains(">.return")) {
                    returnsBySite.computeIfAbsent(site,
                            ignored -> new LinkedHashSet<>()).add(source);
                } else if (!source.isEmpty()) {
                    alternativeSites.add(site);
                }
            }
            Set<String> result = new LinkedHashSet<>();
            for (CallResultSiteKey site : alternativeSites) {
                Set<String> returned = returnsBySite.get(site);
                if (returned != null) {
                    result.addAll(returned);
                }
            }
            callResultsWithCausalAlternativeByRegion.put(draft, result);
            return result;
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

        private boolean fieldDefinedInsideRegion(String fieldKey,
                                                 Set<String> methods,
                                                 String rootMethod) {
            List<Map<String, Object>> reads = fieldReads(fieldKey, methods,
                    rootMethod);
            if (!reads.isEmpty()
                    && !fieldDefinitelyDefinedBeforeAllReads(fieldKey,
                    methods, rootMethod, reads)) {
                return false;
            }
            for (Map<String, Object> edge : edgesForMethods(methods)) {
                String target = string(edge.get("toCell"));
                String targetKey = semanticFieldKey(target, rootMethod);
                if (targetKey.isEmpty()) {
                    Matcher embedded = EMBEDDED_FIELD_PATTERN.matcher(target);
                    if (embedded.matches()) {
                        targetKey = embedded.group(1) + "#" + embedded.group(2);
                    }
                }
                if (!fieldKey.equals(targetKey)) {
                    continue;
                }
                String transfer = string(edge.get("transferKind"));
                String unit = string(edge.get("unit"));
                if ("HEAP_WRITE".equals(transfer)
                        || unit.contains(".<") && unit.contains(" = ")) {
                    return true;
                }
            }
            return false;
        }

        private List<Map<String, Object>> fieldReads(
                String fieldKey, Set<String> methods, String rootMethod) {
            List<Map<String, Object>> result = new ArrayList<>();
            for (Map<String, Object> edge : edgesForMethods(methods)) {
                if (!"HEAP_READ".equals(string(edge.get(
                        "transferKind")))) {
                    continue;
                }
                if (fieldKey.equals(semanticFieldKey(string(edge.get(
                        "fromCell")), rootMethod))) {
                    result.add(edge);
                }
            }
            return result;
        }

        /**
         * Accepts a field as an in-region must-definition only with an exact
         * CFG proof.  Source order alone is insufficient: a syntactically
         * earlier write can be conditional, skipped by a loop, or belong to a
         * different callback invocation.  The proof therefore requires one
         * same-method write, a smaller unit index than every relevant read,
         * and an authoritative dominance set covering every read site.
         */
        private boolean fieldDefinitelyDefinedBeforeAllReads(
                String fieldKey, Set<String> methods, String rootMethod,
                List<Map<String, Object>> reads) {
            if (reads.isEmpty()) {
                return false;
            }
            String readMethod = string(reads.get(0).get("method"));
            Set<String> readSites = new LinkedHashSet<>();
            int earliestRead = Integer.MAX_VALUE;
            for (Map<String, Object> read : reads) {
                String site = string(read.get("siteId"));
                int unit = integer(read.get("unitIndex"), -1);
                if (readMethod.isEmpty()
                        || !readMethod.equals(string(read.get("method")))
                        || site.isEmpty() || unit < 0) {
                    return false;
                }
                readSites.add(site);
                earliestRead = Math.min(earliestRead, unit);
            }
            if (readSites.size() != reads.size()) {
                return false;
            }
            for (Map<String, Object> write : edgesForMethods(methods)) {
                if (!readMethod.equals(string(write.get("method")))
                        || !"HEAP_WRITE".equals(string(write.get(
                        "transferKind")))
                        || !fieldKey.equals(semanticFieldKey(string(
                        write.get("toCell")), rootMethod))) {
                    continue;
                }
                int writeUnit = integer(write.get("unitIndex"), -1);
                Set<String> dominated = new LinkedHashSet<>(strings(
                        write.get("dominatedFieldReadSiteIds")));
                if (writeUnit >= 0 && writeUnit < earliestRead
                        && Boolean.TRUE.equals(write.get(
                        "fieldWriteDominatesAllReads"))
                        && "STATIC_CFG_DOMINANCE_AND_PROGRAM_ORDER".equals(
                        string(write.get("fieldMustDefAuthority")))
                        && dominated.containsAll(readSites)) {
                    return true;
                }
            }
            return false;
        }

        private List<Map<String, Object>> edgesForMethods(
                Set<String> methods) {
            String key = joinSorted(methods);
            List<Map<String, Object>> cached = edgesByMethodSet.get(key);
            if (cached != null) {
                return cached;
            }
            List<Map<String, Object>> selected = new ArrayList<>();
            for (String method : sorted(methods)) {
                selected.addAll(edgesByMethod.getOrDefault(method,
                        Collections.<Map<String, Object>>emptyList()));
            }
            edgesByMethodSet.put(key, selected);
            return selected;
        }

        private Set<String> boundaryInputs(Set<String> methods) {
            Set<String> inputs = new LinkedHashSet<>();
            for (Map<String, Object> edge : edges) {
                if (!isBoundary(edge)) {
                    continue;
                }
                String targetMethod = methodForCell(string(edge.get("toCell")));
                if (targetMethod.isEmpty()) {
                    targetMethod = string(edge.get("method"));
                }
                if (!methods.contains(targetMethod)) {
                    continue;
                }
                String target = string(edge.get("toCell"));
                inputs.add(target.isEmpty() ? string(edge.get("fromCell")) : target);
            }
            return inputs;
        }

        private Set<String> incomingBoundarySources(Set<String> methods) {
            Set<String> sources = new LinkedHashSet<>();
            for (Map<String, Object> edge : edges) {
                if (!isBoundary(edge)) {
                    continue;
                }
                String targetMethod = methodForCell(string(edge.get("toCell")));
                if (targetMethod.isEmpty()) {
                    targetMethod = string(edge.get("method"));
                }
                String sourceMethod = methodForCell(string(edge.get("fromCell")));
                if (methods.contains(targetMethod)
                        && !methods.contains(sourceMethod)) {
                    sources.add(string(edge.get("fromCell")));
                }
            }
            return sources;
        }

        private Set<String> readFieldKeys(Set<String> methods,
                                          String rootMethod) {
            Set<String> keys = new LinkedHashSet<>();
            for (Map<String, Object> edge : edges) {
                if (!methods.contains(string(edge.get("method")))
                        || !"HEAP_READ".equals(string(edge.get("transferKind")))) {
                    continue;
                }
                String key = semanticFieldKey(string(edge.get("fromCell")),
                        rootMethod);
                if (!key.isEmpty()) {
                    keys.add(key);
                }
            }
            return keys;
        }

        private Map<String, String> mutableHeapPrestateCells(
                RegionDraft draft) {
            Map<String, String> readCells = new LinkedHashMap<>();
            Map<String, List<Map<String, Object>>> readsByKey =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
                if (!draft.methods.contains(string(edge.get("method")))
                        || !"HEAP_READ".equals(string(edge.get(
                        "transferKind")))) {
                    continue;
                }
                String cell = string(edge.get("fromCell"));
                String key = semanticFieldKey(cell, draft.rootMethod);
                if (!key.isEmpty()) {
                    readCells.putIfAbsent(key, cell);
                    readsByKey.computeIfAbsent(key,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
            Map<String, String> result = new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
                if (!draft.methods.contains(string(edge.get("method")))
                        || !"HEAP_WRITE".equals(string(edge.get(
                        "transferKind")))) {
                    continue;
                }
                String cell = string(edge.get("toCell"));
                String key = semanticFieldKey(cell, draft.rootMethod);
                if (!key.isEmpty()
                        && "field_mutation".equals(string(edge.get("kind")))
                        && globalFieldCell(cell)) {
                    result.putIfAbsent(key, cell);
                } else if (!key.isEmpty() && readCells.containsKey(key)
                        && !fieldDefinitelyDefinedBeforeAllReads(key,
                        draft.methods, draft.rootMethod,
                        readsByKey.get(key))) {
                    result.putIfAbsent(key, readCells.get(key));
                }
            }
            return result;
        }

        private boolean fieldReadAtFrontier(String candidate, String fieldKey,
                                            Set<String> readFieldKeys,
                                            String rootMethod) {
            if (readFieldKeys.contains(fieldKey)) {
                return true;
            }
            // Some older/static-only slices retain a root receiver projection
            // without an explicit HEAP_READ edge. Preserve it only when no
            // read evidence for that receiver owner exists at all.
            if (candidate.startsWith("@this:")
                    && methodForCell(candidate).isEmpty()) {
                String owner = owner(rootMethod);
                for (String key : readFieldKeys) {
                    if (key.startsWith(owner + "#")) {
                        return false;
                    }
                }
                return true;
            }
            return false;
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
            for (Map<String, Object> edge : edges) {
                String method = string(edge.get("method"));
                if (!methods.contains(method)) {
                    continue;
                }
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
            return outboundProtocolScalarCell(region, output);
        }

        private boolean sharedFieldBoundarySource(
                RegionDraft region, String field) {
            boolean exactDefinition = false;
            boolean anchorDefinition = false;
            for (Map<String, Object> edge : edges) {
                if (region.methods.contains(string(edge.get("method")))
                        && field.equals(string(edge.get("toCell")))
                        && exactSharedFieldDefinition(edge)) {
                    exactDefinition = true;
                    anchorDefinition |= region.anchorMethod.equals(
                            string(edge.get("method")));
                }
            }
            if (!exactDefinition) {
                return false;
            }
            for (Map<String, Object> edge : edges) {
                String method = string(edge.get("method"));
                if (!region.methods.contains(method)
                        && "HEAP_READ".equals(string(edge.get(
                        "transferKind")))
                        && field.equals(string(edge.get("fromCell")))) {
                    return true;
                }
                if (isBoundary(edge)
                        && field.equals(string(edge.get("fromCell")))) {
                    String targetMethod = methodForCell(string(edge.get(
                            "toCell")));
                    if (!targetMethod.isEmpty()
                            && !region.methods.contains(targetMethod)) {
                        return true;
                    }
                }
            }
            if (anchorDefinition) {
                for (Map<String, Object> edge : edges) {
                    if (!"HEAP_READ".equals(string(edge.get(
                            "transferKind")))
                            || !field.equals(string(edge.get("fromCell")))) {
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
            for (Map.Entry<String, Map<String, Object>> entry
                    : plansByMethod.entrySet()) {
                if (!region.methods.contains(entry.getKey())
                        && strings(entry.getValue().get("symbolicInputs"))
                        .contains(field)) {
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
                    && !Boolean.TRUE.equals(edge.get("mappingOnly"))
                    && !string(edge.get("id")).isEmpty()
                    && !string(edge.get("siteId")).isEmpty()
                    && (exactStaticValueFlow(edge)
                    // Legacy compact rows predate explicit value-flow flags,
                    // but their exact HEAP_WRITE kind/cell/site tuple still
                    // names one concrete producer definition.
                    || string(edge.get("relation")).isEmpty()
                    || "value_flow".equals(string(edge.get("relation")))
                    && Boolean.TRUE.equals(edge.get(
                    "semanticAssertionsAllowed"))
                    && Boolean.TRUE.equals(edge.get(
                    "eligibleForAutomaticSmt")));
        }

        private boolean fieldBacksProjectedBoundary(
                RegionDraft region, String fieldCell) {
            FieldSignature field = fieldSignature(fieldCell);
            if (field == null) {
                return false;
            }
            for (Map<String, Object> boundary : edges) {
                if (!isBoundary(boundary)) {
                    continue;
                }
                String raw = string(boundary.get("fromCell"));
                String targetMethod = methodForCell(string(boundary.get(
                        "toCell")));
                if (targetMethod.isEmpty()
                        || region.methods.contains(targetMethod)) {
                    continue;
                }
                for (Map<String, Object> proof : edges) {
                    if (!raw.equals(string(proof.get("toCell")))
                            || !eligibleProjectedReturnAlias(proof,
                            region.methods)) {
                        continue;
                    }
                    String source = string(proof.get("fromCell"));
                    String sourceMethod = methodForCell(source);
                    String base = sourceMethod + ".return#field:";
                    if (source.startsWith(base)
                            && field.owner.equals(declaredReturnType(
                            sourceMethod))
                            && field.name.equals(source.substring(
                            base.length()))) {
                        return true;
                    }
                }
            }
            return false;
        }

        private boolean outboundProtocolScalarCell(
                RegionDraft region, String outputCell) {
            Matcher formal = FORMAL_PARAMETER_PATTERN.matcher(outputCell);
            if (!formal.matches()
                    || !closedProtocolScalarType(formal.group(1).trim())) {
                return false;
            }
            String sourceMethod = methodForCell(outputCell);
            if (sourceMethod.isEmpty()
                    || !region.methods.contains(sourceMethod)) {
                return false;
            }
            for (Map<String, Object> edge : edges) {
                if (!isBoundary(edge)
                        || !outputCell.equals(string(edge.get("fromCell")))) {
                    continue;
                }
                String targetMethod = methodForCell(
                        string(edge.get("toCell")));
                if (targetMethod.isEmpty()) {
                    targetMethod = string(edge.get("method"));
                }
                if (!targetMethod.isEmpty()
                        && !region.methods.contains(targetMethod)) {
                    return true;
                }
            }
            return false;
        }

        private void buildRegionEdges(Result result) {
            Map<String, List<Map<String, Object>>> regionsByMethod = new LinkedHashMap<>();
            for (Map<String, Object> region : result.regions) {
                for (String method : strings(region.get("methods"))) {
                    regionsByMethod.computeIfAbsent(method, ignored -> new ArrayList<>())
                            .add(region);
                }
            }
            Set<String> emitted = new LinkedHashSet<>();
            int index = 0;
            for (Map<String, Object> edge : edges) {
                if (!isBoundary(edge)) {
                    continue;
                }
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
                        String staticMappingKind = string(edge.get("kind"));
                        String key = fromRegionId + "\n" + toRegionId + "\n"
                                + fromCell + "\n" + toCell + "\n"
                                + string(edge.get("siteId"));
                        if (!emitted.add(key)) {
                            continue;
                        }
                        Map<String, Object> regionEdge = object(
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
                                "relation", "",
                                "candidateRelation", "EQUALITY",
                                "requiresOrder", true,
                                "mappingKind", staticMappingKind,
                                "mappingAuthority",
                                "STATIC_FORMAT_AND_PORT_MAPPING",
                                "mappingOnly", true,
                                "semanticAssertionsAllowed", false,
                                "eligibleForAutomaticDerivation", false,
                                "eligibleForAutomaticSmt", false,
                                "payloadEqualityCheckRequired", true,
                                "rootValidation", "RUNTIME_REQUIRED",
                                "siteId", string(edge.get("siteId")),
                                "evidence", Arrays.asList("STATIC_PROTOCOL",
                                        string(edge.get("evidence"))));
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
            for (Map<String, Object> edge : edges) {
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
                                "edgeId", "REGION_EDGE." + index++,
                                "fromRegion", producer,
                                "fromPort", field,
                                "toRegion", consumer,
                                "toPort", field,
                                "kind", "SHARED_STATE",
                                "relation", "READ_FROM_CANDIDATE",
                                "requiresOrder", true,
                                "requiresObjectIdentity", true,
                                "rootValidation", "RUNTIME_REQUIRED",
                                "evidence", Collections.singletonList(
                                        "STATIC_FIELD"));
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
            for (Map<String, Object> proof : edges) {
                if (!rawEndpoint.equals(string(proof.get("toCell")))
                        || !eligibleProjectedReturnAlias(proof,
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
                    || !Boolean.TRUE.equals(proof.get(
                    "semanticAssertionsAllowed"))
                    || !Boolean.TRUE.equals(proof.get(
                    "eligibleForAutomaticDerivation"))
                    || !Boolean.TRUE.equals(proof.get(
                    "eligibleForAutomaticSmt"))
                    || Boolean.TRUE.equals(proof.get("mappingOnly"))
                    || !"backward_provenance".equals(string(
                    proof.get("direction")))
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
            Map<String, Object> match = null;
            Object value = region.get("outputs");
            if (!(value instanceof Collection<?>)) {
                return null;
            }
            for (Object item : (Collection<?>) value) {
                if (!(item instanceof Map<?, ?>)) {
                    continue;
                }
                @SuppressWarnings("unchecked")
                Map<String, Object> output = (Map<String, Object>) item;
                String cell = string(output.get("cell"));
                FieldSignature field = fieldSignature(cell);
                if (!globalFieldCell(cell) || field == null
                        || !owner.equals(field.owner)
                        || !fieldName.equals(field.name)
                        || exactCompleteOutput(region, cell) != output) {
                    continue;
                }
                if (match != null) {
                    return null;
                }
                match = output;
            }
            return match;
        }

        private Map<String, Object> exactCompleteOutput(
                Map<String, Object> region, String endpoint) {
            Map<String, Object> match = null;
            Object outputValue = region.get("outputs");
            if (!(outputValue instanceof Collection<?>)) {
                return null;
            }
            for (Object item : (Collection<?>) outputValue) {
                if (!(item instanceof Map<?, ?>)) {
                    continue;
                }
                @SuppressWarnings("unchecked")
                Map<String, Object> output = (Map<String, Object>) item;
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
            Object sliceValue = region.get("outputSlices");
            if (!(sliceValue instanceof Collection<?>)) {
                return false;
            }
            for (Object item : (Collection<?>) sliceValue) {
                if (!(item instanceof Map<?, ?>)) {
                    continue;
                }
                Map<?, ?> slice = (Map<?, ?>) item;
                if (string(output.get("portId")).equals(string(
                        slice.get("outputPort")))
                        && string(output.get("cell")).equals(string(
                        slice.get("outputCell")))
                        && Boolean.TRUE.equals(slice.get("complete"))) {
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
            FieldSignature signature = fieldSignature(field);
            if (signature == null) {
                return false;
            }
            List<String> candidates = new ArrayList<>();
            candidates.addAll(strings(region.get("symbolicInputs")));
            candidates.addAll(strings(region.get("relevantStates")));
            candidates.addAll(portCells(region.get("inputs")));
            candidates.addAll(portCells(region.get("outputs")));
            String thisProjection = "@this: " + signature.owner
                    + "#field:" + signature.name;
            for (String candidate : candidates) {
                if (field.equals(candidate)
                        || candidate.equals(thisProjection)
                        || candidate.startsWith(thisProjection + "#field:")) {
                    return true;
                }
                String method = methodForCell(candidate);
                if (!method.isEmpty()
                        && signature.owner.equals(ownerOfMethod(method))
                        && (candidate.endsWith("#field:" + signature.name)
                        || candidate.contains("#field:" + signature.name + "#field:"))) {
                    return true;
                }
            }
            return false;
        }

        private List<String> portCells(Object value) {
            List<String> cells = new ArrayList<>();
            if (!(value instanceof Collection)) {
                return cells;
            }
            for (Object item : (Collection<?>) value) {
                if (item instanceof Map) {
                    String cell = string(((Map<?, ?>) item).get("cell"));
                    if (!cell.isEmpty()) {
                        cells.add(cell);
                    }
                }
            }
            return cells;
        }

        private FieldSignature fieldSignature(String field) {
            Matcher matcher = FIELD_SIGNATURE_PATTERN.matcher(
                    field == null ? "" : field);
            if (!matcher.matches()) {
                return null;
            }
            return new FieldSignature(matcher.group(1), matcher.group(2));
        }

        private String ownerOfMethod(String method) {
            Matcher matcher = METHOD_OWNER_PATTERN.matcher(method);
            return matcher.find() ? matcher.group(1) : "";
        }

        private boolean reaches(String from, String target, Set<String> within) {
            if (from.equals(target)) {
                return true;
            }
            Set<String> seen = new LinkedHashSet<>();
            Deque<String> queue = new ArrayDeque<>();
            seen.add(from);
            queue.add(from);
            while (!queue.isEmpty()) {
                String current = queue.removeFirst();
                for (String next : values(calleesByCaller.get(current))) {
                    if (!within.contains(next) || !seen.add(next)) {
                        continue;
                    }
                    if (next.equals(target)) {
                        return true;
                    }
                    queue.addLast(next);
                }
            }
            return false;
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
                Object rows = edge.get(field);
                if (!(rows instanceof Collection)) {
                    continue;
                }
                for (Object row : (Collection<?>) rows) {
                    if (!(row instanceof Map)) {
                        continue;
                    }
                    Object outcome = ((Map<?, ?>) row).get(
                            "requiredOutcome");
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
                List<Map<String, Object>> policyEdges, RegionDraft draft,
                Collection<String> outputCandidates,
                boolean requestedOutputCausal) {
            Map<String, Object> edge = strongestBranchPolicyEdge(
                    policyEdges, draft);
            String site = string(edge.get("siteId"));
            String guard = firstNonEmpty(string(edge.get("unit")),
                    string(edge.get("toCell")), site);
            Map<String, Object> independenceProof = requestedOutputCausal
                    ? null : outputIndependenceProof(policyEdges,
                    outputCandidates);
            boolean outputIndependent = independenceProof != null;
            Map<String, Object> result = object(
                    "siteId", site,
                    "method", string(edge.get("method")),
                    "unitIndex", integer(edge.get("unitIndex"), -1),
                    "policy", outputIndependent
                            ? "PATH_ASSUMPTION" : "EXPLORE",
                    "guard", guard,
                    "requiredOutcome", commonRequiredOutcome(policyEdges),
                    "requiredSuccessorIndices",
                    requiredSuccessorIndices(policyEdges),
                    "branchKind", string(edge.get("branchKind")),
                    "switchCaseKeys", integerValues(edge.get(
                            "switchCaseKeys")),
                    "defaultSuccessorIndex", integer(edge.get(
                            "defaultSuccessorIndex"), -1),
                    "successorCount", integer(edge.get(
                            "successorCount"), -1),
                    "successorIndexAuthority", string(edge.get(
                            "successorIndexAuthority")),
                    "switchArmIdentityAuthority", string(edge.get(
                            "switchArmIdentityAuthority")),
                    "role", "REACHABILITY",
                    "sourceEdgeId", string(edge.get("id")),
                    "sourceEdgeIds", branchPolicyEdgeValues(policyEdges,
                            "id"),
                    "sourceEdgeKind", string(edge.get("kind")),
                    "sourceEdgeKinds", branchPolicyEdgeValues(policyEdges,
                            "kind"),
                    "controlDependenceAuthority", string(edge.get(
                            "controlDependenceAuthority")),
                    "controlDependenceAuthorities",
                    branchPolicyEdgeValues(policyEdges,
                            "controlDependenceAuthority"),
                    "policyAuthority", outputIndependent
                            ? string(independenceProof.get(
                            "outputPathIndependenceAuthority"))
                            : requestedOutputCausal
                            ? "STATIC_REQUESTED_OUTPUT_SLICE_CONTROL_"
                            + "DEPENDENCE_REQUIRES_EXPLORATION_V1"
                            : explorationAuthority(policyEdges, draft));
            if (outputIndependent) {
                result.put("pathAssumptionProof", object(
                        "outputPathIndependenceProven", true,
                        "authority", string(independenceProof.get(
                                "outputPathIndependenceAuthority")),
                        "reason", string(independenceProof.get(
                                "outputPathIndependenceReason")),
                        "checkedOutputs", strings(independenceProof.get(
                                "outputPathIndependenceCheckedOutputs"))));
            } else {
                result.put("explorationReason",
                        "OUTPUT_OR_PATH_INFLUENCE_PRESENT_OR_NOT_PROVEN_"
                                + "ABSENT");
            }
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
                Collection<String> outputCandidates,
                List<Map<String, Object>> branchPolicies,
                Set<String> pathAssumptions, Set<String> exploreBranches,
                Set<String> sites) {
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
            for (Map<String, Object> edge : edges) {
                if (!selectedEdgeIds.contains(string(edge.get("id")))
                        || !"GUARD".equals(string(edge.get(
                        "transferKind")))) {
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
                Map<String, Object> policy = branchPolicy(policyEdges,
                        draft, outputCandidates, true);
                Integer existingIndex = policyIndexBySite.get(entry.getKey());
                if (existingIndex == null) {
                    policyIndexBySite.put(entry.getKey(),
                            branchPolicies.size());
                    branchPolicies.add(policy);
                } else if (!"EXPLORE".equals(string(branchPolicies.get(
                        existingIndex).get("policy")))) {
                    branchPolicies.set(existingIndex, policy);
                }
                pathAssumptions.remove(entry.getKey());
                exploreBranches.add(entry.getKey());
                sites.add(entry.getKey());
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

        private Map<String, Object> outputIndependenceProof(
                Collection<Map<String, Object>> siteEdges,
                Collection<String> outputs) {
            for (Map<String, Object> edge : siteEdges) {
                if (ControlDependenceEdgeSupport
                        .hasAuditableOutputIndependenceProof(edge)
                        && outputIndependenceCovers(edge, outputs)) {
                    return edge;
                }
            }
            return null;
        }

        private List<String> branchPolicyEdgeValues(
                Collection<Map<String, Object>> siteEdges, String field) {
            Set<String> values = new LinkedHashSet<>();
            for (Map<String, Object> edge : siteEdges) {
                String value = string(edge.get(field));
                if (!value.isEmpty()) {
                    values.add(value);
                }
            }
            List<String> result = new ArrayList<>(values);
            Collections.sort(result);
            return result;
        }

        private String explorationAuthority(
                Collection<Map<String, Object>> siteEdges,
                RegionDraft draft) {
            for (Map<String, Object> edge : siteEdges) {
                if (ControlDependenceEdgeSupport.requiresSiteIdentity(
                        string(edge.get("kind")))) {
                    return "STATIC_OUTPUT_CONTROL_DEPENDENCE_REQUIRES_"
                            + "EXPLORATION_V1";
                }
            }
            for (Map<String, Object> edge : siteEdges) {
                if (guardHasSolverControlledFrontier(edge, draft)) {
                    return "SYMBOLIC_FRONTIER_REQUIRES_EXPLORATION_V1";
                }
            }
            return "CONSERVATIVE_UNPROVEN_OUTPUT_INDEPENDENCE_V1";
        }

        private boolean outputIndependenceCovers(
                Map<String, Object> edge, Collection<String> outputs) {
            if (outputs == null || outputs.isEmpty()) {
                return false;
            }
            Set<String> checked = new LinkedHashSet<>(strings(edge.get(
                    "outputPathIndependenceCheckedOutputs")));
            return checked.containsAll(outputs);
        }

        /**
         * Provides audit metadata for an EXPLORE decision.  This provenance
         * walk is deliberately not a gate: an unresolved frontier means the
         * branch remains conservatively explorable, never that it can be
         * pinned to the concrete trace.
         */
        private boolean guardHasSolverControlledFrontier(
                Map<String, Object> edge, RegionDraft draft) {
            String start = string(edge.get("fromCell"));
            if (start.isEmpty()) {
                return false;
            }

            Map<String, List<Map<String, Object>>> incoming =
                    new LinkedHashMap<>();
            for (Map<String, Object> dependency : analysisEdges(draft)) {
                if (isBoundary(dependency)) {
                    continue;
                }
                String target = string(dependency.get("toCell"));
                if (!target.isEmpty()) {
                    incoming.computeIfAbsent(target,
                            ignored -> new ArrayList<>()).add(dependency);
                }
            }
            Set<String> seen = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            seen.add(start);
            work.add(start);
            while (!work.isEmpty() && seen.size() < 4096) {
                String current = work.removeFirst();
                if (solverControlledScalarFrontier(current)) {
                    return true;
                }
                if (scalarMethodReturnFrontier(current)) {
                    return true;
                }
                List<Map<String, Object>> dependencies = incoming.get(current);
                if (dependencies == null) {
                    continue;
                }
                for (Map<String, Object> dependency : dependencies) {
                    String source = string(dependency.get("fromCell"));
                    if (!source.isEmpty() && seen.add(source)) {
                        work.addLast(source);
                    }
                }
            }
            return false;
        }

        private List<Integer> requiredSuccessorIndices(
                Collection<Map<String, Object>> edges) {
            Set<Integer> indices = new LinkedHashSet<>();
            for (Map<String, Object> edge : edges) {
                collectIntegerValues(indices, edge.get(
                        "reachingSuccessorIndices"));
                for (String field : Arrays.asList("controlledDefinitions",
                        "guardedMutations", "guardedEffects")) {
                    Object rows = edge.get(field);
                    if (!(rows instanceof Collection)) {
                        continue;
                    }
                    for (Object row : (Collection<?>) rows) {
                        if (row instanceof Map) {
                            collectIntegerValues(indices,
                                    ((Map<?, ?>) row).get(
                                            "reachingSuccessorIndices"));
                        }
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

        private boolean solverControlledScalarFrontier(String cell) {
            if (isEnvironmentCell(cell)) {
                return true;
            }
            Matcher field = SCALAR_FIELD_PATTERN.matcher(string(cell));
            if (field.matches()) {
                return scalarType(field.group(1));
            }
            Matcher parameter = PARAMETER_TYPE_PATTERN.matcher(string(cell));
            return parameter.find() && scalarType(parameter.group(1));
        }

        private boolean scalarMethodReturnFrontier(String cell) {
            String value = string(cell);
            if (!value.endsWith(">.return")) {
                return false;
            }
            String method = methodForCell(value);
            return !method.isEmpty()
                    && scalarType(declaredReturnType(method));
        }

        private boolean scalarType(String type) {
            String value = string(type).trim();
            return value.matches("boolean|byte|char|short|int|long|float|double")
                    || value.matches("java\\.lang\\.(Boolean|Byte|Character|Short|Integer|Long|Float|Double|String)")
                    || "java.math.BigInteger".equals(value)
                    || "java.math.BigDecimal".equals(value);
        }
    }

    private static final class RegionDraft {
        private String regionId;
        private String rootMethod;
        private final String anchorMethod;
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<Map<String, Object>> causalEdges = new LinkedHashSet<>();
        private final Set<String> causalCells = new LinkedHashSet<>();
        private final List<Map<String, Object>>
                accessorImplementationAdmissions = new ArrayList<>();
        private boolean exceptionDirected;
        private boolean truncated;
        private boolean inheritedRegionTruncated;
        private boolean methodBudgetTruncated;
        private boolean causalCellBudgetTruncated;

        private RegionDraft(String anchorMethod) {
            this.anchorMethod = anchorMethod;
        }
    }

    private static final class CausalSlice {
        private final Set<Map<String, Object>> edges = new LinkedHashSet<>();
        private final Set<String> cells = new LinkedHashSet<>();
        private boolean causalCellBudgetTruncated;
    }

    private static final class InputSelection {
        private final int rawInputCount;
        private final Set<String> externalInputs = new LinkedHashSet<>();
        private final Set<String> mandatorySeedGuardInputs =
                new LinkedHashSet<>();
        private final List<Map<String, Object>> seedGuardInputDerivationGaps =
                new ArrayList<>();
        private final Set<String> derivedInputs = new LinkedHashSet<>();
        private final Set<String> unresolvedInputs = new LinkedHashSet<>();
        private final Map<String, Map<String, Object>>
                unresolvedInputDetails = new LinkedHashMap<>();
        private final Map<String, String> selectionReasons =
                new LinkedHashMap<>();

        private InputSelection(int rawInputCount) {
            this.rawInputCount = rawInputCount;
        }
    }

    private static final class SeedGuardInputFrontier {
        private final Set<String> liveIns = new LinkedHashSet<>();
        private final Set<String> gapCells = new LinkedHashSet<>();
        private final Map<String, Map<String, Object>> gapByCell =
                new LinkedHashMap<>();
        private final List<Map<String, Object>> derivationGaps =
                new ArrayList<>();

        private void addGap(String cell, String reason,
                            Collection<Map<String, Object>> incoming) {
            if (cell == null || cell.isEmpty() || gapByCell.containsKey(cell)) {
                return;
            }
            Set<String> edgeIds = new LinkedHashSet<>();
            Set<String> sites = new LinkedHashSet<>();
            for (Map<String, Object> edge : incoming) {
                String edgeId = string(edge.get("id"));
                String site = string(edge.get("siteId"));
                if (!edgeId.isEmpty()) {
                    edgeIds.add(edgeId);
                }
                if (!site.isEmpty()) {
                    sites.add(site);
                }
            }
            Map<String, Object> gap = object(
                    "dependencyCell", cell,
                    "dependencyMethod", methodForCell(cell),
                    "reason", reason,
                    "incomingEdgeIds", sorted(edgeIds),
                    "incomingSiteIds", sorted(sites),
                    "symbolicEligibility", false,
                    "fallbackPolicy", "CONCRETE_BOUND_OBSERVED_VALUE",
                    "analysisContinuation", "CONCRETE_PATH_ALLOWED",
                    "provenanceAuthority",
                    "NO_FREE_SYMBOL_WITHOUT_LIVE_IN_AUTHORITY_V1");
            gapCells.add(cell);
            gapByCell.put(cell, gap);
            derivationGaps.add(gap);
        }
    }

    private static final class InputPortResolution {
        private final String portId;
        private final String authority;

        private InputPortResolution(String portId, String authority) {
            this.portId = portId == null ? "" : portId;
            this.authority = authority == null ? "" : authority;
        }

        private static InputPortResolution unresolved() {
            return new InputPortResolution("", "UNRESOLVED");
        }
    }

    /** One exact static site that reads a canonical declared scalar field. */
    private static final class DeclaredFieldAccess {
        private final DeclaredFieldIdentity field;
        private final String method;
        private final String siteId;
        private final int unitIndex;
        private final boolean accessorCall;
        private final String invokedMethod;
        private final String accessorImplementationMethod;

        private DeclaredFieldAccess(DeclaredFieldIdentity field,
                                    String method, String siteId,
                                    int unitIndex, boolean accessorCall,
                                    String invokedMethod,
                                    String accessorImplementationMethod) {
            this.field = field;
            this.method = method;
            this.siteId = siteId;
            this.unitIndex = unitIndex;
            this.accessorCall = accessorCall;
            this.invokedMethod = invokedMethod == null ? "" : invokedMethod;
            this.accessorImplementationMethod =
                    accessorImplementationMethod == null ? ""
                            : accessorImplementationMethod;
        }
    }

    /**
     * Exact direct-getfield proof for one projected scalar frontier.  The
     * hook belongs to {@code rootField}; {@code leafField} is the only field
     * that may become symbolic.
     */
    private static final class DeclaredFieldPathAccess {
        private final String cell;
        private final DeclaredFieldIdentity rootField;
        private final DeclaredFieldIdentity leafField;
        private final String method;
        private final String siteId;
        private final int unitIndex;
        private final String accessOwnerCell;
        private final List<String> fieldPath;
        private final List<String> aliases;
        private final List<String> proofEdgeIds;

        private DeclaredFieldPathAccess(
                String cell, DeclaredFieldIdentity rootField,
                DeclaredFieldIdentity leafField, String method,
                String siteId, int unitIndex, String accessOwnerCell,
                Collection<String> fieldPath, Collection<String> aliases,
                Collection<String> proofEdgeIds) {
            this.cell = cell;
            this.rootField = rootField;
            this.leafField = leafField;
            this.method = method;
            this.siteId = siteId;
            this.unitIndex = unitIndex;
            this.accessOwnerCell = accessOwnerCell;
            this.fieldPath = new ArrayList<>(fieldPath);
            this.aliases = new ArrayList<>(aliases);
            this.proofEdgeIds = sorted(proofEdgeIds);
        }
    }

    private static final class OutputCaptureSelection {
        private final List<Map<String, Object>> bindings;
        private final boolean required;
        private final boolean complete;
        private final List<String> issues;

        private OutputCaptureSelection(List<Map<String, Object>> bindings,
                                       boolean required,
                                       boolean complete,
                                       List<String> issues) {
            this.bindings = new ArrayList<>(bindings);
            this.required = required;
            this.complete = complete;
            this.issues = new ArrayList<>(issues);
        }

        private static OutputCaptureSelection notRequired() {
            return new OutputCaptureSelection(
                    Collections.<Map<String, Object>>emptyList(), false, true,
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

    private static int parameterIndex(String cell) {
        Matcher parameter = PARAMETER_INDEX_PATTERN.matcher(string(cell));
        if (!parameter.find()) {
            return -1;
        }
        try {
            return Integer.parseInt(parameter.group(1));
        } catch (NumberFormatException ignored) {
            return -1;
        }
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

    private static String pair(String from, String to) {
        return from + "\n" + to;
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

    private static List<String> limitedSorted(Collection<String> values, int limit) {
        List<String> sorted = sorted(values);
        return sorted.size() <= limit
                ? sorted : new ArrayList<>(sorted.subList(0, limit));
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

    private static void add(Map<String, Set<String>> map, String key, String value) {
        map.computeIfAbsent(key, ignored -> new LinkedHashSet<>()).add(value);
    }

    private static void increment(Map<String, Integer> map, String key) {
        Integer previous = map.get(key);
        map.put(key, previous == null ? 1 : previous + 1);
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
