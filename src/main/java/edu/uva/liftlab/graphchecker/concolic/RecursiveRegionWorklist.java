package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Deterministic backward worklist for recursively discovering upstream
 * regions that define a selected region input.
 *
 * <p>The worklist is deliberately domain-neutral.  It consumes the common
 * region, activation, summary, and validated-edge JSON schemas.  Dynamic call
 * identifiers and event sequence numbers are retained as provenance, but are
 * excluded from the stable query key so that the same semantic query can be
 * reused across executions.</p>
 */
public final class RecursiveRegionWorklist {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Comparator<JsonObject> EDGE_ORDER =
            Comparator.comparing(RecursiveRegionWorklist::edgeSortKey);

    private RecursiveRegionWorklist() {
    }

    public static Result explore(List<JsonObject> regions,
                                 List<JsonObject> activations,
                                 List<JsonObject> edges,
                                 List<JsonObject> summaries,
                                 List<JsonObject> roots,
                                 Bounds bounds) {
        Bounds effectiveBounds = bounds == null ? Bounds.defaults() : bounds;
        Explorer explorer = new Explorer(regions, activations, edges,
                summaries, effectiveBounds);
        return explorer.run(roots == null
                ? Collections.<JsonObject>emptyList() : roots);
    }

    /** Stable SHA-256 key for a semantic upstream-region query. */
    public static String stableQueryKey(String consumerRegion,
                                        String inputPort,
                                        String relationKind,
                                        String requiredStateVersion,
                                        String pathPrefixHash,
                                        String boundedContextHash) {
        String canonical = component(consumerRegion)
                + component(canonicalPort(inputPort))
                + component(firstNonBlank(relationKind, "UNKNOWN"))
                + component(firstNonBlank(requiredStateVersion,
                "UNVERSIONED"))
                + component(firstNonBlank(pathPrefixHash, "NO_PATH"))
                + component(firstNonBlank(boundedContextHash,
                "NO_CONTEXT"));
        return sha256(canonical);
    }

    private static final class Explorer {
        private final Bounds bounds;
        private final long startedNanos = System.nanoTime();
        private final Set<String> regionIds = new LinkedHashSet<>();
        private final Map<String, JsonObject> regionsById =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> activationsByRegion =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> summariesByRegion =
                new LinkedHashMap<>();
        private final Map<String, List<EdgeGroup>> incomingByRegion =
                new LinkedHashMap<>();
        private final Map<String, Work> workByKey = new LinkedHashMap<>();
        private final Deque<Work> pending = new ArrayDeque<>();
        private final List<JsonObject> upstreamRequests = new ArrayList<>();
        private final List<JsonObject> alternativeWriterGroups =
                new ArrayList<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final List<JsonObject> cycles = new ArrayList<>();
        private final Set<String> gapKeys = new LinkedHashSet<>();
        private final Set<String> visitedRegions = new LinkedHashSet<>();
        private final Map<String, JsonObject> ownerSelectionsByEdge =
                new LinkedHashMap<>();
        private int deduplicatedQueries;
        private int deduplicatedConcreteBindingAlternatives;
        private int ambiguousConcreteBindingOwnerGroups;
        private int exploredPaths;
        private boolean wallClockReached;

        private Explorer(List<JsonObject> regions,
                         List<JsonObject> activations,
                         List<JsonObject> edges,
                         List<JsonObject> summaries,
                         Bounds bounds) {
            this.bounds = bounds;
            for (JsonObject region : safeList(regions)) {
                String id = string(region, "regionId");
                if (!id.isEmpty()) {
                    regionIds.add(id);
                    regionsById.put(id, region);
                }
            }
            for (JsonObject activation : safeList(activations)) {
                add(activationsByRegion, string(activation, "regionId"),
                        activation);
            }
            for (List<JsonObject> values : activationsByRegion.values()) {
                Collections.sort(values, Comparator.comparing(value ->
                        firstNonBlank(string(value, "activationId"),
                                string(value, "regionInstanceId"))));
            }
            for (JsonObject summary : safeList(summaries)) {
                add(summariesByRegion, string(summary, "regionId"), summary);
            }
            indexEdges(edges);
        }

        private void indexEdges(List<JsonObject> edges) {
            Map<String, Map<String, List<JsonObject>>> grouped =
                    new LinkedHashMap<>();
            for (JsonObject edge : safeList(edges)) {
                if (!AutomaticRegionEdge.discoverable(edge)) continue;
                String consumer = string(edge, "toRegion");
                String input = string(edge, "toPort");
                String relation = relation(edge);
                if (consumer.isEmpty() || input.isEmpty()) continue;
                Map<String, List<JsonObject>> byInput = grouped.get(consumer);
                if (byInput == null) {
                    byInput = new LinkedHashMap<>();
                    grouped.put(consumer, byInput);
                }
                add(byInput, canonicalPort(input) + "\n" + relation, edge);
            }
            for (Map.Entry<String, Map<String, List<JsonObject>>> region
                    : grouped.entrySet()) {
                List<EdgeGroup> groups = new ArrayList<>();
                for (List<JsonObject> alternatives : region.getValue()
                        .values()) {
                    Collections.sort(alternatives, EDGE_ORDER);
                    groups.add(new EdgeGroup(alternatives));
                }
                Collections.sort(groups, Comparator.comparing(
                        value -> value.groupSortKey));
                incomingByRegion.put(region.getKey(), groups);
            }
        }

        private Result run(List<JsonObject> roots) {
            List<JsonObject> orderedRoots = new ArrayList<>(roots);
            Collections.sort(orderedRoots, Comparator.comparing(value ->
                    firstNonBlank(string(value, "regionId"),
                            string(value, "activationId"))));
            for (JsonObject root : orderedRoots) {
                String region = string(root, "regionId");
                if (region.isEmpty()) continue;
                visitedRegions.add(region);
                List<EdgeGroup> groups = incomingByRegion.get(region);
                if (groups == null || groups.isEmpty()) {
                    gap("NO_UPSTREAM_QUERY", "ROOT_HAS_NO_COMPOSABLE_INPUT",
                            "", region, "", 0);
                    continue;
                }
                String pathHash = rootPathHash(root);
                String contextHash = rootContextHash(root);
                for (EdgeGroup group : groups) {
                    enqueue(new Work(region,
                            string(root, "regionInstanceId"), group.inputPort,
                            group.relationKind, group.stateVersion, pathHash,
                            contextHash, 0, new LinkedHashSet<String>(),
                            new LinkedHashSet<String>()));
                }
            }

            while (!pending.isEmpty()) {
                if (wallClockExceeded()) {
                    wallClockReached = true;
                    Work next = pending.peekFirst();
                    gap("BOUND_REACHED", "MAX_WALL_CLOCK", next == null
                                    ? "" : next.key,
                            next == null ? "" : next.consumerRegion,
                            next == null ? "" : next.inputPort,
                            next == null ? -1 : next.depth);
                    break;
                }
                Work work = pending.removeFirst();
                if (work.processed) continue;
                work.processed = true;
                process(work);
            }

            List<JsonObject> workItems = new ArrayList<>();
            for (Work work : workByKey.values()) workItems.add(work.toJson());
            JsonObject manifest = manifest(workItems);
            return new Result(workItems, upstreamRequests,
                    alternativeWriterGroups, manifest);
        }

        private void process(Work work) {
            List<EdgeGroup> groups = incomingByRegion.get(work.consumerRegion);
            EdgeGroup selected = null;
            if (groups != null) {
                for (EdgeGroup candidate : groups) {
                    if (candidate.matches(work.inputPort, work.relationKind,
                            work.requiredStateVersion)) {
                        selected = candidate;
                        break;
                    }
                }
            }
            if (selected == null) {
                work.status = "GAP";
                gap("MISSING_UPSTREAM_REGION", "NO_MATCHING_COMPOSABLE_EDGE",
                        work.key, work.consumerRegion, work.inputPort,
                        work.depth);
                return;
            }

            List<JsonObject> alternatives = deduplicateConcreteBindings(
                    work, selected.alternatives);
            int limit = Math.min(alternatives.size(),
                    bounds.maxAlternativeWritersPerRead);
            if (alternatives.size() > limit) {
                gap("BOUND_REACHED", "MAX_ALTERNATIVE_WRITERS_PER_READ",
                        work.key, work.consumerRegion, work.inputPort,
                        work.depth);
                work.truncated = true;
            }
            List<JsonObject> composableAlternatives = new ArrayList<>();
            for (JsonObject alternative : alternatives.subList(0, limit)) {
                if (AutomaticRegionEdge.composable(alternative)) {
                    composableAlternatives.add(alternative);
                }
            }
            if (composableAlternatives.size() > 1) {
                alternativeWriterGroups.add(alternativeGroup(work,
                        composableAlternatives));
            }

            int resolved = 0;
            boolean incompleteClosure = false;
            for (int index = 0; index < limit; index++) {
                if (exploredPaths >= bounds.maxPaths) {
                    gap("BOUND_REACHED", "MAX_PATHS", work.key,
                            work.consumerRegion, work.inputPort, work.depth);
                    work.truncated = true;
                    break;
                }
                JsonObject edge = alternatives.get(index);
                exploredPaths++;
                if (!AutomaticRegionEdge.composable(edge)) {
                    gap("UNPROVEN_REGION_EDGE",
                            AutomaticRegionEdge.exclusionReason(edge),
                            work.key, work.consumerRegion, work.inputPort,
                            work.depth);
                }
                String upstreamRegion = string(edge, "fromRegion");
                OutputRef output = resolveEdgeOutput(edge);
                if (upstreamRegion.isEmpty() || output.isEmpty()) {
                    gap("MALFORMED_UPSTREAM_EDGE", "MISSING_ENDPOINT",
                            work.key, work.consumerRegion, work.inputPort,
                            work.depth);
                    continue;
                }
                if (!regionIds.isEmpty() && !regionIds.contains(upstreamRegion)) {
                    gap("MISSING_UPSTREAM_REGION", upstreamRegion, work.key,
                            work.consumerRegion, work.inputPort, work.depth);
                    continue;
                }
                if (!visitedRegions.contains(upstreamRegion)
                        && visitedRegions.size() >= bounds.maxRegions) {
                    gap("BOUND_REACHED", "MAX_REGIONS", work.key,
                            work.consumerRegion, work.inputPort, work.depth);
                    work.truncated = true;
                    continue;
                }
                visitedRegions.add(upstreamRegion);
                JsonObject request = upstreamRequest(work, edge, index,
                        alternatives.size());
                upstreamRequests.add(request);
                incompleteClosure |= !bool(request,
                        "upstreamRelationClosureComplete", false);
                if (!AutomaticRegionEdge.composable(edge)) {
                    request.addProperty("recursiveExpansionAllowed", false);
                    request.addProperty("blockedByUnprovenEdge", true);
                    continue;
                }
                DependencyClosure closure = outputDependencyClosure(
                        upstreamRegion, output, edge, work.consumerInstance);
                request.addProperty("outputDependencyClosureAuthority",
                        closure.authority);
                request.addProperty("outputDependencyClosureComplete",
                        closure.complete);
                request.add("outputDependencyInputPorts",
                        GSON.toJsonTree(closure.inputPorts));
                if (!closure.complete) {
                    incompleteClosure = true;
                    request.addProperty("recursiveExpansionAllowed", false);
                    request.addProperty("blockedByUnprovenEdge", false);
                    request.addProperty(
                            "blockedByIncompleteOutputDependencyClosure",
                            true);
                    gap(closure.gapKind, closure.reason, work.key,
                            upstreamRegion, output.portId, work.depth);
                    continue;
                }

                request.addProperty("recursiveExpansionAllowed", true);
                request.addProperty("blockedByUnprovenEdge", false);
                request.addProperty(
                        "blockedByIncompleteOutputDependencyClosure", false);
                resolved++;

                if (closure.inputPorts.isEmpty()) {
                    request.add("recursiveBoundaryInputPorts",
                            new JsonArray());
                    request.addProperty("terminalUpstreamRegion", true);
                    continue;
                }
                List<EdgeGroup> upstream = dependencyGroups(upstreamRegion,
                        closure, request);
                request.addProperty("terminalUpstreamRegion",
                        upstream.isEmpty());
                for (EdgeGroup group : upstream) {
                    int nextDepth = work.depth + 1;
                    if (nextDepth > bounds.maxDepth) {
                        gap("BOUND_REACHED", "MAX_DEPTH", work.key,
                                upstreamRegion, group.inputPort, nextDepth);
                        work.truncated = true;
                        continue;
                    }
                    LinkedHashSet<String> ancestry = new LinkedHashSet<>(
                            work.ancestryKeys);
                    ancestry.add(work.key);
                    LinkedHashSet<String> provenance = new LinkedHashSet<>(
                            work.provenanceEdges);
                    provenance.add(firstNonBlank(string(edge, "edgeId"),
                            stableEdgeId(edge)));
                    Work next = new Work(upstreamRegion, firstUpstreamInstance(
                            request), group.inputPort, group.relationKind,
                            group.stateVersion, work.pathPrefixHash,
                            work.boundedContextHash, nextDepth, ancestry,
                            provenance);
                    next.parentQueryKeys.add(work.key);
                    if (ancestry.contains(next.key)) {
                        cycle(work, next, edge);
                        continue;
                    }
                    enqueue(next);
                }
            }
            work.resolvedAlternativeCount = resolved;
            work.status = resolved > 0
                    ? work.truncated || incompleteClosure
                    ? "PARTIAL" : "RESOLVED" : "GAP";
        }

        /**
         * A single concrete write/read pair can be attributed to several
         * overlapping static regions.  It is one runtime producer, not an
         * alternative-writer choice.  Collapse the aliases only when the
         * exact target instance and concrete event identity agree and one
         * region has a strictly better runtime-owner rank.
         */
        private List<JsonObject> deduplicateConcreteBindings(
                Work work, List<JsonObject> candidates) {
            Map<String, List<JsonObject>> groups = new LinkedHashMap<>();
            for (JsonObject edge : candidates) {
                String key = concreteBindingGroupKey(work, edge);
                if (key.isEmpty()) {
                    key = "EDGE\n" + firstNonBlank(string(edge, "edgeId"),
                            stableEdgeId(edge));
                }
                add(groups, key, edge);
            }
            List<JsonObject> result = new ArrayList<>();
            for (List<JsonObject> aliases : groups.values()) {
                if (aliases.size() == 1) {
                    result.add(aliases.get(0));
                    continue;
                }
                JsonObject best = null;
                OwnerRank bestRank = null;
                boolean tied = false;
                for (JsonObject edge : aliases) {
                    OwnerRank rank = ownerRank(work, edge);
                    int comparison = bestRank == null ? 1
                            : rank.compareTo(bestRank);
                    if (comparison > 0) {
                        best = edge;
                        bestRank = rank;
                        tied = false;
                    } else if (comparison == 0) {
                        tied = true;
                    }
                }
                if (best == null || tied) {
                    ambiguousConcreteBindingOwnerGroups++;
                    result.addAll(aliases);
                    continue;
                }
                deduplicatedConcreteBindingAlternatives += aliases.size() - 1;
                JsonObject selection = new JsonObject();
                selection.addProperty("selectedRegion", string(best,
                        "fromRegion"));
                selection.addProperty("selectedEdgeId", string(best,
                        "edgeId"));
                selection.addProperty("authority", bestRank.anchorMatchesWriter
                        ? "EXACT_BINDING_WRITER_METHOD_MATCHES_REGION_ANCHOR"
                        : "EXACT_BINDING_NARROWEST_RUNTIME_OWNER");
                selection.addProperty("concreteBindingIdentityHash",
                        shortHash(concreteBindingGroupKey(work, best)));
                JsonArray droppedRegions = new JsonArray();
                JsonArray droppedEdges = new JsonArray();
                for (JsonObject alias : aliases) {
                    if (alias == best) continue;
                    droppedRegions.add(string(alias, "fromRegion"));
                    droppedEdges.add(string(alias, "edgeId"));
                }
                selection.add("deduplicatedOverlappingRegions",
                        droppedRegions);
                selection.add("deduplicatedOverlappingEdges", droppedEdges);
                ownerSelectionsByEdge.put(firstNonBlank(string(best,
                        "edgeId"), stableEdgeId(best)), selection);
                result.add(best);
            }
            Collections.sort(result, EDGE_ORDER);
            return result;
        }

        private String concreteBindingGroupKey(Work work, JsonObject edge) {
            if (!"READ_FROM".equals(relation(edge))
                    || work.consumerInstance.isEmpty()) return "";
            JsonArray bindings = runtimeBindings(edge, work.consumerInstance);
            if (bindings.size() == 0) return "";
            Set<String> identities = new TreeSet<>();
            for (JsonElement element : bindings) {
                if (!element.isJsonObject()) return "";
                String identity = concreteBindingIdentity(
                        element.getAsJsonObject());
                if (identity.isEmpty()) return "";
                identities.add(identity);
            }
            OutputRef output = resolveEdgeOutput(edge);
            String semanticOutput = firstNonBlank(output.cell,
                    output.portId);
            return component(relation(edge))
                    + component(stateVersion(edge))
                    + component(semanticOutput)
                    + component(canonicalPort(work.inputPort))
                    + component(canonicalJson(GSON.toJsonTree(identities)));
        }

        private OwnerRank ownerRank(Work work, JsonObject edge) {
            String region = string(edge, "fromRegion");
            OutputRef output = resolveEdgeOutput(edge);
            List<JsonObject> selected = selectActivations(region, edge,
                    work.consumerInstance, output);
            JsonObject activation = selected.isEmpty()
                    ? null : selected.get(0);
            JsonObject definition = regionsById.get(region);
            int methodCount = array(definition, "methods").size();
            boolean anchorMatchesWriter = false;
            String anchorMethod = string(definition, "anchorMethod");
            for (JsonElement element : runtimeBindings(edge,
                    work.consumerInstance)) {
                if (!element.isJsonObject()) continue;
                String writerMethod = methodFromSite(string(
                        element.getAsJsonObject(), "writerSiteId"));
                anchorMatchesWriter |= !anchorMethod.isEmpty()
                        && anchorMethod.equals(writerMethod);
            }
            return new OwnerRank(activation != null, anchorMatchesWriter,
                    bool(activation, "anchorObserved", false),
                    bool(activation, "replayable", false),
                    activationOutputMatches(activation, output),
                    bool(activation, "requestedOutputSliceComplete", false),
                    bool(activation, "symbolicReady", false),
                    bool(activation, "staticInputSelectionComplete", false),
                    methodCount == 0 ? Integer.MAX_VALUE : methodCount);
        }

        /**
         * Selects only the inputs in the backward slice for the exact output
         * requested by the downstream edge.  A complete merged runtime
         * relation is preferred because its slice may have removed
         * unexecuted static alternatives; otherwise the complete static
         * output slice is used.  Region-wide input enumeration is never a
         * sound substitute for an output-specific dependency closure.
         */
        private DependencyClosure outputDependencyClosure(String region,
                                                          OutputRef output,
                                                          JsonObject edge,
                                                          String downstreamInstance) {
            List<DependencyClosure> runtime = new ArrayList<>();
            List<JsonObject> summaries = summariesByRegion.get(region);
            if (summaries != null) {
                for (JsonObject summary : summaries) {
                    if (!completeSummaryRelation(summary, output)) {
                        continue;
                    }
                    DependencyClosure candidate = summaryDependencies(
                            summary, output);
                    if (candidate.complete) runtime.add(candidate);
                }
            }
            if (!runtime.isEmpty()) {
                DependencyClosure first = runtime.get(0);
                for (int index = 1; index < runtime.size(); index++) {
                    if (!first.inputPorts.equals(runtime.get(index)
                            .inputPorts)) {
                        return DependencyClosure.gap(
                                "AMBIGUOUS_OUTPUT_DEPENDENCY_CLOSURE",
                                "COMPLETE_SUMMARIES_DISAGREE_ON_INPUT_PORTS",
                                "NONE");
                    }
                }
                return first;
            }

            JsonObject definition = regionsById.get(region);
            List<JsonObject> matching = new ArrayList<>();
            for (JsonElement element : array(definition, "outputSlices")) {
                if (!element.isJsonObject()) continue;
                JsonObject slice = element.getAsJsonObject();
                if (output.matches(string(slice, "outputPort"))
                        || output.matches(string(slice, "outputCell"))) {
                    matching.add(slice);
                }
            }
            if (matching.size() > 1) {
                return DependencyClosure.gap(
                        "AMBIGUOUS_OUTPUT_DEPENDENCY_CLOSURE",
                        "MULTIPLE_STATIC_SLICES_FOR_REQUESTED_OUTPUT",
                        "NONE");
            }
            if (matching.size() == 1) {
                JsonObject slice = matching.get(0);
                if (!bool(slice, "complete", false)) {
                    return DependencyClosure.gap(
                            "INCOMPLETE_OUTPUT_DEPENDENCY_CLOSURE",
                            "STATIC_OUTPUT_SLICE_INCOMPLETE",
                            "STATIC_OUTPUT_SLICE");
                }
                if (!hasArray(slice, "inputPorts")) {
                    return DependencyClosure.gap(
                            "INCOMPLETE_OUTPUT_DEPENDENCY_CLOSURE",
                            "STATIC_OUTPUT_SLICE_HAS_NO_INPUT_PORT_SET",
                            "STATIC_OUTPUT_SLICE");
                }
                return DependencyClosure.complete(primitiveStringSet(
                        array(slice, "inputPorts")),
                        "STATIC_REQUESTED_OUTPUT_BACKWARD_SLICE");
            }

            List<DependencyClosure> activations = new ArrayList<>();
            for (JsonObject activation : selectActivations(region, edge,
                    downstreamInstance, output)) {
                DependencyClosure candidate = activationDependencies(
                        activation, region, output);
                if (candidate.complete) activations.add(candidate);
            }
            if (!activations.isEmpty()) {
                DependencyClosure first = activations.get(0);
                for (int index = 1; index < activations.size(); index++) {
                    if (!first.inputPorts.equals(activations.get(index)
                            .inputPorts)) {
                        return DependencyClosure.gap(
                                "AMBIGUOUS_OUTPUT_DEPENDENCY_CLOSURE",
                                "COMPLETE_ACTIVATION_SLICES_DISAGREE_ON_"
                                        + "INPUT_PORTS",
                                "NONE");
                    }
                }
                return first;
            }
            return DependencyClosure.gap(
                    "MISSING_OUTPUT_DEPENDENCY_CLOSURE",
                    "NO_COMPLETE_OUTPUT_SPECIFIC_SLICE_OR_SUMMARY",
                    "NONE");
        }

        private DependencyClosure activationDependencies(
                JsonObject activation, String region, OutputRef output) {
            if (!bool(activation, "requestedOutputSliceComplete", false)) {
                return DependencyClosure.gap(
                        "INCOMPLETE_OUTPUT_DEPENDENCY_CLOSURE",
                        "ACTIVATION_OUTPUT_SLICE_INCOMPLETE", "NONE");
            }
            JsonObject requested = object(activation, "requestedOutput");
            String requestedPort = string(requested, "portId");
            String requestedCell = string(requested, "cell");
            if ((!requestedPort.isEmpty() || !requestedCell.isEmpty())
                    && !output.matches(requestedPort)
                    && !output.matches(requestedCell)) {
                return DependencyClosure.gap(
                        "INCOMPLETE_OUTPUT_DEPENDENCY_CLOSURE",
                        "ACTIVATION_REQUESTS_DIFFERENT_OUTPUT", "NONE");
            }
            if (requestedPort.isEmpty() && requestedCell.isEmpty()
                    && !uniqueRegionOutputMatches(region, output)) {
                return DependencyClosure.gap(
                        "INCOMPLETE_OUTPUT_DEPENDENCY_CLOSURE",
                        "ACTIVATION_OUTPUT_IS_NOT_UNAMBIGUOUS", "NONE");
            }
            JsonObject slice = object(activation, "requestedOutputSlice");
            if (!bool(slice, "complete", true)) {
                return DependencyClosure.gap(
                        "INCOMPLETE_OUTPUT_DEPENDENCY_CLOSURE",
                        "ACTIVATION_OUTPUT_SLICE_INCOMPLETE", "NONE");
            }
            Set<String> inputs = new TreeSet<>();
            if (hasArray(slice, "inputPorts")) {
                inputs.addAll(primitiveStringSet(array(slice, "inputPorts")));
            } else {
                addActionSymbols(inputs, array(activation, "symbolize"));
                addActionSymbols(inputs, array(activation,
                        "materializations"));
            }
            return DependencyClosure.complete(inputs,
                    "COMPLETE_OUTPUT_ACTIVATION_SLICE");
        }

        private boolean uniqueRegionOutputMatches(String region,
                                                  OutputRef expected) {
            JsonObject definition = regionsById.get(region);
            JsonArray outputs = array(definition, "outputs");
            if (outputs.size() != 1 || !outputs.get(0).isJsonObject()) {
                return false;
            }
            JsonObject output = outputs.get(0).getAsJsonObject();
            return expected.matches(string(output, "portId"))
                    || expected.matches(string(output, "cell"));
        }

        private void addActionSymbols(Set<String> inputs,
                                      JsonArray actions) {
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                String input = firstNonBlank(string(
                        element.getAsJsonObject(), "symbol"), string(
                        element.getAsJsonObject(), "inputPort"));
                if (!input.isEmpty()) inputs.add(canonicalPort(input));
            }
        }

        private DependencyClosure summaryDependencies(JsonObject summary,
                                                      OutputRef output) {
            JsonObject slice = object(summary, "requestedOutputSlice");
            JsonObject requested = object(summary, "requestedOutput");
            boolean sliceMatches = output.matches(string(slice,
                    "outputPort")) || output.matches(string(slice,
                    "outputCell")) || output.matches(string(requested,
                    "portId")) || output.matches(string(requested, "cell"));
            boolean sliceComplete = bool(summary,
                    "requestedOutputSliceComplete",
                    bool(slice, "complete", false));
            if (sliceMatches && sliceComplete
                    && hasArray(slice, "inputPorts")) {
                return DependencyClosure.complete(primitiveStringSet(
                        array(slice, "inputPorts")),
                        "COMPLETE_RUNTIME_REGION_RELATION_OUTPUT_SLICE");
            }

            JsonObject relation = object(summary, "regionRelation");
            if (hasArray(relation, "inputPorts")) {
                return DependencyClosure.complete(primitiveStringSet(
                        array(relation, "inputPorts")),
                        "COMPLETE_RUNTIME_REGION_RELATION_DEPENDENCIES");
            }
            if (hasArray(relation, "dependencyInputPorts")) {
                return DependencyClosure.complete(primitiveStringSet(
                        array(relation, "dependencyInputPorts")),
                        "COMPLETE_RUNTIME_REGION_RELATION_DEPENDENCIES");
            }
            if (hasArray(relation, "dependencies")) {
                Set<String> ports = new TreeSet<>();
                for (JsonElement element : array(relation,
                        "dependencies")) {
                    if (element.isJsonPrimitive()) {
                        ports.add(canonicalPort(element.getAsString()));
                    } else if (element.isJsonObject()) {
                        String port = firstNonBlank(string(
                                element.getAsJsonObject(), "inputPort"),
                                string(element.getAsJsonObject(), "portId"));
                        if (!port.isEmpty()) ports.add(canonicalPort(port));
                    }
                }
                return DependencyClosure.complete(ports,
                        "COMPLETE_RUNTIME_REGION_RELATION_DEPENDENCIES");
            }
            return DependencyClosure.gap(
                    "INCOMPLETE_OUTPUT_DEPENDENCY_CLOSURE",
                    "COMPLETE_SUMMARY_HAS_NO_OUTPUT_DEPENDENCY_SET",
                    "COMPLETE_RUNTIME_REGION_RELATION");
        }

        private List<EdgeGroup> dependencyGroups(String region,
                                                 DependencyClosure closure,
                                                 JsonObject request) {
            List<EdgeGroup> available = incomingByRegion.get(region);
            List<EdgeGroup> result = new ArrayList<>();
            Set<String> boundaryInputs = new TreeSet<>();
            for (String inputPort : closure.inputPorts) {
                boolean matched = false;
                if (available != null) {
                    for (EdgeGroup group : available) {
                        if (sameRegionInputEndpoint(region, inputPort,
                                group.inputPort)) {
                            result.add(group);
                            matched = true;
                        }
                    }
                }
                if (!matched) {
                    // No discoverable cross-region writer makes this an
                    // explicit symbolic boundary leaf.  The worklist's
                    // soundness scope is validated edges; it must not invent
                    // a producer equality, but it also need not reject a
                    // complete region relation whose input is exogenous.
                    boundaryInputs.add(inputPort);
                }
            }
            request.add("recursiveBoundaryInputPorts",
                    GSON.toJsonTree(boundaryInputs));
            Collections.sort(result, Comparator.comparing(
                    value -> value.groupSortKey));
            return result;
        }

        /**
         * Static output slices name dependencies by stable input port id,
         * while runtime-validated region edges retain the corresponding
         * source-level cell.  They are the same endpoint when one unique
         * symbolic-input declaration binds both names.  Keep this resolution
         * local to the consumer region so identical field signatures in two
         * regions cannot alias accidentally.
         */
        private boolean sameRegionInputEndpoint(String region,
                                                String left,
                                                String right) {
            String canonicalLeft = canonicalPort(left);
            String canonicalRight = canonicalPort(right);
            if (canonicalLeft.equals(canonicalRight)) return true;
            JsonObject definition = regionsById.get(region);
            int leftMatches = 0;
            int rightMatches = 0;
            JsonObject shared = null;
            for (JsonElement element : array(definition,
                    "symbolicInputs")) {
                if (!element.isJsonObject()) continue;
                JsonObject input = element.getAsJsonObject();
                boolean matchesLeft = inputEndpointMatches(input,
                        canonicalLeft);
                boolean matchesRight = inputEndpointMatches(input,
                        canonicalRight);
                if (matchesLeft) leftMatches++;
                if (matchesRight) rightMatches++;
                if (matchesLeft && matchesRight) shared = input;
            }
            return shared != null && leftMatches == 1 && rightMatches == 1;
        }

        private boolean inputEndpointMatches(JsonObject input,
                                             String endpoint) {
            return !endpoint.isEmpty()
                    && (endpoint.equals(canonicalPort(string(input,
                    "portId"))) || endpoint.equals(canonicalPort(string(
                    input, "cell"))));
        }

        private void enqueue(Work work) {
            Work previous = workByKey.get(work.key);
            if (previous != null) {
                previous.provenanceEdges.addAll(work.provenanceEdges);
                previous.parentQueryKeys.addAll(work.parentQueryKeys);
                deduplicatedQueries++;
                return;
            }
            if (workByKey.size() >= bounds.maxQueries) {
                gap("BOUND_REACHED", "MAX_QUERIES", work.key,
                        work.consumerRegion, work.inputPort, work.depth);
                return;
            }
            workByKey.put(work.key, work);
            pending.addLast(work);
        }

        private JsonObject upstreamRequest(Work work, JsonObject edge,
                                           int alternativeIndex,
                                           int alternativeCount) {
            String upstreamRegion = string(edge, "fromRegion");
            OutputRef output = resolveEdgeOutput(edge);
            JsonObject result = new JsonObject();
            result.addProperty("requestId", "UPSTREAM.REQUEST."
                    + shortHash(work.key + "\n" + stableEdgeId(edge)));
            RegionCaptureGoal.outputClosure().writeTo(result);
            result.addProperty("queryKey", work.key);
            result.addProperty("depth", work.depth);
            result.addProperty("upstreamRegion", upstreamRegion);
            result.addProperty("upstreamOutputPort", output.portId);
            result.addProperty("upstreamOutputCell", output.cell);
            result.addProperty("edgeOutputEndpoint", string(edge,
                    "fromPort"));
            result.addProperty("downstreamRegion", work.consumerRegion);
            result.addProperty("downstreamRegionInstance",
                    work.consumerInstance);
            result.addProperty("downstreamInputPort", work.inputPort);
            result.addProperty("relationKind", work.relationKind);
            result.addProperty("automaticRelationEligible",
                    AutomaticRegionEdge.composable(edge));
            result.addProperty("automaticRelationExclusionReason",
                    AutomaticRegionEdge.exclusionReason(edge));
            result.addProperty("edgeId", string(edge, "edgeId"));
            JsonObject ownerSelection = ownerSelectionsByEdge.get(
                    firstNonBlank(string(edge, "edgeId"),
                            stableEdgeId(edge)));
            if (ownerSelection != null) {
                result.add("dynamicOwnerSelection",
                        ownerSelection.deepCopy());
            }
            result.addProperty("alternativeIndex", alternativeIndex);
            result.addProperty("alternativeCount", alternativeCount);
            result.addProperty("guardSymbol", guardSymbol(work, edge));
            result.add("runtimeEvidence", runtimeBindings(edge,
                    work.consumerInstance).deepCopy());

            JsonArray activationIds = new JsonArray();
            List<JsonObject> selected = selectActivations(upstreamRegion,
                    edge, work.consumerInstance, output);
            int activationLimit = Math.min(selected.size(),
                    bounds.maxActivationsPerRegion);
            if (selected.size() > activationLimit) {
                gap("BOUND_REACHED", "MAX_ACTIVATIONS_PER_REGION",
                        work.key, upstreamRegion, output.portId,
                        work.depth);
            }
            for (int index = 0; index < activationLimit; index++) {
                JsonObject activation = selected.get(index);
                JsonObject reference = new JsonObject();
                reference.addProperty("activationId", string(activation,
                        "activationId"));
                reference.addProperty("regionInstanceId", string(activation,
                        "regionInstanceId"));
                reference.addProperty("invocationOrdinal", integer(activation,
                        "invocationOrdinal", -1));
                activationIds.add(reference);
            }
            result.add("upstreamActivations", activationIds);

            JsonObject cache = summaryCache(upstreamRegion,
                    output, edge, work.consumerInstance);
            result.add("summaryCache", cache);
            String cacheStatus = string(cache, "status");
            boolean cacheHit = "HIT_COMPLETE".equals(cacheStatus)
                    || "HIT_PATHS_PENDING".equals(cacheStatus);
            boolean automaticallyEligible = AutomaticRegionEdge.composable(
                    edge);
            boolean relationClosureComplete = "HIT_COMPLETE".equals(
                    cacheStatus);
            result.addProperty("upstreamRelationClosureComplete",
                    relationClosureComplete);
            result.addProperty("captureRequired",
                    automaticallyEligible && !cacheHit);
            result.addProperty("captureDeferredUntilEdgeValidation",
                    !automaticallyEligible && !cacheHit);
            result.addProperty("pathClosureRequired",
                    automaticallyEligible
                            && "HIT_PATHS_PENDING".equals(cacheStatus));
            if (automaticallyEligible && !cacheHit
                    && activationIds.size() == 0) {
                gap("MISSING_UPSTREAM_ACTIVATION",
                        "NO_RUNTIME_ACTIVATION_OR_COMPLETE_CACHE", work.key,
                        upstreamRegion, output.portId, work.depth);
            }
            if (automaticallyEligible && !relationClosureComplete) {
                gap("INCOMPLETE_UPSTREAM_REGION_RELATION",
                        "SUMMARY_CACHE_" + firstNonBlank(cacheStatus,
                        "UNKNOWN"), work.key, upstreamRegion,
                        output.portId, work.depth);
            }
            return result;
        }

        private List<JsonObject> selectActivations(String upstreamRegion,
                                                   JsonObject edge,
                                                   String downstreamInstance,
                                                   OutputRef output) {
            List<JsonObject> available = activationsByRegion.get(upstreamRegion);
            if (available == null) return Collections.emptyList();
            JsonArray allBindings = runtimeBindings(edge, "");
            JsonArray exactBindings = runtimeBindings(edge,
                    downstreamInstance);
            if (!downstreamInstance.isEmpty() && allBindings.size() > 0
                    && exactBindings.size() == 0) {
                return Collections.emptyList();
            }
            Set<String> evidenced = new LinkedHashSet<>();
            for (JsonElement element : exactBindings) {
                if (!element.isJsonObject()) continue;
                String instance = string(element.getAsJsonObject(),
                        "fromRegionInstance");
                if (!instance.isEmpty()) evidenced.add(instance);
            }
            if (exactBindings.size() > 0 && evidenced.isEmpty()) {
                return Collections.emptyList();
            }
            Map<String, JsonObject> selectedByInstance = new LinkedHashMap<>();
            Map<String, Integer> selectedScores = new LinkedHashMap<>();
            for (JsonObject activation : available) {
                String instance = string(activation, "regionInstanceId");
                if (!evidenced.isEmpty() && !evidenced.contains(instance)) {
                    continue;
                }
                int score = activationSelectionScore(activation, edge,
                        downstreamInstance, output, exactBindings);
                if (score == Integer.MIN_VALUE) continue;
                Integer previousScore = selectedScores.get(instance);
                if (previousScore == null || score > previousScore) {
                    selectedByInstance.put(instance, activation);
                    selectedScores.put(instance, score);
                }
            }
            List<JsonObject> result = new ArrayList<>(
                    selectedByInstance.values());
            Collections.sort(result, Comparator.comparing(value ->
                    firstNonBlank(string(value, "regionInstanceId"),
                            string(value, "activationId"))));
            return result;
        }

        private int activationSelectionScore(JsonObject activation,
                                             JsonObject edge,
                                             String downstreamInstance,
                                             OutputRef output,
                                             JsonArray exactBindings) {
            JsonArray activationBindings = array(activation, "edgeBindings");
            boolean bindingMatch = false;
            for (JsonElement element : activationBindings) {
                if (!element.isJsonObject()) continue;
                if (activationBindingMatches(element.getAsJsonObject(), edge,
                        downstreamInstance, output, exactBindings)) {
                    bindingMatch = true;
                    break;
                }
            }
            if (activationBindings.size() > 0 && !bindingMatch
                    && (!downstreamInstance.isEmpty()
                    || exactBindings.size() > 0)) {
                return Integer.MIN_VALUE;
            }
            int score = bindingMatch ? 100_000 : 0;
            if (activationOutputMatches(activation, output)) score += 10_000;
            if (RegionCaptureGoal.from(activation).isOutputClosure()) {
                score += 1_000;
            }
            if (bool(activation, "requestedOutputSliceComplete", false)) {
                score += 100;
            }
            if (bool(activation, "anchorObserved", false)) score += 40;
            if (bool(activation, "replayable", false)) score += 20;
            if (bool(activation, "symbolicReady", false)) score += 10;
            if (bool(activation, "schedulerReady", false)) score += 5;
            return score;
        }

        private boolean activationBindingMatches(JsonObject candidate,
                                                 JsonObject edge,
                                                 String downstreamInstance,
                                                 OutputRef output,
                                                 JsonArray exactBindings) {
            String requestedEdge = string(edge, "edgeId");
            if (!requestedEdge.isEmpty()
                    && !requestedEdge.equals(string(candidate, "edgeId"))) {
                return false;
            }
            if (!downstreamInstance.isEmpty() && !downstreamInstance.equals(
                    string(candidate, "toRegionInstance"))) return false;
            if (!endpointMatches(output, candidate, "fromOutputPort",
                    "fromOutputCell")) return false;
            OutputRef input = new OutputRef(string(edge, "toPort"),
                    string(edge, "toCell"));
            if (!endpointMatches(input, candidate, "toInputPort",
                    "toInputCell")) return false;
            if (exactBindings.size() == 0) return true;
            for (JsonElement element : exactBindings) {
                if (!element.isJsonObject()) continue;
                JsonObject exact = element.getAsJsonObject();
                String exactFrom = string(exact, "fromRegionInstance");
                String candidateFrom = string(candidate,
                        "fromRegionInstance");
                if (!exactFrom.isEmpty() && !exactFrom.equals(candidateFrom)) {
                    continue;
                }
                if (sameConcreteBinding(candidate, exact)) return true;
            }
            return false;
        }

        private boolean activationOutputMatches(JsonObject activation,
                                                OutputRef output) {
            JsonObject requested = object(activation, "requestedOutput");
            return output.matches(string(requested, "portId"))
                    || output.matches(string(requested, "cell"));
        }

        private boolean endpointMatches(OutputRef endpoint,
                                        JsonObject binding,
                                        String portField,
                                        String cellField) {
            return endpoint.isEmpty()
                    || endpoint.matches(string(binding, portField))
                    || endpoint.matches(string(binding, cellField));
        }

        private JsonObject summaryCache(String region, OutputRef output,
                                        JsonObject edge,
                                        String downstreamInstance) {
            JsonObject result = new JsonObject();
            List<JsonObject> values = summariesByRegion.get(region);
            if (values == null || values.isEmpty()) {
                result.addProperty("status", "MISS");
                return result;
            }
            boolean observedPath = false;
            int matchingSummaryCount = 0;
            for (JsonObject summary : values) {
                if (!bool(summary, "valid", true)) continue;
                if (!requestedOutputMatches(summary, output)) continue;
                matchingSummaryCount++;
                if (completeSummaryRelation(summary, output)
                        && outputDependencyClosure(region, output, edge,
                        downstreamInstance).complete) {
                    result.addProperty("status", "HIT_COMPLETE");
                    result.addProperty("summaryId", string(summary,
                            "summaryId"));
                    result.addProperty("activationId", string(summary,
                            "activationId"));
                    return result;
                }
                JsonObject slice = object(summary, "requestedOutputSlice");
                boolean sliceComplete = bool(summary,
                        "requestedOutputSliceComplete",
                        bool(slice, "complete", false));
                observedPath |= RegionCaptureGoal.from(summary)
                        .isOutputClosure() && sliceComplete
                        && hasArray(slice, "inputPorts");
            }
            if (observedPath) {
                result.addProperty("status", "HIT_PATHS_PENDING");
                result.addProperty("summaryCount", matchingSummaryCount);
                result.addProperty("captureSeedRequired", false);
                result.addProperty("pathClosureRequired", true);
                return result;
            }
            if (matchingSummaryCount == 0) {
                result.addProperty("status", "MISS");
                result.addProperty("summaryCount", 0);
                return result;
            }
            result.addProperty("status", "HIT_INCOMPLETE");
            result.addProperty("summaryCount", matchingSummaryCount);
            return result;
        }

        private boolean completeSummaryRelation(JsonObject summary,
                                                OutputRef output) {
            if (!bool(summary, "valid", true)
                    || !bool(summary, "relationallyComplete", false)
                    || !requestedOutputMatches(summary, output)) {
                return false;
            }
            JsonObject relation = object(summary, "regionRelation");
            return "GUARDED_PATH_MERGE".equals(string(relation, "kind"))
                    && bool(relation, "complete", false);
        }

        private boolean requestedOutputMatches(JsonObject summary,
                                               OutputRef output) {
            JsonObject requested = object(summary, "requestedOutput");
            return !output.isEmpty()
                    && (output.matches(string(requested, "portId"))
                    || output.matches(string(requested, "cell")));
        }

        private OutputRef resolveOutput(String regionId,
                                        String requestedPortOrCell) {
            String requested = canonicalPort(requestedPortOrCell);
            JsonObject definition = regionsById.get(regionId);
            List<JsonObject> matches = new ArrayList<>();
            for (JsonElement element : array(definition, "outputs")) {
                if (!element.isJsonObject()) continue;
                JsonObject output = element.getAsJsonObject();
                if (requested.equals(canonicalPort(string(output, "portId")))
                        || requested.equals(canonicalPort(string(output,
                        "cell")))) {
                    matches.add(output);
                }
            }
            if (matches.size() == 1) {
                JsonObject output = matches.get(0);
                return new OutputRef(firstNonBlank(string(output, "portId"),
                        requested), string(output, "cell"));
            }
            return new OutputRef(requested, "");
        }

        /**
         * Resolves a validated edge's producer output.  Legacy edges with no
         * canonical schema retain exact raw-endpoint behavior.  Once any
         * canonical field is present, however, the schema is atomic: an exact
         * authority, complete non-empty proof set, and one matching port/cell
         * pair are all required.  A partial record returns an empty endpoint
         * instead of falling back to a similarly named raw local.
         */
        private OutputRef resolveEdgeOutput(JsonObject edge) {
            String regionId = string(edge, "fromRegion");
            if (!hasCanonicalOutputMetadata(edge)) {
                return resolveOutput(regionId, string(edge, "fromPort"));
            }
            if (!bool(edge, "aliasProofComplete", false)
                    || !("STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                    + "AND_DECLARED_RETURN_FIELD").equals(string(edge,
                    "aliasProofAuthority"))
                    || string(edge, "fromOutputPort").isEmpty()
                    || string(edge, "fromOutputCell").isEmpty()
                    || !nonEmptyProofIds(edge)) {
                return new OutputRef("", "");
            }
            String expectedPort = canonicalPort(string(edge,
                    "fromOutputPort"));
            String expectedCell = canonicalPort(string(edge,
                    "fromOutputCell"));
            JsonObject definition = regionsById.get(regionId);
            JsonObject match = null;
            for (JsonElement element : array(definition, "outputs")) {
                if (!element.isJsonObject()) continue;
                JsonObject output = element.getAsJsonObject();
                if (!expectedPort.equals(canonicalPort(string(output,
                        "portId"))) || !expectedCell.equals(canonicalPort(
                        string(output, "cell")))) {
                    continue;
                }
                if (match != null) return new OutputRef("", "");
                match = output;
            }
            return match == null ? new OutputRef("", "")
                    : new OutputRef(string(match, "portId"),
                    string(match, "cell"));
        }

        private boolean hasCanonicalOutputMetadata(JsonObject edge) {
            return edge != null && (edge.has("fromOutputPort")
                    || edge.has("fromOutputCell")
                    || edge.has("aliasProofEdgeIds")
                    || edge.has("aliasProofAuthority")
                    || edge.has("aliasProofComplete"));
        }

        private boolean nonEmptyProofIds(JsonObject edge) {
            JsonArray ids = array(edge, "aliasProofEdgeIds");
            if (ids.size() == 0) return false;
            for (JsonElement id : ids) {
                if (!id.isJsonPrimitive()
                        || id.getAsString().trim().isEmpty()) return false;
            }
            return true;
        }

        private JsonObject alternativeGroup(Work work,
                                            List<JsonObject> alternatives) {
            JsonObject group = new JsonObject();
            group.addProperty("groupId", "WRITER.GROUP."
                    + shortHash(work.key));
            group.addProperty("queryKey", work.key);
            group.addProperty("downstreamRegion", work.consumerRegion);
            group.addProperty("downstreamInputPort", work.inputPort);
            group.addProperty("selectionSemantics", "EXACTLY_ONE_GUARDED");
            JsonArray values = new JsonArray();
            for (JsonObject edge : alternatives) {
                JsonObject alternative = new JsonObject();
                alternative.addProperty("guardSymbol", guardSymbol(work,
                        edge));
                alternative.addProperty("edgeId", string(edge, "edgeId"));
                alternative.addProperty("upstreamRegion", string(edge,
                        "fromRegion"));
                OutputRef output = resolveEdgeOutput(edge);
                alternative.addProperty("upstreamOutputPort", output.portId);
                alternative.addProperty("upstreamOutputCell", output.cell);
                alternative.add("runtimeEvidence",
                        runtimeBindings(edge,
                                work.consumerInstance).deepCopy());
                values.add(alternative);
            }
            group.add("alternatives", values);
            return group;
        }

        private JsonArray runtimeBindings(JsonObject edge,
                                          String downstreamInstance) {
            JsonArray validated = array(edge, "validatedBindings");
            JsonArray source = validated.size() > 0
                    ? validated : array(edge, "evidence");
            if (downstreamInstance == null
                    || downstreamInstance.isEmpty()) return source;
            JsonArray exact = new JsonArray();
            for (JsonElement element : source) {
                if (!element.isJsonObject()) continue;
                if (downstreamInstance.equals(string(element.getAsJsonObject(),
                        "toRegionInstance"))) exact.add(element);
            }
            return exact;
        }

        private void cycle(Work from, Work repeated, JsonObject edge) {
            JsonObject cycle = new JsonObject();
            cycle.addProperty("kind", "CYCLE_DETECTED");
            cycle.addProperty("fromQueryKey", from.key);
            cycle.addProperty("repeatedQueryKey", repeated.key);
            cycle.addProperty("edgeId", string(edge, "edgeId"));
            cycle.addProperty("depth", repeated.depth);
            cycle.add("ancestry", GSON.toJsonTree(repeated.ancestryKeys));
            cycles.add(cycle);
            gap("CYCLE_DETECTED", "REPEATED_REGION_STATE_CONTEXT",
                    repeated.key, repeated.consumerRegion,
                    repeated.inputPort, repeated.depth);
        }

        private void gap(String kind, String reason, String queryKey,
                         String region, String port, int depth) {
            String key = kind + "\n" + reason + "\n" + queryKey + "\n"
                    + region + "\n" + canonicalPort(port) + "\n" + depth;
            if (!gapKeys.add(key)) return;
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("reason", reason);
            gap.addProperty("queryKey", queryKey);
            gap.addProperty("region", region);
            gap.addProperty("port", port);
            gap.addProperty("depth", depth);
            gaps.add(gap);
        }

        private JsonObject manifest(List<JsonObject> workItems) {
            JsonObject manifest = new JsonObject();
            manifest.addProperty("schemaVersion", 1);
            manifest.addProperty("kind", "RECURSIVE_REGION_WORKLIST");
            manifest.addProperty("stableKeyAlgorithm",
                    "SHA-256_CANONICAL_SEMANTIC_QUERY_V1");
            manifest.addProperty("dynamicIdsExcludedFromStableKey", true);
            manifest.add("bounds", bounds.toJson());
            manifest.addProperty("workItemCount", workItems.size());
            manifest.addProperty("upstreamRequestCount",
                    upstreamRequests.size());
            manifest.addProperty("deduplicatedQueryCount",
                    deduplicatedQueries);
            manifest.addProperty("deduplicatedConcreteBindingAlternativeCount",
                    deduplicatedConcreteBindingAlternatives);
            manifest.addProperty("ambiguousConcreteBindingOwnerGroupCount",
                    ambiguousConcreteBindingOwnerGroups);
            manifest.addProperty("visitedRegionCount", visitedRegions.size());
            manifest.add("visitedRegions", GSON.toJsonTree(visitedRegions));
            manifest.addProperty("exploredPathCount", exploredPaths);
            manifest.addProperty("alternativeWriterGroupCount",
                    alternativeWriterGroups.size());
            manifest.addProperty("cycleCount", cycles.size());
            manifest.add("cycles", GSON.toJsonTree(cycles));
            manifest.addProperty("gapCount", gaps.size());
            manifest.add("gaps", GSON.toJsonTree(gaps));
            manifest.addProperty("wallClockBoundReached", wallClockReached);
            manifest.addProperty("complete", gaps.isEmpty());
            manifest.addProperty("status", gaps.isEmpty()
                    ? "COMPLETE_BOUNDED_REGION_CLOSURE"
                    : "REGION_CLOSURE_WITH_EXPLICIT_GAPS");
            manifest.addProperty("soundnessScope",
                    "VALIDATED_EDGES_WITHIN_DECLARED_BOUNDS");
            return manifest;
        }

        private boolean wallClockExceeded() {
            long elapsedMillis = (System.nanoTime() - startedNanos)
                    / 1_000_000L;
            return elapsedMillis >= bounds.maxWallClockMillis;
        }
    }

    private static final class OutputRef {
        private final String portId;
        private final String cell;

        private OutputRef(String portId, String cell) {
            this.portId = canonicalPort(portId);
            this.cell = canonicalPort(cell);
        }

        private boolean isEmpty() {
            return portId.isEmpty() && cell.isEmpty();
        }

        private boolean matches(String candidate) {
            String value = canonicalPort(candidate);
            return !value.isEmpty() && (value.equals(portId)
                    || value.equals(cell));
        }
    }

    private static final class OwnerRank implements Comparable<OwnerRank> {
        private final boolean exactActivation;
        private final boolean anchorMatchesWriter;
        private final boolean anchorObserved;
        private final boolean replayable;
        private final boolean outputMatched;
        private final boolean outputSliceComplete;
        private final boolean symbolicReady;
        private final boolean staticInputSelectionComplete;
        private final int methodCount;

        private OwnerRank(boolean exactActivation,
                          boolean anchorMatchesWriter,
                          boolean anchorObserved, boolean replayable,
                          boolean outputMatched,
                          boolean outputSliceComplete,
                          boolean symbolicReady,
                          boolean staticInputSelectionComplete,
                          int methodCount) {
            this.exactActivation = exactActivation;
            this.anchorMatchesWriter = anchorMatchesWriter;
            this.anchorObserved = anchorObserved;
            this.replayable = replayable;
            this.outputMatched = outputMatched;
            this.outputSliceComplete = outputSliceComplete;
            this.symbolicReady = symbolicReady;
            this.staticInputSelectionComplete =
                    staticInputSelectionComplete;
            this.methodCount = methodCount;
        }

        @Override
        public int compareTo(OwnerRank other) {
            int value = Boolean.compare(exactActivation,
                    other.exactActivation);
            if (value != 0) return value;
            value = Boolean.compare(anchorMatchesWriter,
                    other.anchorMatchesWriter);
            if (value != 0) return value;
            value = Boolean.compare(anchorObserved, other.anchorObserved);
            if (value != 0) return value;
            // After the concrete writer/anchor match, the smaller static
            // method closure is the more precise overlapping owner.
            value = Integer.compare(other.methodCount, methodCount);
            if (value != 0) return value;
            value = Boolean.compare(replayable, other.replayable);
            if (value != 0) return value;
            value = Boolean.compare(outputMatched, other.outputMatched);
            if (value != 0) return value;
            value = Boolean.compare(outputSliceComplete,
                    other.outputSliceComplete);
            if (value != 0) return value;
            value = Boolean.compare(symbolicReady, other.symbolicReady);
            if (value != 0) return value;
            return Boolean.compare(staticInputSelectionComplete,
                    other.staticInputSelectionComplete);
        }
    }

    private static final class EdgeGroup {
        private final String inputPort;
        private final String relationKind;
        private final String stateVersion;
        private final List<JsonObject> alternatives;
        private final String groupSortKey;

        private EdgeGroup(List<JsonObject> alternatives) {
            this.alternatives = new ArrayList<>(alternatives);
            JsonObject first = alternatives.get(0);
            inputPort = string(first, "toPort");
            relationKind = relation(first);
            stateVersion = stateVersion(first);
            groupSortKey = canonicalPort(inputPort) + "\n" + relationKind
                    + "\n" + stateVersion;
        }

        private boolean matches(String input, String relation,
                                String version) {
            return canonicalPort(inputPort).equals(canonicalPort(input))
                    && relationKind.equals(relation)
                    && stateVersion.equals(version);
        }
    }

    private static final class DependencyClosure {
        private final boolean complete;
        private final Set<String> inputPorts;
        private final String authority;
        private final String gapKind;
        private final String reason;

        private DependencyClosure(boolean complete, Set<String> inputPorts,
                                  String authority, String gapKind,
                                  String reason) {
            this.complete = complete;
            this.inputPorts = Collections.unmodifiableSet(
                    new LinkedHashSet<>(inputPorts));
            this.authority = authority;
            this.gapKind = gapKind;
            this.reason = reason;
        }

        private static DependencyClosure complete(Set<String> inputPorts,
                                                  String authority) {
            return new DependencyClosure(true, inputPorts, authority, "", "");
        }

        private static DependencyClosure gap(String kind, String reason,
                                             String authority) {
            return new DependencyClosure(false,
                    Collections.<String>emptySet(), authority, kind, reason);
        }
    }

    private static final class Work {
        private final String consumerRegion;
        private final String consumerInstance;
        private final String inputPort;
        private final String relationKind;
        private final String requiredStateVersion;
        private final String pathPrefixHash;
        private final String boundedContextHash;
        private final int depth;
        private final String key;
        private final LinkedHashSet<String> ancestryKeys;
        private final LinkedHashSet<String> provenanceEdges;
        private final LinkedHashSet<String> parentQueryKeys =
                new LinkedHashSet<>();
        private boolean processed;
        private boolean truncated;
        private int resolvedAlternativeCount;
        private String status = "PENDING";

        private Work(String consumerRegion, String consumerInstance,
                     String inputPort, String relationKind,
                     String requiredStateVersion, String pathPrefixHash,
                     String boundedContextHash, int depth,
                     LinkedHashSet<String> ancestryKeys,
                     LinkedHashSet<String> provenanceEdges) {
            this.consumerRegion = consumerRegion;
            this.consumerInstance = consumerInstance;
            this.inputPort = inputPort;
            this.relationKind = relationKind;
            this.requiredStateVersion = requiredStateVersion;
            this.pathPrefixHash = pathPrefixHash;
            this.boundedContextHash = boundedContextHash;
            this.depth = depth;
            this.ancestryKeys = ancestryKeys;
            this.provenanceEdges = provenanceEdges;
            this.key = stableQueryKey(consumerRegion, inputPort,
                    relationKind, requiredStateVersion, pathPrefixHash,
                    boundedContextHash);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("queryKey", key);
            result.addProperty("downstreamRegion", consumerRegion);
            result.addProperty("consumerInstance", consumerInstance);
            result.addProperty("inputPort", inputPort);
            result.addProperty("relationKind", relationKind);
            result.addProperty("requiredStateVersion",
                    requiredStateVersion);
            result.addProperty("pathPrefixHash", pathPrefixHash);
            result.addProperty("boundedContextHash", boundedContextHash);
            result.addProperty("depth", depth);
            result.addProperty("status", status);
            result.addProperty("truncated", truncated);
            result.addProperty("resolvedAlternativeCount",
                    resolvedAlternativeCount);
            result.add("provenanceEdges", GSON.toJsonTree(provenanceEdges));
            result.add("parentQueryKeys", GSON.toJsonTree(parentQueryKeys));
            return result;
        }
    }

    public static final class Bounds {
        public final int maxDepth;
        public final int maxRegions;
        public final int maxActivationsPerRegion;
        public final int maxAlternativeWritersPerRead;
        public final int maxQueries;
        public final int maxPaths;
        public final long maxWallClockMillis;

        public Bounds(int maxDepth, int maxRegions,
                      int maxActivationsPerRegion,
                      int maxAlternativeWritersPerRead, int maxQueries,
                      int maxPaths, long maxWallClockMillis) {
            this.maxDepth = Math.max(0, maxDepth);
            this.maxRegions = Math.max(1, maxRegions);
            this.maxActivationsPerRegion = Math.max(1,
                    maxActivationsPerRegion);
            this.maxAlternativeWritersPerRead = Math.max(1,
                    maxAlternativeWritersPerRead);
            this.maxQueries = Math.max(1, maxQueries);
            this.maxPaths = Math.max(1, maxPaths);
            this.maxWallClockMillis = Math.max(1L, maxWallClockMillis);
        }

        public static Bounds defaults() {
            return new Bounds(8, 64, 8, 8, 256, 512, 30_000L);
        }

        private JsonObject toJson() {
            JsonObject value = new JsonObject();
            value.addProperty("maxDepth", maxDepth);
            value.addProperty("maxRegions", maxRegions);
            value.addProperty("maxActivationsPerRegion",
                    maxActivationsPerRegion);
            value.addProperty("maxAlternativeWritersPerRead",
                    maxAlternativeWritersPerRead);
            value.addProperty("maxQueries", maxQueries);
            value.addProperty("maxPaths", maxPaths);
            value.addProperty("maxWallClockMillis", maxWallClockMillis);
            return value;
        }
    }

    public static final class Result {
        public final List<JsonObject> workItems;
        public final List<JsonObject> upstreamRequests;
        public final List<JsonObject> alternativeWriterGroups;
        public final JsonObject manifest;

        private Result(List<JsonObject> workItems,
                       List<JsonObject> upstreamRequests,
                       List<JsonObject> alternativeWriterGroups,
                       JsonObject manifest) {
            this.workItems = workItems;
            this.upstreamRequests = upstreamRequests;
            this.alternativeWriterGroups = alternativeWriterGroups;
            this.manifest = manifest;
        }
    }

    private static String firstUpstreamInstance(JsonObject request) {
        JsonArray activations = array(request, "upstreamActivations");
        return activations.size() == 0 ? "" : string(
                activations.get(0).getAsJsonObject(), "regionInstanceId");
    }

    private static String rootPathHash(JsonObject root) {
        JsonObject stable = new JsonObject();
        stable.addProperty("regionId", string(root, "regionId"));
        stable.addProperty("rootMethod", string(root, "rootMethod"));
        JsonArray branches = new JsonArray();
        for (JsonElement element : array(root, "branches")) {
            if (!element.isJsonObject()) continue;
            JsonObject source = element.getAsJsonObject();
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", string(source, "siteId"));
            branch.addProperty("requiredOutcome", bool(source,
                    "requiredOutcome", false));
            branch.addProperty("policy", string(source, "policy"));
            branches.add(branch);
        }
        stable.add("branches", branches);
        return sha256(canonicalJson(stable));
    }

    private static String rootContextHash(JsonObject root) {
        return sha256(component(string(root, "test"))
                + component(string(root, "regionId"))
                + component(string(root, "rootMethod")));
    }

    private static String guardSymbol(Work work, JsonObject edge) {
        return "writer_guard__" + shortHash(work.key + "\n"
                + stableEdgeId(edge));
    }

    private static String stableEdgeId(JsonObject edge) {
        return sha256(component(string(edge, "fromRegion"))
                + component(canonicalPort(string(edge, "fromPort")))
                + component(string(edge, "toRegion"))
                + component(canonicalPort(string(edge, "toPort")))
                + component(relation(edge))
                + component(stateVersion(edge)));
    }

    private static String edgeSortKey(JsonObject edge) {
        return string(edge, "fromRegion") + "\n"
                + canonicalPort(string(edge, "fromPort")) + "\n"
                + firstNonBlank(string(edge, "edgeId"), stableEdgeId(edge));
    }

    private static String relation(JsonObject edge) {
        return firstNonBlank(string(edge, "validatedRelation"),
                string(edge, "candidateRelation"),
                string(edge, "relation"), "UNKNOWN");
    }

    private static String stateVersion(JsonObject edge) {
        return firstNonBlank(string(edge, "requiredStateVersion"),
                string(edge, "stateVersion"),
                "READ_FROM".equals(relation(edge))
                        ? "LATEST_BEFORE_READ" : "VALUE_VERSION");
    }

    private static String concreteBindingIdentity(JsonObject binding) {
        String writeSeq = firstNonBlank(string(binding, "writeSeq"),
                string(binding, "writerEventSeq"));
        String readSeq = firstNonBlank(string(binding, "readSeq"),
                string(binding, "readerEventSeq"));
        String writerCall = string(binding, "writerCallId");
        String receiver = string(binding, "receiverObjectId");
        String value = string(binding, "valueObjectId");
        if (writeSeq.isEmpty() && readSeq.isEmpty()
                && writerCall.isEmpty() && receiver.isEmpty()
                && value.isEmpty()) return "";
        return component(concreteInstanceIdentity(string(binding,
                "fromRegionInstance")))
                + component(string(binding, "toRegionInstance"))
                + component(firstNonBlank(string(binding, "test"),
                string(binding, "testId")))
                + component(firstNonBlank(string(binding, "fromProcess"),
                string(binding, "process")))
                + component(string(binding, "fromThreadId"))
                + component(writeSeq)
                + component(readSeq)
                + component(writerCall)
                + component(string(binding, "writerSiteId"))
                + component(string(binding, "writerOccurrence"))
                + component(string(binding, "field"))
                + component(receiver)
                + component(value);
    }

    private static boolean sameConcreteBinding(JsonObject left,
                                               JsonObject right) {
        String[][] aliases = new String[][]{
                {"writeSeq", "writerEventSeq"},
                {"readSeq", "readerEventSeq"},
                {"writerCallId"},
                {"writerSiteId"},
                {"writerOccurrence"},
                {"field"},
                {"receiverObjectId"},
                {"valueObjectId"}
        };
        int compared = 0;
        int strongCompared = 0;
        for (int index = 0; index < aliases.length; index++) {
            String leftValue = firstField(left, aliases[index]);
            String rightValue = firstField(right, aliases[index]);
            if (leftValue.isEmpty() || rightValue.isEmpty()) continue;
            compared++;
            if (index < 3 || index >= 6) strongCompared++;
            if (!leftValue.equals(rightValue)) return false;
        }
        return compared > 0 && strongCompared > 0;
    }

    private static String firstField(JsonObject value, String... fields) {
        for (String field : fields) {
            String candidate = string(value, field);
            if (!candidate.isEmpty()) return candidate;
        }
        return "";
    }

    private static String concreteInstanceIdentity(String instance) {
        String value = firstNonBlank(instance);
        int at = value.indexOf('@');
        if (at >= 0) return value.substring(at + 1);
        int call = value.indexOf("#call");
        return call >= 0 ? value.substring(call) : value;
    }

    private static String methodFromSite(String site) {
        String value = firstNonBlank(site);
        int unit = value.lastIndexOf("#u");
        return unit < 0 ? value : value.substring(0, unit);
    }

    private static String canonicalPort(String value) {
        return firstNonBlank(value).replaceAll("\\s+", " ").trim();
    }

    private static String canonicalJson(JsonElement value) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(canonicalJson(element));
            }
            return result.append(']').toString();
        }
        if (value.isJsonObject()) {
            StringBuilder result = new StringBuilder("{");
            boolean first = true;
            for (String key : new TreeSet<>(value.getAsJsonObject()
                    .keySet())) {
                if (!first) result.append(',');
                first = false;
                result.append(GSON.toJson(key)).append(':')
                        .append(canonicalJson(value.getAsJsonObject().get(key)));
            }
            return result.append('}').toString();
        }
        return GSON.toJson(value);
    }

    private static String component(String value) {
        String safe = value == null ? "" : value;
        return safe.length() + ":" + safe;
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(firstNonBlank(value)
                    .getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 unavailable", impossible);
        }
    }

    private static String shortHash(String value) {
        return sha256(value).substring(0, 16);
    }

    private static <T> List<T> safeList(List<T> values) {
        return values == null ? Collections.<T>emptyList() : values;
    }

    private static void add(Map<String, List<JsonObject>> values, String key,
                            JsonObject value) {
        if (key == null || key.isEmpty()) return;
        List<JsonObject> rows = values.get(key);
        if (rows == null) {
            rows = new ArrayList<>();
            values.put(key, rows);
        }
        rows.add(value);
    }

    private static JsonArray array(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static boolean hasArray(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonArray();
    }

    private static Set<String> primitiveStringSet(JsonArray values) {
        Set<String> result = new TreeSet<>();
        for (JsonElement value : values) {
            if (!value.isJsonPrimitive()) continue;
            String port = canonicalPort(value.getAsString());
            if (!port.isEmpty()) result.add(port);
        }
        return result;
    }

    private static JsonObject object(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject object, String field,
                                boolean fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject object, String field, int fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }
}
