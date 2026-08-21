package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Builds bounded branch-flip work for one region closure. */
public final class RegionPathWorklist {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    public enum State {
        NOT_STARTED,
        PENDING,
        CLOSED,
        GAPPED
    }

    private RegionPathWorklist() {
    }

    public static Result plan(List<JsonObject> summaries,
                              List<JsonObject> executionTasks,
                              List<JsonObject> explorationRecords,
                              Bounds bounds) {
        return plan(summaries, executionTasks, explorationRecords, bounds,
                Collections.<JsonObject>emptyList());
    }

    /**
     * Plans the next obligations from the admitted local cases of one
     * topology.
     *
     * <p>README "Delta ownership is also singular" makes this the consumer of
     * the importer's admitted cases: a path whose own occurrence the delta
     * classified as {@code TOPOLOGY_DIVERGENCE} belongs to the next
     * iteration's plan, so no branch-flip obligation may be built across it.
     * It is named as a coverage gap and never deleted - the evidence stays,
     * it is only outside this iteration's target scope.</p>
     */
    public static Result plan(List<JsonObject> summaries,
                              List<JsonObject> executionTasks,
                              List<JsonObject> explorationRecords,
                              Bounds bounds,
                              List<JsonObject> topologyDelta) {
        return new Planner(summaries, executionTasks, explorationRecords,
                bounds, topologyDelta).run();
    }

    private static final class Planner {
        private final Bounds bounds;
        private final Set<String> divergentTasks = new LinkedHashSet<>();
        private final Set<String> divergentOccurrences =
                new LinkedHashSet<>();
        private final Map<String, JsonObject> taskById =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> records = new LinkedHashMap<>();
        private final List<PathObservation> paths = new ArrayList<>();
        private final List<JsonObject> tasks = new ArrayList<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final Set<String> gapKeys = new LinkedHashSet<>();
        private final List<JsonObject> coverageGaps = new ArrayList<>();
        private final Set<String> coverageGapKeys = new LinkedHashSet<>();
        private final Set<String> emitted = new LinkedHashSet<>();
        private final Set<String> observedFlipKeys = new LinkedHashSet<>();
        private final List<JsonObject> abandonedFlips = new ArrayList<>();
        private final Map<String, Integer> pathCountByRegion =
                new LinkedHashMap<>();
        private Planner(List<JsonObject> summaries,
                        List<JsonObject> executionTasks,
                        List<JsonObject> explorationRecords,
                        Bounds bounds,
                        List<JsonObject> topologyDelta) {
            this.bounds = bounds;
            for (JsonObject row : topologyDelta) {
                if (!TopologyDelta.TOPOLOGY_DIVERGENCE.equals(
                        string(row, "deltaKind"))) {
                    continue;
                }
                String taskId = string(row, "taskId");
                if (!taskId.isEmpty()) divergentTasks.add(taskId);
                divergentOccurrences.add(occurrenceKey(
                        string(row, "sourceKey"),
                        string(row, "occurrenceId")));
            }
            for (JsonObject task : executionTasks) {
                String id = string(task, "taskId");
                if (!id.isEmpty()) this.taskById.put(id, task);
            }
            for (JsonObject record : explorationRecords) {
                String key = string(record, "queryKey");
                if (!key.isEmpty()) this.records.put(key, record);
            }
            for (JsonObject summary : summaries) {
                PathObservation path = PathObservation.decode(summary,
                        taskById.get(string(summary, "taskId")));
                paths.add(path);
                collectAlignmentGaps(summary);
            }
            Collections.sort(paths, Comparator.comparing(value ->
                    value.regionId() + "\n" + value.pathKey()));
        }

        private Result run() {
            indexObservedCoverage();
            Set<String> seenPaths = new LinkedHashSet<>();
            Set<String> observedRegions = new TreeSet<>();
            Map<String, PathObservation.Scope> observedScopes =
                    new LinkedHashMap<>();
            for (JsonObject task : taskById.values()) {
                PathObservation.Scope scope = PathObservation.Scope.decode(null,
                        task);
                observedScopes.put(scope.identity(), scope);
            }
            for (PathObservation path : paths) {
                String region = path.regionId();
                if (region.isEmpty()) continue;
                String pathKey = path.pathKey();
                if (!seenPaths.add(region + "\n" + pathKey)) continue;
                observedRegions.add(region);
                observedScopes.put(path.scope().identity(), path.scope());
                pathCountByRegion.merge(region, 1, Integer::sum);
                if (divergedTopology(path)) {
                    coverageGap(TopologyDelta.TOPOLOGY_DIVERGENCE,
                            "OBLIGATION_BELONGS_TO_THE_NEXT_ITERATION",
                            region, pathKey, "", -1);
                    continue;
                }
                if (!path.branchMappingIssue().isEmpty()) {
                    gap("INVALID_BRANCH_MAPPING_SCHEMA",
                            path.branchMappingIssue(), region, pathKey, "", -1);
                    continue;
                }
                if (!path.relationallyComplete()) {
                    gap("INCOMPLETE_REGION_SUMMARY",
                            "RELATIONAL_INPUT_OUTPUT_SUMMARY_NOT_COMPLETE",
                            region, pathKey, "", -1);
                    continue;
                }
                if (pathCountByRegion.get(region) > bounds.maxPathsPerRegion) {
                    coverageGap("BOUND_REACHED", "MAX_PATHS_PER_REGION", region,
                            pathKey, "", -1);
                    continue;
                }
                planSummary(path);
                if (campaignTaskCount() >= bounds.maxTasks) break;
            }

            int remainingPathSlots = bounds.maxPathsPerRegion
                    - seenPaths.size();
            if (!tasks.isEmpty() && remainingPathSlots <= 0) {
                coverageGap("BOUND_REACHED", "MAX_PATHS_PER_REGION",
                        manifestRegionId(observedRegions),
                        "", "", -1);
                tasks.clear();
            } else if (tasks.size() > remainingPathSlots) {
                coverageGap("BOUND_REACHED", "MAX_PATHS_PER_REGION",
                        manifestRegionId(observedRegions),
                        "", "", -1);
                tasks.subList(remainingPathSlots, tasks.size()).clear();
            }

            JsonObject manifest = manifest(!seenPaths.isEmpty(),
                    observedRegions, observedScopes);
            String coverageState = string(manifest, "coverageState");
            String worklistState = string(manifest, "state");
            // One relation artifact for both coverage states.  Every row
            // states its own coverage in "pathCoverageState", so the closed
            // and the observed merge no longer need separate files.
            List<JsonObject> relations = new ArrayList<>();
            if (State.CLOSED.name().equals(worklistState)
                    && "CLOSED".equals(coverageState)) {
                relations.addAll(outputRelations(observedScopes,
                        false, coverageState));
            } else if (State.PENDING.name().equals(worklistState)
                    || State.CLOSED.name().equals(worklistState)) {
                relations.addAll(outputRelations(observedScopes,
                        true, coverageState));
            }
            if (!gaps.isEmpty()) {
                tasks.clear();
                relations.clear();
                manifest.addProperty("state", State.GAPPED.name());
                // Relations discovered a gap after the manifest was built,
                // so the coverage it reported is no longer closed.
                manifest.addProperty("coverageState",
                        hasReplayPath() ? "PARTIAL" : "SEED_ONLY");
                manifest.add("gaps", GSON.toJsonTree(gaps));
            }
            return new Result(tasks, manifest, relations);
        }

        private List<JsonObject> outputRelations(
                Map<String, PathObservation.Scope> observedScopes,
                boolean observedOnly, String coverageState) {
            if (observedScopes.size() != 1) {
                return Collections.emptyList();
            }
            PathObservation.Scope scope =
                    observedScopes.values().iterator().next();
            if (!scope.goalKind().capturesOutputRelation()) {
                return Collections.emptyList();
            }
            if (scope.outputClosure() == null) {
                gap("INVALID_OUTPUT_CLOSURE",
                        "CANONICAL_OUTPUT_CLOSURE_REQUIRED",
                        "", "", "", -1);
                return Collections.emptyList();
            }

            String region = scope.outputClosure().producer().regionId();
            String outputIdentity = scope.outputClosureIdentity();
            List<PathObservation> validPaths = new ArrayList<>();
            List<JsonObject> bindings = new ArrayList<>();
            for (PathObservation path : paths) {
                if (!path.scope().goalKind().capturesOutputRelation()) {
                    continue;
                }
                OutputClosureContract contract = path.scope().outputClosure();
                if (!outputIdentity.equals(
                        path.scope().outputClosureIdentity())) {
                    gap("OUTPUT_CLOSURE_SCOPE_MISMATCH",
                            "CLOSED_PATHS_HAVE_DIFFERENT_OUTPUT_CLOSURES",
                            path.regionId(), "", "", -1);
                    continue;
                }
                if (!path.hasExactOutputSet(contract.outputPorts())) {
                    gap("OUTPUT_EXPRESSION_SET_MISMATCH",
                            "OUTPUT_EXPRESSION_SET_DOES_NOT_MATCH_DEMAND",
                            region, path.pathKey(), "", -1);
                } else {
                    validPaths.add(path);
                }
                for (JsonElement element : path.edgeBindings()) {
                    if (!element.isJsonObject()) continue;
                    bindings.add(element.getAsJsonObject());
                }
            }
            if (!gaps.isEmpty()) {
                return Collections.emptyList();
            }
            // Two paths whose projected guards are equal and whose relations
            // are not are two cases the relation guard cannot tell apart, so
            // the merged summary's "exactly one case selector" would hold of
            // neither.  README PC-1 imports the selected failure-slice
            // witnesses for the whole occurrence and keeps no full ambient
            // path condition to widen back to, so the collision is named
            // here instead: restating the transport and startup decisions
            // the projection exists to drop would separate these two cases
            // by noise and let a later replay's guard read as this one's.
            Map<String, String> relationByGuard = new LinkedHashMap<>();
            Map<String, PathObservation> caseByPath = new LinkedHashMap<>();
            for (PathObservation path : validPaths) {
                String prior = relationByGuard.putIfAbsent(
                        path.relationGuardKey(), path.relationKey());
                if (prior != null && !prior.equals(path.relationKey())) {
                    gap("RELATION_GUARD_DOES_NOT_SEPARATE_CASES",
                            "TWO_RELATIONS_SHARE_ONE_PROJECTED_GUARD",
                            region, path.relationKey(), "", -1);
                    continue;
                }
                caseByPath.putIfAbsent(path.relationKey(), path);
            }
            if (!gaps.isEmpty()) {
                return Collections.emptyList();
            }
            if (caseByPath.isEmpty()) {
                gap("NO_VALID_OUTPUT_CLOSURE_RELATIONS",
                        "CLOSED_OUTPUT_SCOPE_HAS_NO_CASES",
                        region, "", "", -1);
                return Collections.emptyList();
            }

            RelationSummary merged = observedOnly
                    ? RelationSummary.observedPathMerge(
                    scope.outputClosure(), caseByPath.values(), bindings,
                    coverageState, tasks.isEmpty()
                            ? State.CLOSED.name() : State.PENDING.name())
                    : RelationSummary.guardedPathMerge(
                    scope.outputClosure(), caseByPath.values(), bindings);
            return Collections.singletonList(merged.toJson());
        }

        /** Whether the delta classified this path's own occurrence changed. */
        private boolean divergedTopology(PathObservation path) {
            return divergentTasks.contains(path.sourceTaskId())
                    || divergentOccurrences.contains(occurrenceKey(
                    path.sourceKey(), path.occurrenceId()));
        }

        private void planSummary(PathObservation path) {
            // The target query already complements the exact observed target
            // predicate and composes it with upstream producer cases.  A
            // second local replay of that terminal branch is both redundant
            // and, for container/reference operands, not materializable as a
            // concrete Java input.  Path exploration is therefore reserved
            // for output-producing occurrences that can add a new guarded
            // interaction/state case.
            if (path.scope().goalKind().capturesTargetReach()) {
                return;
            }
            List<SummaryBranchMapping> candidates = new ArrayList<>();
            JsonObject task = taskById.get(path.sourceTaskId());
            Set<String> explicitFaultSymbols = explicitFaultSymbols(task);
            for (SummaryBranchMapping mapping : path.branchMappings()) {
                String site = mapping.siteId();
                if (!path.scope().branchSites().contains(site)) {
                    continue;
                }
                if (mapping.isConcreteObservation()) {
                    continue;
                }
                if (!mapping.isExplore()) continue;
                if (!explicitFaultSymbols.isEmpty()
                        && !dependsOnAny(mapping.witness()
                        .sourceSatisfiedPredicate(),
                        explicitFaultSymbols)) {
                    continue;
                }
                if (abandonsDemandedOutputSite(path, task, mapping)) {
                    continue;
                }
                candidates.add(mapping);
            }
            // Classic depth-first concolic order: flip the latest relevant
            // decision first, then progressively shorter prefixes.
            Collections.sort(candidates, (left, right) -> {
                int byIndex = Integer.compare(right.summaryPcIndex(),
                        left.summaryPcIndex());
                if (byIndex != 0) return byIndex;
                int bySite = left.siteId().compareTo(right.siteId());
                if (bySite != 0) return bySite;
                return Integer.compare(left.occurrence(),
                        right.occurrence());
            });

            int limit = Math.min(candidates.size(), bounds.maxFlipsPerPath);
            if (candidates.size() > limit) {
                coverageGap("BOUND_REACHED", "MAX_FLIPS_PER_PATH",
                        path.regionId(),
                        path.pathKey(), "", -1);
            }
            for (int index = 0; index < limit; index++) {
                // path_exploration_records.jsonl is cumulative for this
                // member.  A completed query consumed one campaign task even
                // though this planner process starts a fresh wave, so only
                // the unspent remainder may be published now.
                if (campaignTaskCount() >= bounds.maxTasks) {
                    coverageGap("BOUND_REACHED", "MAX_TASKS",
                            path.regionId(),
                            path.pathKey(), "", -1);
                    return;
                }
                emitTask(path, candidates.get(index));
            }
        }

        private int campaignTaskCount() {
            return records.size() + tasks.size();
        }

        /**
         * A task with a named fault input explores that controlled fault and
         * keeps the rest of the producer path at its witnessed values.  This
         * is the experiment's explicit degree of freedom; flipping unrelated
         * service/configuration guards would create alternative causes that
         * hide whether the requested RPC failure is load-bearing.
         */
        private Set<String> explicitFaultSymbols(JsonObject task) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : array(task, "inputActions")) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (!"SYMBOLIC".equals(string(action, "mode"))
                        || !"EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                        string(action, "authority"))) {
                    continue;
                }
                String symbol = string(action, "symbol");
                if (!symbol.isEmpty()) result.add(symbol);
            }
            return result;
        }

        private boolean dependsOnAny(JsonElement predicate,
                                     Set<String> symbols) {
            String encoded = CanonicalJson.render(predicate);
            for (String symbol : symbols) {
                if (encoded.contains(symbol)) return true;
            }
            return false;
        }

        /**
         * True when the flipped successor provably cannot reach a site the
         * demanded outputs are published at.  Such a flip walks a fresh path
         * and then ends with the port never written, so the whole replay is
         * spent to learn nothing; the runtime still fails closed on it
         * ({@code OUTPUT_CAPTURE_COUNT:<port>:0}), which is what makes it
         * cost a replay rather than a wrong answer.
         *
         * <p>Only the outcome the static analyzer proved is required to reach
         * that exact site decides this.  A site with no proof, a branch with
         * no recorded control dependence, and a demand published at no site
         * at all all keep the candidate.</p>
         */
        private boolean abandonsDemandedOutputSite(
                PathObservation path, JsonObject task,
                SummaryBranchMapping mapping) {
            OutputClosureContract closure = path.scope().outputClosure();
            if (closure == null || task == null) return false;
            Set<String> demanded =
                    closure.executionScope().outputSites();
            if (demanded.isEmpty()) return false;
            boolean desired = !mapping.sourceTakenOutcome();
            for (JsonElement element : array(task, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!mapping.siteId().equals(string(branch, "siteId"))) {
                    continue;
                }
                for (JsonElement row
                        : array(branch, "guardedSiteOutcomes")) {
                    if (!row.isJsonObject()) continue;
                    JsonObject guarded = row.getAsJsonObject();
                    if (!demanded.contains(string(guarded, "siteId"))) {
                        continue;
                    }
                    JsonElement outcome = guarded.get("requiredOutcome");
                    if (outcome != null && outcome.isJsonPrimitive()
                            && outcome.getAsJsonPrimitive().isBoolean()
                            && outcome.getAsBoolean() != desired) {
                        return true;
                    }
                }
            }
            return false;
        }

        private void emitTask(PathObservation path,
                              SummaryBranchMapping mapping) {
            BranchReplayContract replay = BranchReplayContract.fromSummary(
                    path.replayPayload(), path.branchMappings(), mapping);
            boolean desired = replay.requiredTakenOutcome();
            String key = path.flipKey(mapping, desired);

            JsonObject previous = records.get(key);
            if (previous != null && terminal(previous)) {
                return;
            }
            if (observedFlipKeys.contains(key)) {
                return;
            }
            if (!emitted.add(key)) {
                return;
            }
            JsonObject task = new JsonObject();
            task.addProperty("schemaVersion", 3);
            task.addProperty("kind", "REGION_PATH_FLIP");
            task.addProperty("queryKey", key);
            task.addProperty("regionId", path.regionId());
            task.addProperty("goalId", path.scope().goalId());
            path.scope().loopBound().writeTo(task);
            path.scope().goalKind().writeToTask(task);
            task.addProperty("sourceTaskId", path.sourceTaskId());
            if (path.scope().outputClosure() != null) {
                task.add(OutputClosureContract.FIELD,
                        path.scope().outputClosure().toJson());
            }
            replay.addTo(task);
            attachRecordedReadCut(path, replay, task);
            tasks.add(task);
        }

        /**
         * Carries this path's recorded guarded reads into the query.
         *
         * <p>A solver can only report which competing writer it selected if
         * the query states the choice, and the recorded evidence travels with
         * the observation rather than with the plan - so this is the one place
         * that holds both. Nothing is attached when the execution recorded no
         * guarded read that reaches the flipped condition: an empty choice is
         * not a choice, and a query should not declare one.</p>
         *
         * <p>The query consumes the recorded guarded read's own arms. Loop
         * counts qualify whole guarded cases later; they do not create writer
         * instances in this branch-flip query.</p>
         */
        private void attachRecordedReadCut(PathObservation path,
                                           BranchReplayContract replay,
                                           JsonObject task) {
            JsonObject recorded = path.recordedSharedState();
            if (recorded.size() == 0) return;
            JsonObject row = new JsonObject();
            row.add(SharedStateEvidence.RECORDED_FIELD, recorded);
            JsonObject payload = RecordedSessionModel.of(
                    Collections.singletonList(row),
                    replay.requiredSatisfiedPredicate(),
                    path.regionId()).queryPayload();
            if (payload.size() > 0) {
                task.add(RecordedSessionModel.QUERY_FIELD, payload);
            }
        }

        private void indexObservedCoverage() {
            for (PathObservation path : paths) {
                if (!path.relationallyComplete()) {
                    continue;
                }
                for (SummaryBranchMapping mapping : path.branchMappings()) {
                    if (!mapping.isWitnessed() || !mapping.isExplore()) {
                        continue;
                    }
                    if (!path.regionId().isEmpty()
                            && path.scope().branchSites().contains(
                            mapping.siteId())) {
                        observedFlipKeys.add(path.flipKey(mapping,
                                mapping.sourceTakenOutcome()));
                    }
                }
            }
        }

        private JsonObject manifest(boolean hasObservedPath,
                                    Set<String> observedRegions,
                                    Map<String, PathObservation.Scope> scopes) {
            String regionId = manifestRegionId(observedRegions);
            if (observedRegions.size() > 1) {
                gap("MULTIPLE_REGION_SCOPE",
                        "REGION_PATH_WORKLIST_REQUIRES_ONE_REGION",
                        "", "", "", -1);
            }
            if (!hasObservedPath) {
                gap("NO_OBSERVED_PATH_SEED",
                        "REGION_PATH_SEED_REQUIRED",
                        regionId, "", "", -1);
            }
            if (scopes.size() > 1) {
                gap("MULTIPLE_EXPLORATION_SCOPE",
                        "REGION_PATH_WORKLIST_REQUIRES_ONE_SCOPE",
                        regionId, "", "", -1);
            }
            State state = !hasObservedPath
                    ? State.NOT_STARTED
                    : !gaps.isEmpty()
                    ? State.GAPPED
                    : tasks.isEmpty() ? State.CLOSED : State.PENDING;
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind", "REGION_PATH_WORKLIST");
            result.addProperty("state", state.name());
            Set<String> sources = new TreeSet<>();
            Set<String> occurrences = new TreeSet<>();
            for (PathObservation path : paths) {
                if (!path.sourceKey().isEmpty()) {
                    sources.add(path.sourceKey());
                }
                if (!path.occurrenceId().isEmpty()) {
                    occurrences.add(path.occurrenceId());
                }
            }
            if (sources.size() == 1) {
                result.addProperty("sourceKey", sources.iterator().next());
            }
            if (occurrences.size() == 1) {
                result.addProperty("occurrenceId",
                        occurrences.iterator().next());
            }
            if (scopes.size() != 1 || scopes.values().iterator().next()
                    .outputClosure() == null) {
                result.addProperty("regionId", regionId);
            }
            if (scopes.size() == 1) {
                PathObservation.Scope scope = scopes.values().iterator().next();
                scope.loopBound().writeTo(result);
                if (scope.outputClosure() != null) {
                    result.add(OutputClosureContract.FIELD,
                            scope.outputClosure().toJson());
                } else {
                    result.addProperty("goalId", scope.goalId());
                    scope.goalKind().writeToTask(result);
                }
            }
            result.add("gaps", GSON.toJsonTree(gaps));
            List<JsonObject> explorationGaps = new ArrayList<>();
            for (JsonObject record : records.values()) {
                collectAlignmentGaps(record);
                String kind = explorationGapKind(string(record, "status"));
                if (kind.isEmpty()) continue;
                JsonObject gap = new JsonObject();
                gap.addProperty("kind", kind);
                gap.addProperty("queryKey", string(record, "queryKey"));
                gap.addProperty("reason", string(record, "reason"));
                if (record.has("unsupported")) {
                    gap.add("unsupported", record.get("unsupported"));
                }
                explorationGaps.add(gap);
            }
            explorationGaps.addAll(abandonedFlips);
            result.add("explorationGaps", GSON.toJsonTree(explorationGaps));
            coverageGaps.addAll(explorationGaps);
            result.add("coverageGaps", GSON.toJsonTree(coverageGaps));
            result.addProperty("coverageState",
                    state == State.CLOSED && coverageGaps.isEmpty()
                            ? "CLOSED" : campaignBoundReached()
                            || hasReplayPath()
                            ? "PARTIAL" : "SEED_ONLY");
            return result;
        }

        private boolean campaignBoundReached() {
            for (JsonObject gap : coverageGaps) {
                if ("BOUND_REACHED".equals(string(gap, "kind"))) {
                    return true;
                }
            }
            return false;
        }

        private boolean hasReplayPath() {
            for (PathObservation path : paths) {
                JsonObject task = taskById.get(path.sourceTaskId());
                if (!string(task, "pathQueryKey").isEmpty()) return true;
            }
            return false;
        }

        private String manifestRegionId(Set<String> observedRegions) {
            if (observedRegions.size() == 1) {
                return observedRegions.iterator().next();
            }
            if (!observedRegions.isEmpty()) return "";

            Set<String> inputRegions = new TreeSet<>();
            for (PathObservation path : paths) {
                if (!path.regionId().isEmpty()) inputRegions.add(path.regionId());
            }
            for (JsonObject task : taskById.values()) {
                String region = string(task, "regionId");
                if (!region.isEmpty()) inputRegions.add(region);
            }
            return inputRegions.size() == 1
                    ? inputRegions.iterator().next() : "";
        }

        /**
         * Names a flip this planner refuses to propose.  It joins the flips
         * an execution explored and abandoned rather than the planning gaps,
         * because it is charged to itself: the closure stays auditable and
         * the run proceeds.
         */
        private void abandoned(String kind, String queryKey, String reason) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("queryKey", queryKey);
            gap.addProperty("reason", reason);
            abandonedFlips.add(gap);
        }

        private void gap(String kind, String reason, String region,
                         String pathKey, String site, int occurrence) {
            addIssue(gaps, gapKeys, kind, reason, region, pathKey, site,
                    occurrence);
        }

        private void coverageGap(String kind, String reason, String region,
                                 String pathKey, String site,
                                 int occurrence) {
            addIssue(coverageGaps, coverageGapKeys, kind, reason, region,
                    pathKey, site, occurrence);
        }

        /**
         * Forwards an imported summary's alignment gaps into the coverage
         * gaps.
         *
         * <p>{@code coverageGaps} is what decides {@code CLOSED} against
         * {@code PARTIAL}, and {@link CoverageDivergence} states the rule:
         * only a target divergence with no usable target relation ends the
         * result, and everything else must leave the coverage partial rather
         * than closed.  So this list forwards exactly the kinds
         * {@code CoverageDivergence.classOf} can classify.  A kind a producer
         * raises and the classifier understands, dropped here, would let a
         * run report {@code CLOSED} while that evidence stood -
         * {@code READ_CUT_GATE_GAP} was doing precisely that.</p>
         */
        private void collectAlignmentGaps(JsonObject source) {
            for (JsonElement element : array(source, "alignmentGaps")) {
                if (!element.isJsonObject()) continue;
                JsonObject imported = element.getAsJsonObject().deepCopy();
                String kind = string(imported, "kind");
                if (!RpcExpressionHandoff.GAP_KIND.equals(kind)
                        && !SharedStateEvidence.GAP_KIND.equals(kind)
                        && !SparseReadCutGate.GAP_KIND.equals(kind)
                        && !"OUTPUT_VERSION_ALIGNMENT_GAP".equals(kind)) {
                    continue;
                }
                String key = CanonicalJson.render(imported);
                if (coverageGapKeys.add(key)) {
                    coverageGaps.add(imported);
                }
            }
        }

        private void addIssue(List<JsonObject> destination, Set<String> keys,
                              String kind, String reason, String region,
                              String pathKey, String site, int occurrence) {
            String key = kind + "\n" + reason + "\n" + region + "\n"
                    + pathKey + "\n" + site + "\n" + occurrence;
            if (!keys.add(key)) return;
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("reason", reason);
            gap.addProperty("regionId", region);
            gap.addProperty("pathKey", pathKey);
            gap.addProperty("siteId", site);
            gap.addProperty("occurrence", occurrence);
            destination.add(gap);
        }

    }

    /** The canonical region occurrence, as both stages key it. */
    private static String occurrenceKey(String sourceKey,
                                        String occurrenceId) {
        return sourceKey + "\n" + occurrenceId;
    }

    public static final class Bounds {
        public final int maxPathsPerRegion;
        public final int maxFlipsPerPath;
        public final int maxTasks;

        public Bounds(int maxPathsPerRegion, int maxFlipsPerPath,
                      int maxTasks) {
            this.maxPathsPerRegion = Math.max(1, maxPathsPerRegion);
            this.maxFlipsPerPath = Math.max(1, maxFlipsPerPath);
            this.maxTasks = Math.max(1, maxTasks);
        }

        public static Bounds defaults() {
            return new Bounds(64, 32, 256);
        }

    }

    public static final class Result {
        public final List<JsonObject> tasks;
        public final JsonObject manifest;
        public final List<JsonObject> relations;

        private Result(List<JsonObject> tasks, JsonObject manifest,
                       List<JsonObject> relations) {
            this.tasks = tasks;
            this.manifest = manifest;
            this.relations = relations;
        }
    }

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "UNSAT".equals(status)
                || !explorationGapKind(status).isEmpty()
                || "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY".equals(status)
                || "VALIDATED_FRESH_TARGET_PATH_FLIP_REPLAY".equals(status);
    }

    /** Names an abandoned flip, or empty when the record is not one. */
    private static String explorationGapKind(String status) {
        if ("UNSUPPORTED".equals(status)) return "UNSUPPORTED_PATH_FLIP";
        if ("REPLAY_NOT_ADMITTED".equals(status)) {
            return "PATH_FLIP_REPLAY_NOT_ADMITTED";
        }
        // A flip whose replay never obtained the single symbolic engine was
        // not refuted; it was never explored.  Charging it to the same gap as
        // a replay that ran and missed the relation would make a scheduling
        // outcome indistinguishable from an infeasible path.
        if ("REPLAY_ENGINE_UNAVAILABLE".equals(status)) {
            return "PATH_FLIP_REPLAY_ENGINE_UNAVAILABLE";
        }
        // A replay is bounded in the paths it may walk, not in what those
        // paths cost to keep resident, so one can end before publishing a
        // result.  That flip is abandoned like any other, and the gap says so.
        if ("REPLAY_PRODUCED_NO_RESULT".equals(status)) {
            return "PATH_FLIP_REPLAY_PRODUCED_NO_RESULT";
        }
        // The solver reached a verdict and it was "this flip cannot be
        // materialized".  ConcolicPathFlipSolver already calls that a
        // terminal exploration outcome and exits 0 on it; this is the same
        // fact stated where the planner decides whether to propose the flip
        // again.  Without it the worklist re-proposes a flip whose answer is
        // already known, every wave, forever - the wave loop terminates only
        // because a queryKey carrying a terminal record stops being emitted.
        if ("MATERIALIZATION_GAP".equals(status)) {
            return "PATH_FLIP_MATERIALIZATION_GAP";
        }
        return "";
    }

}
