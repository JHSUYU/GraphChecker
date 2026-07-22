package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.SymbolicEnvironment;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Builds graph-directed concolic jobs from static regions and concrete
 * unit-test activations.
 *
 * <p>The scheduler deliberately separates three phases:</p>
 * <ol>
 *   <li>capture a VM path condition for one runtime-confirmed activation,</li>
 *   <li>keep the prefix and negate one stable branch occurrence, and</li>
 *   <li>solve/materialize a new workload input in a later executor.</li>
 * </ol>
 *
 * <p>Protocol equality and shared-state read-from are not flattened into the
 * same operation.  Equality ports form symbolic alias classes, while heap
 * state is merged as an ordered, object-sensitive version relation.</p>
 */
public final class ConcolicScheduler {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final Gson JSONL_GSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private static final Pattern FIELD_SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+[^()<>]+\\s+([^\\s()>]+)>");
    private static final Pattern FIELD_DETAIL = Pattern.compile(
            "<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>");
    private static final Pattern FIELD_PROJECTION = Pattern.compile(
            "#field:([^#]+)");
    private static final Pattern DEFAULT_OBJECT_IDENTITY_THREAD_NAME =
            Pattern.compile("^([A-Za-z_$][A-Za-z0-9_$.]*?)@"
                    + "[0-9a-fA-F]+$");
    private static final String CONSUMED_FIELD_SITE_AUTHORITY =
            "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                    + "OWNER_WITHIN_REGION_INSTANCE_V1";
    private static final String DIRECT_FIELD_ROOT_AUTHORITY =
            "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1";
    private static final String ARGUMENT_FIELD_ROOT_AUTHORITY =
            "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
    private static final String RECEIVER_FIELD_ROOT_AUTHORITY =
            "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
    private static final String LOCAL_FIELD_ROOT_AUTHORITY =
            "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
    private static final String MAP_STATE_INPUT_OBSERVATION_MODE =
            "MAP_STATE_INPUT_OBSERVATION";
    private static final String FIRST_CONTAINER_OBSERVATION_AUTHORITY =
            "FIRST_MATCHING_CONTAINER_INSTANCE_APPROXIMATION_V1";
    static final String ACCESSOR_INPUT_CANONICALIZATION_AUTHORITY =
            "STATIC_UNIQUE_EXACT_ACCESSOR_FIELD_RETURN_TO_REGION_INPUT_V1";
    private ConcolicScheduler() {
    }

    public static void main(String[] args) throws Exception {
        Arguments arguments = Arguments.parse(args);
        Result result = schedule(arguments);
        System.out.println(GSON.toJson(result.summary));
        if (result.jobs.isEmpty()) {
            System.exit(2);
        }
    }

    public static Result schedule(Arguments arguments) throws IOException {
        requireFile(arguments.regions, "symbolic regions");
        requireFile(arguments.activations, "activation plan");
        requireFile(arguments.edgeValidations, "runtime edge validation");
        if (arguments.runtimeRegionInstances != null) {
            requireFile(arguments.runtimeRegionInstances,
                    "runtime region instances");
        }
        Files.createDirectories(arguments.outputDirectory);

        List<JsonObject> regions = readJsonl(arguments.regions);
        List<JsonObject> activations = readJsonl(arguments.activations);
        List<JsonObject> edges = readJsonl(arguments.edgeValidations);
        List<JsonObject> summaries = arguments.captureOnly
                || arguments.summaries == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.summaries);
        List<JsonObject> staticGraph = arguments.staticGraph == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.staticGraph);
        List<JsonObject> pathRecords = arguments.pathRecords == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.pathRecords);
        List<JsonObject> runtimeRegionInstances =
                arguments.runtimeRegionInstances == null
                        ? Collections.<JsonObject>emptyList()
                        : readJsonl(arguments.runtimeRegionInstances);
        DefinitionIndex definitions = arguments.staticGraph == null
                ? DefinitionIndex.fallback()
                : DefinitionIndex.from(staticGraph);

        Map<String, Region> regionIndex = new LinkedHashMap<>();
        for (JsonObject row : regions) {
            Region region = new Region(row);
            if (!region.regionId.isEmpty()) {
                regionIndex.put(region.regionId, region);
            }
        }

        MergePlan mergePlan = buildMergePlan(regionIndex, edges,
                staticGraph);
        List<Candidate> candidates = candidates(arguments, activations,
                regionIndex, definitions,
                CaptureEvidence.from(runtimeRegionInstances));
        Collections.sort(candidates, Candidate.ORDER);

        Result result = new Result();
        result.mergePlan = mergePlan.json;
        List<JsonObject> worklistRoots = new ArrayList<>();
        Set<String> rootActivations = new LinkedHashSet<>();
        for (Candidate candidate : candidates) {
            String rootKey = candidate.region.regionId + "\n"
                    + candidate.activationId;
            if (rootActivations.add(rootKey)) {
                worklistRoots.add(candidate.activation.deepCopy());
            }
        }
        RecursiveRegionWorklist.Result recursive =
                RecursiveRegionWorklist.explore(regions, activations, edges,
                        summaries, worklistRoots, arguments.regionBounds);
        result.regionWorkItems.addAll(recursive.workItems);
        result.upstreamRequests.addAll(recursive.upstreamRequests);
        result.alternativeWriterGroups.addAll(
                recursive.alternativeWriterGroups);
        result.regionManifest = recursive.manifest;
        RegionPathWorklist.Result pathWork = RegionPathWorklist.plan(
                summaries, activations, pathRecords, arguments.pathBounds);
        result.pathTasks.addAll(pathWork.tasks);
        result.pathManifest = pathWork.manifest;
        Set<String> selectedRegions = new LinkedHashSet<>();
        Map<String, JsonObject> emittedActivationDefinitions =
                new LinkedHashMap<>();
        int upstreamCaptureJobCount = 0;
        int reachabilitySupportActivationCount = 0;
        int activationBundleJobCount = 0;
        for (Candidate candidate : candidates) {
            if (result.jobs.size() >= arguments.maxJobs) {
                break;
            }
            if (!arguments.allowMultipleJobsPerRegion
                    && !selectedRegions.add(candidate.region.regionId)) {
                continue;
            }
            String scheduleId = "SCHEDULE." + result.jobs.size();
            MaterializationPlan materialization = candidate.materialization;
            JsonObject scheduledActivation = candidate.activation.deepCopy();
            mergePlan.attachOutboundValueEqualityBindings(
                    scheduledActivation);
            JsonObject captured = candidate.outputClosure ? null
                    : exactTargetSummary(candidate, summaries);
            String executionPhase = candidate.outputClosure
                    ? "CAPTURE_OUTPUT_PATH"
                    : arguments.captureOnly
                    ? "CAPTURE_ONLY"
                    : captured != null
                    ? "NEGATE_CAPTURED_PATH" : "CAPTURE_THEN_NEGATE";
            RegionCaptureGoal goal = RegionCaptureGoal.from(
                    candidate.activation);
            goal.writeTo(scheduledActivation);
            scheduledActivation.remove("summaryMode");
            scheduledActivation.addProperty("scheduleId", scheduleId);
            scheduledActivation.addProperty("executionPhase", executionPhase);
            scheduledActivation.addProperty("targetReplayRequired", false);
            scheduledActivation.addProperty("branchOverrideProhibited",
                    !arguments.forceBranchValidation);
            scheduledActivation.addProperty("discoverySymbolicReady",
                    bool(candidate.activation, "symbolicReady", false));
            scheduledActivation.addProperty("schedulerReady",
                    materialization.ready);
            scheduledActivation.addProperty("materializationComplete",
                    materialization.complete);
            scheduledActivation.addProperty("executableMaterializationCount",
                    materialization.executableCount);
            scheduledActivation.addProperty("deferredMaterializationCount",
                    materialization.deferredCount);
            scheduledActivation.addProperty("vmIntrinsicPlaceholderCount",
                    materialization.vmIntrinsicPlaceholderCount);
            scheduledActivation.addProperty("concreteFallbackCount",
                    materialization.concreteFallbacks.size());
            scheduledActivation.addProperty("symbolicCoverageComplete",
                    materialization.concreteFallbacks.size() == 0);
            scheduledActivation.addProperty("symbolicReady",
                    materialization.ready);
            scheduledActivation.addProperty("readinessAuthority",
                    "SCHEDULER_MATERIALIZATION_PLAN");
            scheduledActivation.add("materializations",
                    materialization.actions.deepCopy());
            scheduledActivation.add("concreteFallbacks",
                    materialization.concreteFallbacks.deepCopy());
            if (!candidate.outputClosure) {
                scheduledActivation.add("branchCaptureSelector",
                        candidate.target.captureSelector().toJson());
            }

            if (arguments.forceBranchValidation
                    && !candidate.outputClosure) {
                JsonArray forced = new JsonArray();
                JsonObject force = new JsonObject();
                force.addProperty("siteId", candidate.target.siteId);
                force.addProperty("occurrence",
                        candidate.target.selectedOccurrence);
                force.addProperty("desiredOutcome",
                        candidate.target.desiredOutcome);
                force.addProperty("mode", "SOOT_BRANCH_OVERRIDE_VALIDATION");
                force.addProperty("solverDerived", false);
                forced.add(force);
                scheduledActivation.add("forcedBranches", forced);
            }

            JsonObject job = new JsonObject();
            job.addProperty("scheduleId", scheduleId);
            job.addProperty("phase", executionPhase);
            job.addProperty("activationId", candidate.activationId);
            job.addProperty("regionId", candidate.region.regionId);
            job.addProperty("test", string(candidate.activation, "test"));
            job.addProperty("rootMethod",
                    string(candidate.activation, "rootMethod"));
            job.addProperty("invocationOrdinal",
                    integer(candidate.activation, "invocationOrdinal", 1));
            job.addProperty("workloadKind", workloadKind(candidate, edges));
            job.addProperty("selectionReason", candidate.reason);
            job.add("captureGoal", goal.toJson());
            job.addProperty("captureReady", materialization.ready);
            job.addProperty("materializationComplete",
                    materialization.complete);
            job.addProperty("executableMaterializationCount",
                    materialization.executableCount);
            job.addProperty("deferredMaterializationCount",
                    materialization.deferredCount);
            job.addProperty("vmIntrinsicPlaceholderCount",
                    materialization.vmIntrinsicPlaceholderCount);
            job.addProperty("concreteFallbackCount",
                    materialization.concreteFallbacks.size());
            job.addProperty("symbolicCoverageComplete",
                    materialization.concreteFallbacks.size() == 0);
            job.addProperty("forceValidationEnabled",
                    arguments.forceBranchValidation);
            if (!candidate.outputClosure) {
                job.add("branchCaptureSelector",
                        candidate.target.captureSelector().toJson());
            } else {
                upstreamCaptureJobCount++;
                JsonElement requestedOutput = candidate.activation.get(
                        "requestedOutput");
                JsonElement edgeBindings = scheduledActivation.get(
                        "edgeBindings");
                job.add("requestedOutput", requestedOutput == null
                        ? new JsonObject() : requestedOutput.deepCopy());
                job.add("edgeBindings", edgeBindings == null
                        ? new JsonArray() : edgeBindings.deepCopy());
            }
            job.add("materializations", materialization.actions.deepCopy());
            job.add("symbolicContext",
                    mergePlan.contextFor(candidate.region.regionId,
                            string(candidate.activation, "regionInstanceId")));
            if (captured != null && !candidate.outputClosure) {
                JsonObject query = branchQuery(candidate, captured,
                        mergePlan);
                job.add("branchQuery", query);
                if (object(query, "symbolicContext").size() > 0) {
                    job.add("symbolicContext", object(query,
                            "symbolicContext").deepCopy());
                }
                result.queries.add(query);
            }
            List<JsonObject> activationBundle = scheduledActivationBundle(
                    scheduledActivation, scheduleId);
            JsonArray supportActivationIds = new JsonArray();
            for (JsonObject member : activationBundle) {
                if ("REACHABILITY_SUPPORT".equals(string(member,
                        "activationBundleMemberRole"))) {
                    supportActivationIds.add(string(member,
                            "activationId"));
                }
            }
            int supportCount = supportActivationIds.size();
            job.addProperty("reachabilitySupportActivationCount",
                    supportCount);
            job.add("reachabilitySupportActivationIds",
                    supportActivationIds);
            job.addProperty("activationSelectionRequired", supportCount > 0
                    ? "ALL" : candidate.activationId);
            if (supportCount > 0) {
                activationBundleJobCount++;
                reachabilitySupportActivationCount += supportCount;
            }
            result.jobs.add(job);
            appendUniqueActivationBundle(result.scheduledActivations,
                    emittedActivationDefinitions, activationBundle);
        }

        result.summary.addProperty("candidateCount", candidates.size());
        result.summary.addProperty("scheduledJobCount", result.jobs.size());
        result.summary.addProperty("scheduledActivationCount",
                result.scheduledActivations.size());
        result.summary.addProperty("upstreamCaptureJobCount",
                upstreamCaptureJobCount);
        result.summary.addProperty("reachabilitySupportActivationCount",
                reachabilitySupportActivationCount);
        result.summary.addProperty("activationBundleJobCount",
                activationBundleJobCount);
        result.summary.addProperty("activationSelectionRequired",
                activationBundleJobCount > 0 ? "ALL" : "EXACT_JOB_ACTIVATION");
        result.summary.addProperty("equalityClassCount",
                mergePlan.equalityClasses.size());
        result.summary.addProperty("versionedStateMergeCount",
                mergePlan.stateMerges.size());
        result.summary.addProperty("branchQueryCount", result.queries.size());
        result.summary.addProperty("forceBranchValidation",
                arguments.forceBranchValidation);
        result.summary.addProperty("captureOnly", arguments.captureOnly);
        result.summary.addProperty("recursiveRegionQueryCount",
                result.regionWorkItems.size());
        result.summary.addProperty("recursiveUpstreamRequestCount",
                result.upstreamRequests.size());
        result.summary.addProperty("alternativeWriterGroupCount",
                result.alternativeWriterGroups.size());
        result.summary.addProperty("recursiveRegionComplete",
                bool(result.regionManifest, "complete", false));
        result.summary.addProperty("regionPathTaskCount",
                result.pathTasks.size());
        result.summary.addProperty("regionPathClosureComplete",
                bool(result.pathManifest, "complete", false));
        result.summary.addProperty("definitionSiteAuthority",
                definitions.authoritative
                        ? "STATIC_DATAFLOW_DEF_SITE" : "LOCAL_NAME_FALLBACK");
        result.summary.addProperty("precision",
                "STATIC_REGION_PLUS_RUNTIME_ACTIVATION_AND_EDGE_VALIDATION");

        writeJsonl(arguments.outputDirectory.resolve("concolic_schedule.jsonl"),
                result.jobs);
        writeJsonl(arguments.outputDirectory.resolve(
                        "scheduled_activation_plan.jsonl"),
                result.scheduledActivations);
        writeJsonl(arguments.outputDirectory.resolve("branch_queries.jsonl"),
                result.queries);
        writeJson(arguments.outputDirectory.resolve("symbolic_merge_plan.json"),
                result.mergePlan);
        writeJson(arguments.outputDirectory.resolve(
                "concolic_scheduler_summary.json"), result.summary);
        writeJsonl(arguments.outputDirectory.resolve(
                        "recursive_region_worklist.jsonl"),
                result.regionWorkItems);
        writeJsonl(arguments.outputDirectory.resolve(
                        "recursive_upstream_requests.jsonl"),
                result.upstreamRequests);
        writeJsonl(arguments.outputDirectory.resolve(
                        "alternative_writer_groups.jsonl"),
                result.alternativeWriterGroups);
        writeJson(arguments.outputDirectory.resolve(
                        "recursive_region_manifest.json"),
                result.regionManifest);
        writeJsonl(arguments.outputDirectory.resolve(
                        "region_path_worklist.jsonl"), result.pathTasks);
        writeJson(arguments.outputDirectory.resolve(
                        "region_path_manifest.json"), result.pathManifest);
        return result;
    }

    /**
     * Expands the recursively declared reachability support for one selected
     * activation.  Support rows must precede their consumer in the emitted
     * plan so the runtime can activate every upstream region needed by the
     * same concrete execution.  The custom runtime must select ALL rows for a
     * bundle; selecting only the primary activation silently loses the
     * producer path and is therefore recorded as an explicit requirement.
     */
    private static List<JsonObject> scheduledActivationBundle(
            JsonObject primary, String scheduleId) throws IOException {
        List<JsonObject> definitions = new ArrayList<>();
        Map<String, JsonObject> byId = new LinkedHashMap<>();
        Set<String> visiting = new LinkedHashSet<>();
        String primaryId = string(primary, "activationId");
        if (primaryId.isEmpty()) {
            throw new IOException("Scheduled activation has no activationId");
        }
        flattenReachabilityActivation(primary, primaryId, scheduleId, false,
                definitions, byId, visiting);
        int bundleSize = definitions.size();
        for (int index = 0; index < definitions.size(); index++) {
            JsonObject member = definitions.get(index);
            member.addProperty("activationBundleIndex", index);
            member.addProperty("activationBundleSize", bundleSize);
            member.addProperty("activationSelectionRequired",
                    bundleSize > 1 ? "ALL" : primaryId);
        }
        return definitions;
    }

    private static void flattenReachabilityActivation(
            JsonObject activation, String primaryId, String scheduleId,
            boolean support, List<JsonObject> result,
            Map<String, JsonObject> definitions, Set<String> visiting)
            throws IOException {
        String activationId = string(activation, "activationId");
        if (activationId.isEmpty()) {
            throw new IOException("Reachability activation has no "
                    + "activationId for bundle " + primaryId);
        }
        if (!visiting.add(activationId)) {
            throw new IOException("Cyclic reachability activation bundle at "
                    + activationId + " for " + primaryId);
        }
        JsonArray nested = array(activation,
                "reachabilitySupportActivations");
        for (JsonElement element : nested) {
            if (!element.isJsonObject()) {
                throw new IOException("Non-object reachability support in "
                        + activationId);
            }
            flattenReachabilityActivation(element.getAsJsonObject(),
                    primaryId, scheduleId, true, result, definitions,
                    visiting);
        }
        visiting.remove(activationId);

        JsonObject normalized = activation.deepCopy();
        normalized.remove("reachabilitySupportActivations");
        JsonObject previous = definitions.get(activationId);
        if (previous != null) {
            if (!previous.equals(normalized)) {
                throw new IOException("Conflicting reachability activation "
                        + "definitions for " + activationId);
            }
            return;
        }
        definitions.put(activationId, normalized.deepCopy());
        normalized.addProperty("activationBundleRootActivationId",
                primaryId);
        normalized.addProperty("activationBundleScheduleId", scheduleId);
        normalized.addProperty("activationBundleMemberRole", support
                ? "REACHABILITY_SUPPORT" : "PRIMARY");
        if (support) {
            normalized.addProperty("reachabilitySupportForActivationId",
                    primaryId);
        }
        result.add(normalized);
    }

    private static void appendUniqueActivationBundle(
            List<JsonObject> output, Map<String, JsonObject> emitted,
            List<JsonObject> bundle) throws IOException {
        for (JsonObject activation : bundle) {
            String activationId = string(activation, "activationId");
            JsonObject previous = emitted.get(activationId);
            if (previous != null) {
                JsonObject left = previous.deepCopy();
                JsonObject right = activation.deepCopy();
                for (String annotation : new String[]{
                        "activationBundleRootActivationId",
                        "activationBundleScheduleId",
                        "activationBundleMemberRole",
                        "reachabilitySupportForActivationId",
                        "activationBundleIndex", "activationBundleSize",
                        "activationSelectionRequired"}) {
                    left.remove(annotation);
                    right.remove(annotation);
                }
                if (!left.equals(right)) {
                    throw new IOException("Conflicting scheduled activation "
                            + "definitions for " + activationId);
                }
                continue;
            }
            emitted.put(activationId, activation.deepCopy());
            output.add(activation);
        }
    }

    /**
     * Converts one discovered output-closure activation into an executable,
     * scheduler-authorized capture plan.  Campaign execution uses exactly the
     * same definition-site resolver as ordinary scheduling.
     */
    public static JsonObject prepareOutputCapture(
            JsonObject activation, List<JsonObject> staticGraph) {
        JsonObject result = activation == null
                ? new JsonObject() : activation.deepCopy();
        RegionCaptureGoal captureGoal = RegionCaptureGoal.from(result);
        DefinitionIndex definitions = staticGraph == null
                || staticGraph.isEmpty() ? DefinitionIndex.fallback()
                : DefinitionIndex.from(staticGraph);
        MaterializationPlan materialization = materializationPlan(result,
                definitions, Collections.<String>emptySet());
        if (captureGoal.isTransitionDiscovery()) {
            RegionCaptureGoal.transitionDiscovery().writeTo(result);
        } else {
            RegionCaptureGoal.outputClosure().writeTo(result);
        }
        result.remove("summaryMode");
        result.remove("branchCaptureSelector");
        result.remove("forcedBranches");
        result.remove("modelAssignments");
        boolean outputCaptureReady = outputCaptureReady(result);
        boolean transitionTemplateReady =
                transitionDiscoveryCaptureTemplateReady(result);
        boolean schedulerReady = materialization.ready
                && (outputCaptureReady || transitionTemplateReady);
        result.addProperty("executionPhase", transitionTemplateReady
                && !outputCaptureReady
                ? "CAPTURE_TRANSITION_GUARD_PATH"
                : "CAPTURE_OUTPUT_PATH");
        result.addProperty("schedulerReady", schedulerReady);
        result.addProperty("materializationComplete",
                materialization.complete);
        result.addProperty("outputCaptureReady", outputCaptureReady);
        result.addProperty("transitionDiscoveryCaptureTemplateReady",
                transitionTemplateReady);
        result.addProperty("executableMaterializationCount",
                materialization.executableCount);
        result.addProperty("deferredMaterializationCount",
                materialization.deferredCount);
        result.addProperty("vmIntrinsicPlaceholderCount",
                materialization.vmIntrinsicPlaceholderCount);
        result.addProperty("concreteFallbackCount",
                materialization.concreteFallbacks.size());
        result.addProperty("symbolicCoverageComplete",
                materialization.concreteFallbacks.size() == 0);
        result.add("concreteFallbacks",
                materialization.concreteFallbacks.deepCopy());
        result.addProperty("symbolicReady", schedulerReady);
        result.addProperty("readinessAuthority",
                "SCHEDULER_MATERIALIZATION_PLAN");
        result.addProperty("branchOverrideProhibited", true);
        result.add("materializations", materialization.actions.deepCopy());
        return result;
    }

    private static List<Candidate> candidates(Arguments arguments,
                                              List<JsonObject> activations,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions,
                                              CaptureEvidence evidence) {
        List<Candidate> result = new ArrayList<>();
        for (JsonObject discoveredActivation : activations) {
            String activationId = string(discoveredActivation,
                    "activationId");
            String regionId = string(discoveredActivation, "regionId");
            Region region = regions.get(regionId);
            if (region == null || activationId.isEmpty()) {
                continue;
            }
            JsonObject configuredActivation = configuredOutputClosure(
                    arguments, discoveredActivation, region);
            configuredActivation = refineRequestedOutputCapture(arguments,
                    configuredActivation, evidence);
            JsonObject activation = operationalActivation(
                    configuredActivation);
            if (!bool(activation, "replayable", false)) {
                continue;
            }
            if (!arguments.activationId.isEmpty()
                    && !arguments.activationId.equals(activationId)) {
                continue;
            }
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(regionId)) {
                continue;
            }
            RegionCaptureGoal captureGoal = RegionCaptureGoal.from(activation);
            Set<String> definitionMethods = runtimeDefinitionMethods(
                    activation);
            if (captureGoal.isOutputClosure()) {
                MaterializationPlan upstreamPlan = materializationPlan(
                        activation, definitions, definitionMethods);
                if (!bool(activation, "requestedOutputSliceComplete", false)
                        || !upstreamPlan.complete
                        || !outputCaptureReady(activation)
                        && !transitionDiscoveryCaptureTemplateReady(
                        activation)) {
                    upstreamPlan = upstreamPlan.notReady();
                }
                result.add(new Candidate(activation, activationId, region,
                        TargetBranch.outputCapture(), true,
                        upstreamPlan, true));
                continue;
            }
            JsonArray branches = array(activation, "branches");
            for (int index = 0; index < branches.size(); index++) {
                JsonElement element = branches.get(index);
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject branch = element.getAsJsonObject();
                String siteId = string(branch, "siteId");
                if (!arguments.targetSite.isEmpty()
                        && !arguments.targetSite.equals(siteId)) {
                    continue;
                }
                if (!bool(branch, "observed", false)
                        || !branch.has("requiredOutcome")
                        || branch.get("requiredOutcome").isJsonNull()) {
                    continue;
                }
                boolean required = bool(branch, "requiredOutcome", false);
                boolean hasWitness = hasOutcome(branch, required);
                boolean explicitlySelected = !arguments.targetSite.isEmpty();
                boolean explore = "EXPLORE".equals(string(branch, "policy"));
                if (hasWitness && !explicitlySelected && !explore) {
                    continue;
                }
                boolean observed = hasWitness
                        ? required
                        : bool(branch, "observedOutcome", !required);
                int occurrence = selectedOccurrence(branch, required,
                        !hasWitness);
                boolean desired = hasWitness ? !observed : required;
                TargetBranch target = new TargetBranch(siteId, index,
                        occurrence, observed, desired,
                        hasWitness ? "EXPLORE_ALTERNATIVE"
                                : "DIRECTED_REQUIRED_OUTCOME");
                result.add(new Candidate(activation, activationId, region,
                        target, hasWitness,
                        materializationPlan(activation, definitions,
                                definitionMethods), false));
            }
        }
        return result;
    }

    /** Restricts static definition lookup to the concrete runtime call
     * closure selected before the frozen-graph demand re-slice. */
    private static Set<String> runtimeDefinitionMethods(
            JsonObject activation) {
        JsonElement encoded = activation.get("runtimeDefinitionMethods");
        if (encoded == null || !encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "activation requires runtimeDefinitionMethods array: "
                            + string(activation, "activationId"));
        }
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                throw new IllegalArgumentException(
                        "runtimeDefinitionMethods contains non-string value: "
                                + string(activation, "activationId"));
            }
            String method = safe(element.getAsString()).trim();
            if (method.isEmpty()) {
                throw new IllegalArgumentException(
                        "runtimeDefinitionMethods contains empty method: "
                                + string(activation, "activationId"));
            }
            result.add(method);
        }
        return result;
    }

    /**
     * Builds an output-closure request from a configured semantic output
     * cell and the region catalog's existing exact output slice.  This lets a
     * domain adapter request a producer summary without hard-coding generated
     * REGION/ACT ids or rerunning static/runtime discovery.
     */
    private static JsonObject configuredOutputClosure(
            Arguments arguments, JsonObject discovered, Region region) {
        if (arguments.requestedOutputCell.isEmpty()) {
            return discovered;
        }
        JsonObject output = region.outputByCell.get(
                arguments.requestedOutputCell);
        if (output == null) {
            return discovered;
        }
        String outputPort = string(output, "portId");
        JsonObject slice = region.outputSliceByPort.get(outputPort);
        if (outputPort.isEmpty() || slice == null
                || !bool(slice, "structuralComplete",
                bool(slice, "complete", false))) {
            return discovered;
        }

        JsonObject activation = discovered.deepCopy();
        RegionCaptureGoal.outputClosure().writeTo(activation);
        JsonObject requested = output.deepCopy();
        requested.addProperty("selectionAuthority",
                "CONFIGURED_EXACT_REGION_OUTPUT_CELL_V1");
        activation.add("requestedOutput", requested);
        activation.add("requestedOutputSlice", slice.deepCopy());
        activation.addProperty("requestedOutputSliceComplete",
                bool(slice, "complete", false));
        activation.addProperty("requestedOutputSlicePolicy",
                "CONFIGURED_REGION_CATALOG_EXACT_OUTPUT_SLICE");
        activation.addProperty("requestedOutputSliceRefinementComplete",
                true);
        activation.addProperty("requestedOutputCaptureRequired",
                bool(slice, "captureBindingsRequired", false));
        activation.addProperty("requestedOutputCaptureComplete",
                bool(slice, "captureBindingsComplete", true));
        activation.add("requestedOutputCapture",
                array(slice, "captureBindings").deepCopy());
        activation.add("requestedOutputMethods",
                array(slice, "methods").deepCopy());
        activation.addProperty("configuredOutputClosureSynthesized", true);
        activation.addProperty("configuredOutputClosureAuthority",
                "SEMANTIC_OUTPUT_CELL_PLUS_FROZEN_REGION_SLICE_V1");
        activation.addProperty("derivedFromActivationId",
                string(discovered, "activationId"));

        Set<String> inputs = stringSet(slice, "inputPorts");
        if (!inputs.isEmpty()) {
            JsonArray selected = new JsonArray();
            for (JsonElement element : array(discovered, "symbolize")) {
                if (element.isJsonObject()
                        && inputs.contains(firstNonBlank(string(
                        element.getAsJsonObject(), "symbol"), string(
                        element.getAsJsonObject(), "inputPort")))) {
                    selected.add(element.deepCopy());
                }
            }
            activation.add("symbolize", selected);
        }
        Set<String> sites = stringSet(slice, "sites");
        if (!sites.isEmpty()) {
            JsonArray selected = new JsonArray();
            for (JsonElement element : array(discovered, "branches")) {
                if (element.isJsonObject() && sites.contains(string(
                        element.getAsJsonObject(), "siteId"))) {
                    selected.add(element.deepCopy());
                }
            }
            activation.add("branches", selected);
        }
        return activation;
    }

    /**
     * Turns static output-capture templates into an exact runtime request.
     * An explicit selector always names both the static site and dynamic
     * occurrence.  Without one, the frozen runtime-instance catalog may
     * select a single template whose enclosing method was observed in this
     * exact region instance.  Older compact catalogs retain method presence
     * but not per-site counts, so that automatic case deliberately records a
     * first-occurrence approximation instead of claiming exact trace proof.
     */
    private static JsonObject refineRequestedOutputCapture(
            Arguments arguments, JsonObject source,
            CaptureEvidence evidence) {
        if (!RegionCaptureGoal.from(source).isOutputClosure()
                || !bool(source, "requestedOutputCaptureRequired", false)) {
            return source;
        }
        JsonArray templates = array(source, "requestedOutputCapture");
        if (templates.size() == 0) {
            return incompleteCaptureSelection(source,
                    "NO_STATIC_CAPTURE_TEMPLATE", 0, 0);
        }

        String configuredSite = arguments.requestedOutputCaptureSite;
        int configuredOccurrence =
                arguments.requestedOutputCaptureOccurrence;
        if (configuredSite.isEmpty() && configuredOccurrence == 0
                && templates.size() == 1
                && templates.get(0).isJsonObject()
                && runtimeExactOutputCapture(
                templates.get(0).getAsJsonObject())) {
            JsonObject preserved = source.deepCopy();
            JsonObject capture = templates.get(0).getAsJsonObject();
            preserved.addProperty("requestedOutputCaptureComplete", true);
            preserved.addProperty("requestedOutputCaptureRefinementRequired",
                    false);
            preserved.addProperty("requestedOutputCaptureSelectionStatus",
                    "EXACT_RUNTIME_REQUEST_READY");
            preserved.addProperty("requestedOutputCaptureSelectionAuthority",
                    "PRESERVED_RUNTIME_EXACT_OUTPUT_CAPTURE_V1");
            preserved.addProperty("requestedOutputCaptureSelectedSite",
                    string(capture, "siteId"));
            preserved.addProperty("requestedOutputCaptureSelectedOccurrence",
                    integer(capture, "occurrence", 0));
            preserved.addProperty("requestedOutputCaptureTemplateCount", 1);
            preserved.addProperty(
                    "requestedOutputCaptureObservedCandidateCount", 1);
            preserved.addProperty(
                    "requestedOutputCaptureOccurrenceApproximate", false);
            return preserved;
        }
        List<JsonObject> candidates = new ArrayList<>();
        String authority = "";
        boolean firstOccurrenceApproximation = false;
        Set<String> observedMethods = Collections.emptySet();
        if (!configuredSite.isEmpty()) {
            for (JsonElement element : templates) {
                if (element.isJsonObject() && configuredSite.equals(string(
                        element.getAsJsonObject(), "siteId"))) {
                    candidates.add(element.getAsJsonObject());
                }
            }
            if (configuredOccurrence <= 0) {
                return incompleteCaptureSelection(source,
                        "CONFIGURED_CAPTURE_SITE_REQUIRES_POSITIVE_"
                                + "OCCURRENCE",
                        templates.size(), candidates.size());
            }
            authority = "CONFIGURED_EXACT_CAPTURE_SITE_AND_OCCURRENCE_V1";
        } else {
            observedMethods = evidence.observedMethods(source);
            if (!observedMethods.isEmpty()) {
                for (JsonElement element : templates) {
                    if (!element.isJsonObject()) {
                        continue;
                    }
                    JsonObject capture = element.getAsJsonObject();
                    if (observedMethods.contains(captureMethod(capture))) {
                        candidates.add(capture);
                    }
                }
                authority = "FROZEN_INSTANCE_UNIQUE_OBSERVED_CAPTURE_"
                        + "METHOD_V1";
            } else if (templates.size() == 1
                    && templates.get(0).isJsonObject()
                    && integer(templates.get(0).getAsJsonObject(),
                    "occurrence", 0) > 0) {
                candidates.add(templates.get(0).getAsJsonObject());
                authority = "FROZEN_EXACT_CAPTURE_BINDING_V1";
            }
        }
        if (candidates.size() != 1) {
            return incompleteCaptureSelection(source,
                    candidates.isEmpty()
                            ? "NO_UNIQUE_OBSERVED_CAPTURE_SITE"
                            : "AMBIGUOUS_OBSERVED_CAPTURE_SITE",
                    templates.size(), candidates.size());
        }

        JsonObject selected = candidates.get(0).deepCopy();
        int occurrence = configuredOccurrence > 0
                ? configuredOccurrence
                : integer(selected, "occurrence", 0);
        if (occurrence <= 0) {
            occurrence = 1;
            firstOccurrenceApproximation = true;
        }
        selected.addProperty("occurrence", occurrence);
        selected.addProperty("occurrenceAuthority",
                firstOccurrenceApproximation
                        ? "UNIQUE_OBSERVED_CAPTURE_METHOD_FIRST_"
                        + "OCCURRENCE_APPROXIMATION_V1"
                        : authority);
        selected.addProperty("selectionAuthority", authority);

        JsonObject result = source.deepCopy();
        JsonArray exact = new JsonArray();
        exact.add(selected);
        result.add("requestedOutputCapture", exact);
        result.addProperty("requestedOutputCaptureComplete", true);
        result.addProperty("requestedOutputCaptureRefinementRequired", false);
        result.addProperty("requestedOutputCaptureSelectionStatus",
                "EXACT_RUNTIME_REQUEST_READY");
        result.addProperty("requestedOutputCaptureSelectionAuthority",
                authority);
        result.addProperty("requestedOutputCaptureSelectedSite",
                string(selected, "siteId"));
        result.addProperty("requestedOutputCaptureSelectedOccurrence",
                occurrence);
        result.addProperty("requestedOutputCaptureTemplateCount",
                templates.size());
        result.addProperty("requestedOutputCaptureObservedCandidateCount",
                candidates.size());
        result.addProperty("requestedOutputCaptureOccurrenceApproximate",
                firstOccurrenceApproximation);
        if (!observedMethods.isEmpty()) {
            result.add("requestedOutputCaptureObservedMethods",
                    JSONL_GSON.toJsonTree(observedMethods));
        }
        return result;
    }

    private static JsonObject incompleteCaptureSelection(JsonObject source,
                                                         String reason,
                                                         int templateCount,
                                                         int candidateCount) {
        JsonObject result = source.deepCopy();
        result.addProperty("requestedOutputCaptureComplete", false);
        result.addProperty("requestedOutputCaptureSelectionStatus",
                "RUNTIME_REFINEMENT_REQUIRED");
        result.addProperty("requestedOutputCaptureSelectionReason", reason);
        result.addProperty("requestedOutputCaptureTemplateCount",
                templateCount);
        result.addProperty("requestedOutputCaptureObservedCandidateCount",
                candidateCount);
        return result;
    }

    private static String captureMethod(JsonObject capture) {
        return firstNonBlank(string(capture, "callerMethod"),
                string(capture, "method"));
    }

    private static boolean runtimeExactOutputCapture(JsonObject capture) {
        if (integer(capture, "occurrence", 0) < 1
                || integer(capture, "runtimeEventSeq", 0) < 1) {
            return false;
        }
        String authority = string(capture, "occurrenceAuthority");
        String kind = firstNonBlank(string(capture, "captureKind"),
                "CALL_ARGUMENT");
        if ("FIELD_ASSIGNMENT_RHS".equals(kind)) {
            return "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_SITE_"
                    .concat("LAST_WRITE_OCCURRENCE").equals(authority)
                    && integer(capture, "runtimeCallId", 0) > 0
                    && integer(capture,
                    "runtimeFieldOwnerObjectId", 0) > 0;
        }
        return "CALL_ARGUMENT".equals(kind)
                && "RUNTIME_EXACT_CALL_ARGUMENT_OCCURRENCE".equals(authority)
                && integer(capture, "runtimeInvocationId", 0) > 0;
    }

    /** Canonicalizes unstable default object identity in thread names. */
    private static JsonObject operationalActivation(JsonObject discovered) {
        JsonObject configured = discovered;
        Matcher identityThread = DEFAULT_OBJECT_IDENTITY_THREAD_NAME.matcher(
                string(discovered, "threadName"));
        if (identityThread.matches()) {
            configured = discovered.deepCopy();
            int globalOrdinal = integer(configured, "invocationOrdinal", 1);
            configured.addProperty("stableThreadName",
                    identityThread.group(1) + "@*");
            configured.addProperty("invocationOrdinalWithinContext",
                    globalOrdinal);
            configured.addProperty("stableContextOrdinalRebased", true);
            configured.addProperty("stableContextOrdinalRebaseAuthority",
                    "FROZEN_DEFAULT_OBJECT_THREAD_NAME_CANONICALIZATION_V1");
        }
        return configured;
    }

    /**
     * An ordinary output closure may execute only with an exact runtime
     * capture request.  A transition-discovery seed is the sole exception:
     * it captures only the guard path and is quarantined until a fresh
     * flipped execution discovers the concrete occurrence.
     */
    private static boolean outputCaptureReady(JsonObject activation) {
        return !bool(activation, "requestedOutputCaptureRequired", false)
                || bool(activation, "requestedOutputCaptureComplete",
                false);
    }

    private static boolean transitionDiscoveryCaptureTemplateReady(
            JsonObject activation) {
        if (!RegionCaptureGoal.from(activation).isTransitionDiscovery()
                || !bool(activation, "requestedOutputSliceComplete", false)
                || !bool(activation,
                "requestedOutputCaptureRefinementRequired", false)
                || !"STATIC_EXACT_OUTPUT_ENDPOINT_RUNTIME_OCCURRENCE_PENDING"
                .equals(string(activation,
                        "requestedOutputCaptureTemplateAuthority"))) {
            return false;
        }
        JsonArray captures = array(activation, "requestedOutputCapture");
        if (captures.size() != 1 || !captures.get(0).isJsonObject()) {
            return false;
        }
        JsonObject capture = captures.get(0).getAsJsonObject();
        if (integer(capture, "occurrence", -1) != 0
                || string(capture, "captureBindingId").isEmpty()
                || string(capture, "outputPort").isEmpty()
                || string(capture, "outputCell").isEmpty()
                || string(capture, "siteId").isEmpty()
                || integer(capture, "unitIndex", -1) < 0
                || !"RUNTIME_INSTANCE_REFINEMENT_REQUIRED".equals(
                string(capture, "occurrenceAuthority"))) {
            return false;
        }
        String kind = firstNonBlank(string(capture, "captureKind"),
                "CALL_ARGUMENT");
        if ("FIELD_ASSIGNMENT_RHS".equals(kind)) {
            return !string(capture, "method").isEmpty()
                    && !string(capture, "fieldSignature").isEmpty()
                    && "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS".equals(
                    string(capture, "bindingAuthority"));
        }
        return "CALL_ARGUMENT".equals(kind)
                && !string(capture, "callerMethod").isEmpty()
                && !string(capture, "calleeMethod").isEmpty()
                && integer(capture, "argumentIndex", -1) >= 0;
    }

    private static boolean hasOutcome(JsonObject branch, boolean outcome) {
        JsonArray occurrences = array(branch, "occurrences");
        if (occurrences.size() == 0) {
            return bool(branch, "matchesRequiredOutcome", false);
        }
        for (JsonElement element : occurrences) {
            if (element.isJsonObject()
                    && bool(element.getAsJsonObject(), "outcome", !outcome)
                    == outcome) {
                return true;
            }
        }
        return false;
    }

    private static int selectedOccurrence(JsonObject branch,
                                          boolean desiredOutcome,
                                          boolean selectObservedMismatch) {
        JsonArray occurrences = array(branch, "occurrences");
        if (occurrences.size() == 0) {
            return Math.max(1, integer(branch, "selectedOccurrence", 1));
        }
        int fallback = 1;
        for (int index = 0; index < occurrences.size(); index++) {
            JsonObject occurrence = occurrences.get(index).getAsJsonObject();
            boolean value = bool(occurrence, "outcome", false);
            fallback = integer(occurrence, "occurrence", index + 1);
            if (selectObservedMismatch && value != desiredOutcome) {
                return fallback;
            }
            if (!selectObservedMismatch && value == desiredOutcome) {
                return fallback;
            }
        }
        return fallback;
    }

    private static MaterializationPlan materializationPlan(
            JsonObject activation, DefinitionIndex definitions,
            Set<String> regionMethods) {
        JsonArray result = new JsonArray();
        JsonArray concreteFallbacks = new JsonArray();
        Set<String> containerBaseInputs = containerBindingSymbols(
                activation, "baseInputSymbol");
        Set<String> containerInputPorts = containerBindingSymbols(
                activation, "containerInputPort");
        int sourceActionCount = 0;
        int executableCount = 0;
        int deferredCount = 0;
        int vmIntrinsicPlaceholderCount = 0;
        JsonArray sourceActions = array(activation, "symbolize");
        if (sourceActions.size() == 0) {
            sourceActions = array(activation, "materializations");
        }
        for (JsonElement element : sourceActions) {
            if (!element.isJsonObject()) {
                continue;
            }
            sourceActionCount++;
            JsonObject action = element.getAsJsonObject();
            JsonObject binding = action.deepCopy();
            String location = string(action, "location");
            String cell = string(action, "cell");
            boolean vmIntrinsic = verifiedVmIntrinsicPlaceholder(action,
                    location, cell);
            if (configuredRequestedStateCore(activation)
                    && !containerBaseInputs.contains(string(action,
                    "symbol"))
                    && !containerInputPorts.contains(string(action,
                    "symbol"))
                    && !cell.equals(string(object(activation,
                    "requestedOutput"), "cell"))
                    && !vmIntrinsic) {
                concreteFallbacks.add(concreteFallback(binding,
                        "CONFIGURED_REQUESTED_MAP_CORE_USES_WORKLOAD_VALUE"));
                continue;
            }
            if (action.has("observed")
                    && !bool(action, "observed", false)
                    && !containerBaseInputs.contains(string(action,
                    "symbol"))
                    && !authoritativeDefinitionResolutionRequested(action)
                    && !vmIntrinsic) {
                concreteFallbacks.add(concreteFallback(binding,
                        "RUNTIME_EXPLICITLY_UNOBSERVED"));
                continue;
            }
            if (exactContainerSnapshotLeafDeclaration(activation, action)) {
                // Schema-v2 snapshots are materialized dynamically when the
                // observation-only container is consumed.  Keep the exact
                // leaf in the declared symbolize catalog, but do not install
                // an owner-wide FIELD_ACCESS hook or misclassify it as a
                // concrete fallback merely because the static cell starts at
                // an intermediate reference owner.
                continue;
            }
            if ("ARGUMENT".equals(location)
                    || "ARGUMENT_FIELD".equals(location)
                    || "RECEIVER_FIELD".equals(location)) {
                binding.addProperty("bindingMode", "ROOT_ENTRY");
                executableCount++;
            } else if ("ARGUMENT_FIELD_PATH".equals(location)) {
                if (validFieldPaths(action)) {
                    binding.addProperty("bindingMode", "ROOT_ENTRY");
                    executableCount++;
                } else {
                    concreteFallbacks.add(concreteFallback(binding,
                            "UNRESOLVED_ARGUMENT_FIELD_PATH"));
                    continue;
                }
            } else if ("CALL_RETURN".equals(location)) {
                Set<String> requestedMethods =
                        requestedOutputMethods(activation);
                Set<String> allowedMethods = requestedMethods.isEmpty()
                        ? regionMethods : requestedMethods;
                JsonArray sites = definitions.returnSites(cell,
                        allowedMethods,
                        requestedOutputSites(activation));
                boolean pendingArrayFieldRoot =
                        pendingArrayFieldCallReturnRoot(action);
                if (pendingArrayFieldRoot
                        && (!definitions.authoritative
                        || sites.size() != 1)) {
                    binding.add("definitionSites", sites.deepCopy());
                    binding.addProperty("definitionAuthority",
                            definitions.authoritative
                                    ? "STATIC_DATAFLOW_DEF_SITE"
                                    : "LOCAL_NAME_FALLBACK");
                    binding.addProperty(
                            "arrayFieldMaterializationComplete", false);
                    binding.addProperty("materializationIssue",
                            !definitions.authoritative
                                    ? "ARRAY_CALL_RETURN_ROOT_REQUIRES_"
                                    + "AUTHORITATIVE_DEFINITION_INDEX"
                                    : "ARRAY_CALL_RETURN_ROOT_REQUIRES_"
                                    + "ONE_EXACT_FILTERED_RETURN_SITE:"
                                    + sites.size());
                    concreteFallbacks.add(concreteFallback(binding,
                            string(binding, "materializationIssue")));
                    continue;
                }
                if (sites.size() == 0) {
                    binding.addProperty("definitionAuthority",
                            definitions.authoritative
                                    ? "STATIC_DATAFLOW_DEF_SITE"
                                    : "LOCAL_NAME_FALLBACK");
                    concreteFallbacks.add(concreteFallback(binding,
                            "UNRESOLVED_CALL_RETURN_DEFINITION"));
                    continue;
                }
                for (JsonElement siteElement : sites) {
                    JsonObject site = siteElement.getAsJsonObject();
                    JsonObject localBinding = binding.deepCopy();
                    localBinding.addProperty("bindingMode",
                            "LOCAL_DEFINITION");
                    localBinding.addProperty("sourceBindingMode",
                            "CALL_RETURN_DEFINITION");
                    localBinding.addProperty("method",
                            string(site, "method"));
                    localBinding.addProperty("local",
                            string(site, "local"));
                    JsonArray oneSite = new JsonArray();
                    oneSite.add(site.deepCopy());
                    localBinding.add("definitionSites", oneSite);
                    localBinding.addProperty("definitionAuthority",
                            "STATIC_DATAFLOW_DEF_SITE");
                    dischargeDeferredResolution(localBinding,
                            "AUTHORITATIVE_STATIC_CALL_RETURN_DEFINITION_"
                                    + "SITE_V1");
                    localBinding.addProperty("lazy", true);
                    finalizePendingLocalArrayRoot(localBinding,
                            definitions.authoritative);
                    if (!validateExactArrayFieldMaterialization(
                            localBinding)) {
                        concreteFallbacks.add(concreteFallback(localBinding,
                                string(localBinding,
                                        "materializationIssue")));
                        continue;
                    }
                    result.add(localBinding);
                    executableCount++;
                }
                continue;
            } else if (vmIntrinsic) {
                binding.addProperty("bindingMode",
                        "VM_INTRINSIC_PLACEHOLDER");
                binding.addProperty("placeholderFunction",
                        SymbolicEnvironment.CURRENT_TIME_MILLIS_PLACEHOLDER);
                binding.addProperty("captureAuthority",
                        "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
                binding.addProperty("modelControllable", false);
                binding.addProperty("replayPolicy",
                        "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
                vmIntrinsicPlaceholderCount++;
            } else if ("HEAP_OBJECT_FIELD".equals(location)) {
                binding.addProperty("bindingMode", "FIELD_ACCESS");
                List<String> path = fieldPath(cell);
                JsonObject declaredLeaf = exactDeclaredFieldPathLeaf(
                        action, path);
                boolean deepExactDeclarationRequired = path.size() > 2;
                if (deepExactDeclarationRequired && declaredLeaf == null) {
                    concreteFallbacks.add(concreteFallback(binding,
                            "DEEP_FIELD_PATH_LACKS_EXACT_DECLARED_CHAIN"));
                    continue;
                }
                String derivedLeafOwner = declaredLeaf == null
                        ? leafOwnerClass(cell) : string(declaredLeaf,
                        "declaredFieldOwnerClass");
                String derivedLeafField = declaredLeaf == null
                        ? leafField(cell) : declaredFieldName(string(
                        declaredLeaf, "fieldSignature"));
                boolean exactMetadata = retainOrVerifyDerived(
                        binding, "fieldPath",
                        JSONL_GSON.toJsonTree(path))
                        && retainOrVerifyDerived(binding,
                        "accessOwnerClass", accessOwnerClass(cell))
                        && retainOrVerifyDerived(binding, "accessField",
                        path.isEmpty() ? "" : path.get(0))
                        && retainOrVerifyDerived(binding, "leafField",
                        derivedLeafField)
                        && retainOrVerifyDerived(binding,
                        "leafOwnerClass", derivedLeafOwner)
                        && (declaredLeaf == null
                        || retainOrVerifyDerived(binding,
                        "leafFieldSignature", string(declaredLeaf,
                                "fieldSignature"))
                        && retainOrVerifyDerived(binding, "field",
                        string(declaredLeaf, "fieldSignature"))
                        && retainOrVerifyDerived(binding, "javaType",
                        string(declaredLeaf, "declaredFieldType")));
                binding.addProperty("lazy", true);
                if (!exactMetadata) {
                    concreteFallbacks.add(concreteFallback(binding,
                            "PLANNER_EXACT_FIELD_METADATA_CONFLICTS_WITH_"
                                    + "STATIC_CELL"));
                    continue;
                } else if (path.size() > 1
                        && action.has("valueObjectId")
                        && longInteger(action, "valueObjectId", 0L) == 0L) {
                    // The concrete discovery observed the first projected
                    // reference as null.  A later write may make the path
                    // traversable, but that does not make it a region-entry
                    // value; keep the workload value instead of creating a
                    // temporal alias for a future object.
                    concreteFallbacks.add(concreteFallback(binding,
                            "RUNTIME_OBSERVED_NULL_PROJECTED_FIELD_ROOT"));
                    continue;
                } else {
                    executableCount++;
                }
            } else if ("REGION_LIVE_IN".equals(location)) {
                Matcher matcher = LOCAL_CELL.matcher(cell);
                if (matcher.matches()) {
                    binding.addProperty("bindingMode", "LOCAL_DEFINITION");
                    binding.addProperty("method", matcher.group(1));
                    binding.addProperty("local", matcher.group(2));
                    JsonArray sites = definitions.sites(cell);
                    binding.add("definitionSites", sites);
                    binding.addProperty("definitionAuthority",
                            definitions.authoritative
                                    ? "STATIC_DATAFLOW_DEF_SITE"
                                    : "LOCAL_NAME_FALLBACK");
                    if (definitions.authoritative && sites.size() == 1) {
                        dischargeDeferredResolution(binding,
                                "AUTHORITATIVE_STATIC_LOCAL_DEFINITION_"
                                        + "SITE_V1");
                    }
                    finalizePendingLocalArrayRoot(binding,
                            definitions.authoritative);
                    if (definitions.authoritative && sites.size() == 0) {
                        concreteFallbacks.add(concreteFallback(binding,
                                "UNRESOLVED_LOCAL_DEFINITION"));
                        continue;
                    } else {
                        executableCount++;
                    }
                    binding.addProperty("lazy", true);
                } else {
                    concreteFallbacks.add(concreteFallback(binding,
                            "UNSUPPORTED_LIVE_IN"));
                    continue;
                }
            } else {
                concreteFallbacks.add(concreteFallback(binding,
                        "UNSUPPORTED_MATERIALIZATION"));
                continue;
            }
            if (containerInputPorts.contains(string(binding, "symbol"))
                    && ArrayFieldContract.from(binding).fieldBackedArray) {
                binding.addProperty("bindingMode",
                        "CONTAINER_INPUT_OBSERVATION");
                binding.addProperty("arrayFieldObservationOnly", true);
                binding.addProperty("modelControllable", false);
                binding.addProperty("containerObservationPolicy",
                        "FIRST_MATCHING_CONTAINER_INSTANCE");
                binding.addProperty("containerObservationAuthority",
                        "FIRST_MATCHING_CONTAINER_INSTANCE_"
                                + "APPROXIMATION_V1");
                result.add(binding);
                continue;
            }
            if (requestedMapStateObservation(activation, binding)) {
                binding.addProperty("bindingMode",
                        MAP_STATE_INPUT_OBSERVATION_MODE);
                binding.addProperty("mapStateObservationOnly", true);
                binding.addProperty("modelControllable", false);
                binding.addProperty("containerObservationPolicy",
                        "FIRST_MATCHING_CONTAINER_INSTANCE");
                binding.addProperty("containerObservationAuthority",
                        FIRST_CONTAINER_OBSERVATION_AUTHORITY);
                binding.addProperty("mapStateInputCell",
                        string(binding, "cell"));
                binding.addProperty("mapStateRequestedOutputCell",
                        string(object(activation, "requestedOutput"),
                                "cell"));
                result.add(binding);
                continue;
            }
            if (!validateExactArrayFieldMaterialization(binding)) {
                if (isExecutableBindingMode(string(binding,
                        "bindingMode")) && executableCount > 0) {
                    executableCount--;
                }
                concreteFallbacks.add(concreteFallback(binding,
                        string(binding, "materializationIssue")));
                continue;
            }
            result.add(binding);
        }
        boolean ready = sourceActionCount == 0 || executableCount > 0
                || vmIntrinsicPlaceholderCount > 0
                || concreteFallbacks.size() > 0;
        return new MaterializationPlan(result, concreteFallbacks, ready, true,
                executableCount, deferredCount,
                vmIntrinsicPlaceholderCount);
    }

    private static Set<String> containerBindingSymbols(
            JsonObject activation, String member) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(activation,
                "containerElementFieldBindings")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject binding = element.getAsJsonObject();
            String symbol = string(binding, member);
            if (bool(binding, "complete", false) && !symbol.isEmpty()) {
                result.add(symbol);
            }
        }
        return result;
    }

    /**
     * Recognizes only the strict direct-field-path schema whose runtime
     * materializer is the exact container snapshot, not a getfield hook.
     */
    private static boolean exactContainerSnapshotLeafDeclaration(
            JsonObject activation, JsonObject action) {
        String symbol = string(action, "symbol");
        if (symbol.isEmpty()
                || !"HEAP_OBJECT_FIELD".equals(string(action,
                "location"))
                || !"STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1".equals(
                string(action, "fieldPathAuthority"))) {
            return false;
        }
        JsonObject selected = null;
        for (JsonElement element : array(activation,
                "containerElementFieldBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject declaration = element.getAsJsonObject();
            if (!symbol.equals(string(declaration, "baseInputSymbol"))) {
                continue;
            }
            if (selected != null) return false;
            selected = declaration;
        }
        if (selected == null
                || integer(selected, "schemaVersion", -1) != 2
                || !"ARRAY_ELEMENT_FIELD".equals(string(selected, "kind"))
                || !"CONTAINER_SNAPSHOT".equals(string(selected,
                "materializationMode"))
                || !"STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_CHAIN_V1"
                .equals(string(selected, "proofAuthority"))
                || !bool(selected, "complete", false)
                || !"EXACT_ARRAY_INDEX".equals(string(selected,
                "selectorAuthority"))
                || integer(selected, "elementIndex", -1) < 0
                || integer(selected, "elementOccurrence", -1) < 1) {
            return false;
        }
        JsonArray path = array(selected, "fieldPath");
        JsonArray actionPath = array(action, "fieldPath");
        if (path.size() < 2 || path.size() > 4
                || !path.equals(actionPath)
                || array(selected, "proofCausalEdgeIds").size()
                != 4 * path.size()) {
            return false;
        }
        Set<String> proofIds = new LinkedHashSet<>();
        for (JsonElement proof : array(selected, "proofCausalEdgeIds")) {
            if (!proof.isJsonPrimitive()
                    || proof.getAsString().trim().isEmpty()
                    || !proofIds.add(proof.getAsString())) {
                return false;
            }
        }
        String leafSignature = string(selected,
                "declaredFieldSignature");
        String[] leaf = declaredField(leafSignature);
        String[] root = declaredField(string(action, "cell"));
        String[] access = declaredField(string(action,
                "accessFieldSignature"));
        return leaf != null && root != null && access != null
                && ("boolean".equals(leaf[1])
                || "java.lang.Boolean".equals(leaf[1]))
                && leaf[2].equals(path.get(path.size() - 1).getAsString())
                && leafSignature.equals(string(action, "field"))
                && leafSignature.equals(string(action,
                "leafFieldSignature"))
                && leaf[0].equals(string(action, "leafOwnerClass"))
                && leaf[2].equals(string(action, "leafField"))
                && leaf[0].equals(string(selected,
                "declaredFieldOwnerClass"))
                && leaf[1].equals(string(selected, "declaredFieldType"))
                && root[0].equals(access[0])
                && root[1].equals(access[1])
                && root[2].equals(access[2])
                && access[0].equals(string(action, "accessOwnerClass"))
                && access[2].equals(string(action, "accessField"))
                && access[1].equals(string(action, "accessFieldType"))
                && !string(selected, "containerInputPort").isEmpty()
                && !symbol.equals(string(selected, "containerInputPort"))
                && declaredField(string(selected,
                "containerInputCell")) != null
                && string(selected, "fieldMaterializationSiteId")
                .matches("^<.+>#u[0-9]+$")
                && string(selected, "arrayLoadSiteId")
                .matches("^<.+>#u[0-9]+$");
    }

    private static boolean configuredRequestedStateCore(
            JsonObject activation) {
        return "HEAP_STATE".equals(string(object(activation,
                "requestedOutput"), "kind"))
                && bool(activation,
                "configuredOutputClosureSynthesized", false);
    }

    /**
     * A requested Map heap state is a versioned container value, not a
     * scalar reference that the VM must make controllable.  Keep the real
     * getfield hook so runtime identity and mutations remain observable, but
     * never ask the VM to symbolize the Map reference itself.
     */
    private static boolean requestedMapStateObservation(
            JsonObject activation, JsonObject binding) {
        if (!RegionCaptureGoal.from(activation).isOutputClosure()
                || !"BOUNDED_OUTPUT_RELEVANT_PATHS".equals(string(
                object(activation, RegionCaptureGoal.FIELD), "scope"))) {
            return false;
        }
        JsonObject requested = object(activation, "requestedOutput");
        String cell = string(binding, "cell");
        return "HEAP_STATE".equals(string(requested, "kind"))
                && !cell.isEmpty()
                && cell.equals(string(requested, "cell"))
                && "HEAP_OBJECT_FIELD".equals(string(binding, "location"))
                && "FIELD_ACCESS".equals(string(binding, "bindingMode"))
                && fieldPath(cell).size() == 1
                && declaresMapReference(binding);
    }

    private static boolean declaresMapReference(JsonObject binding) {
        for (String candidate : new String[]{
                string(binding, "javaType"),
                string(binding, "inputJavaType"),
                string(binding, "accessFieldType")}) {
            if (isMapReferenceType(candidate)) {
                return true;
            }
        }
        for (String candidate : new String[]{
                string(binding, "leafFieldSignature"),
                string(binding, "accessFieldSignature"),
                string(binding, "field"), string(binding, "cell")}) {
            String[] declared = declaredField(candidate);
            if (declared != null && isMapReferenceType(declared[1])) {
                return true;
            }
        }
        return false;
    }

    private static boolean isMapReferenceType(String type) {
        String candidate = safe(type).trim();
        if (candidate.startsWith("L") && candidate.endsWith(";")) {
            candidate = candidate.substring(1, candidate.length() - 1)
                    .replace('/', '.');
        }
        if (candidate.isEmpty() || candidate.startsWith("[")
                || candidate.endsWith("[]")) {
            return false;
        }
        try {
            ClassLoader loader = Thread.currentThread()
                    .getContextClassLoader();
            Class<?> declared = Class.forName(candidate, false,
                    loader == null ? ConcolicScheduler.class
                            .getClassLoader() : loader);
            return Map.class.isAssignableFrom(declared);
        } catch (Throwable ignored) {
            // Application Map subtypes may be absent from GraphChecker's
            // own class path; the standard Map declaration remains exact.
            return "java.util.Map".equals(candidate);
        }
    }

    private static JsonObject concreteFallback(JsonObject action,
                                               String reason) {
        JsonObject fallback = action.deepCopy();
        fallback.remove("deferred");
        fallback.remove("deferredResolution");
        fallback.remove("deferredResolutionAuthority");
        fallback.addProperty("bindingMode", "CONCRETE_PASSTHROUGH");
        fallback.addProperty("concreteFallback", true);
        fallback.addProperty("modelControllable", false);
        fallback.addProperty("concreteFallbackReason", firstNonBlank(reason,
                "NO_EXACT_SYMBOLIC_MATERIALIZATION"));
        fallback.addProperty("concreteFallbackAuthority",
                "STATIC_RUNTIME_UNCONFIRMED_USE_WORKLOAD_VALUE_V1");
        return fallback;
    }

    /**
     * Returns the one complete leaf declaration that is internally exact for
     * this direct getfield path.  Merely attaching a declaration to a general
     * heap action is not enough: only the planner's strict direct-chain
     * authority may refine the leaf owner derived from the root signature.
     */
    private static JsonObject exactDeclaredFieldPathLeaf(
            JsonObject action, List<String> expectedPath) {
        if (expectedPath.size() < 2
                || !"STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1".equals(
                string(action, "fieldPathAuthority"))) {
            return null;
        }
        JsonArray declarations = array(action,
                "fieldPathLeafDeclarations");
        JsonObject selected = null;
        for (JsonElement element : declarations) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject declaration = element.getAsJsonObject();
            if (!bool(declaration, "complete", false)
                    || string(declaration, "fieldSignature").isEmpty()
                    || string(declaration,
                    "declaredFieldOwnerClass").isEmpty()
                    || string(declaration, "declaredFieldType").isEmpty()) {
                continue;
            }
            JsonArray declaredPath = array(declaration, "fieldPath");
            if (declaredPath.size() != expectedPath.size()) {
                continue;
            }
            boolean matches = true;
            for (int index = 0; index < expectedPath.size(); index++) {
                JsonElement segment = declaredPath.get(index);
                if (!segment.isJsonPrimitive()
                        || !expectedPath.get(index).equals(
                        segment.getAsString())) {
                    matches = false;
                    break;
                }
            }
            if (matches) {
                if (selected != null) {
                    return null;
                }
                selected = declaration;
            }
        }
        if (selected == null) {
            return null;
        }
        String signature = string(selected, "fieldSignature");
        String[] leaf = declaredField(signature);
        return leaf != null
                && leaf[0].equals(string(selected,
                "declaredFieldOwnerClass"))
                && leaf[1].equals(string(selected, "declaredFieldType"))
                && leaf[2].equals(expectedPath.get(
                expectedPath.size() - 1))
                ? selected : null;
    }

    private static String declaredFieldName(String signature) {
        String[] field = declaredField(signature);
        return field == null ? "" : field[2];
    }

    private static void dischargeDeferredResolution(JsonObject binding,
                                                     String authority) {
        String requestAuthority = string(binding,
                "deferredResolutionAuthority");
        boolean requested = bool(binding, "deferredResolution", false)
                || bool(binding, "deferred", false)
                || !requestAuthority.isEmpty();
        binding.remove("deferredResolution");
        binding.remove("deferredResolutionAuthority");
        binding.remove("deferred");
        if (requested) {
            binding.addProperty("deferredResolutionDischarged", true);
            binding.addProperty("deferredResolutionDischargeAuthority",
                    authority);
            if (!requestAuthority.isEmpty()) {
                binding.addProperty("deferredResolutionRequestAuthority",
                        requestAuthority);
            }
        }
    }

    private static boolean verifiedVmIntrinsicPlaceholder(
            JsonObject action, String location, String cell) {
        return "ENVIRONMENT_MODEL".equals(location)
                && "ENVIRONMENT".equals(string(action, "sourceKind"))
                && SymbolicEnvironment.isCurrentTimeMillisReturn(safe(cell));
    }

    /**
     * An unobserved planner candidate is normally concrete passthrough.  A
     * deferred call-return/local candidate is different: its runtime row is
     * deliberately incomplete until the scheduler consults the authoritative
     * static DefinitionIndex.  Give that exact resolution a chance before
     * applying the concrete fallback; the location-specific branches below
     * still fall back when no usable definition exists.
     */
    private static boolean authoritativeDefinitionResolutionRequested(
            JsonObject action) {
        String location = string(action, "location");
        if (!"CALL_RETURN".equals(location)
                && !"REGION_LIVE_IN".equals(location)) {
            return false;
        }
        return bool(action, "deferredResolution", false)
                || bool(action, "deferred", false)
                || !string(action, "deferredResolutionAuthority").isEmpty();
    }

    /**
     * A runtime-proven consumed array field can be rooted in a call-return
     * local only after the authoritative static DefinitionIndex identifies
     * that local's one exact return assignment.  The leaf getfield event does
     * not distinguish two candidate return definitions, so splitting them
     * would turn ambiguity into two false claims of unique root identity.
     */
    private static boolean pendingArrayFieldCallReturnRoot(
            JsonObject action) {
        if (!"CALL_RETURN".equals(string(action, "location"))
                || !"CALL_RETURN_DEFINITION".equals(string(action,
                "consumedFieldPendingRootKind"))
                || !"LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                .concat("SCHEDULER_DEFINITION_INDEX_V1").equals(
                        string(action, "consumedFieldRootAuthority"))) {
            return false;
        }
        return ArrayFieldContract.from(action).fieldBackedArray;
    }

    private static boolean validFieldPaths(JsonObject action) {
        JsonArray paths = array(action, "fieldPaths");
        if (paths.size() == 0) {
            return false;
        }
        for (JsonElement pathElement : paths) {
            if (!pathElement.isJsonArray()
                    || pathElement.getAsJsonArray().size() == 0) {
                return false;
            }
            for (JsonElement segment : pathElement.getAsJsonArray()) {
                if (!segment.isJsonPrimitive()
                        || safe(segment.getAsString()).trim().isEmpty()) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean retainOrVerifyDerived(JsonObject binding,
                                                 String field,
                                                 String derived) {
        return retainOrVerifyDerived(binding, field,
                JSONL_GSON.toJsonTree(safe(derived)));
    }

    /** Preserve planner authority; a scheduler-derived value may only agree. */
    private static boolean retainOrVerifyDerived(JsonObject binding,
                                                 String field,
                                                 JsonElement derived) {
        JsonElement existing = binding.get(field);
        if (existing == null || existing.isJsonNull()) {
            binding.add(field, derived.deepCopy());
            return true;
        }
        return existing.equals(derived);
    }

    private static boolean isExecutableBindingMode(String mode) {
        return "ROOT_ENTRY".equals(mode)
                || "LOCAL_DEFINITION".equals(mode)
                || "FIELD_ACCESS".equals(mode)
                || MAP_STATE_INPUT_OBSERVATION_MODE.equals(mode);
    }

    /**
     * Scheduler-side defense for array-valued fields.  The planner's exact
     * consumed-getfield evidence is data, not a hint: definition refinement
     * may preserve it but cannot synthesize a missing field-read site or
     * silently replace its root authority.
     */
    private static boolean validateExactArrayFieldMaterialization(
            JsonObject binding) {
        ArrayFieldContract contract = ArrayFieldContract.from(binding);
        if (!contract.fieldBackedArray) {
            return true;
        }
        String issue = contract.issue;
        String consumedMethod = string(binding, "consumedFieldMethod");
        int consumedUnit = integer(binding, "consumedFieldUnitIndex", -1);
        String consumedSite = string(binding, "consumedFieldSiteId");
        if (issue.isEmpty() && !bool(binding,
                "consumedFieldBindingComplete", false)) {
            issue = "PLANNER_CONSUMED_FIELD_BINDING_INCOMPLETE";
        }
        if (issue.isEmpty() && (consumedMethod.isEmpty()
                || consumedUnit < 0
                || !consumedSite.equals(consumedMethod + "#u"
                + consumedUnit))) {
            issue = "EXACT_CONSUMED_FIELD_METHOD_UNIT_SITE_MISSING";
        }
        if (issue.isEmpty() && !CONSUMED_FIELD_SITE_AUTHORITY.equals(
                string(binding, "consumedFieldSiteAuthority"))) {
            issue = "EXACT_CONSUMED_FIELD_SITE_AUTHORITY_MISSING";
        }
        if (issue.isEmpty()
                && (integer(binding, "consumedFieldOccurrence", -1) != 1
                || !"UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1".equals(
                string(binding,
                        "consumedFieldOccurrenceAuthority")))) {
            issue = "EXACT_CONSUMED_FIELD_OCCURRENCE_INVALID";
        }
        if (issue.isEmpty()) {
            issue = exactArrayRootIssue(binding, contract.path);
        }
        if (!issue.isEmpty()) {
            binding.addProperty("arrayFieldMaterializationComplete", false);
            binding.addProperty("materializationIssue", issue);
            return false;
        }
        binding.addProperty("arrayFieldMaterializationComplete", true);
        binding.addProperty("arrayFieldMaterializationAuthority",
                "PLANNER_EXACT_CONSUMED_FIELD_EVIDENCE_PRESERVED_V1");
        return true;
    }

    private static void finalizePendingLocalArrayRoot(
            JsonObject binding, boolean authoritativeDefinitions) {
        if (!"LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                .concat("SCHEDULER_DEFINITION_INDEX_V1").equals(
                        string(binding, "consumedFieldRootAuthority"))
                || !bool(binding, "consumedFieldSiteBindingComplete",
                false)
                || !authoritativeDefinitions
                || !"STATIC_DATAFLOW_DEF_SITE".equals(string(binding,
                "definitionAuthority"))) {
            return;
        }
        JsonArray sites = array(binding, "definitionSites");
        String method = string(binding, "method");
        String local = string(binding, "local");
        if (sites.size() != 1 || !sites.get(0).isJsonObject()
                || method.isEmpty() || local.isEmpty()) {
            return;
        }
        JsonObject site = sites.get(0).getAsJsonObject();
        int unit = integer(site, "unitIndex", -1);
        if (unit < 0 || !method.equals(string(site, "method"))
                || !local.equals(string(site, "local"))) {
            return;
        }
        String kind = string(binding, "consumedFieldPendingRootKind");
        if ("LOCAL_DEFINITION".equals(kind)) {
            if (!method.equals(string(binding,
                    "consumedFieldPendingRootMethod"))
                    || !local.equals(string(binding,
                    "consumedFieldPendingRootLocal"))) {
                return;
            }
        } else if (!"CALL_RETURN_DEFINITION".equals(kind)
                || !"CALL_RETURN_DEFINITION".equals(string(binding,
                "sourceBindingMode"))) {
            return;
        }
        binding.addProperty("consumedFieldRootAuthority",
                LOCAL_FIELD_ROOT_AUTHORITY);
        binding.addProperty("consumedFieldBindingComplete", true);
        binding.remove("consumedFieldBindingIssue");
        binding.addProperty("consumedFieldRootResolutionAuthority",
                "AUTHORITATIVE_UNIQUE_STATIC_DEFINITION_SITE_V1");
    }

    private static String exactArrayRootIssue(JsonObject binding,
                                              JsonArray path) {
        String location = string(binding, "location");
        String mode = string(binding, "bindingMode");
        String authority = string(binding, "consumedFieldRootAuthority");
        if ("ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)) {
            return integer(binding, "index", -1) >= 0
                    && ARGUMENT_FIELD_ROOT_AUTHORITY.equals(authority)
                    ? "" : "ARGUMENT_ARRAY_ROOT_AUTHORITY_INVALID";
        }
        if ("RECEIVER_FIELD".equals(location)) {
            return RECEIVER_FIELD_ROOT_AUTHORITY.equals(authority)
                    ? "" : "RECEIVER_ARRAY_ROOT_AUTHORITY_INVALID";
        }
        if ("LOCAL_DEFINITION".equals(mode)) {
            String method = string(binding, "method");
            String local = string(binding, "local");
            JsonArray definitions = array(binding, "definitionSites");
            if (!LOCAL_FIELD_ROOT_AUTHORITY.equals(authority)
                    || method.isEmpty() || local.isEmpty()
                    || definitions.size() != 1
                    || !definitions.get(0).isJsonObject()) {
                return "LOCAL_ARRAY_ROOT_DEFINITION_AUTHORITY_INVALID";
            }
            JsonObject definition = definitions.get(0).getAsJsonObject();
            int unit = integer(definition, "unitIndex", -1);
            return unit >= 0
                    && method.equals(string(definition, "method"))
                    && local.equals(string(definition, "local"))
                    && (string(definition, "siteId").isEmpty()
                    || string(definition, "siteId").equals(method + "#u"
                    + unit))
                    ? "" : "LOCAL_ARRAY_ROOT_DEFINITION_SITE_MISMATCH";
        }
        if (RECEIVER_FIELD_ROOT_AUTHORITY.equals(authority)) {
            return "";
        }
        return DIRECT_FIELD_ROOT_AUTHORITY.equals(authority)
                && path.size() == 1 ? ""
                : "DIRECT_ARRAY_ROOT_REQUIRES_ONE_EXACT_LEAF";
    }

    private static final class ArrayFieldContract {
        private final boolean fieldBackedArray;
        private final JsonArray path;
        private final String issue;

        private ArrayFieldContract(boolean fieldBackedArray,
                                   JsonArray path, String issue) {
            this.fieldBackedArray = fieldBackedArray;
            this.path = path;
            this.issue = safe(issue);
        }

        private static ArrayFieldContract from(JsonObject binding) {
            String location = string(binding, "location");
            String mode = string(binding, "bindingMode");
            boolean fieldShape = "ARGUMENT_FIELD".equals(location)
                    || "ARGUMENT_FIELD_PATH".equals(location)
                    || "RECEIVER_FIELD".equals(location)
                    || "HEAP_OBJECT_FIELD".equals(location)
                    || "FIELD".equals(location)
                    || "FIELD_ACCESS".equals(mode);

            Set<String> signatures = new LinkedHashSet<>();
            for (String field : new String[]{"leafFieldSignature",
                    "accessFieldSignature", "field", "cell"}) {
                signatures.add(string(binding, field));
            }
            JsonArray declarations = array(binding,
                    "fieldPathLeafDeclarations");
            for (JsonElement element : declarations) {
                if (element.isJsonObject()) {
                    signatures.add(string(element.getAsJsonObject(),
                            "fieldSignature"));
                }
            }
            signatures.remove("");
            Set<String> arrayDeclarations = new LinkedHashSet<>();
            String leafName = "";
            String leafType = "";
            for (String signature : signatures) {
                String[] field = declaredField(signature);
                if (field != null && isArrayType(field[1])) {
                    arrayDeclarations.add("<" + field[0] + ": "
                            + field[1] + " " + field[2] + ">");
                    leafName = field[2];
                    leafType = field[1];
                }
            }
            String javaType = firstNonBlank(string(binding, "javaType"),
                    string(binding, "inputJavaType"));
            boolean array = isArrayType(javaType)
                    || !arrayDeclarations.isEmpty();
            if ("CALL_RETURN".equals(location)
                    && "CALL_RETURN_DEFINITION".equals(string(binding,
                    "consumedFieldPendingRootKind"))
                    && (binding.has("fieldPath")
                    || binding.has("fieldPaths")
                    || declarations.size() > 0)) {
                fieldShape = true;
            }
            if ("LOCAL_DEFINITION".equals(mode)
                    && !arrayDeclarations.isEmpty()
                    && (binding.has("fieldPath")
                    || binding.has("fieldPaths")
                    || declarations.size() > 0)) {
                fieldShape = true;
            }
            boolean backed = fieldShape && array;
            if (!backed) {
                return new ArrayFieldContract(false, new JsonArray(), "");
            }

            JsonArray path = exactBindingFieldPath(binding);
            String issue = "";
            if (arrayDeclarations.size() != 1) {
                issue = "EXACT_ARRAY_LEAF_DECLARATION_NOT_UNIQUE";
            } else if (javaType.isEmpty()
                    || !isArrayType(javaType)
                    || !sameArrayType(javaType, leafType)) {
                issue = "ACTION_ARRAY_TYPE_CONFLICTS_WITH_LEAF_DECLARATION";
            } else if (path.size() == 0) {
                issue = "EXACT_ARRAY_FIELD_PATH_NOT_UNIQUE";
            } else if (!leafName.equals(path.get(path.size() - 1)
                    .getAsString())) {
                issue = "EXACT_ARRAY_FIELD_PATH_LEAF_MISMATCH";
            }
            return new ArrayFieldContract(true, path, issue);
        }
    }

    private static JsonArray exactBindingFieldPath(JsonObject binding) {
        JsonArray direct = array(binding, "fieldPath");
        if (validStringPath(direct)) {
            return direct.deepCopy();
        }
        JsonArray paths = array(binding, "fieldPaths");
        if (paths.size() == 1 && paths.get(0).isJsonArray()
                && validStringPath(paths.get(0).getAsJsonArray())) {
            return paths.get(0).getAsJsonArray().deepCopy();
        }
        return new JsonArray();
    }

    private static boolean validStringPath(JsonArray path) {
        if (path == null || path.size() == 0) return false;
        for (JsonElement segment : path) {
            if (!segment.isJsonPrimitive()
                    || safe(segment.getAsString()).trim().isEmpty()) {
                return false;
            }
        }
        return true;
    }

    private static boolean isArrayType(String type) {
        String value = safe(type).trim();
        return value.startsWith("[") || value.endsWith("[]");
    }

    private static boolean sameArrayType(String left, String right) {
        return safe(left).replace(" ", "").equals(
                safe(right).replace(" ", ""));
    }

    private static Set<String> stringSet(JsonObject object, String field) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(object, field)) {
            if (element.isJsonPrimitive()) {
                String value = safe(element.getAsString()).trim();
                if (!value.isEmpty()) {
                    result.add(value);
                }
            }
        }
        return result;
    }

    private static Set<String> requestedOutputSites(JsonObject activation) {
        Set<String> result = new LinkedHashSet<>();
        JsonObject slice = object(activation, "requestedOutputSlice");
        if (slice != null) {
            result.addAll(stringSet(slice, "sites"));
        }
        return result;
    }

    private static Set<String> requestedOutputMethods(
            JsonObject activation) {
        Set<String> result = new LinkedHashSet<>();
        JsonObject slice = object(activation, "requestedOutputSlice");
        if (slice != null) {
            result.addAll(stringSet(slice, "methods"));
        }
        result.addAll(stringSet(activation, "requestedOutputMethods"));
        return result;
    }

    private static MaterializationPlan materializationPlan(
            JsonObject activation) {
        return materializationPlan(activation, DefinitionIndex.fallback(),
                Collections.<String>emptySet());
    }

    private static String leafField(String cell) {
        String value = safe(cell);
        int projected = value.lastIndexOf("#field:");
        if (projected >= 0) {
            String leaf = value.substring(projected + 7);
            int end = leaf.indexOf('#');
            return (end < 0 ? leaf : leaf.substring(0, end)).trim();
        }
        String[] declared = declaredField(value);
        return declared == null ? "" : declared[2];
    }

    private static String leafOwnerClass(String cell) {
        String[] declared = declaredField(cell);
        if (declared == null) {
            return "";
        }
        return safe(cell).contains("#field:")
                ? declared[1] : declared[0];
    }

    private static String accessOwnerClass(String cell) {
        String[] declared = declaredField(cell);
        return declared == null ? "" : declared[0];
    }

    private static List<String> fieldPath(String cell) {
        List<String> result = new ArrayList<>();
        String[] declared = declaredField(cell);
        if (declared != null) {
            result.add(declared[2]);
        }
        Matcher projection = FIELD_PROJECTION.matcher(safe(cell));
        while (projection.find()) {
            String field = projection.group(1).trim();
            if (!field.isEmpty()) {
                result.add(field);
            }
        }
        return result;
    }

    /**
     * Parses only an actual Soot field signature.  Method locals and method
     * returns may also carry {@code #field:...} projections, but the method
     * name (for example {@code <init>}) is not a field-path component and its
     * declaring class is not the runtime owner of the projected value.
     */
    private static String[] declaredField(String cell) {
        String value = safe(cell);
        int projection = value.indexOf("#field:");
        String base = projection < 0 ? value
                : value.substring(0, projection);
        Matcher matcher = FIELD_DETAIL.matcher(base);
        if (!matcher.matches()) {
            return null;
        }
        return new String[]{matcher.group(1).trim(),
                matcher.group(2).trim(), matcher.group(3).trim()};
    }

    private static MergePlan buildMergePlan(Map<String, Region> regions,
                                            List<JsonObject> edges,
                                            List<JsonObject> staticGraph) {
        UnionFind aliases = new UnionFind();
        List<JsonObject> equalityRelations = new ArrayList<>();
        List<JsonObject> stateMerges = new ArrayList<>();
        for (JsonObject edge : edges) {
            if (!AutomaticRegionEdge.composable(edge)) {
                continue;
            }
            String relation = firstNonBlank(
                    string(edge, "validatedRelation"),
                    string(edge, "relation"));
            String fromRegion = string(edge, "fromRegion");
            String toRegion = string(edge, "toRegion");
            String fromCell = producerOutputCell(edge,
                    regions.get(fromRegion));
            String toCell = string(edge, "toPort");
            if (fromCell.isEmpty()) {
                // Canonical producer metadata is atomic.  Once an edge
                // declares it, a partial or mismatched proof must not fall
                // back to the raw transport endpoint.
                continue;
            }
            Endpoint from = endpoint(regions.get(fromRegion), fromRegion,
                    fromCell);
            ConsumerEndpointResolution consumer = consumerEndpoint(
                    regions.get(toRegion), toRegion, toCell, staticGraph);
            Endpoint to = consumer.endpoint;
            if ("EQUALITY".equals(relation)) {
                aliases.union(from.id, to.id);
                JsonObject equality = relation(edge, from, to,
                        "SYMBOLIC_EQUALITY");
                consumer.addProof(equality);
                equalityRelations.add(equality);
            } else if ("READ_FROM".equals(relation)) {
                JsonObject state = relation(edge, from, to,
                        "VERSIONED_HEAP_READ_FROM");
                consumer.addProof(state);
                state.addProperty("requiresOrder",
                        bool(edge, "requiresOrder", true));
                state.addProperty("requiresObjectIdentity",
                        bool(edge, "requiresObjectIdentity", true));
                state.addProperty("confirmedReadFromPairCount",
                        integer(edge, "confirmedReadFromPairCount", 0));
                stateMerges.add(state);
            }
        }

        Map<String, List<JsonObject>> stateByConsumer = new LinkedHashMap<>();
        for (JsonObject state : stateMerges) {
            add(stateByConsumer, string(state, "toEndpoint"), state);
        }
        List<JsonObject> directStateMerges = new ArrayList<>();
        List<JsonObject> alternativeWriterGroups = new ArrayList<>();
        for (Map.Entry<String, List<JsonObject>> entry
                : stateByConsumer.entrySet()) {
            List<JsonObject> alternatives = entry.getValue();
            Collections.sort(alternatives, Comparator.comparing(value ->
                    string(value, "fromEndpoint") + "\n"
                            + string(value, "edgeId")));
            if (alternatives.size() == 1) {
                directStateMerges.add(alternatives.get(0));
                continue;
            }
            String stable = RecursiveRegionWorklist.stableQueryKey(
                    regionOfEndpoint(entry.getKey()), entry.getKey(),
                    "READ_FROM", "LATEST_BEFORE_READ", "MERGE_PLAN",
                    "ALTERNATIVE_WRITERS");
            JsonObject group = new JsonObject();
            group.addProperty("groupId", "MERGED.ALT."
                    + stable.substring(0, 16));
            group.addProperty("kind", "GUARDED_VERSIONED_HEAP_READ_FROM");
            group.addProperty("downstreamEndpoint", entry.getKey());
            group.addProperty("selectionSemantics", "EXACTLY_ONE_GUARDED");
            JsonArray guarded = new JsonArray();
            for (JsonObject alternative : alternatives) {
                JsonObject copy = alternative.deepCopy();
                String guardKey = RecursiveRegionWorklist.stableQueryKey(
                        regionOfEndpoint(string(copy, "fromEndpoint")),
                        string(copy, "fromEndpoint"), "WRITER_GUARD",
                        firstNonBlank(string(copy, "transportKind"),
                                "LATEST_BEFORE_READ"),
                        stable, entry.getKey());
                copy.addProperty("guardSymbol", "writer_guard__"
                        + guardKey.substring(0, 16));
                guarded.add(copy);
            }
            group.add("alternatives", guarded);
            alternativeWriterGroups.add(group);
        }

        Map<String, List<String>> classes = new LinkedHashMap<>();
        for (JsonObject relation : equalityRelations) {
            String left = string(relation, "fromEndpoint");
            String right = string(relation, "toEndpoint");
            add(classes, aliases.find(left), left);
            add(classes, aliases.find(right), right);
        }
        List<JsonObject> equalityClasses = new ArrayList<>();
        int index = 0;
        for (List<String> members : classes.values()) {
            LinkedHashSet<String> unique = new LinkedHashSet<>(members);
            if (unique.size() < 2) {
                continue;
            }
            JsonObject value = new JsonObject();
            value.addProperty("canonicalSymbol", "MERGED.EQ." + index++);
            value.add("members", JSONL_GSON.toJsonTree(unique));
            equalityClasses.add(value);
        }

        JsonObject json = new JsonObject();
        json.addProperty("schemaVersion", 1);
        json.add("equalityClasses", JSONL_GSON.toJsonTree(equalityClasses));
        json.add("equalityRelations", JSONL_GSON.toJsonTree(equalityRelations));
        json.add("versionedStateMerges",
                JSONL_GSON.toJsonTree(directStateMerges));
        json.add("alternativeWriterGroups",
                JSONL_GSON.toJsonTree(alternativeWriterGroups));
        json.addProperty("heapMergeSemantics",
                "SINGLE_READ_FROM_OR_EXACTLY_ONE_GUARDED_ALTERNATIVE");
        return new MergePlan(json, equalityClasses, directStateMerges,
                alternativeWriterGroups);
    }

    private static String regionOfEndpoint(String endpoint) {
        String value = safe(endpoint);
        int marker = -1;
        for (String delimiter : new String[]{".in.", ".out.", "::"}) {
            int candidate = value.indexOf(delimiter);
            if (candidate > 0 && (marker < 0 || candidate < marker)) {
                marker = candidate;
            }
        }
        return marker <= 0 ? "" : endpoint.substring(0, marker);
    }

    private static JsonObject relation(JsonObject edge, Endpoint from,
                                       Endpoint to, String kind) {
        JsonObject result = new JsonObject();
        result.addProperty("edgeId", string(edge, "edgeId"));
        result.addProperty("kind", kind);
        result.addProperty("transportKind", string(edge, "kind"));
        result.addProperty("fromRegion", string(edge, "fromRegion"));
        result.addProperty("toRegion", string(edge, "toRegion"));
        result.addProperty("fromEndpoint", from.id);
        result.addProperty("fromCell", from.cell);
        result.addProperty("toEndpoint", to.id);
        result.addProperty("toCell", to.cell);
        result.addProperty("mappingKind", string(edge, "mappingKind"));
        result.addProperty("mappingAuthority",
                string(edge, "mappingAuthority"));
        result.addProperty("runtimeStatus", string(edge, "status"));
        result.addProperty("endpointOrderAuthority",
                string(edge, "endpointOrderAuthority"));
        result.addProperty("endpointCorrelationAuthority",
                string(edge, "endpointCorrelationAuthority"));
        result.addProperty("discoveredExecutionId",
                string(edge, "discoveredExecutionId"));
        result.add("discoveredExecutionIds", array(edge,
                "discoveredExecutionIds").deepCopy());
        result.add("runtimeBindings", runtimeBindings(edge).deepCopy());
        return result;
    }

    private static Endpoint endpoint(Region region, String regionId,
                                     String cell) {
        if (region != null) {
            String port = region.portByCell.get(cell);
            if (port != null) {
                return new Endpoint(port, cell);
            }
        }
        return new Endpoint(regionId + "::" + cell, cell);
    }

    /**
     * Runtime protocol validation names the concrete callback local, while a
     * static region may expose the declared field returned by that accessor
     * as its symbolic input.  Canonicalize that consumer only with one exact,
     * fully authoritative accessor-return value-flow proof.  A direct input
     * match remains preferred; missing or ambiguous proof retains the raw
     * synthetic endpoint so later context selection fails closed.
     */
    private static ConsumerEndpointResolution consumerEndpoint(
            Region region, String regionId, String rawCell,
            List<JsonObject> staticGraph) {
        if (region == null) {
            return ConsumerEndpointResolution.raw(regionId, rawCell);
        }
        String direct = region.uniqueInputPort(rawCell);
        if (!direct.isEmpty()) {
            return ConsumerEndpointResolution.direct(direct, rawCell);
        }
        // A duplicated exact input is already ambiguous.  Do not escape that
        // ambiguity through a different static projection.
        if (region.hasInputCell(rawCell)) {
            return ConsumerEndpointResolution.raw(regionId, rawCell);
        }
        List<ConsumerInputProof> matches = new ArrayList<>();
        for (JsonObject proof : staticGraph == null
                ? Collections.<JsonObject>emptyList() : staticGraph) {
            String inputCell = string(proof, "fromCell");
            String inputPort = region.uniqueInputPort(inputCell);
            if (inputPort.isEmpty()
                    || !completeAccessorInputProof(proof, rawCell,
                    inputCell)) {
                continue;
            }
            matches.add(new ConsumerInputProof(inputPort, inputCell,
                    string(proof, "id")));
        }
        if (matches.size() != 1) {
            return ConsumerEndpointResolution.raw(regionId, rawCell);
        }
        ConsumerInputProof proof = matches.get(0);
        return ConsumerEndpointResolution.canonical(proof.inputPort,
                proof.inputCell, rawCell, proof.edgeId);
    }

    private static boolean completeAccessorInputProof(JsonObject proof,
                                                       String rawCell,
                                                       String inputCell) {
        if (proof == null || string(proof, "id").isEmpty()
                || !"accessor_field_return".equals(string(proof, "kind"))
                || !"value_flow".equals(string(proof, "relation"))
                || !"backward_provenance".equals(string(proof,
                "direction"))
                || !proof.has("mappingOnly")
                || bool(proof, "mappingOnly", true)
                || !bool(proof, "semanticAssertionsAllowed", false)
                || !bool(proof, "eligibleForAutomaticDerivation", false)
                || !bool(proof, "eligibleForAutomaticSmt", false)
                || !safe(rawCell).equals(string(proof, "toCell"))
                || !safe(inputCell).equals(string(proof, "fromCell"))) {
            return false;
        }
        String declaredSignature = string(proof,
                "declaredFieldSignature");
        String[] declared = declaredField(declaredSignature);
        String invoke = string(proof, "invoke");
        String implementation = string(proof,
                "accessorImplementationMethod");
        return declared != null
                && declaredSignature.equals(inputCell)
                && declared[0].equals(string(proof, "declaredFieldOwner"))
                && declared[1].equals(string(proof, "declaredFieldType"))
                && declared[2].equals(string(proof, "declaredFieldName"))
                && "SOOT_RESOLVED_DECLARATION_HIERARCHY".equals(
                string(proof, "declaredFieldAuthority"))
                && !invoke.isEmpty() && !implementation.isEmpty()
                && declared[1].equals(methodReturnType(invoke))
                && declared[1].equals(methodReturnType(implementation))
                && "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY".equals(
                string(proof, "accessorImplementationAuthority"));
    }

    private static String methodReturnType(String signature) {
        String value = safe(signature);
        int colon = value.indexOf(':');
        int open = value.indexOf('(', colon + 1);
        int separator = open < 0 ? -1 : value.lastIndexOf(' ', open);
        if (colon < 0 || open < 0 || separator <= colon) {
            return "";
        }
        return value.substring(colon + 1, separator).trim();
    }

    private static String producerOutputCell(JsonObject edge,
                                             Region region) {
        if (!hasCanonicalOutputMetadata(edge)) {
            return string(edge, "fromPort");
        }
        String authority = string(edge, "aliasProofAuthority");
        boolean acceptedAuthority = ("STATIC_EXACT_PROJECTED_RETURN_VALUE_"
                + "FLOW_AND_DECLARED_RETURN_FIELD").equals(authority)
                || ("CONFIGURED_RPC_PRODUCER_RETURN_AND_STATIC_EXACT_"
                + "PUBLISH_VALUE_FLOW_V1").equals(authority);
        String outputPort = string(edge, "fromOutputPort");
        String outputCell = string(edge, "fromOutputCell");
        if (!bool(edge, "aliasProofComplete", false)
                || !acceptedAuthority || outputPort.isEmpty()
                || outputCell.isEmpty()
                || array(edge, "aliasProofEdgeIds").size() == 0
                || region == null
                || !outputPort.equals(region.portByCell.get(outputCell))) {
            return "";
        }
        return outputCell;
    }

    private static boolean hasCanonicalOutputMetadata(JsonObject edge) {
        return edge != null && (edge.has("fromOutputPort")
                || edge.has("fromOutputCell")
                || edge.has("aliasProofEdgeIds")
                || edge.has("aliasProofAuthority")
                || edge.has("aliasProofComplete"));
    }

    private static JsonObject branchQuery(Candidate candidate,
                                          JsonObject summary,
                                          MergePlan mergePlan) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 1);
        query.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        query.addProperty("activationId", candidate.activationId);
        query.addProperty("regionId", candidate.region.regionId);
        query.addProperty("regionInstanceId",
                string(candidate.activation, "regionInstanceId"));
        try {
            BranchReplayPlan replay = BranchReplayPlan.fromSummary(summary,
                    candidate.target.siteId,
                    candidate.target.selectedOccurrence);
            BranchReplayContract contract = replay.replayContract();
            if (contract.source().sourceTakenOutcome()
                    != candidate.target.observedOutcome
                    || contract.requiredTakenOutcome()
                    != candidate.target.desiredOutcome) {
                throw new IllegalArgumentException(
                        "captured branch polarity differs from selection");
            }
            query.add("replayContract", contract.toJson());
            query.add("solverPathContext",
                    replay.solverPathContext().toJson());
            query.addProperty("readyForSolver", true);
        } catch (IllegalArgumentException incompleteWitness) {
            query.addProperty("readyForSolver", false);
            query.addProperty("blocker", incompleteWitness.getMessage());
        }
        query.add("engineArrayInputBindings", array(summary,
                "engineArrayInputBindings").deepCopy());
        query.add("symbolicContext",
                mergePlan.contextFor(candidate.region.regionId,
                        string(candidate.activation, "regionInstanceId")));
        return query;
    }

    private static String workloadKind(Candidate candidate,
                                       List<JsonObject> edges) {
        for (JsonObject edge : edges) {
            if (!candidate.region.regionId.equals(string(edge, "toRegion"))) {
                continue;
            }
            for (JsonElement item : runtimeBindings(edge)) {
                if (!item.isJsonObject()) continue;
                JsonObject evidence = item.getAsJsonObject();
                if (bool(evidence, "differentThread", false)
                        || !string(evidence, "fromProcess").equals(
                        string(evidence, "toProcess"))) {
                    return "LOCAL_MULTI_CONTEXT_UNIT_TEST";
                }
            }
        }
        return "LOCAL_UNIT_TEST";
    }

    private static JsonArray runtimeBindings(JsonObject edge) {
        return array(edge, "validatedBindings");
    }

    /**
     * Selects target-PC provenance only from the exact runtime activation.
     * Activation ids restart in every trace (for example every trace has an
     * ACT.0), so an id-only index can silently join a path condition from a
     * different JVM execution to the current region instance.
     */
    private static JsonObject exactTargetSummary(
            Candidate candidate, List<JsonObject> summaries) {
        String expectedInstance = string(candidate.activation,
                "regionInstanceId");
        if (expectedInstance.isEmpty()) return null;
        JsonObject selected = null;
        for (JsonObject summary : summaries) {
            if (!candidate.activationId.equals(string(summary,
                    "activationId"))
                    || !candidate.region.regionId.equals(string(summary,
                    "regionId"))
                    || !expectedInstance.equals(string(summary,
                    "regionInstanceId"))
                    || !RegionCaptureGoal.from(summary).isTargetBranch()
                    || !bool(summary, "valid", false)
                    || bool(summary, "branchOverrideUsed", true)
                    || string(summary, "summaryId").isEmpty()) {
                continue;
            }
            JsonObject admission = object(summary, "executionAdmission");
            if (!bool(admission, "valid", false)
                    || bool(admission, "branchOverrideAccepted", true)) {
                continue;
            }
            if (bool(admission, "required", true)
                    || !"OBSERVED_UNFORCED_TARGET_SEED_PATH_ONLY".equals(
                    string(admission, "authority"))) {
                continue;
            }
            if (selected == null) {
                selected = summary;
            }
        }
        return selected;
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        if (path == null) {
            return Collections.emptyList();
        }
        requireFile(path, "JSONL input");
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonElement parsed = JsonParser.parseString(line);
                if (parsed.isJsonObject()) {
                    result.add(parsed.getAsJsonObject());
                }
            }
        }
        return result;
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder builder = new StringBuilder();
        for (JsonObject row : rows) {
            builder.append(JSONL_GSON.toJson(row)).append('\n');
        }
        writeAtomic(path, builder.toString());
    }

    private static void writeJson(Path path, JsonObject value)
            throws IOException {
        writeAtomic(path, GSON.toJson(value) + System.lineSeparator());
    }

    private static void writeAtomic(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) {
            Files.createDirectories(parent);
        }
        Path temporary = Files.createTempFile(parent, path.getFileName().toString(),
                ".tmp");
        Files.write(temporary, value.getBytes(StandardCharsets.UTF_8));
        try {
            Files.move(temporary, path, StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException ignored) {
            Files.move(temporary, path, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static void requireFile(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static JsonArray array(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonObject object(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull() ? "" : value.getAsString();
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

    private static long longInteger(JsonObject object, String field,
                                    long fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long firstLong(JsonObject object, String... fields) {
        for (String field : fields) {
            if (object != null && object.has(field)) {
                return longInteger(object, field, -1L);
            }
        }
        return -1L;
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

    private static JsonElement firstElement(JsonObject object,
                                            String... names) {
        if (object == null) return null;
        for (String name : names) {
            JsonElement value = object.get(name);
            if (value != null && !value.isJsonNull()) return value;
        }
        return null;
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    private static <T> void add(Map<String, List<T>> map, String key, T value) {
        List<T> values = map.get(key);
        if (values == null) {
            values = new ArrayList<>();
            map.put(key, values);
        }
        values.add(value);
    }

    /** Exact Jimple definitions for live-in locals, recovered from the static graph. */
    private static final class DefinitionIndex {
        private final boolean authoritative;
        private final Map<String, List<JsonObject>> byCell =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> byCallReturn =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> callsByMethod =
                new LinkedHashMap<>();

        private DefinitionIndex(boolean authoritative) {
            this.authoritative = authoritative;
        }

        private static DefinitionIndex fallback() {
            return new DefinitionIndex(false);
        }

        private static DefinitionIndex from(List<JsonObject> edges) {
            DefinitionIndex result = new DefinitionIndex(true);
            Set<String> seen = new LinkedHashSet<>();
            Set<String> seenCallReturns = new LinkedHashSet<>();
            for (JsonObject edge : edges) {
                String caller = string(edge, "method");
                String callee = string(edge, "invoke");
                if (!caller.isEmpty() && !callee.isEmpty()) {
                    result.callsByMethod.computeIfAbsent(caller,
                            ignored -> new LinkedHashSet<>()).add(callee);
                }
                String cell = string(edge, "toCell");
                Matcher localCell = LOCAL_CELL.matcher(cell);
                if (!localCell.matches()) {
                    continue;
                }
                String method = string(edge, "method");
                int unitIndex = integer(edge, "unitIndex", -1);
                String unit = string(edge, "unit");
                if (!localCell.group(1).equals(method) || unitIndex < 0
                        || !definesLocal(unit, localCell.group(2))) {
                    continue;
                }
                String key = cell + "\n" + method + "#u" + unitIndex;
                JsonObject site = new JsonObject();
                site.addProperty("method", method);
                site.addProperty("local", localCell.group(2));
                site.addProperty("unitIndex", unitIndex);
                site.addProperty("siteId", method + "#u" + unitIndex);
                site.addProperty("unit", unit);
                site.addProperty("authority", "STATIC_DATAFLOW_DEF_SITE");
                if (seen.add(key)) {
                    result.byCell.computeIfAbsent(cell,
                            ignored -> new ArrayList<>()).add(site);
                }

                String source = string(edge, "fromCell");
                if (source.contains(">.return")) {
                    String returnKey = source + "\n" + method + "#u"
                            + unitIndex + "\n" + localCell.group(2);
                    if (seenCallReturns.add(returnKey)) {
                        result.byCallReturn.computeIfAbsent(source,
                                ignored -> new ArrayList<>())
                                .add(site.deepCopy());
                    }
                }
            }
            return result;
        }

        private static boolean definesLocal(String unit, String local) {
            if (unit == null || local == null) {
                return false;
            }
            int assignment = unit.indexOf('=');
            if (assignment < 0) {
                return false;
            }
            return local.equals(unit.substring(0, assignment).trim());
        }

        private JsonArray sites(String cell) {
            JsonArray result = new JsonArray();
            List<JsonObject> sites = byCell.get(cell);
            if (sites != null) {
                for (JsonObject site : sites) {
                    result.add(site.deepCopy());
                }
            }
            return result;
        }

        private JsonArray returnSites(String callReturnCell,
                                      Set<String> allowedMethods,
                                      Set<String> allowedSites) {
            JsonArray result = new JsonArray();
            List<JsonObject> sites = byCallReturn.get(callReturnCell);
            if (sites == null) {
                return result;
            }
            for (JsonObject site : sites) {
                String method = string(site, "method");
                String siteId = string(site, "siteId");
                if (allowedMethods != null && !allowedMethods.isEmpty()
                        && !allowedMethods.contains(method)) {
                    continue;
                }
                if (allowedSites != null && !allowedSites.isEmpty()
                        && !allowedSites.contains(siteId)) {
                    continue;
                }
                result.add(site.deepCopy());
            }
            return result;
        }

    }

    private static final class CaptureEvidence {
        private final Map<String, Set<String>> observedMethodsByInstance;

        private CaptureEvidence(
                Map<String, Set<String>> observedMethodsByInstance) {
            this.observedMethodsByInstance = observedMethodsByInstance;
        }

        private static CaptureEvidence from(List<JsonObject> rows) {
            Map<String, Set<String>> observed = new LinkedHashMap<>();
            for (JsonObject row : rows) {
                String instance = string(row, "regionInstanceId");
                if (instance.isEmpty()) {
                    continue;
                }
                Set<String> methods = observed.get(instance);
                if (methods == null) {
                    methods = new LinkedHashSet<>();
                    observed.put(instance, methods);
                }
                methods.addAll(stringSet(row, "observedMethods"));
            }
            return new CaptureEvidence(observed);
        }

        private Set<String> observedMethods(JsonObject activation) {
            String instance = string(activation, "regionInstanceId");
            Set<String> methods = observedMethodsByInstance.get(instance);
            return methods == null
                    ? Collections.<String>emptySet()
                    : methods;
        }
    }

    private static final class Region {
        private final String regionId;
        private final Set<String> methods = new LinkedHashSet<>();
        private final Map<String, String> portByCell = new LinkedHashMap<>();
        private final Map<String, List<String>> inputPortsByCell =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> outputByCell =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> outputSliceByPort =
                new LinkedHashMap<>();

        private Region(JsonObject row) {
            this.regionId = string(row, "regionId");
            this.methods.addAll(stringSet(row, "methods"));
            collectInputs(array(row, "symbolicInputs"));
            collectOutputs(array(row, "outputs"));
            for (JsonElement element : array(row, "outputSlices")) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject slice = element.getAsJsonObject();
                String outputPort = string(slice, "outputPort");
                if (!outputPort.isEmpty()) {
                    outputSliceByPort.put(outputPort, slice.deepCopy());
                }
            }
        }

        private void collectInputs(JsonArray inputs) {
            collectPorts(inputs);
            for (JsonElement element : inputs) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject input = element.getAsJsonObject();
                String id = firstNonBlank(string(input, "portId"),
                        string(input, "symbol"));
                String cell = string(input, "cell");
                if (!id.isEmpty() && !cell.isEmpty()) {
                    add(inputPortsByCell, cell, id);
                }
            }
        }

        private boolean hasInputCell(String cell) {
            return inputPortsByCell.containsKey(safe(cell));
        }

        private String uniqueInputPort(String cell) {
            List<String> ports = inputPortsByCell.get(safe(cell));
            return ports != null && ports.size() == 1 ? ports.get(0) : "";
        }

        private void collectOutputs(JsonArray outputs) {
            collectPorts(outputs);
            for (JsonElement element : outputs) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject output = element.getAsJsonObject();
                String cell = string(output, "cell");
                if (!cell.isEmpty()) {
                    outputByCell.put(cell, output.deepCopy());
                }
            }
        }

        private void collectPorts(JsonArray ports) {
            for (JsonElement element : ports) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject port = element.getAsJsonObject();
                String id = firstNonBlank(string(port, "portId"),
                        string(port, "symbol"));
                String cell = string(port, "cell");
                if (!id.isEmpty() && !cell.isEmpty()) {
                    portByCell.put(cell, id);
                }
            }
        }
    }

    private static final class Endpoint {
        private final String id;
        private final String cell;

        private Endpoint(String id, String cell) {
            this.id = safe(id);
            this.cell = safe(cell);
        }
    }

    private static final class ConsumerInputProof {
        private final String inputPort;
        private final String inputCell;
        private final String edgeId;

        private ConsumerInputProof(String inputPort, String inputCell,
                                   String edgeId) {
            this.inputPort = safe(inputPort);
            this.inputCell = safe(inputCell);
            this.edgeId = safe(edgeId);
        }
    }

    private static final class ConsumerEndpointResolution {
        private final Endpoint endpoint;
        private final String rawCell;
        private final String proofEdgeId;
        private final String proofAuthority;

        private ConsumerEndpointResolution(Endpoint endpoint,
                String rawCell, String proofEdgeId, String proofAuthority) {
            this.endpoint = endpoint;
            this.rawCell = safe(rawCell);
            this.proofEdgeId = safe(proofEdgeId);
            this.proofAuthority = safe(proofAuthority);
        }

        private static ConsumerEndpointResolution direct(String port,
                                                          String cell) {
            return new ConsumerEndpointResolution(new Endpoint(port, cell),
                    cell, "", "");
        }

        private static ConsumerEndpointResolution raw(String regionId,
                                                       String cell) {
            return new ConsumerEndpointResolution(new Endpoint(
                    safe(regionId) + "::" + safe(cell), cell), cell, "", "");
        }

        private static ConsumerEndpointResolution canonical(
                String port, String cell, String rawCell, String proofEdgeId) {
            return new ConsumerEndpointResolution(new Endpoint(port, cell),
                    rawCell, proofEdgeId,
                    ACCESSOR_INPUT_CANONICALIZATION_AUTHORITY);
        }

        private void addProof(JsonObject relation) {
            if (relation == null || proofEdgeId.isEmpty()) {
                return;
            }
            relation.addProperty("rawToCell", rawCell);
            relation.addProperty("toCanonicalizationProofEdgeId",
                    proofEdgeId);
            relation.addProperty("toCanonicalizationAuthority",
                    proofAuthority);
        }
    }

    private static final class MaterializationPlan {
        private final JsonArray actions;
        private final JsonArray concreteFallbacks;
        private final boolean ready;
        private final boolean complete;
        private final int executableCount;
        private final int deferredCount;
        private final int vmIntrinsicPlaceholderCount;

        private MaterializationPlan(JsonArray actions,
                                    JsonArray concreteFallbacks, boolean ready,
                                    boolean complete, int executableCount,
                                    int deferredCount,
                                    int vmIntrinsicPlaceholderCount) {
            this.actions = actions;
            this.concreteFallbacks = concreteFallbacks;
            this.ready = ready;
            this.complete = complete;
            this.executableCount = executableCount;
            this.deferredCount = deferredCount;
            this.vmIntrinsicPlaceholderCount = vmIntrinsicPlaceholderCount;
        }

        private MaterializationPlan notReady() {
            return new MaterializationPlan(actions, concreteFallbacks, false,
                    complete,
                    executableCount, deferredCount,
                    vmIntrinsicPlaceholderCount);
        }
    }

    private static final class TargetBranch {
        private final String siteId;
        private final int branchIndex;
        private final int selectedOccurrence;
        private final boolean observedOutcome;
        private final boolean desiredOutcome;
        private final String selectionMode;

        private TargetBranch(String siteId, int branchIndex,
                             int selectedOccurrence, boolean observedOutcome,
                             boolean desiredOutcome, String selectionMode) {
            this.siteId = safe(siteId);
            this.branchIndex = branchIndex;
            this.selectedOccurrence = Math.max(1, selectedOccurrence);
            this.observedOutcome = observedOutcome;
            this.desiredOutcome = desiredOutcome;
            this.selectionMode = safe(selectionMode);
        }

        private static TargetBranch outputCapture() {
            return new TargetBranch("", -1, 1, false, false,
                    "OUTPUT_CLOSURE_CAPTURE");
        }

        private BranchCaptureSelector captureSelector() {
            return BranchCaptureSelector.of(siteId, selectedOccurrence,
                    desiredOutcome);
        }
    }

    private static final class Candidate {
        private static final Comparator<Candidate> ORDER =
                Comparator.comparing((Candidate value) -> !value.directed)
                        .thenComparing(value -> !value.materialization.ready)
                        .thenComparingInt(value -> value.target.branchIndex)
                        .thenComparingInt(value -> integer(value.activation,
                                "invocationOrdinal", Integer.MAX_VALUE))
                        .thenComparing(value -> value.activationId);

        private final JsonObject activation;
        private final String activationId;
        private final Region region;
        private final TargetBranch target;
        private final boolean directed;
        private final boolean outputClosure;
        private final MaterializationPlan materialization;
        private final String reason;

        private Candidate(JsonObject activation, String activationId,
                          Region region, TargetBranch target,
                          boolean hasRequiredWitness,
                          MaterializationPlan materialization,
                          boolean outputClosure) {
            this.activation = activation;
            this.activationId = activationId;
            this.region = region;
            this.target = target;
            this.outputClosure = outputClosure;
            this.directed = outputClosure || !hasRequiredWitness;
            this.materialization = materialization;
            this.reason = outputClosure
                    ? "runtime-confirmed upstream region selected for output closure"
                    : directed
                    ? "runtime path reaches the branch but misses the static required outcome"
                    : "static branch is explicitly explorable";
        }
    }

    private static final class UnionFind {
        private final Map<String, String> parent = new LinkedHashMap<>();

        private String find(String value) {
            String current = parent.get(value);
            if (current == null) {
                parent.put(value, value);
                return value;
            }
            if (current.equals(value)) {
                return current;
            }
            String root = find(current);
            parent.put(value, root);
            return root;
        }

        private void union(String left, String right) {
            String leftRoot = find(left);
            String rightRoot = find(right);
            if (!leftRoot.equals(rightRoot)) {
                parent.put(rightRoot, leftRoot);
            }
        }
    }

    private static final class MergePlan {
        private final JsonObject json;
        private final List<JsonObject> equalityClasses;
        private final List<JsonObject> stateMerges;
        private final List<JsonObject> alternativeWriterGroups;

        private MergePlan(JsonObject json, List<JsonObject> equalityClasses,
                          List<JsonObject> stateMerges,
                          List<JsonObject> alternativeWriterGroups) {
            this.json = json;
            this.equalityClasses = equalityClasses;
            this.stateMerges = stateMerges;
            this.alternativeWriterGroups = alternativeWriterGroups;
        }

        /**
         * Copies runtime-confirmed protocol equalities onto the producer
         * activation that will own the imported output summary. This is a
         * summary edge, not a READ_FROM edge: serialization may change object
         * identity while preserving the complete endpoint value.
         */
        private void attachOutboundValueEqualityBindings(
                JsonObject activation) {
            if (activation == null) return;
            for (JsonElement element : array(activation,
                    "reachabilitySupportActivations")) {
                if (element.isJsonObject()) {
                    attachOutboundValueEqualityBindings(
                            element.getAsJsonObject());
                }
            }
            String region = string(activation, "regionId");
            String instance = string(activation, "regionInstanceId");
            if (region.isEmpty() || instance.isEmpty()) return;

            JsonArray bindings = new JsonArray();
            JsonElement existing = activation.get("edgeBindings");
            if (existing != null && existing.isJsonArray()) {
                for (JsonElement element : existing.getAsJsonArray()) {
                    bindings.add(element.deepCopy());
                }
            }
            JsonObject requestedOutput = object(activation,
                    "requestedOutput");
            String requestedPort = string(requestedOutput, "portId");
            String requestedCell = string(requestedOutput, "cell");

            for (JsonElement relationElement : array(json,
                    "equalityRelations")) {
                if (!relationElement.isJsonObject()) continue;
                JsonObject relation = relationElement.getAsJsonObject();
                String fromRegion = firstNonBlank(string(relation,
                        "fromRegion"), regionOfEndpoint(string(relation,
                        "fromEndpoint")));
                String toRegion = firstNonBlank(string(relation,
                        "toRegion"), regionOfEndpoint(string(relation,
                        "toEndpoint")));
                String fromPort = string(relation, "fromEndpoint");
                String toPort = string(relation, "toEndpoint");
                boolean requestedPortMismatch = !requestedPort.isEmpty()
                        && !requestedPort.equals(fromPort);
                boolean requestedCellMismatch = requestedPort.isEmpty()
                        && !requestedCell.isEmpty()
                        && !requestedCell.equals(string(relation,
                        "fromCell"));
                if (!region.equals(fromRegion) || toRegion.isEmpty()
                        || !fromPort.startsWith(fromRegion + ".out.")
                        || !toPort.startsWith(toRegion + ".in.")
                        || requestedPortMismatch || requestedCellMismatch) {
                    continue;
                }
                for (JsonElement element : array(relation,
                        "runtimeBindings")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject raw = element.getAsJsonObject();
                    String fromInstance = string(raw,
                            "fromRegionInstance");
                    String toInstance = string(raw, "toRegionInstance");
                    long writer = firstLong(raw, "fromEndpointSeq",
                            "writerEventSeq", "writeSeq");
                    long reader = firstLong(raw, "toEndpointSeq",
                            "readerEventSeq", "readSeq");
                    String orderAuthority = firstNonBlank(string(raw,
                            "endpointOrderAuthority"), string(relation,
                            "endpointOrderAuthority"));
                    String correlationAuthority = firstNonBlank(string(raw,
                            "endpointCorrelationAuthority"), string(relation,
                            "endpointCorrelationAuthority"));
                    String discoveredExecution = firstNonBlank(string(raw,
                            "discoveredExecutionId"), string(relation,
                            "discoveredExecutionId"));
                    if (!instance.equals(fromInstance)
                            || toInstance.isEmpty()
                            || writer < 0L || reader <= writer
                            || !bool(raw, "orderConfirmed", false)
                            || !AutomaticRegionEdge
                            .VALUE_EQUALITY_ORDER_AUTHORITY.equals(
                                    orderAuthority)
                            || !bool(raw, "valueEqualityObserved", false)
                            || !"RUNTIME_COMPLETE_VALUE_FINGERPRINT".equals(
                            string(raw, "valueEqualityAuthority"))
                            || string(raw, "valueFingerprint").isEmpty()) {
                        continue;
                    }
                    JsonObject normalized = new JsonObject();
                    normalized.addProperty("schemaVersion", 1);
                    normalized.addProperty("edgeId", string(relation,
                            "edgeId"));
                    normalized.addProperty("relation", "EQUALITY");
                    normalized.addProperty("relationKind", "EQUALITY");
                    normalized.addProperty("transportKind", string(
                            relation, "transportKind"));
                    normalized.addProperty("mappingKind", string(relation,
                            "mappingKind"));
                    normalized.addProperty("mappingAuthority", string(
                            relation, "mappingAuthority"));
                    normalized.addProperty("fromRegion", fromRegion);
                    normalized.addProperty("toRegion", toRegion);
                    normalized.addProperty("fromRegionInstance",
                            fromInstance);
                    normalized.addProperty("toRegionInstance", toInstance);
                    normalized.addProperty("fromOutputPort", fromPort);
                    normalized.addProperty("toInputPort", toPort);
                    normalized.addProperty("fromOutputCell", string(
                            relation, "fromCell"));
                    normalized.addProperty("toInputCell", string(relation,
                            "toCell"));
                    normalized.addProperty("writerEventSeq", writer);
                    normalized.addProperty("readerEventSeq", reader);
                    normalized.addProperty("fromEndpointSeq", writer);
                    normalized.addProperty("toEndpointSeq", reader);
                    normalized.addProperty("orderConfirmed", true);
                    normalized.addProperty("valueEqualityObserved", true);
                    normalized.addProperty("valueEqualityAuthority",
                            "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
                    normalized.addProperty("valueFingerprint", string(raw,
                            "valueFingerprint"));
                    normalized.addProperty("endpointOrderAuthority",
                            orderAuthority);
                    if (!correlationAuthority.isEmpty()) {
                        normalized.addProperty("endpointCorrelationAuthority",
                                correlationAuthority);
                    }
                    if (!discoveredExecution.isEmpty()) {
                        normalized.addProperty("discoveredExecutionId",
                                discoveredExecution);
                    }
                    JsonElement discoveredExecutions = firstElement(raw,
                            "discoveredExecutionIds");
                    if (discoveredExecutions == null) {
                        discoveredExecutions = firstElement(relation,
                                "discoveredExecutionIds");
                    }
                    if (discoveredExecutions != null) {
                        normalized.add("discoveredExecutionIds",
                                discoveredExecutions.deepCopy());
                    }
                    normalized.addProperty("selectionAuthority",
                            "RUNTIME_CONFIRMED_VALUE_EQUALITY");
                    normalized.addProperty("objectIdentityRequired", false);
                    copyIfPresent(raw, normalized, "test", "fromProcess",
                            "fromThreadId", "toProcess", "toThreadId",
                            "fromFingerprintSource", "toFingerprintSource");
                    addUniqueBinding(bindings, normalized);
                }
            }
            if (bindings.size() > 0) {
                activation.add("edgeBindings", bindings);
            }
        }

        private static void copyIfPresent(JsonObject source,
                                          JsonObject target,
                                          String... fields) {
            for (String field : fields) {
                JsonElement value = source.get(field);
                if (value != null && !value.isJsonNull()) {
                    target.add(field, value.deepCopy());
                }
            }
        }

        private static void addUniqueBinding(JsonArray bindings,
                                             JsonObject candidate) {
            String identity = bindingIdentity(candidate);
            for (int index = 0; index < bindings.size(); index++) {
                JsonElement element = bindings.get(index);
                if (element.isJsonObject()
                        && identity.equals(bindingIdentity(
                        element.getAsJsonObject()))) {
                    if (compareRuntimeEqualityWitness(candidate,
                            element.getAsJsonObject()) < 0) {
                        bindings.set(index, candidate.deepCopy());
                    }
                    return;
                }
            }
            bindings.add(candidate);
        }

        /** Chooses one stable nearest ordered pair for a semantic transfer. */
        private static int compareRuntimeEqualityWitness(JsonObject left,
                                                         JsonObject right) {
            long leftWriter = firstLong(left, "writerEventSeq", "writeSeq",
                    "fromEndpointSeq");
            long leftReader = firstLong(left, "readerEventSeq", "readSeq",
                    "toEndpointSeq");
            long rightWriter = firstLong(right, "writerEventSeq", "writeSeq",
                    "fromEndpointSeq");
            long rightReader = firstLong(right, "readerEventSeq", "readSeq",
                    "toEndpointSeq");
            int compared = Long.compare(leftReader - leftWriter,
                    rightReader - rightWriter);
            if (compared != 0) return compared;
            compared = Long.compare(rightWriter, leftWriter);
            if (compared != 0) return compared;
            compared = Long.compare(leftReader, rightReader);
            if (compared != 0) return compared;
            return JSONL_GSON.toJson(left).compareTo(
                    JSONL_GSON.toJson(right));
        }

        private static String bindingIdentity(JsonObject binding) {
            return string(binding, "edgeId") + "\n"
                    + string(binding, "relationKind") + "\n"
                    + string(binding, "fromRegionInstance") + "\n"
                    + string(binding, "toRegionInstance") + "\n"
                    + string(binding, "fromOutputPort") + "\n"
                    + string(binding, "toInputPort") + "\n"
                    + string(binding, "valueFingerprint");
        }

        private JsonObject contextFor(String regionId, String regionInstanceId) {
            JsonObject context = new JsonObject();
            JsonArray equalityBindings = new JsonArray();
            for (JsonElement element : array(json, "equalityRelations")) {
                JsonObject value = element.getAsJsonObject();
                if (!relevant(value, regionId)) {
                    continue;
                }
                JsonArray selected = selectedBindings(value, regionInstanceId,
                        false);
                if (selected.size() > 0) {
                    JsonObject copy = value.deepCopy();
                    copy.remove("runtimeBindings");
                    copy.add("selectedBindings", selected);
                    equalityBindings.add(copy);
                }
            }
            // Rebuild equality classes from the witness-bearing relations
            // selected for this concrete region instance.  Reusing the global
            // static class here could transitively assert an equality whose
            // runtime fingerprint belonged to a different invocation.
            JsonArray equality = new JsonArray();
            int equalityIndex = 0;
            for (JsonElement element : equalityBindings) {
                JsonObject relation = element.getAsJsonObject();
                JsonArray members = new JsonArray();
                members.add(string(relation, "fromEndpoint"));
                members.add(string(relation, "toEndpoint"));
                JsonObject value = new JsonObject();
                value.addProperty("canonicalSymbol",
                        "SELECTED.EQ." + equalityIndex++);
                value.add("members", members);
                value.addProperty("selectionAuthority",
                        "INSTANCE_MATCHED_COMPLETE_RUNTIME_FINGERPRINT");
                equality.add(value);
            }
            JsonArray states = new JsonArray();
            for (JsonObject value : stateMerges) {
                if (!relevant(value, regionId)) {
                    continue;
                }
                JsonArray selected = selectedBindings(value, regionInstanceId,
                        true);
                if (selected.size() > 0) {
                    JsonObject copy = value.deepCopy();
                    copy.remove("runtimeBindings");
                    copy.add("selectedBindings", selected);
                    states.add(copy);
                }
            }
            JsonArray alternatives = new JsonArray();
            for (JsonObject value : alternativeWriterGroups) {
                if (!GSON.toJson(value).contains(regionId)) {
                    continue;
                }
                JsonObject copy = value.deepCopy();
                JsonArray selectedAlternatives = new JsonArray();
                for (JsonElement element : array(copy, "alternatives")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject alternative = element.getAsJsonObject();
                    JsonArray selected = selectedBindings(alternative,
                            regionInstanceId, true);
                    if (selected.size() > 0) {
                        JsonObject selectedAlternative =
                                alternative.deepCopy();
                        selectedAlternative.remove("runtimeBindings");
                        selectedAlternative.add("selectedBindings", selected);
                        selectedAlternatives.add(selectedAlternative);
                    }
                }
                if (selectedAlternatives.size() == 1) {
                    states.add(selectedAlternatives.get(0).deepCopy());
                } else if (selectedAlternatives.size() > 1) {
                    copy.add("alternatives", selectedAlternatives);
                    alternatives.add(copy);
                }
            }
            context.add("equalityClasses", equality);
            context.add("equalityRelations", equalityBindings);
            context.add("versionedStateMerges", states);
            context.add("alternativeWriterGroups", alternatives);
            context.addProperty("regionInstanceId", regionInstanceId);
            return context;
        }

        private static boolean relevant(JsonObject value, String regionId) {
            return string(value, "fromEndpoint").startsWith(regionId + ".")
                    || string(value, "fromEndpoint").startsWith(regionId + "::")
                    || string(value, "toEndpoint").startsWith(regionId + ".")
                    || string(value, "toEndpoint").startsWith(regionId + "::");
        }

        private static JsonArray selectedBindings(JsonObject relation,
                                                  String regionInstanceId,
                                                  boolean requireHeapWitness) {
            JsonArray result = new JsonArray();
            for (JsonElement element : array(relation, "runtimeBindings")) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject binding = element.getAsJsonObject();
                if (!regionInstanceId.isEmpty()
                        && !regionInstanceId.equals(string(binding,
                        "fromRegionInstance"))
                        && !regionInstanceId.equals(string(binding,
                        "toRegionInstance"))) {
                    continue;
                }
                if (requireHeapWitness
                        && (!binding.has("writeSeq")
                        || !binding.has("readSeq")
                        || !binding.has("receiverObjectId")
                        || !AutomaticRegionEdge
                        .trustedReadFromEvidence(binding))) {
                    continue;
                }
                if (!requireHeapWitness
                        && (!bool(binding, "valueEqualityObserved", false)
                        || !"RUNTIME_COMPLETE_VALUE_FINGERPRINT".equals(
                        string(binding, "valueEqualityAuthority"))
                        || string(binding, "valueFingerprint").isEmpty())) {
                    continue;
                }
                result.add(binding.deepCopy());
            }
            return result;
        }

    }

    public static final class Result {
        public final List<JsonObject> jobs = new ArrayList<>();
        public final List<JsonObject> scheduledActivations = new ArrayList<>();
        public final List<JsonObject> queries = new ArrayList<>();
        public final List<JsonObject> regionWorkItems = new ArrayList<>();
        public final List<JsonObject> upstreamRequests = new ArrayList<>();
        public final List<JsonObject> alternativeWriterGroups =
                new ArrayList<>();
        public final List<JsonObject> pathTasks = new ArrayList<>();
        public final JsonObject summary = new JsonObject();
        public JsonObject mergePlan = new JsonObject();
        public JsonObject regionManifest = new JsonObject();
        public JsonObject pathManifest = new JsonObject();
    }

    public static final class Arguments {
        public final Path regions;
        public final Path activations;
        public final Path edgeValidations;
        public final Path staticGraph;
        public final Path summaries;
        public final Path pathRecords;
        public final Path runtimeRegionInstances;
        public final Path outputDirectory;
        public final String regionId;
        public final String activationId;
        public final String targetSite;
        public final String requestedOutputCell;
        public final String requestedOutputCaptureSite;
        public final int requestedOutputCaptureOccurrence;
        public final int maxJobs;
        public final boolean allowMultipleJobsPerRegion;
        public final boolean forceBranchValidation;
        public final boolean captureOnly;
        public final RecursiveRegionWorklist.Bounds regionBounds;
        public final RegionPathWorklist.Bounds pathBounds;

        private Arguments(Path regions, Path activations,
                          Path edgeValidations, Path staticGraph,
                          Path summaries, Path pathRecords,
                          Path runtimeRegionInstances,
                          Path outputDirectory, String regionId,
                          String activationId, String targetSite,
                          String requestedOutputCell,
                          String requestedOutputCaptureSite,
                          int requestedOutputCaptureOccurrence,
                          int maxJobs,
                          boolean allowMultipleJobsPerRegion,
                          boolean forceBranchValidation,
                          boolean captureOnly,
                          RecursiveRegionWorklist.Bounds regionBounds,
                          RegionPathWorklist.Bounds pathBounds) {
            this.regions = regions;
            this.activations = activations;
            this.edgeValidations = edgeValidations;
            this.staticGraph = staticGraph;
            this.summaries = summaries;
            this.pathRecords = pathRecords;
            this.runtimeRegionInstances = runtimeRegionInstances;
            this.outputDirectory = outputDirectory;
            this.regionId = safe(regionId);
            this.activationId = safe(activationId);
            this.targetSite = safe(targetSite);
            this.requestedOutputCell = safe(requestedOutputCell);
            this.requestedOutputCaptureSite = safe(
                    requestedOutputCaptureSite);
            this.requestedOutputCaptureOccurrence = Math.max(0,
                    requestedOutputCaptureOccurrence);
            this.maxJobs = Math.max(1, maxJobs);
            this.allowMultipleJobsPerRegion = allowMultipleJobsPerRegion;
            this.forceBranchValidation = forceBranchValidation;
            this.captureOnly = captureOnly;
            this.regionBounds = regionBounds;
            this.pathBounds = pathBounds;
        }

        public static Arguments parse(String[] args) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; args != null && index < args.length; index++) {
                String value = args[index];
                if (!value.startsWith("--")) {
                    continue;
                }
                String key = value.substring(2);
                boolean hasNext = index + 1 < args.length;
                String next = hasNext ? args[index + 1] : "";
                if (hasNext && !next.startsWith("--")) {
                    values.put(key, next);
                    index++;
                } else {
                    values.put(key, "true");
                }
            }
            Path regions = requiredPath(values, "regions");
            Path activations = requiredPath(values, "activation-plan");
            Path edges = requiredPath(values, "edge-validations");
            Path output = Paths.get(firstNonBlank(values.get("output-dir"),
                    sibling(activations, "concolic-schedule").toString()));
            Path staticGraph = optionalPath(values.get("static-graph"));
            Path summaries = optionalPath(values.get("summaries"));
            Path pathRecords = optionalPath(values.get("path-records"));
            Path runtimeRegionInstances = optionalPath(values.get(
                    "runtime-region-instances"));
            return new Arguments(regions, activations, edges, staticGraph,
                    summaries, pathRecords, runtimeRegionInstances, output,
                    firstNonBlank(values.get("region-id")),
                    firstNonBlank(values.get("activation-id")),
                    firstNonBlank(values.get("target-site")),
                    firstNonBlank(values.get("requested-output-cell")),
                    firstNonBlank(values.get(
                            "requested-output-capture-site")),
                    parseInt(values.get(
                            "requested-output-capture-occurrence"), 0),
                    parseInt(values.get("max-jobs"), 1),
                    Boolean.parseBoolean(values.get("multiple-per-region")),
                    Boolean.parseBoolean(values.get("force-branch-validation")),
                    Boolean.parseBoolean(values.get("capture-only")),
                    new RecursiveRegionWorklist.Bounds(
                            parseInt(firstNonBlank(values.get(
                                    "max-region-depth"), values.get(
                                    "max-producer-depth")), 8),
                            parseInt(firstNonBlank(values.get(
                                    "max-recursive-regions"), values.get(
                                    "max-producer-regions")), 64),
                            parseInt(values.get(
                                    "max-activations-per-region"), 8),
                            parseInt(values.get(
                                    "max-alternative-writers"), 8),
                            parseInt(firstNonBlank(values.get(
                                    "max-region-queries"), values.get(
                                    "max-producer-queries")), 256),
                            parseInt(firstNonBlank(values.get(
                                    "max-graph-alternatives"), values.get(
                                    "max-producer-paths")), 512),
                            parseLong(firstNonBlank(values.get(
                                    "max-region-wall-clock-ms"), values.get(
                                    "max-producer-wall-clock-ms")), 30000L)),
                    new RegionPathWorklist.Bounds(
                            parseInt(values.get("max-region-paths"), 64),
                            parseInt(values.get("max-flips-per-path"), 32),
                            parseInt(values.get("max-path-tasks"), 256),
                            parseLong(values.get(
                                    "max-path-wall-clock-ms"), 30000L)));
        }

        private static Path requiredPath(Map<String, String> values,
                                         String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }

        private static Path optionalPath(String value) {
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
        }

        private static Path sibling(Path path, String name) {
            Path parent = path.toAbsolutePath().getParent();
            return (parent == null ? Paths.get(".") : parent).resolve(name);
        }

        private static int parseInt(String value, int fallback) {
            try {
                return value == null ? fallback : Integer.parseInt(value);
            } catch (RuntimeException ignored) {
                return fallback;
            }
        }

        private static long parseLong(String value, long fallback) {
            try {
                return value == null ? fallback : Long.parseLong(value);
            } catch (RuntimeException ignored) {
                return fallback;
            }
        }
    }
}
