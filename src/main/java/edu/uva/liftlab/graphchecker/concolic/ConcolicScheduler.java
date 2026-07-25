package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.SymbolicEnvironment;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Builds graph-directed concolic jobs from static regions and concrete
 * runtime-selected region instance plans.
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
    private static final Gson JSONL_GSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private static final String LOCAL_FIELD_ROOT_AUTHORITY =
            "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
    private static final String MAP_STATE_INPUT_OBSERVATION_MODE =
            "MAP_STATE_INPUT_OBSERVATION";
    private static final String FIRST_CONTAINER_OBSERVATION_AUTHORITY =
            "FIRST_MATCHING_CONTAINER_INSTANCE_APPROXIMATION_V1";
    private ConcolicScheduler() {
    }

    public static void main(String[] args) throws Exception {
        Arguments arguments = Arguments.parse(args);
        Result result = schedule(arguments);
        if (result.executionTasks.isEmpty()) {
            System.exit(2);
        }
    }

    public static Result schedule(Arguments arguments) throws IOException {
        requireFile(arguments.regions, "symbolic regions");
        requireFile(arguments.regionPlan, "region plan");
        requireFile(arguments.edgeValidations, "runtime edge validation");
        requireFile(arguments.staticGraph, "static data-flow graph");
        Files.createDirectories(arguments.outputDirectory);

        List<JsonObject> regions = readJsonl(arguments.regions);
        List<JsonObject> regionPlans = readJsonl(arguments.regionPlan);
        List<JsonObject> edges = readJsonl(arguments.edgeValidations);
        List<JsonObject> summaries = arguments.captureOnly
                || arguments.summaries == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.summaries);
        List<JsonObject> staticGraph = readJsonl(arguments.staticGraph);
        DefinitionIndex definitions = DefinitionIndex.from(staticGraph);

        Map<String, Region> regionIndex = new LinkedHashMap<>();
        for (JsonObject row : regions) {
            Region region = new Region(row);
            if (!region.regionId.isEmpty()) {
                regionIndex.put(region.regionId, region);
            }
        }

        MergePlan mergePlan = buildMergePlan(regionIndex, edges,
                staticGraph);
        List<Candidate> candidates = candidates(arguments, regionPlans,
                regionIndex, definitions);
        Collections.sort(candidates, Candidate.ORDER);

        Result result = new Result();
        Set<String> selectedRegions = new LinkedHashSet<>();
        for (Candidate candidate : candidates) {
            if (result.executionTasks.size() >= arguments.maxJobs) {
                break;
            }
            if (!arguments.allowMultipleJobsPerRegion
                    && !selectedRegions.add(candidate.region.regionId)) {
                continue;
            }
            MaterializationPlan materialization = candidate.materialization;
            JsonObject executionTask = candidate.activation.deepCopy();
            executionTask.addProperty("taskId",
                    candidate.seedTaskId());
            mergePlan.attachOutboundValueEqualityBindings(
                    executionTask, candidate.outputContract);
            JsonObject captured = candidate.outputContract != null ? null
                    : exactTargetSummary(candidate, summaries);
            String executionPhase = candidate.outputContract != null
                    ? "CAPTURE_OUTPUT_PATH"
                    : arguments.captureOnly
                    ? "CAPTURE_ONLY"
                    : captured != null
                    ? "NEGATE_CAPTURED_PATH" : "CAPTURE_THEN_NEGATE";
            executionTask.addProperty("executionPhase", executionPhase);
            executionTask.remove("symbolize");
            executionTask.add(InputActionCatalog.FIELD,
                    materialization.inputActions.deepCopy());
            compactExecutionTask(executionTask,
                    materialization.ready);

            if (captured != null && candidate.outputContract == null) {
                JsonObject query = branchQuery(candidate, captured,
                        mergePlan);
                result.queries.add(query);
            }
            result.executionTasks.add(executionTask);
        }

        writeJsonl(arguments.outputDirectory.resolve(
                        "execution_task_plan.jsonl"),
                result.executionTasks);
        if (!arguments.captureOnly) {
            writeJsonl(arguments.outputDirectory.resolve(
                            "branch_queries.jsonl"),
                    result.queries);
        }
        return result;
    }

    /** Promotes one discovery admission to the executable schedule schema. */
    private static void compactExecutionTask(
            JsonObject activation, Boolean scheduledReady) {
        boolean ready = scheduledReady != null
                ? scheduledReady
                : "READY".equals(admissionState(activation))
                || "EXECUTABLE".equals(admissionState(activation));
        JsonObject admission = new JsonObject();
        admission.addProperty("state", ready ? "EXECUTABLE" : "BLOCKED");
        activation.add("admission", admission);
    }

    private static boolean admissionReplayable(JsonObject activation) {
        String state = admissionState(activation);
        return "READY".equals(state) || "DISCOVERED".equals(state)
                || "EXECUTABLE".equals(state);
    }

    private static String admissionState(JsonObject activation) {
        JsonObject admission = object(activation, "admission");
        return admission == null ? "" : string(admission, "state");
    }

    private static List<Candidate> candidates(Arguments arguments,
                                              List<JsonObject> regionPlans,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions) {
        List<Candidate> result = new ArrayList<>();
        for (JsonObject envelope : regionPlans) {
            String regionInstanceId = string(envelope,
                    "regionInstanceId");
            String regionId = string(envelope, "regionId");
            Region region = regions.get(regionId);
            if (region == null || regionInstanceId.isEmpty()) {
                continue;
            }
            if (!arguments.regionInstanceId.isEmpty()
                    && !arguments.regionInstanceId.equals(
                    regionInstanceId)) {
                continue;
            }
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(regionId)) {
                continue;
            }
            Set<String> goalIds = new LinkedHashSet<>();
            for (JsonElement goalElement : array(envelope,
                    "closureGoals")) {
                if (!goalElement.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "closureGoals must contain objects for "
                                    + regionInstanceId);
                }
                JsonObject goal = goalElement.getAsJsonObject();
                String goalId = string(goal, "goalId");
                if (goalId.isEmpty() || !goalIds.add(goalId)) {
                    throw new IllegalArgumentException(
                            "closure goal ids must be nonempty and unique "
                                    + "for " + regionInstanceId);
                }
                if (!arguments.goalId.isEmpty()
                        && !arguments.goalId.equals(goalId)) {
                    continue;
                }
                JsonObject activation = projectGoal(envelope, goal);
                if (!admissionReplayable(activation)) {
                    continue;
                }
                ClosureGoalKind goalKind = ClosureGoalKind.fromTask(
                        activation);
                appendGoalCandidates(arguments, result, activation,
                        regionInstanceId, goalId, region, definitions,
                        goalKind);
            }
        }
        return result;
    }

    /**
     * Projects one semantic goal into the current executable task shape.
     * The envelope remains the canonical discovery row; no derived activation
     * is created or persisted.
     */
    private static JsonObject projectGoal(JsonObject envelope,
                                          JsonObject goal) {
        JsonObject task = envelope.deepCopy();
        task.remove("closureGoals");
        for (Map.Entry<String, JsonElement> entry : goal.entrySet()) {
            String field = entry.getKey();
            if ("kind".equals(field)) {
                continue;
            }
            task.add(field, entry.getValue().deepCopy());
        }
        ClosureGoalKind.fromGoal(goal).writeToTask(task);
        return task;
    }

    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result,
            JsonObject activation, String regionInstanceId, String goalId,
            Region region, DefinitionIndex definitions,
            ClosureGoalKind goalKind) {
            Set<String> definitionMethods = runtimeDefinitionMethods(
                    activation);
            activation.remove("runtimeDefinitionMethods");
            if (goalKind.capturesOutputRelation()) {
                if (!activation.has(OutputClosureContract.FIELD)) {
                    return;
                }
                OutputClosureContract outputClosure =
                        OutputClosureCodec.decode(activation);
                compileOutputClosure(activation, outputClosure);
                MaterializationPlan upstreamPlan = materializationPlan(
                        activation, definitions, definitionMethods,
                        outputClosure);
                boolean closureReady = outputClosureMembersReady(outputClosure)
                        && executionScopeReady(activation,
                        outputClosure,
                        definitions, definitionMethods);
                if (!closureReady) {
                    upstreamPlan = upstreamPlan.notReady();
                }
                result.add(new Candidate(activation,
                        regionInstanceId,
                        goalId, region,
                        TargetBranch.outputCapture(), true,
                        upstreamPlan, outputClosure));
                return;
            }
            JsonArray branches = array(activation, "branches");
            MaterializationPlan plan = null;
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
                TargetBranch target = new TargetBranch(siteId,
                        occurrence, observed, desired);
                if (plan == null) {
                    plan = materializationPlan(activation, definitions,
                            definitionMethods, null);
                }
                result.add(new Candidate(activation, regionInstanceId, goalId,
                        region, target, hasWitness,
                        plan, null));
            }
    }

    /** Restricts static definition lookup to the concrete runtime call
     * closure selected before the frozen-graph demand re-slice. */
    private static Set<String> runtimeDefinitionMethods(
            JsonObject activation) {
        JsonElement encoded = activation.get("runtimeDefinitionMethods");
        if (encoded == null || !encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "execution task requires runtimeDefinitionMethods array: "
                            + string(activation, "regionInstanceId"));
        }
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                throw new IllegalArgumentException(
                        "runtimeDefinitionMethods contains non-string value: "
                                + string(activation, "regionInstanceId"));
            }
            String method = safe(element.getAsString()).trim();
            if (method.isEmpty()) {
                throw new IllegalArgumentException(
                        "runtimeDefinitionMethods contains empty method: "
                                + string(activation, "regionInstanceId"));
            }
            result.add(method);
        }
        return result;
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

    /** Compiles the contract union needed by execution, without mirrors. */
    private static void compileOutputClosure(
            JsonObject activation, OutputClosureContract contract) {
        OutputClosureContract.ExecutionScope scope =
                contract.executionScope();
        activation.add("symbolize", selectExecutionRows(
                array(activation, "symbolize"), scope.inputPorts(),
                "symbol", "inputPort"));
        activation.add("branches", selectExecutionRows(
                array(activation, "branches"), scope.branchSites(),
                "siteId", ""));
    }

    private static JsonArray selectExecutionRows(
            JsonArray source, Set<String> selected,
            String primaryIdentity, String alternateIdentity) {
        JsonArray result = new JsonArray();
        for (JsonElement element : source) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String identity = firstNonBlank(string(row, primaryIdentity),
                    alternateIdentity.isEmpty()
                            ? "" : string(row, alternateIdentity));
            if (selected.contains(identity)) result.add(row.deepCopy());
        }
        return result;
    }

    /**
     * Dynamic capture proof stays at the scheduler boundary.  A joint
     * closure is all-or-nothing: one incomplete member closes the activation.
     */
    private static boolean outputClosureMembersReady(
            OutputClosureContract contract) {
        for (OutputClosureContract.Member member : contract.members()) {
            JsonObject slice = member.slice();
            if (!bool(slice, "complete", false)
                    || !member.captureComplete()) {
                return false;
            }
            if (!member.captureRequired()) continue;
            JsonArray captures = member.captures();
            if (captures.size() != 1
                    || !captures.get(0).isJsonObject()
                    || !runtimeExactOutputCapture(
                    captures.get(0).getAsJsonObject())) {
                return false;
            }
        }
        return true;
    }

    /**
     * Ensures the compiled union names declarations that exist in this exact
     * activation.  Explicit empty sets remain empty and never mean wildcard.
     */
    private static boolean executionScopeReady(
            JsonObject activation, OutputClosureContract contract,
            DefinitionIndex definitions, Set<String> regionMethods) {
        OutputClosureContract.ExecutionScope scope =
                contract.executionScope();
        return validExecutionRows(array(activation, "symbolize"),
                scope.inputPorts(),
                "symbol", "inputPort", true)
                && validExecutionRows(array(activation, "branches"),
                scope.branchSites(),
                "siteId", "", false)
                && regionMethods.containsAll(scope.methods())
                && (scope.causalEdgeIds().isEmpty()
                || definitions.containsAllEdges(scope.causalEdgeIds()));
    }

    private static boolean validExecutionRows(
            JsonArray rows, Set<String> allowed,
            String primaryIdentity, String alternateIdentity,
            boolean requireAll) {
        Set<String> actual = new LinkedHashSet<>();
        for (JsonElement element : rows) {
            if (!element.isJsonObject()) return false;
            JsonObject row = element.getAsJsonObject();
            String identity = firstNonBlank(string(row, primaryIdentity),
                    alternateIdentity.isEmpty()
                            ? "" : string(row, alternateIdentity));
            if (identity.isEmpty() || !allowed.contains(identity)
                    || !actual.add(identity)) {
                return false;
            }
        }
        return !requireAll || actual.equals(allowed);
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
            Set<String> regionMethods,
            OutputClosureContract outputClosure) {
        JsonArray result = new JsonArray();
        JsonArray concreteFallbacks = new JsonArray();
        Set<String> containerBaseInputs = containerBindingSymbols(
                activation, "baseInputSymbol");
        Set<String> containerInputPorts = containerBindingSymbols(
                activation, "containerInputPort");
        JsonArray sourceActions = array(activation, "symbolize");
        for (JsonElement element : sourceActions) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            JsonObject binding = action.deepCopy();
            String location = string(action, "location");
            String cell = string(action, "cell");
            boolean vmIntrinsic = verifiedVmIntrinsicPlaceholder(action,
                    location, cell);
            if (action.has("observed")
                    && !bool(action, "observed", false)
                    && !containerBaseInputs.contains(string(action,
                    "symbol"))
                    && !authoritativeDefinitionResolutionRequested(action)
                    && !vmIntrinsic) {
                concreteFallbacks.add(binding);
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
            } else if ("ARGUMENT_FIELD_PATH".equals(location)) {
                if (validFieldPaths(action)) {
                    binding.addProperty("bindingMode", "ROOT_ENTRY");
                } else {
                    concreteFallbacks.add(binding);
                    continue;
                }
            } else if ("CALL_RETURN".equals(location)) {
                Set<String> requestedMethods = outputClosure != null
                        ? outputClosure.executionScope().methods()
                        : Collections.<String>emptySet();
                Set<String> allowedMethods =
                        outputClosure == null
                                ? regionMethods : requestedMethods;
                Set<String> requestedSites = outputClosure != null
                        ? outputClosure.executionScope().branchSites()
                        : Collections.<String>emptySet();
                Set<String> requestedEdges = outputClosure != null
                        ? outputClosure.executionScope().causalEdgeIds()
                        : Collections.<String>emptySet();
                JsonArray sites = definitions.returnSites(cell,
                        allowedMethods, requestedSites, requestedEdges,
                        outputClosure != null);
                boolean pendingArrayFieldRoot =
                        pendingArrayFieldCallReturnRoot(action);
                if (pendingArrayFieldRoot && sites.size() != 1) {
                    concreteFallbacks.add(binding);
                    continue;
                }
                if (sites.size() == 0) {
                    concreteFallbacks.add(binding);
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
                    dischargeDeferredResolution(localBinding);
                    localBinding.addProperty("lazy", true);
                    finalizePendingLocalArrayRoot(localBinding, true);
                    result.add(localBinding);
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
            } else if ("HEAP_OBJECT_FIELD".equals(location)) {
                binding.addProperty("bindingMode", "FIELD_ACCESS");
                List<String> path = fieldPath(cell);
                JsonObject declaredLeaf = exactDeclaredFieldPathLeaf(
                        action, path);
                boolean deepExactDeclarationRequired = path.size() > 2;
                if (deepExactDeclarationRequired && declaredLeaf == null) {
                    concreteFallbacks.add(binding);
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
                    concreteFallbacks.add(binding);
                    continue;
                } else if (path.size() > 1
                        && action.has("valueObjectId")
                        && longInteger(action, "valueObjectId", 0L) == 0L) {
                    // The concrete discovery observed the first projected
                    // reference as null.  A later write may make the path
                    // traversable, but that does not make it a region-entry
                    // value; keep the workload value instead of creating a
                    // temporal alias for a future object.
                    concreteFallbacks.add(binding);
                    continue;
                }
            } else if ("REGION_LIVE_IN".equals(location)) {
                Matcher matcher = LOCAL_CELL.matcher(cell);
                if (matcher.matches()) {
                    binding.addProperty("bindingMode", "LOCAL_DEFINITION");
                    binding.addProperty("method", matcher.group(1));
                    binding.addProperty("local", matcher.group(2));
                    JsonArray sites = outputClosure == null
                            ? definitions.sites(cell)
                            : definitions.sites(cell,
                            outputClosure.executionScope().methods(),
                            outputClosure.executionScope().branchSites(),
                            outputClosure.executionScope().causalEdgeIds(),
                            true);
                    binding.add("definitionSites", sites);
                    binding.addProperty("definitionAuthority",
                            "STATIC_DATAFLOW_DEF_SITE");
                    if (sites.size() == 1) {
                        dischargeDeferredResolution(binding);
                    }
                    finalizePendingLocalArrayRoot(binding, true);
                    if (sites.size() == 0) {
                        concreteFallbacks.add(binding);
                        continue;
                    }
                    binding.addProperty("lazy", true);
                } else {
                    concreteFallbacks.add(binding);
                    continue;
                }
            } else {
                concreteFallbacks.add(binding);
                continue;
            }
            if (containerInputPorts.contains(string(binding, "symbol"))
                    && fieldBackedArray(binding)) {
                binding.addProperty("bindingMode",
                        "CONTAINER_INPUT_OBSERVATION");
                binding.addProperty("arrayFieldObservationOnly", true);
                binding.addProperty("modelControllable", false);
                binding.addProperty("containerObservationAuthority",
                        "FIRST_MATCHING_CONTAINER_INSTANCE_"
                                + "APPROXIMATION_V1");
                result.add(binding);
                continue;
            }
            String requestedMapStateCell = requestedMapStateCell(
                    activation, outputClosure, binding);
            if (!requestedMapStateCell.isEmpty()) {
                binding.addProperty("bindingMode",
                        MAP_STATE_INPUT_OBSERVATION_MODE);
                binding.addProperty("mapStateObservationOnly", true);
                binding.addProperty("modelControllable", false);
                binding.addProperty("containerObservationAuthority",
                        FIRST_CONTAINER_OBSERVATION_AUTHORITY);
                binding.addProperty("mapStateInputCell",
                        string(binding, "cell"));
                binding.addProperty("mapStateRequestedOutputCell",
                        requestedMapStateCell);
                result.add(binding);
                continue;
            }
            result.add(binding);
        }
        boolean ready = sourceActions.size() == 0 || result.size() > 0
                || concreteFallbacks.size() > 0;
        return new MaterializationPlan(inputActionCatalog(sourceActions,
                result, concreteFallbacks), ready);
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
        if (selected == null) return false;
        return integer(selected, "schemaVersion", -1) == 2
                && "ARRAY_ELEMENT_FIELD".equals(string(selected, "kind"))
                && "CONTAINER_SNAPSHOT".equals(string(selected,
                "materializationMode"))
                && "STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_CHAIN_V1"
                .equals(string(selected, "proofAuthority"))
                && bool(selected, "complete", false)
                && "EXACT_ARRAY_INDEX".equals(string(selected,
                "selectorAuthority"))
                && integer(selected, "elementIndex", -1) >= 0
                && integer(selected, "elementOccurrence", -1) > 0
                && array(selected, "fieldPath").equals(array(action,
                "fieldPath"))
                && string(selected, "declaredFieldSignature").equals(
                string(action, "field"))
                && !string(selected, "containerInputPort").isEmpty()
                && !symbol.equals(string(selected, "containerInputPort"));
    }

    /**
     * A requested Map heap state is a versioned container value, not a
     * scalar reference that the VM must make controllable.  Keep the real
     * getfield hook so runtime identity and mutations remain observable, but
     * never ask the VM to symbolize the Map reference itself.
     */
    private static String requestedMapStateCell(
            JsonObject activation, OutputClosureContract contract,
            JsonObject binding) {
        if (!ClosureGoalKind.fromTask(activation)
                .capturesOutputRelation()) {
            return "";
        }
        String cell = string(binding, "cell");
        if (cell.isEmpty()
                || !"HEAP_OBJECT_FIELD".equals(string(binding, "location"))
                || !"FIELD_ACCESS".equals(string(binding, "bindingMode"))
                || fieldPath(cell).size() != 1
                || !declaresMapReference(binding)) {
            return "";
        }
        if (contract != null) {
            for (OutputClosureContract.Member member : contract.members()) {
                if ("HEAP_STATE".equals(member.outputKind())
                        && cell.equals(member.cell())) {
                    return cell;
                }
            }
            return "";
        }
        return "";
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
            DeclaredField declared = FieldPathSpec.declaredField(candidate);
            if (declared != null && isMapReferenceType(declared.type())) {
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

    private static JsonArray inputActionCatalog(
            JsonArray declared, JsonArray symbolic, JsonArray concrete) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        for (JsonElement element : symbolic) {
            JsonObject action = element.getAsJsonObject().deepCopy();
            action.addProperty("mode",
                    InputActionCatalog.Mode.SYMBOLIC.name());
            represented.add(string(action, "symbol"));
            result.add(action);
        }
        for (JsonElement element : concrete) {
            JsonObject action = element.getAsJsonObject().deepCopy();
            action.addProperty("mode",
                    InputActionCatalog.Mode.CONCRETE.name());
            represented.add(string(action, "symbol"));
            result.add(action);
        }
        for (JsonElement element : declared) {
            if (!element.isJsonObject()
                    || represented.contains(string(
                    element.getAsJsonObject(), "symbol"))) {
                continue;
            }
            JsonObject action = element.getAsJsonObject().deepCopy();
            action.addProperty("mode",
                    InputActionCatalog.Mode.DECLARATION_ONLY.name());
            result.add(action);
        }
        return result;
    }

    /**
     * Returns the one complete leaf declaration that is internally exact for
     * this direct getfield path.  Merely attaching a declaration to a general
     * heap action is not enough: only the planner's strict direct-chain
     * authority may refine the leaf owner derived from the root signature.
     */
    private static JsonObject exactDeclaredFieldPathLeaf(
            JsonObject action, List<String> expectedPath) {
        return FieldPathSpec.exactLeafDeclaration(action, expectedPath,
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
    }

    private static String declaredFieldName(String signature) {
        DeclaredField field = FieldPathSpec.declaredField(signature);
        return field == null ? "" : field.name();
    }

    private static void dischargeDeferredResolution(JsonObject binding) {
        binding.remove("deferredResolution");
        binding.remove("deferredResolutionAuthority");
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
        return fieldBackedArray(action);
    }

    private static boolean validFieldPaths(JsonObject action) {
        return FieldPathSpec.hasNonEmptyPaths(action, "fieldPaths");
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
    }

    private static boolean fieldBackedArray(JsonObject binding) {
        String location = string(binding, "location");
        String mode = string(binding, "bindingMode");
        boolean fieldShape = "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "RECEIVER_FIELD".equals(location)
                || "HEAP_OBJECT_FIELD".equals(location)
                || "FIELD".equals(location)
                || "FIELD_ACCESS".equals(mode)
                || "LOCAL_DEFINITION".equals(mode)
                || "CALL_RETURN_DEFINITION".equals(string(binding,
                "consumedFieldPendingRootKind"));
        if (!fieldShape) return false;
        for (String member : new String[]{"leafFieldSignature",
                "accessFieldSignature", "field", "cell"}) {
            DeclaredField declaration = FieldPathSpec.declaredField(
                    string(binding, member));
            if (declaration != null
                    && (declaration.type().startsWith("[")
                    || declaration.type().endsWith("[]"))) {
                return true;
            }
        }
        for (JsonElement element : array(binding,
                "fieldPathLeafDeclarations")) {
            if (!element.isJsonObject()) continue;
            DeclaredField declaration = FieldPathSpec.declaredField(string(
                    element.getAsJsonObject(), "fieldSignature"));
            if (declaration != null
                    && (declaration.type().startsWith("[")
                    || declaration.type().endsWith("[]"))) {
                return true;
            }
        }
        String type = firstNonBlank(string(binding, "javaType"),
                string(binding, "inputJavaType"));
        return type.startsWith("[") || type.endsWith("[]");
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

    private static String leafField(String cell) {
        return FieldPathSpec.leafName(cell);
    }

    private static String leafOwnerClass(String cell) {
        return FieldPathSpec.leafOwner(cell);
    }

    private static String accessOwnerClass(String cell) {
        return FieldPathSpec.accessOwner(cell);
    }

    private static List<String> fieldPath(String cell) {
        return FieldPathSpec.path(cell);
    }

    private static MergePlan buildMergePlan(Map<String, Region> regions,
                                            List<JsonObject> edges,
                                            List<JsonObject> staticGraph) {
        List<JsonObject> equalityRelations = new ArrayList<>();
        List<JsonObject> stateMerges = new ArrayList<>();
        for (JsonObject edge : edges) {
            if (!AutomaticRegionEdge.composable(edge)) {
                continue;
            }
            String relation = AutomaticRegionEdge.relation(edge);
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
            Endpoint to = consumerEndpoint(regions.get(toRegion), toRegion,
                    toCell, staticGraph);
            if ("EQUALITY".equals(relation)) {
                JsonObject equality = relation(edge, from, to,
                        "SYMBOLIC_EQUALITY");
                equalityRelations.add(equality);
            } else if ("READ_FROM".equals(relation)) {
                JsonObject state = relation(edge, from, to,
                        "VERSIONED_HEAP_READ_FROM");
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
            String stable = stableQueryKey(
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
                String guardKey = stableQueryKey(
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

        return new MergePlan(equalityRelations, directStateMerges,
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
        result.addProperty("transportKind", string(edge, "transportKind"));
        result.addProperty("fromRegion", string(edge, "fromRegion"));
        result.addProperty("toRegion", string(edge, "toRegion"));
        result.addProperty("fromEndpoint", from.id);
        result.addProperty("fromCell", from.cell);
        result.addProperty("toEndpoint", to.id);
        result.addProperty("toCell", to.cell);
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
    private static Endpoint consumerEndpoint(
            Region region, String regionId, String rawCell,
            List<JsonObject> staticGraph) {
        if (region == null) {
            return new Endpoint(regionId + "::" + rawCell, rawCell);
        }
        String direct = region.uniqueInputPort(rawCell);
        if (!direct.isEmpty()) {
            return new Endpoint(direct, rawCell);
        }
        // A duplicated exact input is already ambiguous.  Do not escape that
        // ambiguity through a different static projection.
        if (region.hasInputCell(rawCell)) {
            return new Endpoint(regionId + "::" + rawCell, rawCell);
        }
        List<Endpoint> matches = new ArrayList<>();
        for (JsonObject proof : staticGraph == null
                ? Collections.<JsonObject>emptyList() : staticGraph) {
            String inputCell = string(proof, "fromCell");
            String inputPort = region.uniqueInputPort(inputCell);
            if (inputPort.isEmpty()
                    || !completeAccessorInputProof(proof, rawCell,
                    inputCell)) {
                continue;
            }
            matches.add(new Endpoint(inputPort, inputCell));
        }
        if (matches.size() != 1) {
            return new Endpoint(regionId + "::" + rawCell, rawCell);
        }
        return matches.get(0);
    }

    private static boolean completeAccessorInputProof(JsonObject proof,
                                                       String rawCell,
                                                       String inputCell) {
        if (proof == null || string(proof, "id").isEmpty()
                || integer(proof, "schemaVersion", -1) != 2
                || !"accessor_field_return".equals(string(proof, "kind"))
                || !"value_flow".equals(string(proof, "relation"))
                || !"ASSERTABLE".equals(string(proof, "semanticMode"))
                || !safe(rawCell).equals(string(proof, "toCell"))
                || !safe(inputCell).equals(string(proof, "fromCell"))) {
            return false;
        }
        String declaredSignature = string(proof,
                "declaredFieldSignature");
        DeclaredField declared = FieldPathSpec.declaredField(
                declaredSignature);
        String invoke = string(proof, "invoke");
        String implementation = string(proof,
                "accessorImplementationMethod");
        return declared != null
                && declaredSignature.equals(inputCell)
                && !invoke.isEmpty() && !implementation.isEmpty()
                && declared.type().equals(methodReturnType(invoke))
                && declared.type().equals(methodReturnType(implementation));
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
        query.addProperty("goalId", candidate.goalId);
        query.addProperty("regionId", candidate.region.regionId);
        query.addProperty("regionInstanceId",
                candidate.regionInstanceId);
        try {
            BranchReplayContract contract =
                    BranchReplayContract.fromSummary(summary,
                    candidate.target.siteId,
                    candidate.target.selectedOccurrence);
            if (contract.source().sourceTakenOutcome()
                    != candidate.target.observedOutcome
                    || contract.requiredTakenOutcome()
                    != candidate.target.desiredOutcome) {
                throw new IllegalArgumentException(
                        "captured branch polarity differs from selection");
            }
            contract.addTo(query);
            query.addProperty("readyForSolver", true);
        } catch (IllegalArgumentException incompleteWitness) {
            query.addProperty("readyForSolver", false);
            query.addProperty("blocker", incompleteWitness.getMessage());
        }
        query.add("engineArrayInputBindings", array(summary,
                "engineArrayInputBindings").deepCopy());
        query.add("symbolicContext",
                mergePlan.contextFor(candidate.region.regionId,
                        candidate.regionInstanceId));
        return query;
    }

    private static JsonArray runtimeBindings(JsonObject edge) {
        return array(edge, "bindings");
    }

    /**
     * Selects target-PC provenance only from the exact runtime region
     * instance and closure goal.
     */
    private static JsonObject exactTargetSummary(
            Candidate candidate, List<JsonObject> summaries) {
        String expectedInstance = candidate.regionInstanceId;
        if (expectedInstance.isEmpty()) return null;
        JsonObject selected = null;
        for (JsonObject summary : summaries) {
            if (!candidate.goalId.equals(string(summary, "goalId"))
                    || !candidate.region.regionId.equals(string(summary,
                    "regionId"))
                    || !expectedInstance.equals(string(summary,
                    "regionInstanceId"))
                    || !ClosureGoalKind.fromTask(summary)
                    .capturesTargetReach()
                    || !bool(summary, "relationallyComplete", false)
                    || string(summary, "summaryId").isEmpty()) {
                continue;
            }
            if (selected == null) {
                selected = summary;
            }
        }
        return selected;
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        return path == null ? Collections.<JsonObject>emptyList()
                : ArtifactIO.readJsonl(path);
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        ArtifactIO.replaceJsonl(path, rows);
    }

    private static void requireFile(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
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
        private final Set<String> edgeIds = new LinkedHashSet<>();
        private final Map<String, List<JsonObject>> byCell =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> byCallReturn =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> callsByMethod =
                new LinkedHashMap<>();

        private static DefinitionIndex from(List<JsonObject> edges) {
            DefinitionIndex result = new DefinitionIndex();
            Set<String> seen = new LinkedHashSet<>();
            Set<String> seenCallReturns = new LinkedHashSet<>();
            for (JsonObject edge : edges) {
                String edgeId = string(edge, "id");
                if (!edgeId.isEmpty()) result.edgeIds.add(edgeId);
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
                if (!edgeId.isEmpty()) {
                    site.addProperty("causalEdgeId", edgeId);
                }
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

        private JsonArray sites(String cell,
                                Set<String> allowedMethods,
                                Set<String> allowedSites,
                                Set<String> allowedEdges,
                                boolean strict) {
            return filteredSites(byCell.get(cell), allowedMethods,
                    allowedSites, allowedEdges, strict);
        }

        private JsonArray returnSites(String callReturnCell,
                                      Set<String> allowedMethods,
                                      Set<String> allowedSites,
                                      Set<String> allowedEdges,
                                      boolean strict) {
            return filteredSites(byCallReturn.get(callReturnCell),
                    allowedMethods, allowedSites, allowedEdges, strict);
        }

        private JsonArray filteredSites(
                List<JsonObject> sites, Set<String> allowedMethods,
                Set<String> allowedSites, Set<String> allowedEdges,
                boolean strict) {
            JsonArray result = new JsonArray();
            if (sites == null) {
                return result;
            }
            for (JsonObject site : sites) {
                String method = string(site, "method");
                String siteId = string(site, "siteId");
                String edgeId = string(site, "causalEdgeId");
                if (allowedMethods != null
                        && (strict || !allowedMethods.isEmpty())
                        && !allowedMethods.contains(method)) {
                    continue;
                }
                if (allowedSites != null
                        && (strict || !allowedSites.isEmpty())
                        && !allowedSites.contains(siteId)) {
                    continue;
                }
                if (allowedEdges != null
                        && (strict || !allowedEdges.isEmpty())
                        && !allowedEdges.contains(edgeId)) {
                    continue;
                }
                result.add(site.deepCopy());
            }
            return result;
        }

        private boolean containsAllEdges(Set<String> expected) {
            return edgeIds.containsAll(expected);
        }

    }

    private static final class Region {
        private static final int STATIC_REGION_SCHEMA_VERSION = 2;
        private final String regionId;
        private final Set<String> methods = new LinkedHashSet<>();
        private final Map<String, String> portByCell = new LinkedHashMap<>();
        private final Map<String, List<String>> inputPortsByCell =
                new LinkedHashMap<>();

        private Region(JsonObject row) {
            int schemaVersion = integer(row, "schemaVersion", -1);
            if (schemaVersion != STATIC_REGION_SCHEMA_VERSION) {
                throw new IllegalArgumentException(
                        "symbolic region requires schemaVersion "
                                + STATIC_REGION_SCHEMA_VERSION);
            }
            this.regionId = string(row, "regionId");
            this.methods.addAll(stringSet(row, "methods"));
            collectInputs(array(row, "symbolicInputs"));
            collectPorts(array(row, "outputs"));
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

    private static String stableQueryKey(String consumerRegion,
                                         String inputPort,
                                         String relationKind,
                                         String requiredStateVersion,
                                         String pathPrefixHash,
                                         String boundedContextHash) {
        String canonical = keyComponent(consumerRegion)
                + keyComponent(canonicalQueryPort(inputPort))
                + keyComponent(firstNonBlank(relationKind, "UNKNOWN"))
                + keyComponent(firstNonBlank(requiredStateVersion,
                "UNVERSIONED"))
                + keyComponent(firstNonBlank(pathPrefixHash, "NO_PATH"))
                + keyComponent(firstNonBlank(boundedContextHash,
                "NO_CONTEXT"));
        return ArtifactIO.sha256(canonical);
    }

    private static String canonicalQueryPort(String value) {
        return firstNonBlank(value).replaceAll("\\s+", " ").trim();
    }

    private static String keyComponent(String value) {
        String safe = value == null ? "" : value;
        return safe.length() + ":" + safe;
    }

    private static final class Endpoint {
        private final String id;
        private final String cell;

        private Endpoint(String id, String cell) {
            this.id = safe(id);
            this.cell = safe(cell);
        }
    }

    private static final class MaterializationPlan {
        private final JsonArray inputActions;
        private final boolean ready;

        private MaterializationPlan(JsonArray inputActions, boolean ready) {
            this.inputActions = inputActions;
            this.ready = ready;
        }

        private MaterializationPlan notReady() {
            return new MaterializationPlan(inputActions, false);
        }
    }

    private static final class TargetBranch {
        private final String siteId;
        private final int selectedOccurrence;
        private final boolean observedOutcome;
        private final boolean desiredOutcome;

        private TargetBranch(String siteId, int selectedOccurrence,
                             boolean observedOutcome,
                             boolean desiredOutcome) {
            this.siteId = safe(siteId);
            this.selectedOccurrence = Math.max(1, selectedOccurrence);
            this.observedOutcome = observedOutcome;
            this.desiredOutcome = desiredOutcome;
        }

        private static TargetBranch outputCapture() {
            return new TargetBranch("", 1, false, false);
        }

    }

    private static final class Candidate {
        private static final Comparator<Candidate> ORDER =
                Comparator.comparing((Candidate value) -> !value.directed)
                        .thenComparing(value -> !value.materialization.ready)
                        .thenComparing(value -> value.target.siteId)
                        .thenComparingInt(value -> integer(object(
                                value.activation, "rootSelector"),
                                "ordinal", Integer.MAX_VALUE))
                        .thenComparing(value -> value.regionInstanceId)
                        .thenComparing(value -> value.goalId);

        private final JsonObject activation;
        private final String regionInstanceId;
        private final String goalId;
        private final Region region;
        private final TargetBranch target;
        private final boolean directed;
        private final OutputClosureContract outputContract;
        private final MaterializationPlan materialization;

        private Candidate(JsonObject activation, String regionInstanceId,
                          String goalId, Region region, TargetBranch target,
                          boolean hasRequiredWitness,
                          MaterializationPlan materialization,
                          OutputClosureContract outputContract) {
            this.activation = activation;
            this.regionInstanceId = regionInstanceId;
            this.goalId = goalId;
            this.region = region;
            this.target = target;
            this.outputContract = outputContract;
            this.directed = outputContract != null || !hasRequiredWitness;
            this.materialization = materialization;
        }

        private String seedTaskId() {
            String identity = regionInstanceId + "\n" + goalId + "\n"
                    + target.siteId + "\n" + target.selectedOccurrence
                    + "\n" + target.observedOutcome
                    + "\n" + target.desiredOutcome;
            return "TASK.SEED." + ArtifactIO.sha256(identity);
        }
    }

    private static final class MergePlan {
        private final List<JsonObject> equalityRelations;
        private final List<JsonObject> stateMerges;
        private final List<JsonObject> alternativeWriterGroups;

        private MergePlan(List<JsonObject> equalityRelations,
                          List<JsonObject> stateMerges,
                          List<JsonObject> alternativeWriterGroups) {
            this.equalityRelations = equalityRelations;
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
                JsonObject activation,
                OutputClosureContract outputClosure) {
            if (activation == null) return;
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
            Set<String> requestedPorts = outputClosure == null
                    ? Collections.<String>emptySet()
                    : outputClosure.outputPorts();

            for (JsonObject relation : equalityRelations) {
                String fromRegion = string(relation, "fromRegion");
                String toRegion = string(relation, "toRegion");
                String fromPort = string(relation, "fromEndpoint");
                String toPort = string(relation, "toEndpoint");
                if (!region.equals(fromRegion) || toRegion.isEmpty()
                        || !fromPort.startsWith(fromRegion + ".out.")
                        || !toPort.startsWith(toRegion + ".in.")
                        || outputClosure != null
                        && !requestedPorts.contains(fromPort)) {
                    continue;
                }
                for (JsonElement element : array(relation,
                        "runtimeBindings")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject raw = element.getAsJsonObject();
                    String fromInstance = string(raw,
                            "fromRegionInstance");
                    String toInstance = string(raw, "toRegionInstance");
                    if (!instance.equals(fromInstance)
                            || toInstance.isEmpty()
                            || !AutomaticRegionEdge
                            .trustedRuntimeValueEqualityEvidence(raw)) {
                        continue;
                    }
                    JsonObject normalized = new JsonObject();
                    normalized.addProperty("schemaVersion", 2);
                    normalized.addProperty("edgeId", string(relation,
                            "edgeId"));
                    normalized.addProperty("evidenceKind",
                            AutomaticRegionEdge.COMPLETE_VALUE_EQUALITY);
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
                    normalized.addProperty("writerEventSeq",
                            raw.get("writerEventSeq").getAsLong());
                    normalized.addProperty("readerEventSeq",
                            raw.get("readerEventSeq").getAsLong());
                    normalized.addProperty("valueFingerprint", string(raw,
                            "valueFingerprint"));
                    String correlationAuthority = string(raw,
                            "correlationAuthority");
                    if (!correlationAuthority.isEmpty()) {
                        normalized.addProperty("correlationAuthority",
                                correlationAuthority);
                    }
                    addUniqueBinding(bindings, normalized);
                }
            }
            if (bindings.size() > 0) {
                activation.add("edgeBindings", bindings);
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
            long leftWriter = longInteger(left, "writerEventSeq", -1L);
            long leftReader = longInteger(left, "readerEventSeq", -1L);
            long rightWriter = longInteger(right, "writerEventSeq", -1L);
            long rightReader = longInteger(right, "readerEventSeq", -1L);
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
                    + string(binding, "evidenceKind") + "\n"
                    + string(binding, "fromRegionInstance") + "\n"
                    + string(binding, "toRegionInstance") + "\n"
                    + string(binding, "fromOutputPort") + "\n"
                    + string(binding, "toInputPort") + "\n"
                    + string(binding, "valueFingerprint");
        }

        private JsonObject contextFor(String regionId, String regionInstanceId) {
            JsonObject context = new JsonObject();
            JsonArray equalityBindings = new JsonArray();
            for (JsonObject value : equalityRelations) {
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
            for (JsonElement element : equalityBindings) {
                JsonObject relation = element.getAsJsonObject();
                JsonArray members = new JsonArray();
                members.add(string(relation, "fromEndpoint"));
                members.add(string(relation, "toEndpoint"));
                JsonObject value = new JsonObject();
                value.add("members", members);
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
                        && !AutomaticRegionEdge
                        .trustedReadFromEvidence(binding)) {
                    continue;
                }
                if (!requireHeapWitness
                        && !AutomaticRegionEdge
                        .trustedRuntimeValueEqualityEvidence(binding)) {
                    continue;
                }
                result.add(binding.deepCopy());
            }
            return result;
        }

    }

    public static final class Result {
        public final List<JsonObject> executionTasks = new ArrayList<>();
        public final List<JsonObject> queries = new ArrayList<>();
    }

    public static final class Arguments {
        public final Path regions;
        public final Path regionPlan;
        public final Path edgeValidations;
        public final Path staticGraph;
        public final Path summaries;
        public final Path outputDirectory;
        public final String regionId;
        public final String regionInstanceId;
        public final String goalId;
        public final String targetSite;
        public final int maxJobs;
        public final boolean allowMultipleJobsPerRegion;
        public final boolean captureOnly;

        private Arguments(Path regions, Path regionPlan,
                          Path edgeValidations, Path staticGraph,
                          Path summaries, Path outputDirectory, String regionId,
                          String regionInstanceId, String goalId,
                          String targetSite,
                          int maxJobs,
                          boolean allowMultipleJobsPerRegion,
                          boolean captureOnly) {
            this.regions = regions;
            this.regionPlan = regionPlan;
            this.edgeValidations = edgeValidations;
            this.staticGraph = staticGraph;
            this.summaries = summaries;
            this.outputDirectory = outputDirectory;
            this.regionId = safe(regionId);
            this.regionInstanceId = safe(regionInstanceId);
            this.goalId = safe(goalId);
            this.targetSite = safe(targetSite);
            this.maxJobs = Math.max(1, maxJobs);
            this.allowMultipleJobsPerRegion = allowMultipleJobsPerRegion;
            this.captureOnly = captureOnly;
        }

        public static Arguments parse(String[] args) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; args != null && index < args.length; index++) {
                String value = args[index];
                if (!value.startsWith("--")) {
                    throw new IllegalArgumentException(
                            "Unexpected scheduler argument: " + value);
                }
                String key = value.substring(2);
                if (!knownOption(key)) {
                    throw new IllegalArgumentException(
                            "Unknown scheduler option --" + key);
                }
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
            Path regionPlan = requiredPath(values, "region-plan");
            Path edges = requiredPath(values, "edge-validations");
            Path output = Paths.get(firstNonBlank(values.get("output-dir"),
                    sibling(regionPlan, "concolic-schedule").toString()));
            Path staticGraph = requiredPath(values, "static-graph");
            Path summaries = optionalPath(values.get("summaries"));
            return new Arguments(regions, regionPlan, edges, staticGraph,
                    summaries, output,
                    firstNonBlank(values.get("region-id")),
                    firstNonBlank(values.get("region-instance-id")),
                    firstNonBlank(values.get("goal-id")),
                    firstNonBlank(values.get("target-site")),
                    parseInt(values.get("max-jobs"), 1),
                    Boolean.parseBoolean(values.get("multiple-per-region")),
                    Boolean.parseBoolean(values.get("capture-only")));
        }

        private static boolean knownOption(String key) {
            return "regions".equals(key)
                    || "region-plan".equals(key)
                    || "edge-validations".equals(key)
                    || "static-graph".equals(key)
                    || "summaries".equals(key)
                    || "output-dir".equals(key)
                    || "region-id".equals(key)
                    || "region-instance-id".equals(key)
                    || "goal-id".equals(key)
                    || "target-site".equals(key)
                    || "max-jobs".equals(key)
                    || "multiple-per-region".equals(key)
                    || "capture-only".equals(key);
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

    }
}
