package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.SymbolicEnvironment;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.GoalKind;

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
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private static final String LOCAL_FIELD_ROOT_AUTHORITY =
            "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
    private static final String MAP_STATE_INPUT_OBSERVATION_MODE =
            "MAP_STATE_INPUT_OBSERVATION";
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

        MergePlan mergePlan = buildMergePlan(regionIndex, edges);
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
                    && !selectedRegions.add(
                    candidate.goal.plan().regionId())) {
                continue;
            }
            OutputClosureContract outputContract =
                    candidate.outputContract();
            JsonObject captured = outputContract != null ? null
                    : exactTargetSummary(candidate, summaries);
            JsonObject executionTask = ExecutionTask.create(
                    candidate.goal, candidate.seedTaskId(),
                    candidate.inputActions, candidate.branches,
                    mergePlan.outboundValueEqualityBindings(
                            candidate.goal, outputContract),
                    candidate.ready).json();

            if (captured != null && outputContract == null) {
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

    private static List<Candidate> candidates(Arguments arguments,
                                              List<JsonObject> regionPlans,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions) {
        List<Candidate> result = new ArrayList<>();
        for (JsonObject encoded : regionPlans) {
            RegionInstancePlan plan = RegionInstancePlan.decode(encoded);
            Region region = regions.get(plan.regionId());
            if (region == null) {
                continue;
            }
            if (!arguments.regionInstanceId.isEmpty()
                    && !arguments.regionInstanceId.equals(
                    plan.regionInstanceId())) {
                continue;
            }
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(plan.regionId())) {
                continue;
            }
            for (Goal goal : plan.goals()) {
                if (!arguments.goalId.isEmpty()
                        && !arguments.goalId.equals(goal.goalId())) {
                    continue;
                }
                if (!goal.replayable()) {
                    continue;
                }
                appendGoalCandidates(arguments, result, goal, definitions);
            }
        }
        return result;
    }

    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result,
            Goal goal, DefinitionIndex definitions) {
            Set<String> definitionMethods =
                    goal.runtimeDefinitionMethods();
            if (goal.kind() == GoalKind.OUTPUT_RELATION_CLOSURE) {
                OutputClosureContract outputClosure =
                        goal.outputClosure();
                if (outputClosure == null) {
                    return;
                }
                OutputClosureContract.ExecutionScope scope =
                        outputClosure.executionScope();
                JsonArray symbolize = selectExecutionRows(
                        goal.symbolize(), scope.inputPorts(),
                        "symbol", "inputPort", true);
                JsonArray branches = selectExecutionRows(
                        goal.branches(), scope.branchSites(),
                        "siteId", "", false);
                boolean closureReady = symbolize != null && branches != null
                        && regionMethodsCover(definitionMethods, scope,
                        definitions)
                        && outputClosureMembersReady(outputClosure,
                        symbolize);
                if (symbolize == null) symbolize = new JsonArray();
                if (branches == null) branches = new JsonArray();
                JsonArray inputActions = materializationPlan(
                        goal, symbolize, definitions, definitionMethods,
                        outputClosure);
                result.add(new Candidate(goal, branches,
                        TargetBranch.outputCapture(), true,
                        inputActions, closureReady));
                return;
            }
            goal.rejectOutputClosure();
            JsonArray branches = goal.branches();
            JsonArray inputActions = null;
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
                TargetBranch target = TargetBranch.select(
                        siteId, array(branch, "occurrences"), required);
                if (target == null) {
                    continue;
                }
                boolean hasWitness = target.observedOutcome == required;
                boolean explicitlySelected = !arguments.targetSite.isEmpty();
                boolean explore = "EXPLORE".equals(string(branch, "policy"));
                if (hasWitness && !explicitlySelected && !explore) {
                    continue;
                }
                if (inputActions == null) {
                    JsonArray symbolize = goal.symbolize();
                    inputActions = materializationPlan(goal, symbolize,
                            definitions,
                            definitionMethods, null);
                }
                result.add(new Candidate(goal, branches, target,
                        hasWitness, inputActions, true));
            }
    }

    private static JsonArray selectExecutionRows(
            JsonArray source, Set<String> selected,
            String primaryIdentity, String alternateIdentity,
            boolean requireAll) {
        JsonArray result = new JsonArray();
        Set<String> actual = new LinkedHashSet<>();
        for (JsonElement element : source) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String identity = firstNonBlank(string(row, primaryIdentity),
                    alternateIdentity.isEmpty()
                            ? "" : string(row, alternateIdentity));
            if (!selected.contains(identity)) continue;
            if (identity.isEmpty() || !actual.add(identity)) return null;
            result.add(row.deepCopy());
        }
        return !requireAll || actual.equals(selected) ? result : null;
    }

    /**
     * Dynamic capture proof stays at the scheduler boundary.  A joint
     * closure is all-or-nothing: one incomplete member closes the activation.
     */
    private static boolean outputClosureMembersReady(
            OutputClosureContract contract, JsonArray symbolize) {
        for (OutputClosureContract.Member member : contract.members()) {
            JsonObject slice = member.slice();
            if (!bool(slice, "complete", false)
                    || !member.captureComplete()) {
                return false;
            }
            for (JsonElement element : member.captures()) {
                JsonObject capture = element.getAsJsonObject();
                if (!hasRegionExitPrestate(member, capture,
                        symbolize)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * One logical request covers every normal return of the region root.
     * Assignment sites and seed-path occurrences are deliberately absent:
     * the runtime reads the declared receiver path after the replay has
     * reached whichever normal exit it took.
     */
    private static boolean hasRegionExitPrestate(
            OutputClosureContract.Member member, JsonObject capture,
            JsonArray symbolize) {
        String root = string(capture, "accessRootInputPort");
        List<String> path = FieldPathSpec.stringArray(capture, "fieldPath");
        int matches = 0;
        for (JsonElement element : symbolize) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (root.equals(string(action, "symbol"))
                    && member.cell().equals(string(action, "cell"))
                    && "HEAP_PRESTATE".equals(string(action, "sourceKind"))
                    && "RECEIVER_FIELD".equals(string(action, "location"))
                    && string(capture, "fieldSignature").equals(
                    string(action, "leafFieldSignature"))
                    && path.equals(FieldPathSpec.stringArray(action,
                    "fieldPath"))) {
                matches++;
            }
        }
        return matches == 1;
    }

    private static boolean regionMethodsCover(
            Set<String> regionMethods,
            OutputClosureContract.ExecutionScope scope,
            DefinitionIndex definitions) {
        return regionMethods.containsAll(scope.methods())
                && (scope.causalEdgeIds().isEmpty()
                || definitions.containsAllEdges(scope.causalEdgeIds()));
    }

    private static JsonArray materializationPlan(
            Goal goal, JsonArray sourceActions,
            DefinitionIndex definitions,
            Set<String> regionMethods,
            OutputClosureContract outputClosure) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        OutputClosureContract.ExecutionScope scope = outputClosure == null
                ? null : outputClosure.executionScope();
        JsonArray containerBindings =
                goal.containerElementFieldBindings();
        Set<String> containerBaseInputs = containerBindingSymbols(
                containerBindings, "baseInputSymbol");
        Set<String> containerInputPorts = containerBindingSymbols(
                containerBindings, "containerInputPort");
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
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            if (exactContainerSnapshotLeafDeclaration(
                    containerBindings, action)) {
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
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
            } else if ("CALL_RETURN".equals(location)) {
                JsonArray sites = definitions.returnSites(cell,
                        scope == null ? regionMethods : scope.methods(),
                        scope);
                boolean pendingArrayFieldRoot =
                        pendingArrayFieldCallReturnRoot(action);
                if (pendingArrayFieldRoot && sites.size() != 1) {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
                if (sites.size() == 0) {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
                for (JsonElement siteElement : sites) {
                    JsonObject site = siteElement.getAsJsonObject();
                    JsonObject localBinding = binding.deepCopy();
                    localBinding.addProperty("bindingMode",
                            "LOCAL_DEFINITION");
                    localBinding.addProperty("method",
                            string(site, "method"));
                    localBinding.addProperty("local",
                            string(site, "local"));
                    JsonArray oneSite = new JsonArray();
                    oneSite.add(site.deepCopy());
                    localBinding.add("definitionSites", oneSite);
                    dischargeDeferredResolution(localBinding);
                    localBinding.addProperty("lazy", true);
                    finalizePendingLocalArrayRoot(localBinding);
                    addInputAction(result, represented, localBinding,
                            InputActionCatalog.Mode.SYMBOLIC);
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
                if (path.size() > 2 && declaredLeaf == null) {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
                binding.addProperty("lazy", true);
                if (path.size() > 1
                        && action.has("valueObjectId")
                        && longInteger(action, "valueObjectId", 0L) == 0L) {
                    // The concrete discovery observed the first projected
                    // reference as null.  A later write may make the path
                    // traversable, but that does not make it a region-entry
                    // value; keep the workload value instead of creating a
                    // temporal alias for a future object.
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
            } else if ("REGION_LIVE_IN".equals(location)) {
                Matcher matcher = LOCAL_CELL.matcher(cell);
                if (matcher.matches()) {
                    binding.addProperty("bindingMode", "LOCAL_DEFINITION");
                    binding.addProperty("method", matcher.group(1));
                    binding.addProperty("local", matcher.group(2));
                    JsonArray sites = definitions.sites(cell,
                            scope == null ? regionMethods : scope.methods(),
                            scope);
                    binding.add("definitionSites", sites);
                    if (sites.size() == 1) {
                        dischargeDeferredResolution(binding);
                    }
                    finalizePendingLocalArrayRoot(binding);
                    if (sites.size() == 0) {
                        addInputAction(result, represented, binding,
                                InputActionCatalog.Mode.CONCRETE);
                        continue;
                    }
                    binding.addProperty("lazy", true);
                } else {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
            } else {
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            if (containerInputPorts.contains(string(binding, "symbol"))
                    && fieldBackedArray(binding)) {
                binding.addProperty("bindingMode",
                        "CONTAINER_INPUT_OBSERVATION");
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.SYMBOLIC);
                continue;
            }
            if (requestedMapState(outputClosure, binding)) {
                binding.addProperty("bindingMode",
                        MAP_STATE_INPUT_OBSERVATION_MODE);
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.SYMBOLIC);
                continue;
            }
            addInputAction(result, represented, binding,
                    InputActionCatalog.Mode.SYMBOLIC);
        }
        for (JsonElement element : sourceActions) {
            if (!element.isJsonObject()
                    || represented.contains(string(
                    element.getAsJsonObject(), "symbol"))) {
                continue;
            }
            addInputAction(result, represented,
                    element.getAsJsonObject().deepCopy(),
                    InputActionCatalog.Mode.DECLARATION_ONLY);
        }
        return result;
    }

    private static Set<String> containerBindingSymbols(
            JsonArray containerBindings, String member) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : containerBindings) {
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
            JsonArray containerBindings, JsonObject action) {
        String symbol = string(action, "symbol");
        if (symbol.isEmpty()
                || !"HEAP_OBJECT_FIELD".equals(string(action,
                "location"))
                || !"STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1".equals(
                string(action, "fieldPathAuthority"))) {
            return false;
        }
        JsonObject selected = null;
        for (JsonElement element : containerBindings) {
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
    private static boolean requestedMapState(
            OutputClosureContract contract,
            JsonObject binding) {
        if (contract == null) {
            return false;
        }
        String cell = string(binding, "cell");
        if (cell.isEmpty()
                || !"HEAP_OBJECT_FIELD".equals(string(binding, "location"))
                || !"FIELD_ACCESS".equals(string(binding, "bindingMode"))
                || fieldPath(cell).size() != 1
                || !declaresMapReference(binding)) {
            return false;
        }
        for (OutputClosureContract.Member member : contract.members()) {
            if ("HEAP_STATE".equals(member.outputKind())
                    && cell.equals(member.cell())) {
                return true;
            }
        }
        return false;
    }

    private static boolean declaresMapReference(JsonObject binding) {
        if (JavaContainerTypes.isMap(string(binding, "javaType"))) {
            return true;
        }
        for (String candidate : new String[]{
                string(binding, "leafFieldSignature"),
                string(binding, "accessFieldSignature"),
                string(binding, "field"), string(binding, "cell")}) {
            DeclaredField declared = FieldPathSpec.declaredField(candidate);
            if (declared != null && JavaContainerTypes.isMap(
                    declared.type())) {
                return true;
            }
        }
        return false;
    }

    private static void addInputAction(
            JsonArray result, Set<String> represented,
            JsonObject action, InputActionCatalog.Mode mode) {
        dischargeDeferredResolution(action);
        action.addProperty("mode", mode.name());
        represented.add(string(action, "symbol"));
        result.add(action);
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
        return bool(action, "deferredResolution", false);
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

    private static void finalizePendingLocalArrayRoot(JsonObject binding) {
        if (!"LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                .concat("SCHEDULER_DEFINITION_INDEX_V1").equals(
                        string(binding, "consumedFieldRootAuthority"))) {
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
                || !"CALL_RETURN".equals(string(binding, "location"))) {
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
        String type = string(binding, "javaType");
        return type.startsWith("[") || type.endsWith("[]");
    }

    private static List<String> fieldPath(String cell) {
        return FieldPathSpec.path(cell);
    }

    private static MergePlan buildMergePlan(Map<String, Region> regions,
                                            List<JsonObject> edges) {
        List<JsonObject> equalityRelations = new ArrayList<>();
        List<JsonObject> stateMerges = new ArrayList<>();
        for (JsonObject edge : edges) {
            if (!AutomaticRegionEdge.composable(edge)) {
                continue;
            }
            String relation = AutomaticRegionEdge.relation(edge);
            String fromRegion = string(edge, "fromRegion");
            String toRegion = string(edge, "toRegion");
            Endpoint from = producerEndpoint(edge, regions.get(fromRegion));
            Endpoint to = consumerEndpoint(edge, regions.get(toRegion));
            if (from == null || to == null) {
                continue;
            }
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
        for (String delimiter : new String[]{".in.", ".out."}) {
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

    private static Endpoint producerEndpoint(JsonObject edge,
                                             Region region) {
        if (region == null) return null;
        if (!hasCanonicalOutputMetadata(edge)) {
            return region.outputEndpoint(string(edge, "fromPort"), "");
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
                || !outputPort.equals(region.uniqueOutputPort(outputCell))) {
            return null;
        }
        return new Endpoint(outputPort, outputCell);
    }

    private static Endpoint consumerEndpoint(JsonObject edge,
                                             Region region) {
        if (region == null) return null;
        return region.inputEndpoint(
                firstNonBlank(string(edge, "toInputPort"),
                        string(edge, "toPort")),
                string(edge, "toInputCell"));
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
        query.addProperty("goalId", candidate.goal.goalId());
        query.addProperty("regionId", candidate.goal.plan().regionId());
        query.addProperty("regionInstanceId",
                candidate.goal.plan().regionInstanceId());
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
                mergePlan.contextFor(candidate.goal.plan().regionId(),
                        candidate.goal.plan().regionInstanceId()));
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
        String expectedInstance = candidate.goal.plan().regionInstanceId();
        if (expectedInstance.isEmpty()) return null;
        JsonObject selected = null;
        for (JsonObject summary : summaries) {
            if (!candidate.goal.goalId().equals(string(summary, "goalId"))
                    || !candidate.goal.plan().regionId().equals(
                    string(summary, "regionId"))
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
        private static DefinitionIndex from(List<JsonObject> edges) {
            DefinitionIndex result = new DefinitionIndex();
            Set<String> seen = new LinkedHashSet<>();
            Set<String> seenCallReturns = new LinkedHashSet<>();
            for (JsonObject edge : edges) {
                String edgeId = string(edge, "id");
                if (!edgeId.isEmpty()) result.edgeIds.add(edgeId);
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

        private JsonArray sites(String cell,
                                Set<String> allowedMethods,
                                OutputClosureContract.ExecutionScope scope) {
            return filteredSites(byCell.get(cell), allowedMethods, scope);
        }

        private JsonArray returnSites(String callReturnCell,
                                      Set<String> allowedMethods,
                                      OutputClosureContract.ExecutionScope
                                              scope) {
            return filteredSites(byCallReturn.get(callReturnCell),
                    allowedMethods, scope);
        }

        private JsonArray filteredSites(
                List<JsonObject> sites, Set<String> allowedMethods,
                OutputClosureContract.ExecutionScope scope) {
            JsonArray result = new JsonArray();
            if (sites == null) {
                return result;
            }
            for (JsonObject site : sites) {
                String method = string(site, "method");
                String siteId = method + "#u"
                        + integer(site, "unitIndex", -1);
                String edgeId = string(site, "causalEdgeId");
                if (!allowedMethods.contains(method)) {
                    continue;
                }
                if (scope != null
                        && (!scope.branchSites().contains(siteId)
                        || !scope.causalEdgeIds().contains(edgeId))) {
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
        private final Map<String, List<String>> inputPortsByCell =
                new LinkedHashMap<>();
        private final Map<String, String> inputCellByPort =
                new LinkedHashMap<>();
        private final Map<String, List<String>> outputPortsByCell =
                new LinkedHashMap<>();
        private final Map<String, String> outputCellByPort =
                new LinkedHashMap<>();

        private Region(JsonObject row) {
            int schemaVersion = integer(row, "schemaVersion", -1);
            if (schemaVersion != STATIC_REGION_SCHEMA_VERSION) {
                throw new IllegalArgumentException(
                        "symbolic region requires schemaVersion "
                                + STATIC_REGION_SCHEMA_VERSION);
            }
            this.regionId = string(row, "regionId");
            collectPorts(array(row, "symbolicInputs"),
                    inputPortsByCell, inputCellByPort);
            collectPorts(array(row, "outputs"),
                    outputPortsByCell, outputCellByPort);
        }

        private String uniqueOutputPort(String cell) {
            return uniquePort(outputPortsByCell, cell);
        }

        private Endpoint inputEndpoint(String portOrCell, String cellHint) {
            return canonicalEndpoint(portOrCell, cellHint,
                    inputPortsByCell, inputCellByPort);
        }

        private Endpoint outputEndpoint(String portOrCell, String cellHint) {
            return canonicalEndpoint(portOrCell, cellHint,
                    outputPortsByCell, outputCellByPort);
        }

        private static Endpoint canonicalEndpoint(
                String portOrCell, String cellHint,
                Map<String, List<String>> portsByCell,
                Map<String, String> cellByPort) {
            String cell = cellByPort.get(portOrCell);
            if (cell != null) {
                return cellHint.isEmpty() || cellHint.equals(cell)
                        ? new Endpoint(portOrCell, cell) : null;
            }
            cell = firstNonBlank(cellHint, portOrCell);
            String port = uniquePort(portsByCell, cell);
            return port.isEmpty() ? null : new Endpoint(port, cell);
        }

        private static String uniquePort(
                Map<String, List<String>> portsByCell, String cell) {
            List<String> ports = portsByCell.get(safe(cell));
            return ports != null && ports.size() == 1 ? ports.get(0) : "";
        }

        private static void collectPorts(
                JsonArray ports, Map<String, List<String>> portsByCell,
                Map<String, String> cellByPort) {
            for (JsonElement element : ports) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject port = element.getAsJsonObject();
                String id = firstNonBlank(string(port, "portId"),
                        string(port, "symbol"));
                String cell = string(port, "cell");
                if (!id.isEmpty() && !cell.isEmpty()) {
                    add(portsByCell, cell, id);
                    cellByPort.put(id, cell);
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

        private static TargetBranch select(
                String siteId, JsonArray occurrences, boolean required) {
            TargetBranch mismatch = null;
            for (int index = 0; index < occurrences.size(); index++) {
                JsonElement element = occurrences.get(index);
                if (!element.isJsonObject()) continue;
                JsonObject occurrence = element.getAsJsonObject();
                boolean observed = bool(occurrence, "outcome", false);
                int ordinal = integer(occurrence, "occurrence", index + 1);
                TargetBranch selected = new TargetBranch(siteId, ordinal,
                        observed, observed == required ? !observed : required);
                if (observed == required) return selected;
                if (mismatch == null) mismatch = selected;
            }
            return mismatch;
        }

    }

    private static final class Candidate {
        private static final Comparator<Candidate> ORDER =
                Comparator.comparing((Candidate value) -> !value.directed)
                        .thenComparing(value -> !value.ready)
                        .thenComparing(value -> value.target.siteId)
                        .thenComparingInt(value ->
                                value.goal.plan().rootOrdinal())
                        .thenComparing(value ->
                                value.goal.plan().regionInstanceId())
                        .thenComparing(value -> value.goal.goalId());

        private final Goal goal;
        private final JsonArray branches;
        private final TargetBranch target;
        private final boolean directed;
        private final JsonArray inputActions;
        private final boolean ready;

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready) {
            this.goal = goal;
            this.branches = branches;
            this.target = target;
            this.directed = goal.kind()
                    == GoalKind.OUTPUT_RELATION_CLOSURE
                    || !hasRequiredWitness;
            this.inputActions = inputActions;
            this.ready = ready;
        }

        private OutputClosureContract outputContract() {
            return goal.kind() == GoalKind.OUTPUT_RELATION_CLOSURE
                    ? goal.outputClosure() : null;
        }

        private String seedTaskId() {
            String identity = goal.plan().regionInstanceId() + "\n"
                    + goal.goalId() + "\n"
                    + target.siteId + "\n" + target.selectedOccurrence
                    + "\n" + target.observedOutcome
                    + "\n" + target.desiredOutcome;
            return "TASK.SEED." + ArtifactIO.sha256(identity);
        }
    }

    private static final class MergePlan {
        private final Map<String, List<JsonObject>> equalityByInstance;
        private final Map<String, List<JsonObject>> stateByInstance;
        private final Map<String, List<JsonObject>> alternativesByInstance;
        private final Map<String, List<JsonObject>> outboundByInstance;

        private MergePlan(List<JsonObject> equalityRelations,
                          List<JsonObject> stateMerges,
                          List<JsonObject> alternativeWriterGroups) {
            equalityByInstance = indexRelations(equalityRelations, false);
            stateByInstance = indexRelations(stateMerges, true);
            alternativesByInstance = indexAlternatives(
                    alternativeWriterGroups, stateByInstance);
            outboundByInstance = indexOutboundBindings(equalityRelations);
        }

        /**
         * Copies runtime-confirmed protocol equalities onto the producer
         * activation that will own the imported output summary. This is a
         * summary edge, not a READ_FROM edge: serialization may change object
         * identity while preserving the complete endpoint value.
         */
        private JsonArray outboundValueEqualityBindings(
                Goal goal,
                OutputClosureContract outputClosure) {
            String region = goal.plan().regionId();
            String instance = goal.plan().regionInstanceId();

            JsonArray bindings = goal.edgeBindings().deepCopy();
            Set<String> requestedPorts = outputClosure == null
                    ? Collections.<String>emptySet()
                    : outputClosure.outputPorts();

            for (JsonObject normalized : values(
                    outboundByInstance, instance)) {
                String fromPort = string(normalized, "fromOutputPort");
                if (!region.equals(string(normalized, "fromRegion"))
                        || outputClosure != null
                        && !requestedPorts.contains(fromPort)) {
                    continue;
                }
                addUniqueBinding(bindings, normalized);
            }
            return bindings;
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
            return CanonicalJson.render(left).compareTo(
                    CanonicalJson.render(right));
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
            for (JsonObject value : values(
                    equalityByInstance, regionInstanceId)) {
                if (relevant(value, regionId)) {
                    equalityBindings.add(value.deepCopy());
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
            for (JsonObject value : values(
                    stateByInstance, regionInstanceId)) {
                if (relevant(value, regionId)) {
                    states.add(value.deepCopy());
                }
            }
            JsonArray alternatives = new JsonArray();
            for (JsonObject value : values(
                    alternativesByInstance, regionInstanceId)) {
                alternatives.add(value.deepCopy());
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
                    || string(value, "toEndpoint").startsWith(regionId + ".");
        }

        private static Map<String, List<JsonObject>> indexRelations(
                List<JsonObject> relations, boolean heap) {
            Map<String, List<JsonObject>> result = new LinkedHashMap<>();
            for (JsonObject relation : relations) {
                for (Map.Entry<String, JsonObject> selected
                        : selectedByInstance(relation, heap).entrySet()) {
                    add(result, selected.getKey(), selected.getValue());
                }
            }
            return result;
        }

        private static Map<String, List<JsonObject>> indexAlternatives(
                List<JsonObject> groups,
                Map<String, List<JsonObject>> stateIndex) {
            Map<String, List<JsonObject>> result = new LinkedHashMap<>();
            for (JsonObject group : groups) {
                Map<String, JsonArray> alternativesByInstance =
                        new LinkedHashMap<>();
                for (JsonElement element : array(group, "alternatives")) {
                    if (!element.isJsonObject()) continue;
                    for (Map.Entry<String, JsonObject> selected
                            : selectedByInstance(
                            element.getAsJsonObject(), true).entrySet()) {
                        alternativesByInstance.computeIfAbsent(
                                selected.getKey(), ignored -> new JsonArray())
                                .add(selected.getValue());
                    }
                }
                for (Map.Entry<String, JsonArray> selected
                        : alternativesByInstance.entrySet()) {
                    if (selected.getValue().size() == 1) {
                        add(stateIndex, selected.getKey(),
                                selected.getValue().get(0)
                                        .getAsJsonObject());
                    } else {
                        JsonObject copy = group.deepCopy();
                        copy.add("alternatives", selected.getValue());
                        add(result, selected.getKey(), copy);
                    }
                }
            }
            return result;
        }

        private static Map<String, JsonObject> selectedByInstance(
                JsonObject relation, boolean heap) {
            Map<String, JsonArray> bindings = new LinkedHashMap<>();
            for (JsonElement element : array(relation, "runtimeBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (heap && !AutomaticRegionEdge
                        .trustedReadFromEvidence(binding)
                        || !heap && !AutomaticRegionEdge
                        .trustedRuntimeValueEqualityEvidence(binding)) {
                    continue;
                }
                Set<String> instances = new LinkedHashSet<>();
                instances.add(string(binding, "fromRegionInstance"));
                instances.add(string(binding, "toRegionInstance"));
                instances.remove("");
                for (String instance : instances) {
                    bindings.computeIfAbsent(instance,
                            ignored -> new JsonArray())
                            .add(binding.deepCopy());
                }
            }
            Map<String, JsonObject> result = new LinkedHashMap<>();
            for (Map.Entry<String, JsonArray> entry : bindings.entrySet()) {
                JsonObject selected = relation.deepCopy();
                selected.remove("runtimeBindings");
                selected.add("selectedBindings", entry.getValue());
                result.put(entry.getKey(), selected);
            }
            return result;
        }

        private static Map<String, List<JsonObject>> indexOutboundBindings(
                List<JsonObject> relations) {
            Map<String, List<JsonObject>> result = new LinkedHashMap<>();
            for (JsonObject relation : relations) {
                String fromRegion = string(relation, "fromRegion");
                String toRegion = string(relation, "toRegion");
                String fromPort = string(relation, "fromEndpoint");
                String toPort = string(relation, "toEndpoint");
                if (!fromPort.startsWith(fromRegion + ".out.")
                        || !toPort.startsWith(toRegion + ".in.")) {
                    continue;
                }
                for (JsonElement element : array(relation,
                        "runtimeBindings")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject raw = element.getAsJsonObject();
                    String fromInstance = string(raw,
                            "fromRegionInstance");
                    String toInstance = string(raw, "toRegionInstance");
                    if (fromInstance.isEmpty() || toInstance.isEmpty()
                            || !AutomaticRegionEdge
                            .trustedRuntimeValueEqualityEvidence(raw)) {
                        continue;
                    }
                    JsonObject normalized = new JsonObject();
                    normalized.addProperty("schemaVersion", 2);
                    normalized.addProperty("edgeId",
                            string(relation, "edgeId"));
                    normalized.addProperty("evidenceKind",
                            AutomaticRegionEdge.COMPLETE_VALUE_EQUALITY);
                    normalized.addProperty("fromRegion", fromRegion);
                    normalized.addProperty("toRegion", toRegion);
                    normalized.addProperty("fromRegionInstance",
                            fromInstance);
                    normalized.addProperty("toRegionInstance", toInstance);
                    normalized.addProperty("fromOutputPort", fromPort);
                    normalized.addProperty("toInputPort", toPort);
                    normalized.addProperty("fromOutputCell",
                            string(relation, "fromCell"));
                    normalized.addProperty("toInputCell",
                            string(relation, "toCell"));
                    normalized.addProperty("writerEventSeq",
                            longInteger(raw, "writerEventSeq", -1L));
                    normalized.addProperty("readerEventSeq",
                            longInteger(raw, "readerEventSeq", -1L));
                    normalized.addProperty("valueFingerprint",
                            string(raw, "valueFingerprint"));
                    String authority = string(raw,
                            "correlationAuthority");
                    if (!authority.isEmpty()) {
                        normalized.addProperty("correlationAuthority",
                                authority);
                    }
                    add(result, fromInstance, normalized);
                }
            }
            return result;
        }

        private static List<JsonObject> values(
                Map<String, List<JsonObject>> index, String key) {
            List<JsonObject> values = index.get(key);
            return values == null
                    ? Collections.<JsonObject>emptyList() : values;
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
