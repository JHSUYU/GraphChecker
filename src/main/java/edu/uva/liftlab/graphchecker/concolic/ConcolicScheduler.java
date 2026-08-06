package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.SymbolicEnvironment;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

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
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private static final Pattern METHOD_PARAMETER_CELL = Pattern.compile(
            "^(<.+>)\\.param([0-9]+):(.+)$");
    private ConcolicScheduler() {
    }

    public static void main(String[] args) throws Exception {
        Arguments arguments = Arguments.parse(args);
        Result result = schedule(arguments);
        if (result.executionTasks.isEmpty()) {
            throw new IllegalStateException(noCandidateDiagnostic(arguments,
                    readJsonl(arguments.regionPlan)));
        }
    }

    public static Result schedule(Arguments arguments) throws IOException {
        requireFile(arguments.regions, "symbolic regions");
        requireFile(arguments.regionPlan, "region plan");
        requireFile(arguments.edgeValidations, "runtime edge validation");
        requireFile(arguments.refinedGraph, "runtime-refined graph");
        Files.createDirectories(arguments.outputDirectory);

        List<JsonObject> regions = readJsonl(arguments.regions);
        List<JsonObject> regionPlans = readJsonl(arguments.regionPlan);
        List<JsonObject> edges = readJsonl(arguments.edgeValidations);
        List<JsonObject> summaries = arguments.summaries == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.summaries);
        List<JsonObject> refinedGraph = readJsonl(arguments.refinedGraph);
        requireRefinedGraph(refinedGraph);
        DefinitionIndex definitions = DefinitionIndex.from(refinedGraph);
        ProducerOutputProjection producerProjection =
                readProducerProjection(arguments.producerProjection);

        Map<String, Region> regionIndex = new LinkedHashMap<>();
        for (JsonObject row : regions) {
            Region region = new Region(row);
            if (!region.regionId.isEmpty()) {
                regionIndex.put(region.regionId, region);
            }
        }

        MergePlan mergePlan = buildMergePlan(regionIndex, edges);
        List<Candidate> candidates = candidates(arguments, regionPlans,
                regionIndex, definitions, producerProjection);
        Collections.sort(candidates, Candidate.ORDER);

        Result result = new Result();
        for (Candidate candidate : candidates) {
            if (result.executionTasks.size() >= arguments.maxJobs) {
                break;
            }
            OutputClosureContract outputContract = candidate.outputContract();
            JsonObject captured = outputContract != null ? null
                    : exactTargetSummary(candidate, summaries);
            JsonArray edgeBindings = mergePlan
                    .outboundValueEqualityBindings(candidate.goal,
                            outputContract, candidate.projection);
            ExecutionTask scheduled = candidate.projection == null
                    ? ExecutionTask.create(candidate.goal,
                    candidate.seedTaskId(), candidate.inputActions,
                    candidate.branches, edgeBindings,
                    LoopBoundPolicy.cfgBackedges(
                            arguments.maxLoopIterations), candidate.ready)
                    : ExecutionTask.createProjectedOutput(candidate.goal,
                    candidate.seedTaskId(), candidate.inputActions,
                    candidate.branches, edgeBindings,
                    LoopBoundPolicy.cfgBackedges(
                            arguments.maxLoopIterations), candidate.ready,
                    outputContract, candidate.occurrenceCatalog,
                    candidate.projection.json());
            JsonObject executionTask = scheduled.json();
            if (candidate.goal.kind().capturesTargetReach()) {
                JsonObject stop = new JsonObject();
                stop.addProperty("siteId", candidate.target.siteId);
                stop.addProperty("occurrence",
                        candidate.target.selectedOccurrence);
                executionTask.add("stopAfterBranch", stop);
            }

            if (captured != null && outputContract == null) {
                JsonObject query = branchQuery(candidate, captured,
                        mergePlan);
                result.queries.add(query);
            }
            result.executionTasks.add(executionTask);
        }
        if (producerProjection != null
                && result.executionTasks.size() != 1) {
            throw new IllegalStateException("producer projection must select "
                    + "exactly one execution task; found "
                    + result.executionTasks.size());
        }
        writeJsonl(arguments.outputDirectory.resolve(
                        "execution_task_plan.jsonl"),
                result.executionTasks);
        writeJsonl(arguments.outputDirectory.resolve(
                        "branch_queries.jsonl"),
                result.queries);
        return result;
    }

    private static List<Candidate> candidates(Arguments arguments,
                                              List<JsonObject> regionPlans,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions,
                                              ProducerOutputProjection
                                                      producerProjection) {
        List<Candidate> result = new ArrayList<>();
        for (JsonObject encoded : regionPlans) {
            RegionInstancePlan plan = RegionInstancePlan.decode(encoded);
            Region region = regions.get(plan.regionId());
            if (region == null) {
                continue;
            }
            if (!arguments.regionInstanceId.isEmpty()
                    && !plan.containsRegionInstance(
                    arguments.regionInstanceId)) {
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
                appendGoalCandidates(arguments, result, goal, definitions,
                        producerProjection);
            }
        }
        return result;
    }

    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result,
            Goal goal, DefinitionIndex definitions,
            ProducerOutputProjection producerProjection) {
            Set<String> definitionMethods =
                    goal.runtimeDefinitionMethods();
            if (goal.kind().capturesOutputRelation()) {
                if (!"READY".equals(goal.admissionState())) {
                    return;
                }
                OutputClosureContract outputClosure = goal.outputClosure();
                if (outputClosure == null) {
                    return;
                }
                ProjectedProducer projected = producerProjection == null
                        ? null : ProjectedProducer.create(goal,
                        producerProjection);
                if (projected != null) {
                    outputClosure = projected.outputClosure;
                }
                JsonArray symbolize = projected == null
                        ? goal.symbolize() : projected.symbolize;
                JsonArray inputActions = materializationPlan(
                        goal, symbolize, definitions, definitionMethods,
                        outputClosure);
                JsonArray branches = projected == null
                        ? goal.branches() : projected.branches;
                result.add(new Candidate(goal, branches,
                        TargetBranch.outputCapture(), true,
                        inputActions, true,
                        goal.executionRegionInstanceId(),
                        new JsonObject(), producerProjection,
                        outputClosure, projected == null
                        ? goal.occurrenceInstantiationCatalog()
                        : projected.occurrenceCatalog));
                return;
            }
            if (producerProjection != null) {
                throw new IllegalArgumentException("producer projection "
                        + "cannot select a target reach goal");
            }
            goal.rejectOutputClosure();
            JsonArray branches = goal.branches();
            boolean hasFailureTarget = false;
            for (JsonElement element : branches) {
                if (element.isJsonObject()
                        && bool(element.getAsJsonObject(),
                        "failureTarget", false)) {
                    hasFailureTarget = true;
                    break;
                }
            }
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
                if (arguments.targetSite.isEmpty() && hasFailureTarget
                        && !bool(branch, "failureTarget", false)) {
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
                result.add(new Candidate(goal,
                        targetReachBranchSlice(branches, target), target,
                        hasWitness, inputActions, true,
                        targetQueryInstance(arguments, goal),
                        targetQueryOccurrence(arguments, goal), null,
                        null, goal.occurrenceInstantiationCatalog()));
            }
    }

    private static String targetQueryInstance(
            Arguments arguments, Goal goal) {
        return arguments.regionInstanceId.isEmpty()
                ? goal.executionRegionInstanceId()
                : arguments.regionInstanceId;
    }

    /**
     * Selects trace evidence for query instantiation only.  The VM task keeps
     * the canonical semantic path seed; this row later alpha-renames that
     * relation into the selected exact consumer occurrence without encoding
     * an invocation ordinal into cross-execution replay.
     */
    private static JsonObject targetQueryOccurrence(
            Arguments arguments, Goal goal) {
        String selected = targetQueryInstance(arguments, goal);
        JsonObject catalog = goal.occurrenceInstantiationCatalog();
        JsonObject match = null;
        for (JsonElement element : array(catalog, "occurrences")) {
            if (!element.isJsonObject()) continue;
            JsonObject occurrence = element.getAsJsonObject();
            if (!selected.equals(string(occurrence,
                    "regionInstanceId"))) {
                continue;
            }
            if (match != null) {
                throw new IllegalArgumentException(
                        "ambiguous selected target occurrence " + selected);
            }
            match = occurrence;
        }
        if (match == null) {
            throw new IllegalArgumentException(
                    "logical target goal has no selected occurrence "
                            + selected);
        }
        JsonObject result = match.deepCopy();
        Set<String> exactInputs = new LinkedHashSet<>();
        for (JsonElement element : array(result, "inputPortMap")) {
            if (element.isJsonObject()) {
                String port = string(element.getAsJsonObject(),
                        "exactPort");
                if (!port.isEmpty()) exactInputs.add(port);
            }
        }
        Set<String> demandedBindingIds = new LinkedHashSet<>();
        for (JsonElement element : goal.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!selected.equals(string(binding, "toRegionInstance"))
                    || !exactInputs.contains(string(binding,
                    "toInputPort"))) {
                continue;
            }
            String edgeId = string(binding, "edgeId");
            if (edgeId.isEmpty()) {
                throw new IllegalArgumentException(
                        "selected target binding has no edgeId: "
                                + selected);
            }
            demandedBindingIds.add(edgeId);
        }
        JsonArray ledger = new JsonArray();
        for (String edgeId : demandedBindingIds) ledger.add(edgeId);
        result.add("bindingIds", ledger);
        return result;
    }

    /**
     * A target task solves one failure-directed branch.  Other observed
     * decisions remain in the replay prefix, but are assumptions rather than
     * independent flip targets.  This keeps enabler constraints without
     * reopening every branch in a long-running thread activation.
     */
    private static JsonArray targetReachBranchSlice(
            JsonArray branches, TargetBranch target) {
        JsonArray result = new JsonArray();
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject().deepCopy();
            if (target.siteId.equals(string(branch, "siteId"))) {
                branch.addProperty("policy", "EXPLORE");
                branch.addProperty("policyReason",
                        "TARGET_REACH_SELECTED_FAILURE_BRANCH");
            } else if ("EXPLORE".equals(string(branch, "policy"))) {
                branch.addProperty("policy", "PATH_ASSUMPTION");
                branch.addProperty("policyReason",
                        "TARGET_REACH_PREFIX_CONTEXT");
            }
            result.add(branch);
        }
        return result;
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
        for (JsonElement element : sourceActions) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            JsonObject binding = action.deepCopy();
            String location = string(action, "location");
            String cell = string(action, "cell");
            String dependencyRole = DependencyRole.normalize(
                    action.get("dependencyRole"));
            if (concreteOnlyInput(action)
                    || !DependencyRole.VALUE_FRONTIER.equals(
                    dependencyRole)) {
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            boolean boundedContainerState =
                    supportedBoundedContainerState(action, location, cell);
            if ((!supportedSymbolicLeaf(action, location, cell)
                    && !boundedContainerState)
                    || staticSyntheticConstant(action)) {
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            String structureControl = structureControlReason(action);
            if (!structureControl.isEmpty()) {
                // These values describe the concrete execution structure
                // selected for replay.  They may remain in path conditions,
                // but changing them would vary dispatch/container shape
                // rather than a failure-relevant value leaf.
                binding.addProperty("symbolicDemand",
                        "CONCRETE_STRUCTURE_CONTROL");
                binding.addProperty("structureControlReason",
                        structureControl);
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            if ("PROTOCOL_ARGUMENT".equals(location)
                    && !trustedIncomingProtocolBinding(
                    goal, string(action, "symbol"))) {
                // A consumer argument is a materialized symbolic expression
                // only when the existing edge contract binds it to a
                // producer output.  Otherwise it would become an unrelated
                // new solver leaf.
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            if (scope != null && !scope.inputPorts().contains(
                    string(action, "symbol"))) {
                // The output closure is the authority for symbolic demand.
                // Keep the declaration for rooted output capture, but do not
                // let unrelated region live-ins enter the VM/SMT state.
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            boolean vmIntrinsic = verifiedVmIntrinsicPlaceholder(action,
                    location, cell);
            if (action.has("observed")
                    && !bool(action, "observed", false)
                    && !bool(action, "deferredResolution", false)
                    && !vmIntrinsic) {
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
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
                if (!boundedContainerState
                        && JavaPrimitiveBoxing.deterministicValueOfReturn(
                        cell)) {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
                if (!boundedContainerState
                        && JavaContainerTypes.symbolicResultReturn(cell)) {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
                if (!boundedContainerState
                        && structuralContainerReferenceReturn(action)) {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
                JsonArray sites = definitions.returnSites(cell,
                        scope == null ? regionMethods : scope.methods(),
                        scope);
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
                    addInputAction(result, represented, localBinding,
                            InputActionCatalog.Mode.SYMBOLIC);
                }
                continue;
            } else if (vmIntrinsic) {
                binding.addProperty("bindingMode",
                        "VM_INTRINSIC_PLACEHOLDER");
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
            } else if ("REGION_LIVE_IN".equals(location)
                    || "PROTOCOL_RETURN".equals(location)) {
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
                    if (sites.size() == 0) {
                        addInputAction(result, represented, binding,
                                InputActionCatalog.Mode.CONCRETE);
                        continue;
                    }
                } else {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
            } else if ("PROTOCOL_ARGUMENT".equals(location)) {
                Matcher parameter = METHOD_PARAMETER_CELL.matcher(cell);
                int argumentIndex = integer(action, "serverParameterIndex",
                        integer(action, "argumentIndex", -1));
                if (!parameter.matches()
                        || argumentIndex < 0
                        || argumentIndex != Integer.parseInt(
                        parameter.group(2))) {
                    addInputAction(result, represented, binding,
                            InputActionCatalog.Mode.CONCRETE);
                    continue;
                }
                binding.addProperty("bindingMode", "METHOD_ARGUMENT");
                binding.addProperty("method", parameter.group(1));
                binding.addProperty("index", argumentIndex);
                binding.addProperty("javaType", parameter.group(3));
            } else {
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
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

    private static boolean concreteOnlyInput(JsonObject action) {
        String demand = string(action, "symbolicDemand");
        return bool(action, "captureRootOnly", false)
                || bool(action, "loopControlOnly", false)
                || bool(action, "controlOnly", false)
                || bool(action, "pathAssumptionOnly", false)
                || demand.startsWith("CONCRETE_");
    }

    /**
     * Admits only values for which the current VM/SMT contract has a compact
     * scalar representation.  Reference owners and containers remain
     * concrete; their exact primitive/String leaves are separate actions.
     */
    private static boolean supportedSymbolicLeaf(
            JsonObject action, String location, String cell) {
        String javaType = string(action, "javaType");
        if ("PROTOCOL_ARGUMENT".equals(location)) {
            Matcher parameter = METHOD_PARAMETER_CELL.matcher(cell);
            if (parameter.matches()) javaType = parameter.group(3);
        }
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                javaType);
        boolean supportedScalar = (descriptor.length() == 1
                && "ZBCSIJFD".contains(descriptor))
                || "Ljava/lang/String;".equals(descriptor);
        boolean supportedPrimitiveArray = false;
        int component = 0;
        while (component < descriptor.length()
                && descriptor.charAt(component) == '[') {
            component++;
        }
        if (component > 0 && component + 1 == descriptor.length()) {
            supportedPrimitiveArray = "ZBCSIJFD".indexOf(
                    descriptor.charAt(component)) >= 0;
        }
        if (!supportedScalar && !supportedPrimitiveArray) return false;

        if (!("RECEIVER_FIELD".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "HEAP_OBJECT_FIELD".equals(location))) {
            return true;
        }

        List<String> path = exactActionFieldPath(action, cell);
        if (path.isEmpty()) return false;
        FieldPathSpec.DeclaredField leaf = declaredLeaf(action, cell);
        return leaf != null
                && leaf.name().equals(path.get(path.size() - 1))
                && descriptor.equals(
                JavaPrimitiveSmtSemantics.javaTypeDescriptor(leaf.type()));
    }

    /**
     * Admits a container identity only as a bounded relational state port.
     * The marker is authored by the target-first exact-port closure; it is
     * never inferred merely from a reference type. Container cardinality,
     * traversal and owner identity therefore stay concrete while demanded
     * slot relations may cross region boundaries.
     */
    private static boolean supportedBoundedContainerState(
            JsonObject action, String location, String cell) {
        if (!"BOUNDED_CONTAINER_STATE".equals(
                string(action, "symbolicDemand"))) {
            return false;
        }
        String javaType = string(action, "javaType");
        if ("PROTOCOL_ARGUMENT".equals(location)) {
            Matcher parameter = METHOD_PARAMETER_CELL.matcher(cell);
            if (parameter.matches()) javaType = parameter.group(3);
        }
        if (JavaContainerTypes.shape(javaType)
                == JavaContainerTypes.Shape.NONE) {
            return false;
        }
        return "ARGUMENT".equals(location)
                || "RECEIVER_FIELD".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "HEAP_OBJECT_FIELD".equals(location)
                || "CALL_RETURN".equals(location)
                || "REGION_LIVE_IN".equals(location)
                || "PROTOCOL_RETURN".equals(location)
                || "PROTOCOL_ARGUMENT".equals(location);
    }

    private static List<String> exactActionFieldPath(
            JsonObject action, String cell) {
        List<List<String>> paths = FieldPathSpec.paths(action, "fieldPaths");
        if (action.has("fieldPaths")) {
            return paths.size() == 1
                    ? paths.get(0) : Collections.<String>emptyList();
        }
        List<String> path = FieldPathSpec.stringArray(action, "fieldPath");
        if (action.has("fieldPath")) return path;
        return FieldPathSpec.path(cell);
    }

    private static FieldPathSpec.DeclaredField declaredLeaf(
            JsonObject action, String cell) {
        for (String signature : new String[]{
                string(action, "leafFieldSignature"),
                string(action, "accessFieldSignature"), cell}) {
            FieldPathSpec.DeclaredField declared =
                    FieldPathSpec.declaredField(signature);
            if (declared != null) return declared;
        }
        return null;
    }

    private static boolean staticSyntheticConstant(JsonObject action) {
        if (bool(action, "staticFinal", false)
                || bool(action, "immutable", false)
                || bool(action, "syntheticConstant", false)
                || bool(action, "constructorOnly", false)
                || "CONSTANT".equals(string(action, "sourceKind"))) {
            return true;
        }
        List<String> path = exactActionFieldPath(action,
                string(action, "cell"));
        return !path.isEmpty()
                && "$assertionsDisabled".equals(
                path.get(path.size() - 1));
    }

    /**
     * Classifies compiler/runtime structure projections, not application
     * values.  The checks use Java-level contracts rather than project field
     * names: compiler switch-table conventions, Enum.ordinal(), and exact
     * zero-argument container-cardinality accessors.  In the bounded model
     * these values replay the observed dispatch/container shape and are not
     * independent symbolic solver dimensions.
     */
    private static String structureControlReason(JsonObject action) {
        List<String> path = exactActionFieldPath(action,
                string(action, "cell"));
        String leaf = path.isEmpty() ? "" : path.get(path.size() - 1);
        if (compilerSwitchDispatchTable(leaf)) {
            return "COMPILER_SWITCH_DISPATCH_TABLE";
        }
        if (enumOrdinalProjection(action)) {
            return "ENUM_DISPATCH_ORDINAL";
        }
        if (structuralContainerCardinality(action, leaf)) {
            return "FIXED_CONTAINER_CARDINALITY";
        }
        return "";
    }

    private static boolean compilerSwitchDispatchTable(String leaf) {
        // javac and Eclipse ECJ use these two synthetic-field conventions.
        return leaf.startsWith("$SwitchMap$")
                || leaf.startsWith("$SWITCH_TABLE$");
    }

    private static boolean enumOrdinalProjection(JsonObject action) {
        for (String signature : accessorSignatures(action)) {
            if ("<java.lang.Enum: int ordinal()>".equals(signature)) {
                return true;
            }
        }
        return false;
    }

    private static boolean structuralContainerCardinality(
            JsonObject action, String leaf) {
        for (String signature : accessorSignatures(action)) {
            if (JavaContainerTypes.structuralCardinalityOperation(
                    signature)) {
                return true;
            }
            // Custom collection implementations commonly expose their exact
            // backing cardinality through a direct size() accessor.  Require
            // both sides of that accessor contract so an unrelated method or
            // application field containing "size" is not classified here.
            if ("size".equals(leaf)
                    && signature.matches("^<[^:>]+: int size\\(\\)>$")) {
                return true;
            }
        }
        if (!"size".equals(leaf)
                || !"I".equals(JavaPrimitiveSmtSemantics
                .javaTypeDescriptor(string(action, "javaType")))) {
            return false;
        }
        // A direct read of an owner's exact `int size` backing field is the
        // same cardinality projection even when no accessor call is present.
        FieldPathSpec.DeclaredField declared = declaredLeaf(action,
                string(action, "cell"));
        return declared != null && "size".equals(declared.name())
                && "I".equals(JavaPrimitiveSmtSemantics
                .javaTypeDescriptor(declared.type()));
    }

    private static List<String> accessorSignatures(JsonObject action) {
        List<String> result = new ArrayList<>();
        for (String field : new String[]{"declaredCallee",
                "accessorDeclaredCallee", "implementationMethod",
                "accessorImplementationMethod"}) {
            String signature = string(action, field);
            if (!signature.isEmpty() && !result.contains(signature)) {
                result.add(signature);
            }
        }
        JsonObject materialization = object(action, "materialization");
        for (String field : new String[]{"declaredCallee",
                "implementationMethod"}) {
            String signature = string(materialization, field);
            if (!signature.isEmpty() && !result.contains(signature)) {
                result.add(signature);
            }
        }
        return result;
    }

    private static boolean trustedIncomingProtocolBinding(
            Goal goal, String canonicalInput) {
        Set<String> acceptedPorts = new LinkedHashSet<>();
        acceptedPorts.add(canonicalInput);
        String instance = goal.executionRegionInstanceId();
        JsonObject catalog = goal.occurrenceInstantiationCatalog();
        for (JsonElement occurrenceElement : array(catalog,
                "occurrences")) {
            if (!occurrenceElement.isJsonObject()) continue;
            JsonObject occurrence = occurrenceElement.getAsJsonObject();
            if (!instance.equals(string(occurrence,
                    "regionInstanceId"))) {
                continue;
            }
            for (JsonElement mappingElement : array(occurrence,
                    "inputPortMap")) {
                if (!mappingElement.isJsonObject()) continue;
                JsonObject mapping = mappingElement.getAsJsonObject();
                if (canonicalInput.equals(string(mapping,
                        "canonicalPort"))) {
                    acceptedPorts.add(string(mapping, "exactPort"));
                }
            }
        }
        acceptedPorts.remove("");
        for (JsonElement element : goal.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (instance.equals(string(binding, "toRegionInstance"))
                    && acceptedPorts.contains(string(binding,
                    "toInputPort"))
                    && AutomaticRegionEdge
                    .trustedRuntimeValueEqualityBinding(binding)) {
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

    private static boolean validFieldPaths(JsonObject action) {
        return FieldPathSpec.hasNonEmptyPaths(action, "fieldPaths");
    }

    static boolean structuralContainerReferenceReturn(JsonObject action) {
        if (!"CALL_RETURN".equals(string(action, "location"))
                || !"OPAQUE_CALL".equals(string(action, "sourceKind"))) {
            return false;
        }
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                string(action, "javaType"));
        if (!(descriptor.startsWith("L") || descriptor.startsWith("["))) {
            return false;
        }
        String cell = string(action, "cell");
        int separator = cell.indexOf(':');
        if (!cell.startsWith("<") || separator <= 1) {
            return false;
        }
        return JavaContainerTypes.structuralTraversalOwner(
                cell.substring(1, separator).trim());
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
        return region.outputEndpoint(string(edge, "fromPort"), "");
    }

    private static Endpoint consumerEndpoint(JsonObject edge,
                                             Region region) {
        if (region == null) return null;
        return region.inputEndpoint(
                firstNonBlank(string(edge, "toInputPort"),
                        string(edge, "toPort")),
                string(edge, "toInputCell"));
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
                candidate.queryRegionInstanceId);
        query.addProperty("canonicalRegionInstanceId",
                candidate.goal.executionRegionInstanceId());
        query.add("selectedTargetOccurrence",
                candidate.queryOccurrence.deepCopy());
        query.addProperty("targetSiteId", candidate.target.siteId);
        try {
            BranchReplayContract contract;
            boolean seedContextOnly = false;
            try {
                contract = BranchReplayContract.fromSummary(summary,
                    candidate.target.siteId,
                    candidate.target.selectedOccurrence);
                if (contract.source().isPcPredicateDecision()
                        || contract.source().sourceTakenOutcome()
                        != candidate.target.observedOutcome
                        || contract.requiredTakenOutcome()
                        != candidate.target.desiredOutcome) {
                    throw new IllegalArgumentException(
                            "captured branch polarity differs from selection");
                }
            } catch (IllegalArgumentException noDirectTargetWitness) {
                contract = latestTargetSeedDecision(candidate, summary);
                seedContextOnly = true;
            }
            contract.addTo(query);
            query.addProperty("readyForSolver", true);
            if (seedContextOnly) {
                query.addProperty("seedContextOnly", true);
            }
        } catch (IllegalArgumentException incompleteWitness) {
            query.addProperty("readyForSolver", false);
            query.addProperty("blocker", incompleteWitness.getMessage());
        }
        query.add("symbolicContext",
                mergePlan.contextFor(candidate.goal.plan().regionId(),
                        candidate.queryRegionInstanceId,
                        candidate.queryOccurrence));
        return query;
    }

    /**
     * Target closure starts from the imported seed path, not from one
     * privileged Jimple branch. A lowered compound guard may therefore use
     * its latest observed PC decision solely to carry replay/context schema
     * until the target path set is closed.
     */
    private static BranchReplayContract latestTargetSeedDecision(
            Candidate candidate, JsonObject summary) {
        Set<String> sites = new LinkedHashSet<>();
        for (JsonElement element : candidate.branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if ("EXPLORE".equals(string(branch, "policy"))) {
                sites.add(string(branch, "siteId"));
            }
        }
        List<SummaryBranchMapping> mappings =
                SummaryBranchMapping.fromSummary(summary);
        SummaryBranchMapping selected = null;
        for (SummaryBranchMapping mapping : mappings) {
            if (!mapping.isWitnessed() || !mapping.isExplore()
                    || !sites.contains(mapping.siteId())) {
                continue;
            }
            if (selected == null || mapping.summaryPcIndex()
                    > selected.summaryPcIndex()) {
                selected = mapping;
            }
        }
        if (selected == null) {
            throw new IllegalArgumentException(
                    "target seed path has no solver decision");
        }
        return BranchReplayContract.fromSummary(summary, mappings, selected);
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
        String expectedInstance = candidate.goal.executionRegionInstanceId();
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

    private static ProducerOutputProjection readProducerProjection(Path path)
            throws IOException {
        if (path == null) return null;
        requireFile(path, "producer output projection");
        List<JsonObject> rows = ArtifactIO.readJsonl(path);
        if (rows.size() != 1) {
            throw new IOException("producer output projection must contain "
                    + "exactly one row; found " + rows.size());
        }
        return ProducerOutputProjection.decode(rows.get(0));
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

    private static void requireRefinedGraph(List<JsonObject> rows) {
        if (rows.isEmpty()) {
            throw new IllegalArgumentException(
                    "runtime-refined graph must not be empty");
        }
        for (JsonObject row : rows) {
            if (integer(row, "schemaVersion", -1) != 3
                    || integer(row, "refinementSchemaVersion", -1) != 1
                    || !"RUNTIME_REFINED_DATAFLOW".equals(
                    string(row, "graphKind"))) {
                throw new IllegalArgumentException(
                        "scheduler accepts only the runtime-refined graph");
            }
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
        private final Map<String, List<JsonObject>> byCell =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> byCallReturn =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> guardSitesByInputCell =
                new LinkedHashMap<>();
        private static DefinitionIndex from(List<JsonObject> edges) {
            DefinitionIndex result = new DefinitionIndex();
            Set<String> seen = new LinkedHashSet<>();
            Set<String> seenCallReturns = new LinkedHashSet<>();
            for (JsonObject edge : edges) {
                String edgeId = string(edge, "id");
                String source = string(edge, "fromCell");
                if ("GUARD".equals(string(edge, "transferKind"))) {
                    String guardSite = string(edge, "siteId");
                    if (!source.isEmpty() && !guardSite.isEmpty()) {
                        result.guardSitesByInputCell.computeIfAbsent(source,
                                ignored -> new LinkedHashSet<>())
                                .add(guardSite);
                    }
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
                if (!edgeId.isEmpty()) {
                    site.addProperty("causalEdgeId", edgeId);
                }
                if (seen.add(key)) {
                    result.byCell.computeIfAbsent(cell,
                            ignored -> new ArrayList<>()).add(site);
                }

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
            return filteredSites(byCell.get(cell), allowedMethods, scope,
                    false);
        }

        private JsonArray returnSites(String callReturnCell,
                                      Set<String> allowedMethods,
                                      OutputClosureContract.ExecutionScope
                                              scope) {
            return filteredSites(byCallReturn.get(callReturnCell),
                    allowedMethods, scope,
                    MaterializationSpec.repeatedPrimitiveAccessorReturn(
                            callReturnCell));
        }

        private JsonArray filteredSites(
                List<JsonObject> sites, Set<String> allowedMethods,
                OutputClosureContract.ExecutionScope scope,
                boolean includeGuardDefinitions) {
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
                        && !scope.staticSites().contains(siteId)
                        && (!scope.branchSites().contains(siteId)
                        || !scope.causalEdgeIds().contains(edgeId))
                        && (!includeGuardDefinitions
                        || Collections.disjoint(scope.branchSites(),
                        guardSitesByInputCell.getOrDefault(
                                method + "::" + string(site, "local"),
                                Collections.<String>emptySet())))) {
                    continue;
                }
                result.add(site.deepCopy());
            }
            return result;
        }

    }

    private static final class Region {
        private static final int STATIC_REGION_SCHEMA_VERSION = 3;
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

    /**
     * One internally consistent view of a target-first producer task.
     * Output members, inputs, guards, exact edges and occurrence adapters are
     * projected together; no layer retains an unrelated placement edge.
     */
    private static final class ProjectedProducer {
        private final OutputClosureContract outputClosure;
        private final JsonArray symbolize;
        private final JsonArray branches;
        private final JsonObject occurrenceCatalog;

        private ProjectedProducer(OutputClosureContract outputClosure,
                                  JsonArray symbolize,
                                  JsonArray branches,
                                  JsonObject occurrenceCatalog) {
            this.outputClosure = outputClosure;
            this.symbolize = symbolize;
            this.branches = branches;
            this.occurrenceCatalog = occurrenceCatalog;
        }

        private static ProjectedProducer create(
                Goal goal, ProducerOutputProjection projection) {
            projection.requireMatches(goal);
            OutputClosureContract closure = projectClosure(goal,
                    projection);
            JsonArray symbolize = projectSymbolize(goal,
                    closure.executionScope().inputPorts());
            JsonArray branches = projectBranches(goal, closure,
                    closure.executionScope().branchSites());
            JsonObject catalog = projectOccurrenceCatalog(goal, projection,
                    closure.executionScope().inputPorts());
            return new ProjectedProducer(closure, symbolize, branches,
                    catalog);
        }

        private static OutputClosureContract projectClosure(
                Goal goal, ProducerOutputProjection projection) {
            OutputClosureContract original = goal.outputClosure();
            if (original == null) {
                throw new IllegalArgumentException(
                        "producer projection requires output closure");
            }
            JsonObject envelope = original.toJson();
            JsonArray members = new JsonArray();
            Set<String> found = new LinkedHashSet<>();
            Set<String> causalIds = new LinkedHashSet<>();
            for (JsonElement element : array(envelope, "members")) {
                if (!element.isJsonObject()) continue;
                JsonObject member = element.getAsJsonObject().deepCopy();
                String port = string(object(member, "output"), "portId");
                if (!projection.outputPorts().contains(port)) continue;
                found.add(port);
                JsonObject slice = object(member, "slice");
                JsonArray selectedIds = new JsonArray();
                for (JsonElement id : array(slice, "causalEdgeIds")) {
                    if (id.isJsonPrimitive()
                            && projection.edgeIds().contains(
                            id.getAsString())) {
                        selectedIds.add(id.getAsString());
                        causalIds.add(id.getAsString());
                    }
                }
                if (selectedIds.size() == 0) {
                    throw new IllegalArgumentException("selected output has "
                            + "no exact projected causal edge: " + port);
                }
                slice.add("causalEdgeIds", selectedIds);
                member.add("slice", slice);
                members.add(member);
            }
            if (!found.equals(projection.outputPorts())) {
                throw new IllegalArgumentException("producer projection "
                        + "references output outside closure: expected="
                        + projection.outputPorts() + "; found=" + found);
            }
            JsonArray edges = new JsonArray();
            Set<String> foundEdges = new LinkedHashSet<>();
            for (JsonElement element : array(envelope, "causalEdges")) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                String id = string(edge, "edgeId");
                if (causalIds.contains(id)) {
                    edges.add(edge.deepCopy());
                    foundEdges.add(id);
                }
            }
            if (!foundEdges.equals(causalIds)) {
                throw new IllegalArgumentException("projected output member "
                        + "cites an absent causal edge");
            }
            envelope.add("members", members);
            envelope.add("causalEdges", edges);
            return edu.uva.liftlab.graphchecker.contract.OutputClosureCodec
                    .decodeEnvelope(envelope);
        }

        private static JsonArray projectSymbolize(Goal goal,
                                                  Set<String> inputPorts) {
            JsonArray result = new JsonArray();
            Set<String> found = new LinkedHashSet<>();
            for (JsonElement element : goal.symbolize()) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                String port = string(action, "symbol");
                if (inputPorts.contains(port)) {
                    result.add(action.deepCopy());
                    found.add(port);
                }
            }
            if (!found.equals(inputPorts)) {
                Set<String> missing = new LinkedHashSet<>(inputPorts);
                missing.removeAll(found);
                throw new IllegalArgumentException("projected output inputs "
                        + "have no dependency actions: " + missing);
            }
            return result;
        }

        private static JsonArray projectBranches(
                Goal goal, OutputClosureContract closure,
                Set<String> branchSites) {
            Map<String, JsonObject> exactReplay = new LinkedHashMap<>();
            for (OutputClosureContract.Member member : closure.members()) {
                JsonArray replay = member.slice().has("branchReplay")
                        ? member.slice().getAsJsonArray("branchReplay")
                        : new JsonArray();
                for (JsonElement item : replay) {
                    if (!item.isJsonObject()) {
                        throw new IllegalArgumentException(
                                "branchReplay must contain objects");
                    }
                    JsonObject branch = item.getAsJsonObject();
                    String site = string(branch, "siteId");
                    JsonObject prior = exactReplay.putIfAbsent(site,
                            branch.deepCopy());
                    if (site.isEmpty() || prior != null
                            && !CanonicalJson.render(prior).equals(
                            CanonicalJson.render(branch))) {
                        throw new IllegalArgumentException(
                                "conflicting exact branch replay for "
                                        + site);
                    }
                }
            }
            JsonArray result = new JsonArray();
            Set<String> found = new LinkedHashSet<>();
            for (JsonElement element : goal.branches()) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                String site = string(branch, "siteId");
                if (branchSites.contains(site)) {
                    JsonObject exact = exactReplay.get(site);
                    result.add(exact == null ? branch.deepCopy()
                            : exact.deepCopy());
                    found.add(site);
                }
            }
            if (!found.containsAll(exactReplay.keySet())) {
                Set<String> missing = new LinkedHashSet<>(
                        exactReplay.keySet());
                missing.removeAll(found);
                throw new IllegalArgumentException(
                        "exact branch replay has no goal policy: "
                                + missing);
            }
            return result;
        }

        private static JsonObject projectOccurrenceCatalog(
                Goal goal, ProducerOutputProjection projection,
                Set<String> inputPorts) {
            JsonObject original = goal.occurrenceInstantiationCatalog();
            String canonical = string(original,
                    "canonicalRegionInstanceId");
            Map<String, JsonObject> bindingById = new LinkedHashMap<>();
            Set<String> touchedInstances = new LinkedHashSet<>();
            for (JsonElement element : goal.edgeBindings()) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                String id = string(binding, "edgeId");
                if (!projection.edgeIds().contains(id)) continue;
                if (!AutomaticRegionEdge
                        .trustedRuntimeCompositionBinding(binding)) {
                    throw new IllegalArgumentException("projected edge is "
                            + "not trusted runtime evidence: " + id);
                }
                if (bindingById.putIfAbsent(id, binding) != null) {
                    throw new IllegalArgumentException(
                            "duplicate projected edge " + id);
                }
                touchedInstances.add(string(binding,
                        "fromRegionInstance"));
                touchedInstances.add(string(binding, "toRegionInstance"));
            }
            if (!bindingById.keySet().equals(projection.edgeIds())) {
                Set<String> missing = new LinkedHashSet<>(
                        projection.edgeIds());
                missing.removeAll(bindingById.keySet());
                throw new IllegalArgumentException("projected edges are "
                        + "absent from goal ledger: " + missing);
            }

            JsonObject result = original.deepCopy();
            JsonArray occurrences = new JsonArray();
            Set<String> representedEdges = new LinkedHashSet<>();
            Set<String> representedInstances = new LinkedHashSet<>();
            for (JsonElement element : array(original, "occurrences")) {
                if (!element.isJsonObject()) continue;
                JsonObject occurrence = element.getAsJsonObject();
                String instance = string(occurrence, "regionInstanceId");
                if (!canonical.equals(instance)
                        && !touchedInstances.contains(instance)) {
                    continue;
                }
                JsonObject selected = occurrence.deepCopy();
                selected.add("inputPortMap", projectPortMap(occurrence,
                        "inputPortMap", inputPorts));
                selected.add("outputPortMap", projectPortMap(occurrence,
                        "outputPortMap", projection.outputPorts()));
                JsonArray ids = new JsonArray();
                for (JsonElement id : array(occurrence, "bindingIds")) {
                    if (id.isJsonPrimitive()
                            && projection.edgeIds().contains(
                            id.getAsString())) {
                        ids.add(id.getAsString());
                        representedEdges.add(id.getAsString());
                    }
                }
                selected.add("bindingIds", ids);
                occurrences.add(selected);
                representedInstances.add(instance);
            }
            if (!representedInstances.contains(canonical)
                    || !representedEdges.equals(projection.edgeIds())) {
                Set<String> missing = new LinkedHashSet<>(
                        projection.edgeIds());
                missing.removeAll(representedEdges);
                throw new IllegalArgumentException("projected occurrence "
                        + "ledger is incomplete; missingEdges=" + missing);
            }
            result.add("occurrences", occurrences);
            return result;
        }

        private static JsonArray projectPortMap(JsonObject occurrence,
                                                String field,
                                                Set<String> canonicalPorts) {
            JsonArray result = new JsonArray();
            Set<String> found = new LinkedHashSet<>();
            for (JsonElement element : array(occurrence, field)) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                String canonical = string(mapping, "canonicalPort");
                if (canonicalPorts.contains(canonical)) {
                    result.add(mapping.deepCopy());
                    found.add(canonical);
                }
            }
            if (!found.equals(canonicalPorts)) {
                Set<String> missing = new LinkedHashSet<>(canonicalPorts);
                missing.removeAll(found);
                throw new IllegalArgumentException("projected occurrence "
                        + field + " is incomplete; missing=" + missing);
            }
            return result;
        }
    }

    private static final class Candidate {
        private static final Comparator<Candidate> ORDER =
                Comparator.comparing((Candidate value) -> !value.directed)
                        .thenComparing(value -> !value.ready)
                        .thenComparing(value -> value.target.siteId)
                        .thenComparing(value ->
                                value.goal.executionRegionInstanceId())
                        .thenComparing(value -> value.goal.goalId());

        private final Goal goal;
        private final JsonArray branches;
        private final TargetBranch target;
        private final boolean directed;
        private final JsonArray inputActions;
        private final boolean ready;
        private final String queryRegionInstanceId;
        private final JsonObject queryOccurrence;
        private final ProducerOutputProjection projection;
        private final OutputClosureContract projectedOutputClosure;
        private final JsonObject occurrenceCatalog;

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryRegionInstanceId,
                          JsonObject queryOccurrence,
                          ProducerOutputProjection projection,
                          OutputClosureContract projectedOutputClosure,
                          JsonObject occurrenceCatalog) {
            this.goal = goal;
            this.branches = branches;
            this.target = target;
            this.directed = goal.kind().capturesOutputRelation()
                    || !hasRequiredWitness;
            this.inputActions = inputActions;
            this.ready = ready;
            this.queryRegionInstanceId = firstNonBlank(
                    queryRegionInstanceId,
                    goal.executionRegionInstanceId());
            this.queryOccurrence = queryOccurrence == null
                    ? new JsonObject() : queryOccurrence.deepCopy();
            this.projection = projection;
            this.projectedOutputClosure = projectedOutputClosure;
            this.occurrenceCatalog = occurrenceCatalog == null
                    ? new JsonObject() : occurrenceCatalog.deepCopy();
        }

        private OutputClosureContract outputContract() {
            return goal.kind().capturesOutputRelation()
                    ? (projectedOutputClosure == null
                    ? goal.outputClosure() : projectedOutputClosure) : null;
        }

        private String seedTaskId() {
            String identity = goal.plan().logicalRegionId() + "\n"
                    + goal.goalId() + "\n"
                    + goal.pathSeedKey() + "\n"
                    + target.siteId + "\n" + target.selectedOccurrence
                    + "\n" + target.observedOutcome
                    + "\n" + target.desiredOutcome + "\n"
                    + (projection == null ? "UNPROJECTED"
                    : projection.fingerprint());
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
                OutputClosureContract outputClosure,
                ProducerOutputProjection projection) {
            String region = goal.plan().regionId();
            String instance = goal.executionRegionInstanceId();

            JsonArray bindings = new JsonArray();
            for (JsonElement element : goal.edgeBindings()) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (projection == null || projection.edgeIds().contains(
                        string(binding, "edgeId"))) {
                    bindings.add(binding.deepCopy());
                }
            }
            Set<String> requestedPorts = outputClosure == null
                    ? Collections.<String>emptySet()
                    : outputClosure.outputPorts();

            for (JsonObject normalized : values(
                    outboundByInstance, instance)) {
                String fromPort = string(normalized, "fromOutputPort");
                if (!region.equals(string(normalized, "fromRegion"))
                        || outputClosure != null
                        && !requestedPorts.contains(fromPort)
                        || projection != null
                        && !projection.edgeIds().contains(
                        string(normalized, "edgeId"))) {
                    continue;
                }
                // Each runtime occurrence remains a merge occurrence.  A
                // later execution layer may reuse an executable summary
                // payload, but the scheduler must not collapse the bindings
                // that place that payload into distinct dynamic contexts.
                bindings.add(normalized.deepCopy());
            }
            return bindings;
        }

        private JsonObject contextFor(String regionId,
                                      String regionInstanceId,
                                      JsonObject selectedOccurrence) {
            JsonObject context = new JsonObject();
            Set<String> canonicalInputs = new LinkedHashSet<>();
            Set<String> exactInputs = new LinkedHashSet<>();
            for (JsonElement element : array(selectedOccurrence,
                    "inputPortMap")) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                String canonical = string(mapping, "canonicalPort");
                String exact = string(mapping, "exactPort");
                if (!canonical.isEmpty() && !exact.isEmpty()) {
                    canonicalInputs.add(canonical);
                    exactInputs.add(exact);
                }
            }
            JsonArray equalityBindings = new JsonArray();
            for (JsonObject value : values(
                    equalityByInstance, regionInstanceId)) {
                JsonObject selected = demandedIncoming(value, regionId,
                        regionInstanceId, canonicalInputs, exactInputs);
                if (selected != null) equalityBindings.add(selected);
            }
            // Rebuild equality classes from the witness-bearing relations
            // selected for this concrete region instance. Reusing the global
            // static class here could transitively assert an equality for a
            // different invocation.
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
                JsonObject selected = demandedIncoming(value, regionId,
                        regionInstanceId, canonicalInputs, exactInputs);
                if (selected != null) states.add(selected);
            }
            JsonArray alternatives = new JsonArray();
            for (JsonObject value : values(
                    alternativesByInstance, regionInstanceId)) {
                JsonArray demanded = new JsonArray();
                for (JsonElement element : array(value, "alternatives")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject selected = demandedIncoming(
                            element.getAsJsonObject(), regionId,
                            regionInstanceId, canonicalInputs, exactInputs);
                    if (selected != null) demanded.add(selected);
                }
                if (demanded.size() > 0) {
                    JsonObject selected = value.deepCopy();
                    selected.add("alternatives", demanded);
                    alternatives.add(selected);
                }
            }
            context.add("equalityClasses", equality);
            context.add("equalityRelations", equalityBindings);
            context.add("versionedStateMerges", states);
            context.add("alternativeWriterGroups", alternatives);
            context.addProperty("regionInstanceId", regionInstanceId);
            return context;
        }

        private static JsonObject demandedIncoming(
                JsonObject relation, String regionId, String instance,
                Set<String> canonicalInputs, Set<String> exactInputs) {
            String target = string(relation, "toEndpoint");
            if (!target.startsWith(regionId + ".in.")
                    || !canonicalInputs.contains(target)
                    && !exactInputs.contains(target)) {
                return null;
            }
            JsonArray selected = new JsonArray();
            for (JsonElement element : array(relation,
                    "selectedBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (instance.equals(string(binding, "toRegionInstance"))
                        && exactInputs.contains(string(binding,
                        "toInputPort"))) {
                    selected.add(binding.deepCopy());
                }
            }
            if (selected.size() == 0) return null;
            JsonObject result = relation.deepCopy();
            result.add("selectedBindings", selected);
            return result;
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
                    normalized.addProperty("schemaVersion", 3);
                    normalized.addProperty("edgeId",
                            string(relation, "edgeId"));
                    normalized.addProperty("evidenceKind",
                            AutomaticRegionEdge.CONFIGURED_PROTOCOL_EQUALITY);
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
                    normalized.addProperty("mappingId",
                            string(raw, "mappingId"));
                    normalized.addProperty("protocolDirection",
                            firstNonBlank(string(raw, "protocolDirection"),
                                    string(raw, "direction")));
                    normalized.addProperty("protocolPort",
                            firstNonBlank(string(raw, "protocolPort"),
                                    string(raw, "port")));
                    normalized.addProperty("callerSiteEventSeq",
                            longInteger(raw, "callerSiteEventSeq", -1L));
                    normalized.addProperty("sendEventSeq",
                            longInteger(raw, "sendEventSeq", -1L));
                    normalized.addProperty("receiveEventSeq",
                            longInteger(raw, "receiveEventSeq", -1L));
                    String authority = firstNonBlank(string(raw,
                            "correlationAuthority"), string(raw,
                            "authority"));
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

    /** Describes the existing selection/admission decision without adding one. */
    private static String noCandidateDiagnostic(
            Arguments arguments, List<JsonObject> rows) {
        JsonObject selected = null;
        Goal selectedGoal = null;
        boolean regionFound = false;
        String reason = "REGION_NOT_FOUND";
        for (JsonObject row : rows) {
            RegionInstancePlan plan = RegionInstancePlan.decode(row);
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(plan.regionId())) continue;
            regionFound = true;
            if (!arguments.regionInstanceId.isEmpty()
                    && !plan.containsRegionInstance(
                    arguments.regionInstanceId)) continue;
            selected = row;
            reason = "GOAL_NOT_FOUND";
            for (Goal goal : plan.goals()) {
                if (!arguments.goalId.isEmpty()
                        && !arguments.goalId.equals(goal.goalId())) continue;
                selectedGoal = goal;
                boolean targetFound = arguments.targetSite.isEmpty();
                for (JsonElement branch : goal.branches()) {
                    targetFound |= branch.isJsonObject()
                            && arguments.targetSite.equals(string(
                            branch.getAsJsonObject(), "siteId"));
                }
                reason = !goal.replayable() ? "GOAL_NOT_REPLAYABLE"
                        : goal.kind().capturesOutputRelation()
                        && !"READY".equals(goal.admissionState())
                        ? "OUTPUT_GOAL_NOT_READY"
                        : goal.kind().capturesOutputRelation()
                        && goal.outputClosure() == null
                        ? "OUTPUT_CLOSURE_MISSING"
                        : !targetFound ? "TARGET_SITE_NOT_FOUND"
                        : "NO_ELIGIBLE_CANDIDATE";
                break;
            }
            if (selectedGoal != null || !arguments.goalId.isEmpty()) break;
        }
        if (selected == null && regionFound) {
            reason = "REGION_INSTANCE_NOT_FOUND";
        }
        String targetMethod = selected == null ? ""
                : string(selected, "targetMethod");
        JsonObject root = selected == null ? new JsonObject()
                : object(selected, "rootSelector");
        String state = selectedGoal == null ? ""
                : selectedGoal.admissionState();
        String blockers = selectedGoal == null ? ""
                : selectedGoal.admissionBlockers().toString();
        return "component=SCHEDULER reason=" + reason
                + " region=" + display(arguments.regionId)
                + " instance=" + display(arguments.regionInstanceId)
                + " goal=" + display(arguments.goalId)
                + " targetSite=" + display(arguments.targetSite)
                + " targetMethod=" + display(targetMethod)
                + " root=" + display(root.size() == 0 ? ""
                : CanonicalJson.render(root))
                + " admissionState=" + display(state)
                + " blockers=" + display(blockers)
                + " artifacts={regions=" + artifact(arguments.regions)
                + ",regionPlan=" + artifact(arguments.regionPlan)
                + ",edgeValidations=" + artifact(arguments.edgeValidations)
                + ",refinedGraph=" + artifact(arguments.refinedGraph)
                + ",summaries=" + artifact(arguments.summaries) + "}";
    }

    private static String display(String value) {
        return safe(value).isEmpty() ? "<none>" : value;
    }

    private static String artifact(Path path) {
        return path == null ? "<none>"
                : path.toAbsolutePath().normalize().toString();
    }

    public static final class Result {
        public final List<JsonObject> executionTasks = new ArrayList<>();
        public final List<JsonObject> queries = new ArrayList<>();
    }

    public static final class Arguments {
        public final Path regions;
        public final Path regionPlan;
        public final Path edgeValidations;
        public final Path refinedGraph;
        public final Path summaries;
        public final Path producerProjection;
        public final Path outputDirectory;
        public final String regionId;
        public final String regionInstanceId;
        public final String goalId;
        public final String targetSite;
        public final int maxJobs;
        public final int maxLoopIterations;

        private Arguments(Path regions, Path regionPlan,
                          Path edgeValidations, Path refinedGraph,
                          Path summaries, Path producerProjection,
                          Path outputDirectory, String regionId,
                          String regionInstanceId, String goalId,
                          String targetSite, int maxJobs,
                          int maxLoopIterations) {
            this.regions = regions;
            this.regionPlan = regionPlan;
            this.edgeValidations = edgeValidations;
            this.refinedGraph = refinedGraph;
            this.summaries = summaries;
            this.producerProjection = producerProjection;
            this.outputDirectory = outputDirectory;
            this.regionId = safe(regionId);
            this.regionInstanceId = safe(regionInstanceId);
            this.goalId = safe(goalId);
            this.targetSite = safe(targetSite);
            this.maxJobs = Math.max(1, maxJobs);
            this.maxLoopIterations = maxLoopIterations;
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
            Path refinedGraph = requiredPath(values, "refined-graph");
            Path summaries = optionalPath(values.get("summaries"));
            Path producerProjection = optionalPath(values.get(
                    "producer-projection"));
            return new Arguments(regions, regionPlan, edges, refinedGraph,
                    summaries, producerProjection, output,
                    firstNonBlank(values.get("region-id")),
                    firstNonBlank(values.get("region-instance-id")),
                    firstNonBlank(values.get("goal-id")),
                    firstNonBlank(values.get("target-site")),
                    parseInt(values.get("max-jobs"), 1),
                    positiveInt(values.get("max-loop-iterations"),
                            LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                            "max-loop-iterations"));
        }

        private static boolean knownOption(String key) {
            return "regions".equals(key)
                    || "region-plan".equals(key)
                    || "edge-validations".equals(key)
                    || "refined-graph".equals(key)
                    || "summaries".equals(key)
                    || "producer-projection".equals(key)
                    || "output-dir".equals(key)
                    || "region-id".equals(key)
                    || "region-instance-id".equals(key)
                    || "goal-id".equals(key)
                    || "target-site".equals(key)
                    || "max-jobs".equals(key)
                    || "max-loop-iterations".equals(key);
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

        private static int positiveInt(String value, int fallback,
                                       String option) {
            int parsed;
            try {
                parsed = value == null ? fallback : Integer.parseInt(value);
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException("--" + option
                        + " requires a positive integer", malformed);
            }
            if (parsed < 1) {
                throw new IllegalArgumentException("--" + option
                        + " requires a positive integer");
            }
            return parsed;
        }

    }
}
