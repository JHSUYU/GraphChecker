package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.SymbolicEnvironment;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
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
        Result result = arguments.targetFirst
                ? scheduleTargetFirst(arguments) : schedule(arguments);
        if (result.executionTasks.isEmpty()) {
            throw new IllegalStateException(noCandidateDiagnostic(arguments,
                    readJsonl(arguments.regionPlan)));
        }
    }

    public static Result schedule(Arguments arguments) throws IOException {
        if (arguments.targetFirst) {
            return scheduleTargetFirst(arguments);
        }
        LoadedInputs loaded = loadInputs(arguments);
        ProducerOutputProjection producerProjection =
                readProducerProjection(arguments.producerProjection);
        Result result = scheduleLoaded(arguments, loaded,
                producerProjection);
        writeResult(arguments.outputDirectory, result);
        return result;
    }

    private static LoadedInputs loadInputs(Arguments arguments)
            throws IOException {
        requireFile(arguments.regions, "symbolic regions");
        requireFile(arguments.regionPlan, "region plan");
        requireFile(arguments.edgeValidations, "runtime edge validation");
        requireFile(arguments.refinedGraph, "runtime-refined graph");
        Files.createDirectories(arguments.outputDirectory);

        JsonObject regionPlanIdentity = arguments.targetFirst
                ? artifactIdentity(arguments.regionPlan) : null;
        List<JsonObject> regions = readJsonl(arguments.regions);
        List<JsonObject> regionPlans = readJsonl(arguments.regionPlan);
        List<JsonObject> edges = readJsonl(arguments.edgeValidations);
        List<JsonObject> summaries = arguments.summaries == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.summaries);
        List<JsonObject> refinedGraph = readJsonl(arguments.refinedGraph);
        requireRefinedGraph(refinedGraph);
        DefinitionIndex definitions = DefinitionIndex.from(refinedGraph);

        Map<String, Region> regionIndex = new LinkedHashMap<>();
        for (JsonObject row : regions) {
            Region region = new Region(row);
            if (!region.regionId.isEmpty()) {
                regionIndex.put(region.regionId, region);
            }
        }

        MergePlan mergePlan = buildMergePlan(regionIndex, edges);
        if (regionPlanIdentity != null) {
            requireArtifactIdentity(arguments.regionPlan,
                    regionPlanIdentity, "region plan changed while loading");
        }
        return new LoadedInputs(regionPlans, summaries, regionIndex,
                definitions, mergePlan, regionPlanIdentity);
    }

    private static Result scheduleLoaded(
            Arguments arguments, LoadedInputs loaded,
            ProducerOutputProjection producerProjection) {
        List<Candidate> candidates = candidates(arguments,
                loaded.regionPlans, loaded.regionIndex,
                loaded.definitions, producerProjection);
        Collections.sort(candidates, Candidate.ORDER);

        Result result = new Result();
        Map<String, Integer> semanticIdUses = new LinkedHashMap<>();
        for (Candidate candidate : candidates) {
            if (result.executionTasks.size() >= arguments.maxJobs) {
                break;
            }
            OutputClosureContract outputContract = candidate.outputContract();
            JsonObject captured = outputContract != null ? null
                    : exactTargetSummary(candidate, loaded.summaries);
            JsonArray edgeBindings = loaded.mergePlan
                    .outboundValueEqualityBindings(candidate.goal,
                            outputContract, candidate.projection);
            if (candidate.targetEdgeBindings != null) {
                edgeBindings = candidate.targetEdgeBindings.deepCopy();
            }
            // Two candidates with byte-identical semantic content are
            // interchangeable; a deterministic ordinal suffix keeps their
            // task ids unique without reintroducing trace ordinals.
            String taskId = candidate.seedTaskId();
            int uses = semanticIdUses.merge(taskId, 1, Integer::sum);
            if (uses > 1) {
                taskId = taskId + "-dup" + uses;
            }
            ExecutionTask scheduled = candidate.projection == null
                    ? ExecutionTask.create(candidate.goal,
                    taskId, candidate.inputActions,
                    candidate.branches, edgeBindings,
                    LoopBoundPolicy.cfgBackedges(
                            arguments.maxLoopIterations), candidate.ready)
                    : ExecutionTask.createProjectedOutput(candidate.goal,
                    taskId, candidate.inputActions,
                    candidate.branches, edgeBindings,
                    LoopBoundPolicy.cfgBackedges(
                            arguments.maxLoopIterations), candidate.ready,
                    outputContract, candidate.occurrenceCatalog,
                    candidate.projection.json());
            JsonObject executionTask = scheduled.json();
            if (outputContract != null) {
                // The timeline annotation is derived after the immutable
                // planner goal was decoded.  Replace only that canonical
                // envelope; the VM task semantics and captures are unchanged.
                executionTask.add(OutputClosureContract.FIELD,
                        outputContract.toJson());
            }
            if (candidate.goal.kind().capturesTargetReach()) {
                executionTask.add(RegionInstancePlan.OCCURRENCE_CATALOG,
                        candidate.occurrenceCatalog.deepCopy());
                JsonObject stop = new JsonObject();
                stop.addProperty("siteId", candidate.target.siteId);
                stop.addProperty("occurrence",
                        candidate.target.selectedOccurrence);
                executionTask.add("stopAfterBranch", stop);
            }

            if (captured != null && outputContract == null) {
                JsonObject query = branchQuery(candidate, captured,
                        loaded.mergePlan);
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
        return result;
    }

    private static void writeResult(Path output, Result result)
            throws IOException {
        writeJsonl(output.resolve("execution_task_plan.jsonl"),
                result.executionTasks);
        writeJsonl(output.resolve("branch_queries.jsonl"), result.queries);
    }

    private static Result scheduleTargetFirst(Arguments arguments)
            throws IOException {
        LoadedInputs loaded = loadInputs(arguments);
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(
                        loaded.regionPlans);
        if (workflow.scheduledTaskCount() > arguments.maxJobs) {
            throw new IOException("selected exact closure exceeds max jobs: "
                    + workflow.scheduledTaskCount() + " > "
                    + arguments.maxJobs);
        }

        Map<String, JsonObject> tasks = new LinkedHashMap<>();
        Map<String, JsonObject> producerComponents = new LinkedHashMap<>();
        Map<String, JsonObject> queries = new LinkedHashMap<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : workflow.selections()) {
            Result selected = scheduleLoaded(
                    arguments.forSelection(selection), loaded,
                    selection.producerProjection);
            if (selected.executionTasks.size() != 1) {
                throw new IOException("target-first selection emitted "
                        + selected.executionTasks.size()
                        + " execution tasks; campaign="
                        + selection.campaignId);
            }
            JsonObject task = selected.executionTasks.get(0);
            if (selection.producerProjection == null) {
                putUnique(tasks, task, "taskId");
            } else {
                JsonObject prior = producerComponents.putIfAbsent(
                        selection.campaignId, task);
                if (prior != null && !prior.equals(task)) {
                    throw new IOException("conflicting producer component "
                            + selection.campaignId);
                }
            }
            for (JsonObject query : selected.queries) {
                putUnique(queries, query, "queryKey");
            }
        }
        for (JsonObject atomic : atomicProducerTasks(workflow,
                producerComponents)) {
            putUnique(tasks, atomic, "taskId");
        }

        Result result = new Result();
        result.executionTasks.addAll(sortedValues(tasks));
        result.queries.addAll(sortedValues(queries));
        writeResult(arguments.outputDirectory, result);
        Path taskPlan = arguments.outputDirectory.resolve(
                "execution_task_plan.jsonl");
        JsonObject taskPlanIdentity = artifactIdentity(taskPlan);
        JsonObject index = workflow.scheduleIndex(result.executionTasks,
                loaded.regionPlanIdentity, taskPlanIdentity);
        requireArtifactIdentity(arguments.regionPlan,
                loaded.regionPlanIdentity,
                "region plan changed while scheduling");
        requireArtifactIdentity(taskPlan, taskPlanIdentity,
                "execution task plan changed before index publication");
        ArtifactIO.replace(arguments.outputDirectory.resolve(
                        "selected_target_binding.tsv"),
                workflow.targetBinding() + "\n");
        StringBuilder closure = new StringBuilder();
        for (String binding : workflow.closureBindings()) {
            closure.append(binding).append('\n');
        }
        ArtifactIO.replace(arguments.outputDirectory.resolve(
                        "selected_closure_bindings.tsv"),
                closure.toString());
        // The integrity-checked index is the commit record.  Publish it only
        // after every artifact it describes or accompanies is durable.
        ArtifactIO.replace(arguments.outputDirectory.resolve(
                        "runtime_workflow_schedule_index.json"),
                CanonicalJson.render(index) + "\n");
        return result;
    }

    private static JsonObject artifactIdentity(Path path)
            throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("sha256", ArtifactIO.sha256(path));
        result.addProperty("sizeBytes", Files.size(path));
        return result;
    }

    private static void requireArtifactIdentity(
            Path path, JsonObject expected, String message)
            throws IOException {
        JsonObject actual = artifactIdentity(path);
        if (expected == null || !expected.equals(actual)) {
            throw new IOException(message + ": " + path);
        }
    }

    private static void putUnique(Map<String, JsonObject> values,
                                  JsonObject row, String identity)
            throws IOException {
        String key = JsonFields.string(row, identity);
        if (key.isEmpty()) {
            throw new IOException("scheduled row has no " + identity);
        }
        JsonObject prior = values.putIfAbsent(key, row);
        if (prior != null && !prior.equals(row)) {
            throw new IOException("conflicting scheduled " + identity
                    + ": " + key);
        }
    }

    private static List<JsonObject> sortedValues(
            Map<String, JsonObject> values) {
        List<String> keys = new ArrayList<>(values.keySet());
        Collections.sort(keys);
        List<JsonObject> result = new ArrayList<>();
        for (String key : keys) result.add(values.get(key));
        return result;
    }

    private static final Set<String> ATOMIC_PRODUCER_MERGED_FIELDS =
            new LinkedHashSet<>(java.util.Arrays.asList(
                    "taskId", "goalId", "pathSeedKey", "inputActions",
                    "branches", "edgeBindings", "outputClosure",
                    "occurrenceInstantiationCatalog",
                    "producerProjection"));

    private static List<JsonObject> atomicProducerTasks(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            Map<String, JsonObject> componentsByCampaign)
            throws IOException {
        List<JsonObject> result = new ArrayList<>();
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            List<JsonObject> components = new ArrayList<>();
            for (RuntimeWorkflowDiscovery.Selection selection
                    : group.selections) {
                JsonObject component = componentsByCampaign.get(
                        selection.campaignId);
                if (component == null) {
                    throw new IOException("missing scheduled producer "
                            + "component " + selection.campaignId);
                }
                components.add(component);
            }
            result.add(mergeAtomicProducerTasks(group, components));
        }
        return result;
    }

    static List<JsonObject> atomicProducerTasksForTests(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            Map<String, JsonObject> componentsByCampaign)
            throws IOException {
        return atomicProducerTasks(workflow, componentsByCampaign);
    }

    /**
     * Joins independently validated projections of one exact producer
     * invocation into the single task that must capture their outputs
     * atomically.
     */
    private static JsonObject mergeAtomicProducerTasks(
            RuntimeWorkflowDiscovery.ProducerGroup group,
            List<JsonObject> encodedComponents) throws IOException {
        if (encodedComponents == null || encodedComponents.isEmpty()) {
            throw new IOException("atomic producer group has no tasks");
        }
        List<ExecutionTask> components = new ArrayList<>();
        Set<String> encodedIdentities = new LinkedHashSet<>();
        for (JsonObject encoded : encodedComponents) {
            ExecutionTask task = ExecutionTask.decode(encoded);
            if (!group.regionId.equals(task.regionId())
                    || !group.logicalRegionId.equals(task.logicalRegionId())
                    || !group.pathSeedKey.equals(string(
                    task.producerProjection(), "pathSeedKey"))) {
                throw new IOException("atomic producer component crosses "
                        + "invocation or path boundary");
            }
            requireExactProducerOccurrence(task
                    .occurrenceInstantiationCatalog(), group);
            // seedTaskId deliberately ignores exact projection provenance.
            // Two output slices of one invocation can therefore have the
            // same replay-stable id while carrying different demanded ports
            // or edges.  They are atomic components, not an id conflict.
            // Only byte-identical duplicate components are redundant.
            if (encodedIdentities.add(CanonicalJson.render(encoded))) {
                components.add(task);
            }
        }
        components.sort(Comparator
                .comparing(ExecutionTask::taskId)
                .thenComparing(task -> CanonicalJson.render(
                        task.producerProjection()))
                .thenComparing(ExecutionTask::goalId));
        if (components.size() == 1) {
            return components.get(0).json().deepCopy();
        }
        JsonObject merged = components.get(0).json().deepCopy();
        for (ExecutionTask component : components) {
            requireSameAtomicProducerEnvelope(merged, component.json());
        }

        JsonArray inputs = mergeInputActions(components);
        JsonArray branches = mergeObjectArrays(components, "branches",
                "siteId", "branch site");
        JsonArray edges = mergeEdgeBindings(components);
        List<OutputClosureContract> closures = new ArrayList<>();
        List<String> componentIds = new ArrayList<>();
        for (ExecutionTask component : components) {
            closures.add(component.outputClosure());
            componentIds.add(component.taskId());
        }
        OutputClosureContract closure = OutputClosureCodec.merge(closures);
        JsonObject catalog = mergeOccurrenceCatalogs(components);
        addObservedIntraRegionFieldHandoffs(group, merged, inputs,
                closure, edges, catalog);
        // The group goal digest includes every constituent projection.  It
        // disambiguates colliding replay-stable component ids without making
        // the VM task depend on component enumeration order.
        String atomicIdentity = group.goalId() + "\n"
                + String.join("\n", componentIds);
        String taskId = "TASK.SEED." + ArtifactIO.sha256(
                "ATOMIC_PROJECTED_PRODUCER_TASK_V1\n" + atomicIdentity);
        ProducerOutputProjection projection = group.projection();

        merged.addProperty("taskId", taskId);
        merged.addProperty("goalId", group.goalId());
        merged.add("inputActions", inputs);
        merged.add("branches", branches);
        if (string(merged, "pathSeedKey").isEmpty()) {
            merged.remove("pathSeedKey");
        } else {
            merged.addProperty("pathSeedKey",
                    edu.uva.liftlab.graphchecker.contract.BoundedPathSeed
                            .key(branches));
        }
        merged.add("edgeBindings", edges);
        OutputClosureCodec.writeTo(merged, closure);
        merged.add(RegionInstancePlan.OCCURRENCE_CATALOG, catalog);
        merged.add("producerProjection", projection.json());
        ExecutionTask verified = ExecutionTask.decode(merged);
        if (!verified.outputClosure().executionScope().inputPorts().equals(
                group.inputPorts())) {
            throw new IOException("atomic producer input closure does not "
                    + "match grouped demand");
        }
        return verified.json().deepCopy();
    }

    /**
     * Connects a leaf written by one helper invocation to an exact accessor
     * of the same runtime object in a later helper invocation of this atomic
     * region.  The trace object id is used only to discover the observed
     * relation; replay materializes the later accessor as a normal symbolic
     * port and the composer enforces this read-from equality.
     */
    private static void addObservedIntraRegionFieldHandoffs(
            RuntimeWorkflowDiscovery.ProducerGroup group,
            JsonObject envelope, JsonArray inputs,
            OutputClosureContract closure, JsonArray edges,
            JsonObject catalog) throws IOException {
        List<JsonObject> outputs = new ArrayList<>();
        for (OutputClosureContract.Member member : closure.members()) {
            JsonObject slice = member.slice();
            long receiver = longInteger(slice,
                    "selectedFieldReceiverObjectId", 0L);
            long writer = longInteger(slice,
                    "selectedRuntimeEventSeq", -1L);
            String declaration = member.cell();
            if (receiver == 0L || writer < 0L || declaration.isEmpty()) {
                continue;
            }
            JsonObject output = new JsonObject();
            output.addProperty("portId", member.portId());
            output.addProperty("receiverObjectId", receiver);
            output.addProperty("eventSeq", writer);
            output.addProperty("declaration", declaration);
            outputs.add(output);
        }
        if (outputs.isEmpty()) return;

        Set<String> closureInputs = closure.executionScope().inputPorts();
        String lane = string(envelope, "laneId");
        if (lane.isEmpty()) lane = String.valueOf(
                longInteger(envelope, "laneId", -1L));
        for (JsonElement element : inputs) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String input = firstNonBlank(string(action, "portId"),
                    string(action, "symbol"));
            if (!closureInputs.contains(input)
                    || !InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    string(action, "mode"))
                    || !"FIELD_ACCESS".equals(
                    string(action, "bindingMode"))
                    || longInteger(action, "rootCallId", -1L)
                    != group.rootCallId) {
                continue;
            }
            long receiver = longInteger(action,
                    "fieldReceiverObjectId", 0L);
            long reader = longInteger(action, "eventSeq", -1L);
            String declaration = firstNonBlank(
                    string(action, "declaredFieldSignature"),
                    string(action, "accessFieldSignature"));
            if (receiver == 0L || reader < 0L || declaration.isEmpty()) {
                continue;
            }
            JsonObject selected = null;
            long latest = -1L;
            for (JsonObject output : outputs) {
                long writer = longInteger(output, "eventSeq", -1L);
                if (receiver != longInteger(output,
                        "receiverObjectId", 0L)
                        || !declaration.equals(string(output,
                        "declaration"))
                        || writer >= reader || writer < latest) {
                    continue;
                }
                if (writer == latest && selected != null
                        && !string(selected, "portId").equals(
                        string(output, "portId"))) {
                    throw new IOException("ambiguous intra-region field "
                            + "handoff for " + input);
                }
                selected = output;
                latest = writer;
            }
            if (selected == null) continue;

            String output = string(selected, "portId");
            String edgeId = "RF.INTERNAL." + ArtifactIO.sha256(
                    group.regionInstanceId + "\n" + output + "\n"
                            + input + "\n" + latest + "\n" + reader);
            action.addProperty("intraRegionSourceOutputPort", output);
            action.addProperty("intraRegionReadFromAuthority",
                    "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");

            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 3);
            binding.addProperty("edgeId", edgeId);
            binding.addProperty("fromRegion", group.regionId);
            binding.addProperty("toRegion", group.regionId);
            binding.addProperty("transportKind", "HEAP");
            binding.addProperty("evidenceKind",
                    AutomaticRegionEdge.FIELD_ASSIGNMENT_READ_FROM);
            binding.addProperty("fromRegionInstance",
                    group.regionInstanceId);
            binding.addProperty("toRegionInstance",
                    group.regionInstanceId);
            binding.addProperty("fromRootCallId", group.rootCallId);
            binding.addProperty("toRootCallId", group.rootCallId);
            binding.addProperty("fromOutputPort", output);
            binding.addProperty("toInputPort", input);
            binding.addProperty("receiverObjectId", receiver);
            binding.addProperty("writerReceiverObjectId", receiver);
            binding.addProperty("readerReceiverObjectId", receiver);
            binding.addProperty("writerEventSeq", latest);
            binding.addProperty("readerEventSeq", reader);
            binding.addProperty("programOrderRequired", true);
            binding.addProperty("writerLaneId", lane);
            binding.addProperty("readerLaneId", lane);
            binding.addProperty("correlationAuthority",
                    "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
            JsonArray declarations = new JsonArray();
            declarations.add(declaration);
            binding.add("fieldPathDeclarations", declarations);
            edges.add(binding);
            addOccurrenceBinding(catalog, group.regionInstanceId, edgeId);
        }
    }

    private static void addOccurrenceBinding(JsonObject catalog,
                                             String instance,
                                             String edgeId)
            throws IOException {
        JsonObject selected = null;
        for (JsonElement element : array(catalog, "occurrences")) {
            if (!element.isJsonObject()) continue;
            JsonObject occurrence = element.getAsJsonObject();
            if (!instance.equals(string(occurrence,
                    "regionInstanceId"))) continue;
            if (selected != null) {
                throw new IOException("duplicate exact occurrence "
                        + instance);
            }
            selected = occurrence;
        }
        if (selected == null) {
            throw new IOException("missing exact occurrence " + instance);
        }
        Set<String> ids = new LinkedHashSet<>();
        for (JsonElement id : array(selected, "bindingIds")) {
            if (id.isJsonPrimitive()) ids.add(id.getAsString());
        }
        ids.add(edgeId);
        List<String> ordered = new ArrayList<>(ids);
        Collections.sort(ordered);
        JsonArray encoded = new JsonArray();
        for (String id : ordered) encoded.add(id);
        selected.add("bindingIds", encoded);
    }

    private static JsonObject requireExactProducerOccurrence(
            JsonObject catalog,
            RuntimeWorkflowDiscovery.ProducerGroup group)
            throws IOException {
        JsonObject selected = null;
        for (JsonElement element : array(catalog, "occurrences")) {
            if (!element.isJsonObject()) continue;
            JsonObject occurrence = element.getAsJsonObject();
            if (!group.regionInstanceId.equals(string(occurrence,
                    "regionInstanceId"))) {
                continue;
            }
            if (selected != null || longInteger(occurrence, "rootCallId",
                    -1L) != group.rootCallId) {
                throw new IOException("atomic producer exact occurrence is "
                        + "duplicated or has inconsistent root: "
                        + group.regionInstanceId);
            }
            selected = occurrence;
        }
        if (selected == null) {
            throw new IOException("atomic producer component catalog omits "
                    + "exact occurrence " + group.regionInstanceId);
        }
        return selected;
    }

    private static void requireSameAtomicProducerEnvelope(
            JsonObject expected, JsonObject actual) throws IOException {
        Set<String> fields = new LinkedHashSet<>(expected.keySet());
        fields.addAll(actual.keySet());
        for (String field : fields) {
            if (ATOMIC_PRODUCER_MERGED_FIELDS.contains(field)) continue;
            JsonElement left = expected.get(field);
            JsonElement right = actual.get(field);
            if (left == null ? right != null : !left.equals(right)) {
                throw new IOException("atomic producer components disagree "
                        + "on " + field);
            }
        }
    }

    private static JsonArray mergeInputActions(
            List<ExecutionTask> components) throws IOException {
        JsonArray result = new JsonArray();
        Set<String> exactRows = new LinkedHashSet<>();
        Map<String, String> symbolBySelector = new LinkedHashMap<>();
        for (ExecutionTask component : components) {
            for (JsonElement element : component.inputActions().all()) {
                JsonObject action = element.getAsJsonObject();
                String canonical = CanonicalJson.render(action);
                if (!exactRows.add(canonical)) continue;
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        string(action, "mode"))) {
                    for (String selector : materializationSelectors(action)) {
                        String prior = symbolBySelector.putIfAbsent(selector,
                                string(action, "symbol"));
                        if (prior != null) {
                            throw new IOException("atomic producer inputs "
                                    + "share runtime materialization selector "
                                    + selector + ": " + prior + " and "
                                    + string(action, "symbol"));
                        }
                    }
                }
                result.add(action.deepCopy());
            }
        }
        return result;
    }

    private static Set<String> materializationSelectors(JsonObject action)
            throws IOException {
        Set<String> result = new LinkedHashSet<>();
        String mode = string(action, "bindingMode");
        String occurrence = String.valueOf(integer(action,
                "replayOccurrence", -1));
        if ("METHOD_ARGUMENT".equals(mode)) {
            result.add("METHOD_ARGUMENT\n" + string(action, "method")
                    + "\n" + integer(action, "index", -1) + "\n"
                    + occurrence);
        } else if ("LOCAL_DEFINITION".equals(mode)) {
            Set<Integer> units = new LinkedHashSet<>();
            int direct = integer(action, "unitIndex", -1);
            if (direct >= 0) units.add(direct);
            for (JsonElement element : array(action, "definitionSites")) {
                if (element.isJsonObject()) {
                    int unit = integer(element.getAsJsonObject(),
                            "unitIndex", -1);
                    if (unit >= 0) units.add(unit);
                }
            }
            if (units.isEmpty()) units.add(-1);
            for (Integer unit : units) {
                result.add("LOCAL_DEFINITION\n"
                        + string(action, "method") + "\n" + unit + "\n"
                        + string(action, "local") + "\n" + occurrence);
            }
        } else if ("FIELD_ACCESS".equals(mode)) {
            String caller = string(action, "accessorCallerMethod");
            int callUnit = integer(action, "accessorCallUnitIndex", -1);
            String callee = string(action, "accessorDeclaredCallee");
            String implementation = string(action,
                    "accessorImplementationMethod");
            if (!caller.isEmpty() || callUnit >= 0 || !callee.isEmpty()
                    || !implementation.isEmpty()) {
                result.add("ACCESSOR_RETURN\n" + caller + "\n" + callUnit
                        + "\n" + callee + "\n" + implementation + "\n"
                        + occurrence);
            } else {
                JsonArray sites = array(action, "accessSites");
                if (sites.size() == 0) {
                    result.add("FIELD_ACCESS\n<NO_SITE>\n"
                            + string(action, "accessFieldSignature") + "\n"
                            + CanonicalJson.render(array(action,
                            "fieldPath")) + "\n" + occurrence);
                }
                for (JsonElement site : sites) {
                    result.add("FIELD_ACCESS\n" + site.getAsString() + "\n"
                            + string(action, "accessFieldSignature") + "\n"
                            + CanonicalJson.render(array(action,
                            "fieldPath")) + "\n" + occurrence);
                }
            }
        } else if ("ROOT_ENTRY".equals(mode)) {
            String location = string(action, "location");
            if ("ARGUMENT".equals(location)) {
                result.add("ROOT_ARGUMENT\n"
                        + integer(action, "index", -1));
            } else {
                result.add("ROOT_ENTRY\n" + location + "\n"
                        + integer(action, "index", -1) + "\n"
                        + CanonicalJson.render(array(action, "fieldPath"))
                        + "\n" + CanonicalJson.render(array(action,
                        "fieldPaths")) + "\n"
                        + string(action, "accessFieldSignature"));
            }
        } else if ("VM_INTRINSIC_PLACEHOLDER".equals(mode)) {
            result.add("VM_INTRINSIC_PLACEHOLDER\n"
                    + string(action, "cell"));
        } else {
            throw new IOException("atomic producer symbolic input has "
                    + "unsupported runtime selector mode " + mode);
        }
        return result;
    }

    private static JsonArray mergeObjectArrays(
            List<ExecutionTask> components, String field, String identity,
            String subject) throws IOException {
        Map<String, JsonObject> rows = new LinkedHashMap<>();
        for (ExecutionTask component : components) {
            for (JsonElement element : array(component.json(), field)) {
                if (!element.isJsonObject()) {
                    throw new IOException(subject + " must be an object");
                }
                JsonObject row = element.getAsJsonObject();
                String key = string(row, identity);
                if (key.isEmpty()) {
                    throw new IOException(subject + " has no " + identity);
                }
                JsonObject prior = rows.putIfAbsent(key, row);
                if (prior != null && !prior.equals(row)) {
                    throw new IOException("conflicting " + subject + " "
                            + key);
                }
            }
        }
        JsonArray result = new JsonArray();
        for (JsonObject row : rows.values()) result.add(row.deepCopy());
        return result;
    }

    /**
     * One causal edge can be represented by a refined runtime row and by a
     * compact closure row.  They share an edgeId and may carry complementary
     * fields, so join compatible views without weakening conflict checks.
     */
    private static JsonArray mergeEdgeBindings(
            List<ExecutionTask> components) throws IOException {
        Map<String, JsonObject> rows = new LinkedHashMap<>();
        for (ExecutionTask component : components) {
            for (JsonElement element : component.edgeBindings()) {
                if (!element.isJsonObject()) {
                    throw new IOException("edge binding must be an object");
                }
                JsonObject row = element.getAsJsonObject();
                String edgeId = string(row, "edgeId");
                if (edgeId.isEmpty()) {
                    throw new IOException("edge binding has no edgeId");
                }
                JsonObject merged = rows.get(edgeId);
                if (merged == null) {
                    rows.put(edgeId, row.deepCopy());
                    continue;
                }
                for (Map.Entry<String, JsonElement> field
                        : row.entrySet()) {
                    JsonElement prior = merged.get(field.getKey());
                    if (prior == null) {
                        merged.add(field.getKey(), field.getValue().deepCopy());
                    } else if (!prior.equals(field.getValue())) {
                        throw new IOException("conflicting edge binding "
                                + edgeId + " field " + field.getKey());
                    }
                }
            }
        }
        JsonArray result = new JsonArray();
        for (JsonObject row : rows.values()) result.add(row.deepCopy());
        return result;
    }

    private static JsonObject mergeOccurrenceCatalogs(
            List<ExecutionTask> components) throws IOException {
        JsonObject merged = components.get(0)
                .occurrenceInstantiationCatalog();
        Map<String, JsonObject> occurrences = new LinkedHashMap<>();
        for (ExecutionTask component : components) {
            JsonObject catalog = component.occurrenceInstantiationCatalog();
            requireSameObjectExcept(merged, catalog,
                    Collections.singleton("occurrences"),
                    "occurrence catalog");
            for (JsonElement element : array(catalog, "occurrences")) {
                if (!element.isJsonObject()) {
                    throw new IOException("occurrence must be an object");
                }
                JsonObject occurrence = element.getAsJsonObject();
                String instance = string(occurrence, "regionInstanceId");
                if (instance.isEmpty()) {
                    throw new IOException("occurrence has no instance");
                }
                JsonObject target = occurrences.get(instance);
                if (target == null) {
                    target = occurrence.deepCopy();
                    target.add("inputPortMap", new JsonArray());
                    target.add("outputPortMap", new JsonArray());
                    target.add("bindingIds", new JsonArray());
                    occurrences.put(instance, target);
                } else {
                    requireSameObjectExcept(target, occurrence,
                            new LinkedHashSet<>(java.util.Arrays.asList(
                                    "inputPortMap", "outputPortMap",
                                    "bindingIds")), "occurrence " + instance);
                }
                target.add("inputPortMap", mergePortMappings(
                        array(target, "inputPortMap"),
                        array(occurrence, "inputPortMap"),
                        "input port", instance));
                target.add("outputPortMap", mergePortMappings(
                        array(target, "outputPortMap"),
                        array(occurrence, "outputPortMap"),
                        "output port", instance));
                target.add("bindingIds", mergeStrings(
                        array(target, "bindingIds"),
                        array(occurrence, "bindingIds")));
            }
        }
        JsonArray encoded = new JsonArray();
        for (JsonObject occurrence : occurrences.values()) {
            encoded.add(occurrence);
        }
        merged.add("occurrences", encoded);
        return merged;
    }

    private static JsonArray mergePortMappings(
            JsonArray left, JsonArray right, String subject,
            String instance) throws IOException {
        Map<String, JsonObject> mappings = new LinkedHashMap<>();
        Map<String, String> canonicalByExact = new LinkedHashMap<>();
        for (JsonArray source : java.util.Arrays.asList(left, right)) {
            for (JsonElement element : source) {
                if (!element.isJsonObject()) {
                    throw new IOException(subject + " mapping must be an "
                            + "object");
                }
                JsonObject mapping = element.getAsJsonObject();
                String canonical = string(mapping, "canonicalPort");
                String exact = string(mapping, "exactPort");
                if (canonical.isEmpty() || exact.isEmpty()) {
                    throw new IOException(subject + " mapping has no exact "
                            + "canonicalPort/exactPort pair");
                }
                JsonObject prior = mappings.putIfAbsent(canonical, mapping);
                if (prior != null && !prior.equals(mapping)) {
                    throw new IOException("conflicting " + subject
                            + " mapping for " + instance + ": "
                            + canonical);
                }
                String priorCanonical = canonicalByExact.putIfAbsent(exact,
                        canonical);
                if (priorCanonical != null
                        && !priorCanonical.equals(canonical)) {
                    throw new IOException("conflicting " + subject
                            + " inverse mapping for " + instance + ": "
                            + exact);
                }
            }
        }
        JsonArray result = new JsonArray();
        for (JsonObject mapping : mappings.values()) {
            result.add(mapping.deepCopy());
        }
        return result;
    }

    private static JsonArray mergeStrings(JsonArray left, JsonArray right) {
        Set<String> values = new LinkedHashSet<>();
        for (JsonArray source : java.util.Arrays.asList(left, right)) {
            for (JsonElement element : source) {
                if (element.isJsonPrimitive()) {
                    values.add(element.getAsString());
                }
            }
        }
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static void requireSameObjectExcept(
            JsonObject expected, JsonObject actual, Set<String> ignored,
            String subject) throws IOException {
        Set<String> fields = new LinkedHashSet<>(expected.keySet());
        fields.addAll(actual.keySet());
        for (String field : fields) {
            if (ignored.contains(field)) continue;
            JsonElement left = expected.get(field);
            JsonElement right = actual.get(field);
            if (left == null ? right != null : !left.equals(right)) {
                throw new IOException(subject + " disagrees on " + field);
            }
        }
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
                appendGoalCandidates(arguments, result, goal, region,
                        definitions, producerProjection);
            }
        }
        return result;
    }

    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result,
            Goal goal, Region region, DefinitionIndex definitions,
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
                outputClosure = region.withBoundedContainerTimeline(
                        outputClosure);
                JsonArray symbolize = projected == null
                        ? goal.symbolize() : projected.symbolize;
                JsonArray branches = projected == null
                        ? goal.branches() : projected.branches;
                JsonArray inputActions = materializationPlan(
                        goal, symbolize, definitions, definitionMethods,
                        outputClosure, branches,
                        goal.executionRegionInstanceId());
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
            int eligibleFailureTargets = 0;
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (eligibleFailureTarget(branch)) {
                    eligibleFailureTargets++;
                }
            }
            if (eligibleFailureTargets != 1) {
                throw new IllegalArgumentException(
                        "UNSUPPORTED_AMBIGUOUS_TARGET_PATH: expected one "
                                + "eligible failure target; found "
                                + eligibleFailureTargets);
            }
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
                if (arguments.targetSite.isEmpty()
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
                // A target task explores exactly one branch; the rest of the
                // slice is replayed prefix.  Materialization is decided
                // against that slice so a leaf is not kept symbolic for a
                // decision this task never reopens.
                JsonArray reachSlice = targetReachBranchSlice(branches,
                        target);
                String queryInstance = targetQueryInstance(arguments, goal);
                JsonArray inputActions = materializationPlan(goal,
                        goal.symbolize(), definitions,
                        definitionMethods, null, reachSlice,
                        queryInstance);
                inputActions = targetSymbolicFrontier(goal, inputActions,
                        queryInstance);
                JsonArray targetBindings = targetInputBindings(goal,
                        inputActions, queryInstance);
                JsonObject occurrenceCatalog = targetOccurrenceCatalog(
                        goal, inputActions, targetBindings);
                result.add(new Candidate(goal,
                        reachSlice, target,
                        hasWitness, inputActions, true,
                        queryInstance,
                        targetQueryOccurrence(arguments, goal,
                                occurrenceCatalog), null,
                        null, occurrenceCatalog, targetBindings));
            }
    }

    private static boolean eligibleFailureTarget(JsonObject branch) {
        if (!bool(branch, "failureTarget", false)
                || !bool(branch, "observed", false)
                || !branch.has("requiredOutcome")
                || branch.get("requiredOutcome").isJsonNull()) {
            return false;
        }
        return TargetBranch.select(string(branch, "siteId"),
                array(branch, "occurrences"),
                bool(branch, "requiredOutcome", false)) != null;
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
            Arguments arguments, Goal goal, JsonObject catalog) {
        String selected = targetQueryInstance(arguments, goal);
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
        return result;
    }

    /**
     * A target VM job has no reason to materialize a concrete owner merely
     * because the backward slice traversed through it.  Keep only actual
     * solver leaves.  BOUNDED_STATE_FRONTIER is authored for producer
     * mutation summaries; on a target it is admissible only when an exact
     * upstream edge supplies that leaf, otherwise it is unrelated regional
     * mutation context (for example a serialization buffer count).
     */
    private static JsonArray targetSymbolicFrontier(
            Goal goal, JsonArray actions, String queryInstance) {
        JsonArray result = new JsonArray();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    string(action, "mode"))) {
                continue;
            }
            if ("BOUNDED_STATE_FRONTIER".equals(
                    string(action, "symbolicDemand"))
                    && !trustedIncomingBinding(goal,
                    string(action, "symbol"), queryInstance)) {
                continue;
            }
            result.add(action.deepCopy());
        }
        return result;
    }

    private static boolean trustedIncomingBinding(
            Goal goal, String canonicalInput, String queryInstance) {
        Set<String> acceptedPorts = exactInputPorts(goal, canonicalInput,
                queryInstance);
        for (JsonElement element : goal.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (queryInstance.equals(string(binding, "toRegionInstance"))
                    && acceptedPorts.contains(string(binding,
                    "toInputPort"))
                    && AutomaticRegionEdge
                    .trustedRuntimeCompositionBinding(binding)) {
                return true;
            }
        }
        return false;
    }

    private static Set<String> exactInputPorts(
            Goal goal, String canonicalInput, String queryInstance) {
        Set<String> result = new LinkedHashSet<>();
        result.add(canonicalInput);
        for (JsonElement occurrenceElement : array(
                goal.occurrenceInstantiationCatalog(), "occurrences")) {
            if (!occurrenceElement.isJsonObject()) continue;
            JsonObject occurrence = occurrenceElement.getAsJsonObject();
            if (!queryInstance.equals(string(occurrence,
                    "regionInstanceId"))) {
                continue;
            }
            for (JsonElement mappingElement : array(
                    occurrence, "inputPortMap")) {
                if (!mappingElement.isJsonObject()) continue;
                JsonObject mapping = mappingElement.getAsJsonObject();
                if (canonicalInput.equals(string(mapping,
                        "canonicalPort"))) {
                    result.add(string(mapping, "exactPort"));
                }
            }
        }
        result.remove("");
        return result;
    }

    private static JsonArray targetInputBindings(
            Goal goal, JsonArray actions, String queryInstance) {
        Set<String> exactPorts = new LinkedHashSet<>();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            exactPorts.addAll(exactInputPorts(goal,
                    string(element.getAsJsonObject(), "symbol"),
                    queryInstance));
        }
        JsonArray result = new JsonArray();
        for (JsonElement element : goal.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (queryInstance.equals(string(binding,
                    "toRegionInstance"))
                    && exactPorts.contains(string(binding, "toInputPort"))
                    && AutomaticRegionEdge
                    .trustedRuntimeCompositionBinding(binding)) {
                result.add(binding.deepCopy());
            }
        }
        return result;
    }

    private static JsonObject targetOccurrenceCatalog(
            Goal goal, JsonArray actions, JsonArray bindings) {
        Set<String> canonicalPorts = new LinkedHashSet<>();
        for (JsonElement element : actions) {
            if (element.isJsonObject()) {
                canonicalPorts.add(string(element.getAsJsonObject(),
                        "symbol"));
            }
        }
        Map<String, Set<String>> bindingIdsByInstance =
                new LinkedHashMap<>();
        for (JsonElement element : bindings) {
            JsonObject binding = element.getAsJsonObject();
            String edgeId = string(binding, "edgeId");
            for (String field : new String[]{"fromRegionInstance",
                    "toRegionInstance"}) {
                String instance = string(binding, field);
                if (!instance.isEmpty() && !edgeId.isEmpty()) {
                    bindingIdsByInstance.computeIfAbsent(instance,
                            ignored -> new LinkedHashSet<>()).add(edgeId);
                }
            }
        }
        JsonObject original = goal.occurrenceInstantiationCatalog();
        JsonObject result = original.deepCopy();
        JsonArray occurrences = new JsonArray();
        for (JsonElement element : array(original, "occurrences")) {
            if (!element.isJsonObject()) continue;
            JsonObject occurrence = element.getAsJsonObject();
            JsonObject selected = occurrence.deepCopy();
            JsonArray portMap = new JsonArray();
            for (JsonElement mappingElement : array(occurrence,
                    "inputPortMap")) {
                if (mappingElement.isJsonObject()
                        && canonicalPorts.contains(string(
                        mappingElement.getAsJsonObject(),
                        "canonicalPort"))) {
                    portMap.add(mappingElement.deepCopy());
                }
            }
            selected.add("inputPortMap", portMap);
            JsonArray ids = new JsonArray();
            for (String id : bindingIdsByInstance.getOrDefault(
                    string(occurrence, "regionInstanceId"),
                    Collections.<String>emptySet())) {
                ids.add(id);
            }
            selected.add("bindingIds", ids);
            occurrences.add(selected);
        }
        result.add("occurrences", occurrences);
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
            OutputClosureContract outputClosure,
            JsonArray demandedBranches,
            String bindingInstance) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        OutputClosureContract.ExecutionScope scope = outputClosure == null
                ? null : outputClosure.executionScope();
        Set<String> guardDependent = definitions.guardDependentCells(
                exploredGuardOperands(demandedBranches));
        Set<String> exactOutputGuardDependent = scope == null
                ? Collections.<String>emptySet()
                : definitions.methodLocalGuardDependentCells(
                        demandedBranches);
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
            String outputDemand = scope == null ? ""
                    : outputSymbolicDemand(goal, action, definitions,
                    exactOutputGuardDependent, bindingInstance);
            if (scope != null && outputDemand.isEmpty()) {
                // Output capture is demand-first.  A broad static slice may
                // still contain replay-local payload and library state, but
                // absence of an exact incoming binding, explored guard use,
                // or authored state demand is not authority to turn that
                // value into a new solver dimension.
                binding.addProperty("symbolicDemand",
                        "CONCRETE_UNDEMANDED_OUTPUT_PAYLOAD");
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            if (scope != null
                    && string(binding, "symbolicDemand").isEmpty()) {
                binding.addProperty("symbolicDemand", outputDemand);
            }
            if (scope == null && unguardedPayloadLeaf(action, definitions,
                    guardDependent)) {
                // Symbolic freedom is only worth its cost when some explored
                // decision can read the value.  A leaf that is merely carried
                // into an encoding or a payload opens no new outcome, while
                // symbolising it turns every expression built from it
                // symbolic as well.
                binding.addProperty("symbolicDemand",
                        "CONCRETE_UNGUARDED_PAYLOAD");
                addInputAction(result, represented, binding,
                        InputActionCatalog.Mode.CONCRETE);
                continue;
            }
            if ("PROTOCOL_ARGUMENT".equals(location)
                    && !trustedIncomingProtocolBinding(
                    goal, string(action, "symbol"), bindingInstance)) {
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
                sites = exactExplicitFaultReturnSite(action, sites);
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

    /** Positive authority for one producer-side symbolic leaf. */
    private static String outputSymbolicDemand(
            Goal goal, JsonObject action, DefinitionIndex definitions,
            Set<String> guardDependent, String bindingInstance) {
        String authored = string(action, "symbolicDemand");
        if ("BOUNDED_CONTAINER_STATE".equals(authored)
                || "BOUNDED_STATE_FRONTIER".equals(authored)) {
            return authored;
        }
        if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                string(action, "sourceKind"))) {
            return "EXPLICIT_SYMBOLIC_FAULT";
        }
        if (trustedIncomingBinding(goal, string(action, "symbol"),
                bindingInstance)) {
            return "EXACT_INCOMING_COMPOSITION";
        }
        if (definitions.exactlyFeedsAny(action, guardDependent)) {
            return "EXACT_EXPLORED_GUARD_DEPENDENCE";
        }
        String location = string(action, "location");
        if ("ARGUMENT".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "PROTOCOL_RETURN".equals(location)) {
            return "EXACT_ROOT_INPUT_TO_OUTPUT";
        }
        return "";
    }

    static JsonArray exactExplicitFaultReturnSite(
            JsonObject action, JsonArray sites) {
        if (!RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                string(action, "sourceKind"))) {
            return sites;
        }
        String caller = string(action, "callerMethod");
        int unitIndex = integer(action, "unitIndex", -1);
        JsonArray exact = new JsonArray();
        if (caller.isEmpty() || unitIndex < 0) return exact;
        for (JsonElement element : sites) {
            if (!element.isJsonObject()) continue;
            JsonObject site = element.getAsJsonObject();
            if (caller.equals(string(site, "method"))
                    && unitIndex == integer(site, "unitIndex", -1)) {
                exact.add(site.deepCopy());
            }
        }
        return exact;
    }

    /**
     * Operands of the decisions this task actually reopens.  Branches kept as
     * replay assumptions are excluded: their recorded outcome is preserved by
     * the concrete value, so they demand no solver dimension.
     */
    private static Set<String> exploredGuardOperands(JsonArray branches) {
        Set<String> result = new LinkedHashSet<>();
        if (branches == null) {
            return result;
        }
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!"EXPLORE".equals(string(branch, "policy"))) continue;
            for (JsonElement operand : array(branch, "operandCells")) {
                String cell = operand.isJsonPrimitive()
                        ? operand.getAsString().trim() : "";
                if (!cell.isEmpty()) result.add(cell);
            }
        }
        return result;
    }

    /**
     * R1: a leaf earns a solver dimension only by being able to move some
     * explored decision.  The check is the fail-closed direction of that
     * rule: a leaf is released only when the dependence relation is known for
     * it and proves no explored guard reads it, so an unrecorded or
     * unrepresented cell keeps its symbolic demand.
     */
    private static boolean unguardedPayloadLeaf(
            JsonObject action, DefinitionIndex definitions,
            Set<String> guardDependent) {
        if (guardDependent.isEmpty()) {
            return false;
        }
        boolean represented = false;
        for (String cell : dependenceOrigins(action)) {
            if (guardDependent.contains(cell)) {
                return false;
            }
            represented |= definitions.knownCell(cell);
        }
        return represented;
    }

    private static List<String> dependenceOrigins(JsonObject action) {
        List<String> result = new ArrayList<>();
        for (JsonElement element : array(action, "dependencyCells")) {
            if (element.isJsonPrimitive()) {
                result.add(element.getAsString().trim());
            }
        }
        String cell = string(action, "cell");
        if (!cell.isEmpty() && !result.contains(cell)) {
            result.add(cell);
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
            Goal goal, String canonicalInput, String bindingInstance) {
        Set<String> acceptedPorts = exactInputPorts(goal, canonicalInput,
                bindingInstance);
        for (JsonElement element : goal.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (bindingInstance.equals(string(binding,
                    "toRegionInstance"))
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
        private final Map<String, List<String>> transferSources =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                transferSourcesByMethod = new LinkedHashMap<>();
        private final Set<String> transferCells = new LinkedHashSet<>();
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
                } else {
                    String target = string(edge, "toCell");
                    if (!source.isEmpty() && !target.isEmpty()) {
                        result.transferSources.computeIfAbsent(target,
                                ignored -> new ArrayList<>()).add(source);
                        String method = string(edge, "method");
                        if (!method.isEmpty()) {
                            result.transferSourcesByMethod.computeIfAbsent(
                                    method, ignored -> new LinkedHashMap<>())
                                    .computeIfAbsent(target,
                                            ignored -> new ArrayList<>())
                                    .add(source);
                        }
                        result.transferCells.add(source);
                        result.transferCells.add(target);
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

        private boolean knownCell(String cell) {
            return transferCells.contains(cell);
        }

        private boolean exactlyFeedsAny(JsonObject action,
                                        Set<String> demanded) {
            if (demanded.isEmpty()) return false;
            for (String cell : dependenceOrigins(action)) {
                if (demanded.contains(cell)) return true;
            }
            return false;
        }

        /**
         * Cells from which one of the given guard operands is still
         * reachable.  Resolving it once by reverse reachability costs one
         * graph traversal instead of one per candidate input port.
         */
        private Set<String> guardDependentCells(Collection<String> operands) {
            Set<String> result = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>(operands);
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!result.add(cell)) continue;
                work.addAll(transferSources.getOrDefault(cell,
                        Collections.<String>emptyList()));
            }
            return result;
        }

        /**
         * Exact producer guard demand never crosses a method boundary.  A
         * whole-program reverse walk can re-enter unrelated heap/library
         * paths through aliases and make every payload appear guard-relevant.
         * Inter-region values already have an explicit composition binding;
         * this walk is solely for the local branch the VM is asked to reopen.
         */
        private Set<String> methodLocalGuardDependentCells(
                JsonArray branches) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!"EXPLORE".equals(string(branch, "policy"))) continue;
                String site = string(branch, "siteId");
                int marker = site.lastIndexOf("#u");
                if (marker <= 0) continue;
                Map<String, List<String>> incoming =
                        transferSourcesByMethod.get(site.substring(0,
                                marker));
                if (incoming == null) continue;
                Deque<String> work = new ArrayDeque<>();
                for (JsonElement operand : array(branch, "operandCells")) {
                    if (operand.isJsonPrimitive()) {
                        work.add(operand.getAsString().trim());
                    }
                }
                while (!work.isEmpty()) {
                    String cell = work.removeFirst();
                    if (cell.isEmpty() || !result.add(cell)) continue;
                    work.addAll(incoming.getOrDefault(cell,
                            Collections.<String>emptyList()));
                }
            }
            return result;
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
                    JavaPrimitiveBoxing.unboxReturn(callReturnCell));
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
        private static final String TIMELINE_STEP_KIND =
                "SINGLE_WRITER_BOUNDED_CONTAINER_TIMELINE_STEP";
        private static final String MEMBER_PROJECTION_AUTHORITY =
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1";
        private final String regionId;
        private final Map<String, List<String>> inputPortsByCell =
                new LinkedHashMap<>();
        private final Map<String, String> inputCellByPort =
                new LinkedHashMap<>();
        private final Map<String, List<String>> outputPortsByCell =
                new LinkedHashMap<>();
        private final Map<String, String> outputCellByPort =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> inputRowsByPort =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> outputRowsByPort =
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
            indexPorts(array(row, "symbolicInputs"), inputRowsByPort);
            indexPorts(array(row, "outputs"), outputRowsByPort);
        }

        /**
         * Carries the finalizer's exact member identity into the canonical
         * output relation.  The VM still owns the transition formula; this
         * small contract only says which pre/post ports form one repeatable
         * single-writer step.
         */
        private OutputClosureContract withBoundedContainerTimeline(
                OutputClosureContract contract) {
            JsonObject envelope = contract.toJson();
            Map<String, JsonObject> causalEdgesById =
                    new LinkedHashMap<>();
            for (JsonElement element : array(envelope, "causalEdges")) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                causalEdgesById.put(string(edge, "edgeId"), edge);
            }
            boolean changed = false;
            for (JsonElement element : array(envelope, "members")) {
                if (!element.isJsonObject()) continue;
                JsonObject member = element.getAsJsonObject();
                JsonObject output = object(member, "output");
                JsonObject slice = object(member, "slice");
                JsonObject source = outputRowsByPort.get(
                        string(output, "portId"));
                if (source == null || !"MUTATION_POST_STATE".equals(
                        string(source, "boundedContainerStateRole"))) {
                    continue;
                }
                if (!hasMultipleDownstreamReaders(slice,
                        causalEdgesById)) {
                    continue;
                }
                JsonObject step = boundedContainerTimelineStep(
                        source, slice);
                if (step.size() == 0) continue;
                slice.add("boundedContainerTimelineStep", step);
                changed = true;
            }
            return changed ? OutputClosureCodec.decodeEnvelope(envelope)
                    : contract;
        }

        private static boolean hasMultipleDownstreamReaders(
                JsonObject slice,
                Map<String, JsonObject> causalEdgesById) {
            Set<String> readers = new LinkedHashSet<>();
            for (JsonElement element : array(slice, "causalEdgeIds")) {
                if (!element.isJsonPrimitive()) continue;
                JsonObject edge = causalEdgesById.get(
                        element.getAsString().trim());
                String instance = string(edge, "toRegionInstance");
                String input = string(edge, "toInputPort");
                if (instance.isEmpty() || input.isEmpty()) continue;
                readers.add(instance + "\n" + input);
                if (readers.size() >= 2) return true;
            }
            return false;
        }

        private JsonObject boundedContainerTimelineStep(
                JsonObject output, JsonObject slice) {
            JsonObject step = new JsonObject();
            step.addProperty("schemaVersion", 1);
            step.addProperty("kind", TIMELINE_STEP_KIND);
            step.addProperty("boundAuthority",
                    "ENGINE_STATE_CHAIN_BOUND_V1");
            step.addProperty("stateChainBound",
                    LoopBoundPolicy.MAX_STATE_TIMELINE_TRANSITIONS);
            step.addProperty("writerPolicy", "SINGLE_WRITER_REQUIRED");
            step.addProperty("postStatePort", string(slice,
                    "outputPort"));

            String admission = string(output,
                    "boundedContainerMemberProjectionAdmission");
            if (!"PROVED".equals(admission)
                    || !"SINGLE_WRITER_REQUIRED".equals(string(output,
                    "containerTimelineWriterPolicy"))) {
                step.addProperty("admission", "BLOCKED");
                step.addProperty("blocker", firstNonBlank(string(output,
                        "boundedContainerMemberProjectionBlocker"),
                        "MISSING_MEMBER_PROJECTION"));
                return step;
            }

            String preStatePort = string(slice, "containerPreStatePort");
            if (preStatePort.isEmpty()) {
                JsonArray candidates = array(output,
                        "boundedContainerPreStatePorts");
                if (candidates.size() == 1
                        && candidates.get(0).isJsonPrimitive()) {
                    preStatePort = candidates.get(0).getAsString().trim();
                }
            }
            JsonObject input = inputRowsByPort.get(preStatePort);
            JsonObject postProjection = selectedPostProjection(output,
                    longInteger(slice, "selectedRuntimeEventSeq", -1L));
            JsonObject preProjection = matchingProjection(input,
                    string(postProjection, "memberToken"), "PRE_STATE");
            String blocker = validateProjectionPair(preStatePort,
                    postProjection, preProjection);
            if (blocker.isEmpty()) {
                blocker = validateRestartableTransition(slice);
            }
            if (!blocker.isEmpty()) {
                step.addProperty("admission", "BLOCKED");
                step.addProperty("blocker", blocker);
                return step;
            }

            step.addProperty("admission", "PROVED");
            step.addProperty("authority", MEMBER_PROJECTION_AUTHORITY);
            step.addProperty("transitionGranularity",
                    "ONE_DEFINITION_INVOCATION");
            step.addProperty("transitionAuthority",
                    "EXACT_PRE_STATE_TO_NORMAL_DEFINITION_EXIT_V1");
            step.addProperty("preStatePort", preStatePort);
            step.addProperty("memberToken", string(postProjection,
                    "memberToken"));
            step.addProperty("writerLaneId", string(postProjection,
                    "writerLaneId"));
            step.addProperty("containerObjectId", longInteger(
                    postProjection, "containerObjectId", 0L));
            JsonArray projections = new JsonArray();
            projections.add(normalizedProjection(preProjection));
            projections.add(normalizedProjection(postProjection));
            step.add("memberProjections", projections);
            return step;
        }

        /**
         * Proves that the output relation is one restartable state
         * transition, rather than a prefix ending at an arbitrary execution
         * of a mutator inside a long-running root.  Internal mutations remain
         * VM semantics; this contract only certifies their shared pre/post
         * activation boundary.
         */
        private static String validateRestartableTransition(
                JsonObject slice) {
            if (!"DEFINITION_INVOCATION_NORMAL_EXIT".equals(string(slice,
                    "outputBoundaryKind"))
                    || !"EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1"
                    .equals(string(slice, "containerPreStateAuthority"))) {
                return "MISSING_RESTARTABLE_TRANSITION_BOUNDARY";
            }
            long definition = longInteger(slice,
                    "observedDefinitionCallId", -1L);
            long pre = longInteger(slice, "containerPreStateEventSeq", -1L);
            long selected = longInteger(slice,
                    "selectedRuntimeEventSeq", -1L);
            long completion = longInteger(slice,
                    "definitionCompletionSeq", -1L);
            int folded = integer(slice, "foldedMutationCount", -1);
            JsonArray completions = array(slice,
                    "foldedMutationCompletionSeqs");
            if (definition <= 0L || pre < 0L || selected < pre
                    || completion < selected || folded < 1
                    || completions.size() != folded) {
                return "INCOMPLETE_RESTARTABLE_TRANSITION_EVIDENCE";
            }
            boolean selectedMutation = false;
            long previous = -1L;
            for (JsonElement element : completions) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isNumber()) {
                    return "MALFORMED_MUTATION_COMPLETION_SEQUENCE";
                }
                long event = element.getAsLong();
                if (event < pre || event > completion
                        || previous >= event) {
                    return "MALFORMED_MUTATION_COMPLETION_SEQUENCE";
                }
                selectedMutation |= event == selected;
                previous = event;
            }
            return selectedMutation ? ""
                    : "SELECTED_MUTATION_OUTSIDE_TRANSITION";
        }

        private static JsonObject selectedPostProjection(
                JsonObject output, long selectedEvent) {
            if (selectedEvent >= 0L) {
                JsonObject selected = null;
                for (JsonElement element : array(output,
                        "runtimeAccesses")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject access = element.getAsJsonObject();
                    JsonObject projection = object(access,
                            "boundedContainerMemberProjection");
                    if (longInteger(access, "eventSeq", -1L)
                            != selectedEvent || projection.size() == 0) {
                        continue;
                    }
                    if (selected != null) return new JsonObject();
                    selected = projection;
                }
                if (selected != null) return selected.deepCopy();
            }
            JsonObject selected = null;
            for (JsonElement element : array(output,
                    "boundedContainerMemberProjections")) {
                if (!element.isJsonObject()
                        || !"POST_STATE".equals(string(
                        element.getAsJsonObject(), "stateRole"))) {
                    continue;
                }
                if (selected != null) return new JsonObject();
                selected = element.getAsJsonObject();
            }
            return selected == null ? new JsonObject()
                    : selected.deepCopy();
        }

        private static JsonObject matchingProjection(
                JsonObject port, String token, String role) {
            if (port == null || token.isEmpty()) return new JsonObject();
            JsonObject selected = null;
            for (JsonElement element : array(port,
                    "boundedContainerMemberProjections")) {
                if (!element.isJsonObject()) continue;
                JsonObject projection = element.getAsJsonObject();
                if (!token.equals(string(projection, "memberToken"))
                        || !role.equals(string(projection, "stateRole"))) {
                    continue;
                }
                if (selected != null) return new JsonObject();
                selected = projection;
            }
            return selected == null ? new JsonObject()
                    : selected.deepCopy();
        }

        private static String validateProjectionPair(
                String preStatePort, JsonObject post, JsonObject pre) {
            if (preStatePort.isEmpty() || pre.size() == 0
                    || post.size() == 0) {
                return "MISSING_PRE_OR_POST_MEMBER_PROJECTION";
            }
            String token = string(post, "memberToken");
            String lane = string(post, "writerLaneId");
            long container = longInteger(post, "containerObjectId", 0L);
            if (token.isEmpty() || lane.isEmpty() || container <= 0L
                    || !MEMBER_PROJECTION_AUTHORITY.equals(string(post,
                    "identityAuthority"))
                    || !token.equals(string(pre, "memberToken"))
                    || !lane.equals(string(pre, "writerLaneId"))
                    || container != longInteger(pre, "containerObjectId",
                    0L)
                    || !sameLeaves(pre, post)) {
                return "MISMATCHED_MEMBER_OR_WRITER_PROJECTION";
            }
            return "";
        }

        private static boolean sameLeaves(JsonObject left,
                                          JsonObject right) {
            JsonArray leftLeaves = array(left, "leaves");
            JsonArray rightLeaves = array(right, "leaves");
            if (leftLeaves.size() == 0 || rightLeaves.size() == 0) {
                return false;
            }
            Set<String> first = new LinkedHashSet<>();
            Set<String> second = new LinkedHashSet<>();
            boolean present = false;
            for (JsonElement element : leftLeaves) {
                if (!element.isJsonObject()) return false;
                JsonObject leaf = element.getAsJsonObject();
                present |= "PRESENT".equals(string(leaf, "kind"));
                first.add(projectionLeafKey(leaf));
            }
            for (JsonElement element : rightLeaves) {
                if (!element.isJsonObject()) return false;
                second.add(projectionLeafKey(element.getAsJsonObject()));
            }
            return present && first.equals(second) && !first.contains("");
        }

        private static String projectionLeafKey(JsonObject leaf) {
            String kind = string(leaf, "kind");
            String javaType = string(leaf, "javaType");
            String field = string(leaf, "field");
            if (kind.isEmpty() || javaType.isEmpty()
                    || "VALUE_FIELD".equals(kind) && field.isEmpty()) {
                return "";
            }
            return kind + "\n" + javaType + "\n" + field;
        }

        private static JsonObject normalizedProjection(JsonObject source) {
            JsonObject result = source.deepCopy();
            // Event ids prove the discovery attachment but are not replay
            // identity and must not leak into the repeated transition.
            for (JsonElement element : array(result, "leaves")) {
                if (element.isJsonObject()) {
                    element.getAsJsonObject().remove("fieldEventSeq");
                }
            }
            return result;
        }

        private static void indexPorts(JsonArray rows,
                                       Map<String, JsonObject> target) {
            for (JsonElement element : rows) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String id = string(row, "portId");
                if (id.isEmpty()) continue;
                JsonObject previous = target.put(id, row.deepCopy());
                if (previous != null) {
                    target.put(id, new JsonObject());
                }
            }
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
            Map<String, JsonObject> selectedBindings =
                    selectedProjectedBindings(goal, projection);
            JsonObject occurrenceCatalog =
                    goal.occurrenceInstantiationCatalog();
            OutputClosureContract closure = projectClosure(goal,
                    projection, selectedBindings, occurrenceCatalog);
            JsonArray symbolize = projectSymbolize(goal,
                    closure.executionScope().inputPorts());
            JsonArray branches = projectBranches(goal, closure,
                    closure.executionScope().branchSites());
            JsonObject catalog = projectOccurrenceCatalog(projection,
                    closure.executionScope().inputPorts(), selectedBindings,
                    occurrenceCatalog);
            return new ProjectedProducer(closure, symbolize, branches,
                    catalog);
        }

        private static OutputClosureContract projectClosure(
                Goal goal, ProducerOutputProjection projection,
                Map<String, JsonObject> selectedBindings,
                JsonObject occurrenceCatalog) {
            OutputClosureContract original = goal.outputClosure();
            if (original == null) {
                throw new IllegalArgumentException(
                        "producer projection requires output closure");
            }
            Set<String> producerInstances = new LinkedHashSet<>();
            Map<String, String> canonicalOutputByExact =
                    new LinkedHashMap<>();
            for (JsonElement element : array(occurrenceCatalog,
                    "occurrences")) {
                if (!element.isJsonObject()) continue;
                JsonObject occurrence = element.getAsJsonObject();
                String instance = string(occurrence,
                        "regionInstanceId");
                if (instance.isEmpty() || !producerInstances.add(instance)) {
                    throw new IllegalArgumentException(
                            "projected producer occurrence is missing or "
                                    + "duplicated");
                }
                for (JsonElement mappingElement : array(occurrence,
                        "outputPortMap")) {
                    if (!mappingElement.isJsonObject()) continue;
                    JsonObject mapping = mappingElement.getAsJsonObject();
                    String canonical = string(mapping, "canonicalPort");
                    String exact = string(mapping, "exactPort");
                    if (canonical.isEmpty() || exact.isEmpty()) {
                        throw new IllegalArgumentException(
                                "projected producer output mapping is "
                                        + "incomplete for " + instance);
                    }
                    String key = instance + "\n" + exact;
                    String prior = canonicalOutputByExact.putIfAbsent(key,
                            canonical);
                    if (prior != null && !prior.equals(canonical)) {
                        throw new IllegalArgumentException(
                                "ambiguous exact producer output mapping: "
                                        + key);
                    }
                }
            }

            Map<String, Set<String>> edgesByCanonicalOutput =
                    new LinkedHashMap<>();
            for (JsonObject binding : selectedBindings.values()) {
                String instance = string(binding, "fromRegionInstance");
                if (!producerInstances.contains(instance)) continue;
                String exact = string(binding, "fromOutputPort");
                String canonical = canonicalOutputByExact.get(
                        instance + "\n" + exact);
                if (canonical == null) {
                    throw new IllegalArgumentException(
                            "selected exact producer edge has no canonical "
                                    + "output mapping: "
                                    + string(binding, "edgeId"));
                }
                if (!projection.outputPorts().contains(canonical)) {
                    continue;
                }
                edgesByCanonicalOutput.computeIfAbsent(canonical,
                        ignored -> new LinkedHashSet<>()).add(
                        string(binding, "edgeId"));
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
                for (String id : edgesByCanonicalOutput.getOrDefault(port,
                        Collections.<String>emptySet())) {
                    selectedIds.add(id);
                    causalIds.add(id);
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
            for (String id : causalIds) {
                // causalIds are populated exclusively from selectedBindings.
                edges.add(selectedBindings.get(id).deepCopy());
            }
            envelope.add("members", members);
            envelope.add("causalEdges", edges);
            return edu.uva.liftlab.graphchecker.contract.OutputClosureCodec
                    .decodeEnvelope(envelope);
        }

        private static Map<String, JsonObject> selectedProjectedBindings(
                Goal goal, ProducerOutputProjection projection) {
            Map<String, JsonObject> result = new LinkedHashMap<>();
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
                JsonObject prior = result.putIfAbsent(id, binding);
                if (prior != null && !CanonicalJson.render(prior).equals(
                        CanonicalJson.render(binding))) {
                    throw new IllegalArgumentException(
                            "duplicate projected edge has conflicting "
                                    + "occurrence projection " + id);
                }
            }
            if (!result.keySet().equals(projection.edgeIds())) {
                Set<String> missing = new LinkedHashSet<>(
                        projection.edgeIds());
                missing.removeAll(result.keySet());
                throw new IllegalArgumentException("projected edges are "
                        + "absent from goal ledger: " + missing);
            }
            return result;
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
                ProducerOutputProjection projection, Set<String> inputPorts,
                Map<String, JsonObject> bindingById,
                JsonObject original) {
            String canonical = string(original,
                    "canonicalRegionInstanceId");
            Set<String> touchedInstances = new LinkedHashSet<>();
            for (JsonObject binding : bindingById.values()) {
                touchedInstances.add(string(binding,
                        "fromRegionInstance"));
                touchedInstances.add(string(binding, "toRegionInstance"));
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
        private final JsonArray targetEdgeBindings;

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryRegionInstanceId,
                          JsonObject queryOccurrence,
                          ProducerOutputProjection projection,
                          OutputClosureContract projectedOutputClosure,
                          JsonObject occurrenceCatalog) {
            this(goal, branches, target, hasRequiredWitness, inputActions,
                    ready, queryRegionInstanceId, queryOccurrence,
                    projection, projectedOutputClosure, occurrenceCatalog,
                    null);
        }

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryRegionInstanceId,
                          JsonObject queryOccurrence,
                          ProducerOutputProjection projection,
                          OutputClosureContract projectedOutputClosure,
                          JsonObject occurrenceCatalog,
                          JsonArray targetEdgeBindings) {
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
            this.targetEdgeBindings = targetEdgeBindings == null
                    ? null : targetEdgeBindings.deepCopy();
        }

        private OutputClosureContract outputContract() {
            return goal.kind().capturesOutputRelation()
                    ? (projectedOutputClosure == null
                    ? goal.outputClosure() : projectedOutputClosure) : null;
        }

        /**
         * Purely semantic task identity: region content hash x path seed x
         * exact port set (x target predicate for reach goals).
         *
         * <p>Trace-run ordinals deliberately do not participate.  The
         * previous identity hashed {@code logicalRegionId} (which embeds a
         * per-recording runtime owner id) and {@code goalId} (minted from a
         * {@code regionInstanceId} that embeds a trace root call id), so a
         * fresh recording of the semantically identical closure renamed
         * every task and orphaned every previously imported summary.  All
         * components below survive re-recording as long as the closure
         * semantics are unchanged; the importer's pairing is untouched
         * because results echo whatever id the scheduled plan carried, and
         * summary reuse still requires the full canonical task payload to
         * match.</p>
         */
        private String seedTaskId() {
            StringBuilder identity = new StringBuilder(
                    "TASK.SEED.SEMANTIC.V3");
            identity.append('\n').append(goal.plan().regionId());
            identity.append('\n').append(goal.kind().name());
            identity.append('\n').append(regionContentHash());
            identity.append('\n').append(goal.pathSeedKey());
            identity.append('\n').append(portSetHash());
            identity.append('\n').append(target.siteId)
                    .append('\n').append(target.selectedOccurrence)
                    .append('\n').append(target.observedOutcome)
                    .append('\n').append(target.desiredOutcome)
                    .append('\n').append(projection == null
                            ? "UNPROJECTED" : "PROJECTED_OUTPUT");
            return "TASK.SEED." + ArtifactIO.sha256(identity.toString());
        }

        /** Sorted definition methods and explored branch sites. */
        private String regionContentHash() {
            java.util.TreeSet<String> methods = new java.util.TreeSet<>(
                    goal.runtimeDefinitionMethods());
            java.util.TreeSet<String> sites = new java.util.TreeSet<>();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                String site = string(element.getAsJsonObject(), "siteId");
                if (!site.isEmpty()) sites.add(site);
            }
            return ArtifactIO.sha256(String.join("\n", methods)
                    + "\n--BRANCH-SITES--\n" + String.join("\n", sites));
        }

        /**
         * Canonical ordinal-free port descriptors.  Runtime port ids embed
         * trace call ids, so the identity uses each port's static semantic
         * shape instead: location/cell/site/declared field path for inputs,
         * and cell/kind/type plus static capture endpoints (with their
         * replay-stable bounded occurrence) for demanded outputs.
         */
        private String portSetHash() {
            java.util.TreeSet<String> descriptors = new java.util.TreeSet<>();
            for (JsonElement element : inputActions) {
                if (!element.isJsonObject()) continue;
                descriptors.add("IN\n" + semanticPortDescriptor(
                        element.getAsJsonObject()));
            }
            OutputClosureContract contract = outputContract();
            if (contract == null) {
                descriptors.add("OUT\nNO_OUTPUT_RELATION");
            } else {
                for (OutputClosureContract.Member member
                        : contract.members()) {
                    StringBuilder descriptor = new StringBuilder("OUT");
                    descriptor.append('\n').append(member.cell());
                    descriptor.append('\n').append(member.outputKind());
                    descriptor.append('\n').append(
                            member.javaTypeDescriptor());
                    java.util.TreeSet<String> captures =
                            new java.util.TreeSet<>();
                    for (JsonElement capture : member.captures()) {
                        if (!capture.isJsonObject()) continue;
                        captures.add(semanticPortDescriptor(
                                capture.getAsJsonObject()));
                    }
                    for (String capture : captures) {
                        descriptor.append("\n--CAPTURE--\n")
                                .append(capture);
                    }
                    JsonObject timeline = object(member.slice(),
                            "boundedContainerTimelineStep");
                    if (timeline.size() == 0) {
                        descriptor.append("\n--TIMELINE--\nONE_SHOT");
                    } else {
                        JsonObject semanticTimeline = new JsonObject();
                        for (String field : SEMANTIC_TIMELINE_FIELDS) {
                            JsonElement value = timeline.get(field);
                            if (value != null && !value.isJsonNull()) {
                                semanticTimeline.add(field, value);
                            }
                        }
                        descriptor.append("\n--TIMELINE--\n")
                                .append(CanonicalJson.render(
                                        semanticTimeline));
                    }
                    descriptors.add(descriptor.toString());
                }
            }
            return ArtifactIO.sha256(String.join(
                    "\n==PORT==\n", descriptors));
        }

        /** Static, replay-stable fields of one port/capture row. */
        private static final String[] SEMANTIC_PORT_FIELDS = {
                "accessFieldSignature", "accessSites", "argumentIndex",
                "boundedContainerStateRole", "captureKind", "cell",
                "containerCapacity", "declaredCallee", "definitionMethod",
                "definitionUnitIndex", "dependencyRole", "fieldPath",
                "fieldPathDeclarations", "fieldPaths", "fieldSignature",
                "helperActivationBoundedOccurrence", "javaType",
                "leafFieldSignature", "location", "outputCell",
                "outputOccurrence", "outputSiteId", "protocolDirection",
                "replayOccurrence", "rootKind", "rootMethod", "siteId",
                "sourceKind", "symbolicDemand"};

        private static final String[] SEMANTIC_TIMELINE_FIELDS = {
                "admission", "authority", "boundAuthority", "kind",
                "schemaVersion", "stateChainBound",
                "transitionAuthority", "transitionGranularity",
                "writerPolicy"};

        private static String semanticPortDescriptor(JsonObject row) {
            JsonObject filtered = new JsonObject();
            for (String field : SEMANTIC_PORT_FIELDS) {
                JsonElement value = row.get(field);
                if (value != null && !value.isJsonNull()) {
                    filtered.add(field, value);
                }
            }
            return CanonicalJson.render(filtered);
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

    private static final class LoadedInputs {
        private final List<JsonObject> regionPlans;
        private final List<JsonObject> summaries;
        private final Map<String, Region> regionIndex;
        private final DefinitionIndex definitions;
        private final MergePlan mergePlan;
        private final JsonObject regionPlanIdentity;

        private LoadedInputs(List<JsonObject> regionPlans,
                             List<JsonObject> summaries,
                             Map<String, Region> regionIndex,
                             DefinitionIndex definitions,
                             MergePlan mergePlan,
                             JsonObject regionPlanIdentity) {
            this.regionPlans = regionPlans;
            this.summaries = summaries;
            this.regionIndex = regionIndex;
            this.definitions = definitions;
            this.mergePlan = mergePlan;
            this.regionPlanIdentity = regionPlanIdentity;
        }
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
        public final boolean targetFirst;
        public final int maxJobs;
        public final int maxLoopIterations;

        private Arguments(Path regions, Path regionPlan,
                          Path edgeValidations, Path refinedGraph,
                          Path summaries, Path producerProjection,
                          Path outputDirectory, String regionId,
                          String regionInstanceId, String goalId,
                          String targetSite, boolean targetFirst, int maxJobs,
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
            this.targetFirst = targetFirst;
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
            boolean targetFirst = Boolean.parseBoolean(
                    values.getOrDefault("target-first", "false"));
            if (targetFirst && (producerProjection != null
                    || !firstNonBlank(values.get("region-id")).isEmpty()
                    || !firstNonBlank(values.get("region-instance-id"))
                    .isEmpty()
                    || !firstNonBlank(values.get("goal-id")).isEmpty()
                    || !firstNonBlank(values.get("target-site")).isEmpty())) {
                throw new IllegalArgumentException("--target-first cannot "
                        + "be combined with goal filters or "
                        + "--producer-projection");
            }
            return new Arguments(regions, regionPlan, edges, refinedGraph,
                    summaries, producerProjection, output,
                    firstNonBlank(values.get("region-id")),
                    firstNonBlank(values.get("region-instance-id")),
                    firstNonBlank(values.get("goal-id")),
                    firstNonBlank(values.get("target-site")),
                    targetFirst,
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
                    || "target-first".equals(key)
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

        private Arguments forSelection(
                RuntimeWorkflowDiscovery.Selection selection) {
            return new Arguments(regions, regionPlan, edgeValidations,
                    refinedGraph, summaries, null, outputDirectory,
                    selection.regionId, selection.regionInstanceId,
                    selection.goalId, "", false, 1,
                    maxLoopIterations);
        }

    }
}
